/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import static edu.mit.csail.sdg.alloy4.Util.tail;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import scala.collection.JavaConverters;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitReturn;

import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.App;
import fortress.msfol.BuiltinApp;
import fortress.msfol.Closure;
import fortress.msfol.Eq;
import fortress.msfol.Forall;
import fortress.msfol.FuncDecl;
import fortress.msfol.Implication;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.ReflexiveClosure;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

/**
 * Translate an Alloy AST into Fortress AST then attempt to solve it using Fortress.
 */

public final class TranslateAlloyToFortress extends VisitReturn<Object> {
    /**
     * If frame!=null, it stores the scope, bounds, and other settings necessary for
     * performing a solve.
     */
    private final A4Solution                  frame;

    /** The current reporter. */
    private A4Reporter                        rep;

    private final A4Options                   opt;

    /** If nonnull, it's the current command. */
    private final Command                     cmd;

    private final TheoryComputer              tc;

    /** The unique name generator. */
    private final NameGenerator               nameGenerator; 

    private final List<Func>                  current_function = new ArrayList<Func>();

    private Env<ExprVar, Var>                 env              = new Env<ExprVar, Var>();

    private Env<ExprVar, Expr>                letMappings      = new Env<ExprVar, Expr>();

    private Map<Expr, FuncDecl>               cache            = new HashMap<Expr, FuncDecl>();
    private Map<String, FuncDecl>             closureCache      = new HashMap<String, FuncDecl>();
    private Map<String, FuncDecl>             cardinCache      = new HashMap<String, FuncDecl>();

    private Env<Expr, List<Var>>              envVars          = new Env<Expr, List<Var>>();

    private int                               funcCount;
    /**
     * Construct a translator based on the given list of sigs and the given command.
     *
     * @param rep - if nonnull, it's the reporter that will receive diagnostics and
     *            progress reports
     * @param opt - the solving options (must not be null)
     * @param sigs - the list of sigs (must not be null, and must be a complete
     *            list)
     * @param cmd - the command to solve (must not be null)
     */
    private TranslateAlloyToFortress(A4Solution sol, ScopeComputer sc, A4Reporter rep, A4Options opt, Iterable<Sig> sigs, Command cmd) throws Err {
        this.opt = opt;
        this.rep = (rep != null) ? rep : A4Reporter.NOP;
        this.cmd = cmd;
        this.frame = sol;
        this.tc = TheoryComputer.compute(rep, frame, sigs, sc, opt);
        this.nameGenerator = tc.nameGenerator();
        this.funcCount = 0;
    }

    /**
     * Conjoin the constraints for "field declarations" and "fact" paragraphs
     */
    private void makeFacts(Expr facts, Iterable<Sig> sigs) throws Err {
        // add the field facts and appended facts
        for (Sig s : sigs) {
            if (s.builtin || (opt.orderingModule && s.label.split("/")[1].equals("Ord")))
                continue;
            for (Decl d : s.getFieldDecls()) {
                for (ExprHasName n : d.names) {
                    Field f = (Field) n;
                    Expr form = s.decl.get().join(f).in(d.expr);
                    // if (s.isOne != null)
                    //     throw new RuntimeException("Not implemented yet!");
                    // form = s.isOne == null ? form.forAll(s.decl) : ExprLet.make(null, (ExprVar) (s.decl.get()), s, form);
                    final Expr dexexpr = addOne(s.decl.expr);
                    Sort sort = getSorts(dexexpr).get(0);
                    ExprHasName dex = s.decl.names.get(0);
                    String label = skolem(dex.label);
                    final Var v = Term.mkVar(nameGenerator.freshName(label));
                    env.put((ExprVar) dex, v);
                    envVars.put(dexexpr, List.of(v));
                    Term tmp = cterm(dexexpr);
                    envVars.remove(dexexpr);
                    frame.addDecl(v.of(sort), new Pair<String, Type>(label, dexexpr.type()));
                    Term t = isIn(s.decl.get().join(f), d.expr, true);
                    if (t != Term.mkTop())
                        frame.addAxiom(getQtTerm(false, List.of(v.of(sort)), List.of(tmp), t));
                    env.remove((ExprVar) dex);
                }
                if (s.isOne == null && d.disjoint2 != null)
                    throw new RuntimeException("Not implemented yet!");
                if (d.names.size() > 1 && d.disjoint != null)
                    throw new RuntimeException("Not implemented yet!");
            }
            for (Expr f : s.getFacts()) {
                Expr form = s.isOne == null ? f.forAll(s.decl) : ExprLet.make(null, (ExprVar) (s.decl.get()), s, f);
                frame.addAxiom(cterm(form));
            }
        }
        recursiveAddFormula(facts);
    }

    /**
     * Break up x into conjuncts then add them each as a fact.
     */
    private void recursiveAddFormula(Expr x) throws Err {
        if (x instanceof ExprList && ((ExprList) x).op == ExprList.Op.AND) {
            for (Expr e : ((ExprList) x).args)
                recursiveAddFormula(e);
        } else {
            frame.addAxiom(cterm(x));
        }
    }

    /**
     * Based on the specified "options", execute one command and return the
     * resulting A4Solution object.
     *
     * @param sol - A4Solution object created by Kodkod
     * @param rep - if nonnull, we'll send compilation diagnostic messages to it
     * @param sigs - the list of sigs; this list must be complete
     * @param cmd - the Command to execute
     */
    public static void translate(A4Solution sol, ScopeComputer sc, A4Reporter rep, A4Options opt, Iterable<Sig> sigs, Command cmd) throws Err {
        TranslateAlloyToFortress tr = null;
        try {
            tr = new TranslateAlloyToFortress(sol, sc, rep, opt, sigs, cmd);
            tr.makeFacts(cmd.formula, sigs);
        } catch (UnsatisfiedLinkError ex) {
            throw new ErrorFatal("The required JNI library cannot be found: " + ex.toString().trim(), ex);
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    // ==============================================================================================================//

    /**
     * Convenience method that evaluates x and casts the result to be a Fortress Term.
     *
     * @return the axiom - if x evaluates to a Term
     * @throws ErrorFatal - if x does not evaluate to a Term
     */
    private Term cterm(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object y = visitThis(x);
        if (y instanceof Term)
            return (Term) y;
        throw new ErrorFatal(x.span(), "This should have been a term.\nInstead it is " + y);
    }

    /**
     * Convenience method that evaluаtes x and cast the result to be a Fortress FuncDecl
     *
     * @return the expression - if x evaluates to an Expression
     * @throws ErrorFatal - if x does not evaluate to an Expression
     */
    private FuncDecl cfunc(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object obj = visitThis(x);
        if (obj instanceof FuncDecl)
            return (FuncDecl) obj;
        throw new ErrorFatal(x.span(), "This should have been a function.\nInstead it is " + obj);
    }

    /**
     * Given a variable name "name", prepend the current function name to form a
     * meaningful "skolem name". 
     */
    private String skolem(String name) {
        if (current_function.size() == 0) {
            if (cmd != null && cmd.label.length() > 0 && cmd.label.indexOf('$') < 0)
                return cmd.label + "_" + name;
            else
                return name;
        }
        Func last = current_function.get(current_function.size() - 1);
        String funcname = tail(last.label);
        if (funcname.indexOf('$') < 0)
            return funcname + "_" + name;
        else
            return name;
    }

    private String getFreshFunc() {
        funcCount++;
        return "func_"+funcCount;
    }

    private List<Sort> getSorts(Expr e) {
        Type.ProductType it = removeRClosure(e).type().iterator().next();
        List<Sort> sorts = new ArrayList<>(it.arity());
        for (int i = 0; i < it.arity(); i++) {
            Sort tmp = frame.a2s(it.get(i));
            if (tmp != null)
                sorts.add(tmp);
            else if (frame.a2c(it.get(i)) != null)
                sorts.add(frame.a2c(it.get(i)).sort());
            else
                sorts.add(cfunc(it.get(i)).argSorts().head());
        }
        return sorts;
    }

    private List<Var> getVars(int numVars) {
        List<Var> vars = new ArrayList<>();
        for (int i = 0; i < numVars; i++)
            vars.add(tc.getFreshVar());
        return vars;
    }

    private List<AnnotatedVar> getAnnotatedVars(List<Var> vars, List<Sort> sorts) {
        List<AnnotatedVar> avars = new ArrayList<>();
        for (int i = 0; i < vars.size(); i++)
            avars.add(vars.get(i).of(sorts.get(i)));
        return avars;
    }

    private Term compareVars(List<Var> vars, List<Var> vars2) {
        Term t = Term.mkEq(vars.get(0), vars2.get(0));
        for (int i = 1; i < vars.size(); i++)
            t = Term.mkAnd(t, Term.mkEq(vars.get(i), vars2.get(i)));
        return t;
    }

    private Expr removeExprUnary(Expr a) {
        if (a instanceof ExprUnary)
            return ((ExprUnary) a).sub;
        return a;
    }

    private boolean isExprVar(Expr a) {
        a = removeExprUnary(a);
        if (a instanceof ExprVar)
            return !letMappings.has((ExprVar) a);
        if (a instanceof Sig)
            return frame.a2c((Sig) a) != null;
        return false;
    }

    private Expr getLetMappingIfAny(Expr a) {
        Expr b = null;
        if (a instanceof ExprVar)
            b = letMappings.get((ExprVar) a);
        if (a instanceof ExprUnary && ((ExprUnary) a).sub instanceof ExprVar)
            b = letMappings.get((ExprVar) ((ExprUnary) a).sub);
        return b == null ? a : b;
    }

    private Expr removeRClosure(Expr e) {
        if (e instanceof ExprUnary && ((ExprUnary) e).op != ExprUnary.Op.TRANSPOSE)
            return ((ExprUnary) e).sub;
        if (e instanceof ExprBinary && ((ExprBinary) e).op == ExprBinary.Op.JOIN) {
            ExprBinary eb = (ExprBinary) e;
            return ExprBinary.Op.JOIN.make(e.pos, e.closingBracket, removeRClosure(eb.left), removeRClosure(eb.right));
        }
        return e;
    }

    private static List<List<Term>> getCartesianProduct(List<List<Term>> values) {
        List<List<Term>> combos = new ArrayList<>();
        if (values.isEmpty()) {
            combos.add(new ArrayList<>());
            return combos;
        } else {
            process(values, combos);
        }
        return combos;
    }

    private static void process(List<List<Term>> values, List<List<Term>> combos) {
        List<Term> head = values.get(0);
        List<List<Term>> tail = getCartesianProduct(values.subList(1, values.size()));

        for (Term h : head) {
            for (List<Term> t : tail) {
                List<Term> tmp = new ArrayList<>(t.size());
                tmp.add(h);
                tmp.addAll(t);
                combos.add(tmp);
            }
        }
    }

    private static Term helperForall(List<AnnotatedVar> avars, Term t) {
        if (avars.size() == 0)
            return t;
        return Term.mkForall(avars, t);
    }

    private static boolean isApp(Term t) {
        return t instanceof App || t instanceof Closure || t instanceof ReflexiveClosure;
    }

    private static Term helperEqApp(Eq eq, Term t) {
        App app = null;
        if (t instanceof App)
            app = (App) t;
        else if (t instanceof Closure) {
            Closure c = (Closure) t;
            app = (App) Term.mkApp(c.getFunctionName(), c.getArguments());
        } else if (t instanceof ReflexiveClosure) {
            ReflexiveClosure rc = (ReflexiveClosure) t;
            app = (App) Term.mkApp(rc.getFunctionName(), rc.getArguments());
        }
        List<Term> args = new ArrayList<>(app.getArguments());
        for (int i = 0; i < args.size(); i++) {
            if (args.get(i) == eq.right()) {
                args.set(i, eq.left());
                break;
            }
        }
        app = (App) Term.mkApp(app.getFunctionName(), args);
        if (t instanceof Closure) {
            Closure c = (Closure) t;
            Term arg1 = c.arg1() == eq.right() ? eq.left() : c.arg1();
            Term arg2 = c.arg2() == eq.right() ? eq.left() : c.arg2();
            return Term.mkClosure(app, arg1, arg2);
        } else if (t instanceof ReflexiveClosure) {
            ReflexiveClosure rc = (ReflexiveClosure) t;
            Term arg1 = rc.arg1() == eq.right() ? eq.left() : rc.arg1();
            Term arg2 = rc.arg2() == eq.right() ? eq.left() : rc.arg2();
            return Term.mkClosure(app, arg1, arg2);
        }
        return app;
    }

    private final class BoundVariableEliminator extends VisitReturn<Expr> {

        public List<ExprVar> boundVars;
        public boolean hasLetMappings = false;

        public BoundVariableEliminator(List<ExprVar> boundVars, Expr e) {
            this.boundVars = new ArrayList<>(boundVars);
            visitThis(e);
        }

        public BoundVariableEliminator(Expr e) {
            this.boundVars = new ArrayList<>();
            visitThis(e);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprITE x) throws Err {
            return visitThis(x.cond).ite(visitThis(x.left), visitThis(x.right));
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprLet x) throws Err {
            return ExprLet.make(x.pos, (ExprVar) visitThis(x.var), visitThis(x.expr), visitThis(x.sub));
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprConstant x) throws Err {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprUnary x) throws Err {
            return x.op.make(x.pos, visitThis(x.sub));
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprVar x) throws Err {
            if (letMappings.has(x)) {
                BoundVariableEliminator bve = new BoundVariableEliminator(letMappings.get(x));
                boundVars.addAll(bve.boundVars);
                this.hasLetMappings = true;
            } else if (!boundVars.contains(x)) {
                boundVars.add(x);
                env.put(x, tc.getFreshVar());
            }
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(Field x) throws Err {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(Sig x) throws Err {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprCall x) throws Err {
            List<Expr> args = new ArrayList<>();
            for (int i = 0; i < x.args.size(); i++) {
                args.add(visitThis(x.args.get(i)));
            }
            return ExprCall.make(x.pos, x.closingBracket, x.fun, args, x.extraWeight);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprList x) throws Err {
            List<Expr> args = new ArrayList<>();
            for (int i = 0; i < x.args.size(); i++) {
                args.add(visitThis(x.args.get(i)));
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, args);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprBinary x) throws Err {
            return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprQt x) throws Err {
            return x.op.make(x.pos, x.closingBracket, x.decls, visitThis(x.sub));
        }
    }
    // ==============================================================================================================//

    /* ============================ */
    /* Evaluates an ExprITE node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprITE x) throws Err {
        Term t = cterm(x.cond);
        if (x.left.type().is_bool)
            return Term.mkIfThenElse(t, cterm(x.left), cterm(x.right));
        // TODO: handle expressions
        throw new RuntimeException("Not implemented yet!");
    }

    /* ============================ */
    /* Evaluates an ExprLet node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprLet x) throws Err {
        letMappings.put(x.var, x.expr);
        if (envVars.has(x))
            envVars.put(x.sub, envVars.get(x));
        Object o = visitThis(x.sub);
        envVars.remove(x.sub);
        letMappings.remove(x.var);
        return o;
    }

    /* ================================= */
    /* Evaluates an ExprConstant node. */
    /* ================================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprConstant x) throws Err {
        switch (x.op) {
            case MIN :
                throw new RuntimeException("Not implemented yet!");
            case MAX :
                throw new RuntimeException("Not implemented yet!");
            case NEXT :
                throw new RuntimeException("Not implemented yet!");
            case TRUE :
                return Term.mkTop();
            case FALSE :
                return Term.mkBottom();
            case EMPTYNESS :
                return Term.mkBottom();
            case IDEN :
                return Term.mkEq(envVars.get(x).get(0), envVars.get(x).get(1));
            case STRING :
                throw new RuntimeException("Not implemented yet!");
            case NUMBER :
                return new IntegerLiteral(x.num);
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprConstant.accept()");
    }

    /* ============================== */
    /* Evaluates an ExprUnary node. */
    /* ============================== */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprUnary x) throws Err {
        Term t;
        Object o;
        if (envVars.has(x))
            envVars.put(x.sub, envVars.get(x));
        switch (x.op) {
            case EXACTLYOF :
            case SOMEOF :
            case LONEOF :
            case ONEOF :
            case SETOF :
            case NOOP :
                o = visitThis(x.sub);
                envVars.remove(x.sub);
                return o;
            case NOT :
                t = cterm(x.sub);
                envVars.remove(x.sub);
                return Term.mkNot(t);
            case SOME :
                return some(x.sub);
            case LONE :
                return lone(x.sub);
            case ONE :
                return one(x.sub);
            case NO :
                return no(x.sub);
            case TRANSPOSE :
                if (envVars.get(x).size() != 2)
                    throw new ErrorFatal(x.pos, "Two transpose variables (" + x + ") not provided!");
                envVars.remove(x.sub);
                envVars.put(x.sub, List.of(envVars.get(x).get(1), envVars.get(x).get(0)));
                o = visitThis(x.sub);
                envVars.remove(x.sub);
                return o;
            case CARDINALITY :
                t = cardinality(x.sub);
                envVars.remove(x.sub);
                return t;
            case CAST2SIGINT :
                return cterm(x.sub);
            case CAST2INT :
                return cterm(x.sub);
            case RCLOSURE :
                if (envVars.get(x).size() != 2)
                    throw new ErrorFatal(x.pos, "Two rclosure variables (" + x + ") not provided!");
                return closure(x.sub, false);
            case CLOSURE :
                if (envVars.get(x).size() != 2)
                    throw new ErrorFatal(x.pos, "Two closure variables (" + x + ") not provided!");
                return closure(x.sub, true);
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprUnary.visit()");
    }

    private Term lone(Expr e) {
        List<Sort> sorts = getSorts(e);
        List<Var> vars = getVars(sorts.size());
        envVars.put(e, vars);
        Term t = cterm(e);
        envVars.remove(e);
        List<Var> vars2 = getVars(sorts.size());
        envVars.put(e, vars2);
        t = Term.mkForall(getAnnotatedVars(vars2, sorts), Term.mkImp(cterm(e), Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkImp(t, compareVars(vars, vars2)))));
        envVars.remove(e);
        return t;
    }

    private Term one(Expr e) {
        List<Sort> sorts = getSorts(e);
        List<Var> vars = getVars(sorts.size());
        envVars.put(e, vars);
        Term t = cterm(e);
        envVars.remove(e);
        List<Var> vars2 = getVars(sorts.size());
        return Term.mkExists(getAnnotatedVars(vars2, sorts), Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkImp(t, compareVars(vars, vars2))));
    }

    private Term some(Expr e) {
        List<Sort> sorts = getSorts(e);
        List<Var> vars = getVars(sorts.size());
        envVars.put(e, vars);
        Term t = cterm(e);
        envVars.remove(e);
        return Term.mkExists(getAnnotatedVars(vars, sorts), t);
    }

    private Term no(Expr e) {
        List<Sort> sorts = getSorts(e);
        List<Var> vars = getVars(sorts.size());
        envVars.put(e, vars);
        Term t = cterm(e);
        envVars.remove(e);
        return Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkNot(t));
    }

    private Term cardinality(Expr e) {
        BoundVariableEliminator bve = new BoundVariableEliminator(e);
        List<Var> tmpVars = getVars(e.type().arity());
        envVars.put(e, tmpVars);
        Term t = cterm(e);
        envVars.remove(e);
        String func;
        if (t instanceof App)
            func = ((App) t).getFunctionName();
        else
            throw new RuntimeException("Not implemented yet!");
        List<Sort> sorts = getSorts(e);
        List<List<Term>> domainValues = new ArrayList<>();
        if (!cardinCache.containsKey(func)) {
            List<Sort> argSorts = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            List<Var> vars = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            for (ExprVar bv : bve.boundVars) {
                argSorts.add(getSorts(bv).get(0));
                vars.add(env.get(bv));
            }
            vars.addAll(tmpVars);
            argSorts.addAll(sorts);
            String funcName = getFreshFunc();
            cardinCache.put(func, frame.addFuncDecl(funcName, argSorts, Sort.Int()));
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkOr(Term.mkAnd(Term.mkEq(Term.mkApp(funcName, vars), new IntegerLiteral(1)), t), Term.mkAnd(Term.mkEq(Term.mkApp(funcName, vars), new IntegerLiteral(0)), Term.mkNot(t)))));
        }
        for (ExprVar bv : bve.boundVars) {
            env.remove(bv);
            domainValues.add(List.of(cterm(bv)));
        }
        for (Sort s : sorts) {
            List<Term> domainVal = new ArrayList<>();
            for (int j = 0; j < frame.getScope(s); j++)
                domainVal.add(Term.mkDomainElement(j+1, s));
            domainValues.add(domainVal);
        }
        List<List<Term>> appValues = getCartesianProduct(domainValues);
        Term term = Term.mkApp(cardinCache.get(func).name(), appValues.get(0));
        for (int i = 1; i < appValues.size(); i++)
            term = Term.mkPlus(term, Term.mkApp(cardinCache.get(func).name(), appValues.get(i)));
        return term;
    }

    // Naive closure approach
    // private Term closure(Expr e, boolean c) {
    //     Sort sort = getSorts(e).get(0);
    //     Expr expr = e;
    //     Term t = cterm(x.sub);
    //     for (int i = 1; i < frame.getScope(sort); i++) {
    //         expr = expr.join(e);
    //         envVars.put(expr, envVars.get(e));
    //         t = Term.mkOr(cterm(expr));
    //         envVars.remove(expr);
    //     } 
    //     if (!c)
    //         t = Term.mkOr(t, Term.mkEq(envVars.get(e).get(0), envVars.get(e).get(1)));
    //     envVars.remove(e);
    //     return t;
    // }

    private Term getClosureTerm(String func, List<Var> bv, List<Var> vars, AnnotatedVar var) {
        List<Term> args = new ArrayList<>(bv);
        args.add(vars.get(0));
        args.add(var.variable());
        Term t = Term.mkApp(func, args);
        args.set(bv.size(), var.variable());
        args.set(bv.size()+1, vars.get(1));
        t = Term.mkAnd(t, Term.mkApp(func, args));
        args.set(bv.size(), vars.get(0));
        return Term.mkOr(Term.mkApp(func, args), Term.mkExists(var, t));
    }

    // Approach 1: Iterative squaring
    // private Term closure(Expr e, boolean c) {
    //     BoundVariableEliminator bve = new BoundVariableEliminator(e);
    //     List<Var> tmpVars = getVars(e.type().arity());
    //     Var tmpVar = tc.getFreshVar();
    //     envVars.put(e, List.of(tmpVars.get(0), tmpVar));
    //     Term t = cterm(e);
    //     envVars.remove(e);
    //     String func;
    //     if (t instanceof App)
    //         func = ((App) t).getFunctionName();
    //     else
    //         throw new RuntimeException("Not implemented yet!");
    //     List<Sort> sorts = getSorts(e);
    //     if (!closureCache.containsKey(func)) {
    //         List<Sort> argSorts = new ArrayList<>(e.type().arity()+bve.boundVars.size());
    //         List<Var> vars = new ArrayList<>(e.type().arity()+bve.boundVars.size());
    //         for (ExprVar bv : bve.boundVars) {
    //             argSorts.add(getSorts(bv).get(0));
    //             vars.add(env.get(bv));
    //         }
    //         argSorts.addAll(sorts);
    //         vars.addAll(tmpVars);
    //         envVars.put(e, List.of(tmpVar, tmpVars.get(1)));
    //         t = Term.mkAnd(t, cterm(e));
    //         envVars.remove(e);
    //         envVars.put(e, tmpVars);
    //         t = Term.mkOr(cterm(e), Term.mkExists(tmpVar.of(sorts.get(0)), t));
    //         envVars.remove(e);
    //         String newFunc = func;
    //         for (int i = 1; i < Math.ceil(Math.log(frame.getScope(sorts.get(0))))/Math.log(2); i++) {
    //             newFunc = getFreshFunc();
    //             closureCache.put(func, frame.addFuncDecl(newFunc, argSorts, Sort.Bool()));
    //             frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkIff(Term.mkApp(newFunc, vars), t)));
    //             t = getClosureTerm(newFunc, vars.subList(0, bve.boundVars.size()), tmpVars, tmpVar.of(sorts.get(0)));
    //         }
    //     }
    //     List<Var> finalArgs = new ArrayList<>();
    //     for (ExprVar bv : bve.boundVars) {
    //         env.remove(bv);
    //         finalArgs.add((Var) cterm(bv));
    //     }
    //     t = getClosureTerm(closureCache.get(func).name(), finalArgs, envVars.get(e), tmpVar.of(sorts.get(0)));
    //     return c ? t : Term.mkOr(t, Term.mkEq(envVars.get(e).get(0),envVars.get(e).get(1)));
    // }

    private List<Term> getList(List<Var> vars, Term v1, Term v2) {
        List<Term> res = new ArrayList<>(vars);
        res.add(v1);
        res.add(v2);
        return res;
    }

    private List<Term> getList(List<Var> vars, Term v1, Term v2, Term v3) {
        List<Term> res = new ArrayList<>(vars);
        res.add(v1);
        res.add(v2);
        res.add(v3);
        return res;
    }

    // Approach 2: Claessen
    // private Term closure(Expr e, boolean c) {
    //     BoundVariableEliminator bve = new BoundVariableEliminator(e);
    //     List<Var> tmpVars = getVars(e.type().arity());
    //     Var tmpVar = tc.getFreshVar();
    //     envVars.put(e, tmpVars);
    //     Term t = cterm(e);
    //     envVars.remove(e);
    //     String func;
    //     if (t instanceof App)
    //         func = ((App) t).getFunctionName();
    //     else
    //         throw new RuntimeException("Not implemented yet!");
    //     Sort sort = getSorts(e).get(0);
    //     if (!closureCache.containsKey(func)) {
    //         List<Sort> argSorts = new ArrayList<>(e.type().arity()+bve.boundVars.size());
    //         List<Var> vars = new ArrayList<>(e.type().arity()+bve.boundVars.size());
    //         for (ExprVar bv : bve.boundVars) {
    //             argSorts.add(getSorts(bv).get(0));
    //             vars.add(env.get(bv));
    //         }
    //         String starR = getFreshFunc(), aux1 = getFreshFunc(), aux2 = getFreshFunc();
    //         List<Var> boundVars = new ArrayList<>(vars);
    //         argSorts.add(sort);
    //         vars.add(tmpVars.get(0));
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkApp(starR, getList(boundVars, tmpVars.get(0), tmpVars.get(0))))); // I1
    //         argSorts.add(sort);
    //         vars.add(tmpVars.get(1));
    //         closureCache.put(func, frame.addFuncDecl(starR, argSorts, Sort.Bool()));
    //         frame.addFuncDecl(aux2, argSorts, sort);
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkNot(Term.mkApp(aux1, getList(boundVars, tmpVars.get(0), tmpVars.get(0), tmpVars.get(1)))))); // C1
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(t, Term.mkApp(starR, vars)))); // I2
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(starR, vars), Term.mkNot(Term.mkEq(tmpVars.get(0), tmpVars.get(1)))), Term.mkApp(func, getList(boundVars, tmpVars.get(0), Term.mkApp(aux2, vars)))))); // E1
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(starR, vars), Term.mkNot(Term.mkEq(tmpVars.get(0), tmpVars.get(1)))), Term.mkApp(starR, getList(boundVars, Term.mkApp(aux2, vars), tmpVars.get(1)))))); // E2
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(starR, vars), Term.mkNot(Term.mkEq(tmpVars.get(0), tmpVars.get(1)))), Term.mkApp(aux1, getList(boundVars, tmpVars.get(0), Term.mkApp(aux2, vars), tmpVars.get(1)))))); // E3
    //         argSorts.add(sort);
    //         vars.add(tmpVar);
    //         frame.addFuncDecl(aux1, argSorts, Sort.Bool());
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(starR, getList(boundVars, tmpVars.get(0), tmpVars.get(1))), Term.mkApp(starR, getList(boundVars, tmpVars.get(1), tmpVar))), Term.mkApp(starR, getList(boundVars, tmpVars.get(0), tmpVar))))); // I3
    //         argSorts.add(sort);
    //         Var tmpVar1 = tc.getFreshVar();
    //         vars.add(tmpVar1);
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(aux1, getList(boundVars, tmpVars.get(0), tmpVars.get(1), tmpVar1)), Term.mkApp(aux1, getList(boundVars, tmpVars.get(1), tmpVar, tmpVar1))), Term.mkApp(aux1, getList(boundVars, tmpVars.get(0), tmpVar, tmpVar1))))); // C2
    //     }
    //     List<Var> finalArgs = new ArrayList<>();
    //     for (ExprVar bv : bve.boundVars) {
    //         env.remove(bv);
    //         finalArgs.add((Var) cterm(bv));
    //     }
    //     if (!c)
    //         return Term.mkApp(closureCache.get(func).name(), getList(finalArgs, envVars.get(e).get(0), envVars.get(e).get(1)));
    //     envVars.put(e, List.of(envVars.get(e).get(0), tmpVar));
    //     t = cterm(e);
    //     envVars.remove(e);
    //     return Term.mkExists(tmpVar.of(sort), Term.mkAnd(t, Term.mkApp(closureCache.get(func).name(), getList(finalArgs, tmpVar, envVars.get(e).get(1)))));
    // }

    // Approach 3: Ejick
    private Term closure(Expr e, boolean c) {
        BoundVariableEliminator bve = new BoundVariableEliminator(e);
        List<Var> tmpVars = getVars(e.type().arity());
        Var tmpVar = tc.getFreshVar();
        envVars.put(e, tmpVars);
        Term t = cterm(e);
        envVars.remove(e);
        String func;
        if (t instanceof App)
            func = ((App) t).getFunctionName();
        else
            throw new RuntimeException("Not implemented yet!");
        Sort sort = getSorts(e).get(0);
        if (!closureCache.containsKey(func)) {
            List<Sort> argSorts = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            List<Var> vars = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            for (ExprVar bv : bve.boundVars) {
                argSorts.add(getSorts(bv).get(0));
                vars.add(env.get(bv));
            }
            String aux = getFreshFunc();
            List<Var> boundVars = new ArrayList<>(vars);
            argSorts.add(sort);
            argSorts.add(sort);
            vars.addAll(tmpVars);
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkNot(Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVars.get(0), tmpVars.get(1)))))); // C1
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(t, Term.mkNot(Term.mkEq(tmpVars.get(0), tmpVars.get(1)))), Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVars.get(1), tmpVars.get(1)))))); // C4
            vars.set(vars.size()-1, tmpVar);
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVar, tmpVar)), Term.mkExists(tmpVars.get(1).of(sort), Term.mkAnd(t, Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVars.get(1), tmpVar))))))); // C5
            vars.set(vars.size()-1, tmpVars.get(1));
            argSorts.add(sort);
            vars.add(tmpVar);
            closureCache.put(func, frame.addFuncDecl(aux, argSorts, Sort.Bool()));
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(aux, vars), Term.mkNot(Term.mkEq(tmpVars.get(1), tmpVar))), Term.mkApp(aux, getList(boundVars, tmpVars.get(1), tmpVar, tmpVar))))); // C6
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVars.get(1), tmpVars.get(1))), Term.mkAnd(Term.mkApp(aux, getList(boundVars, tmpVars.get(1), tmpVar, tmpVar)), Term.mkNot(Term.mkEq(tmpVars.get(0), tmpVar)))), Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVar, tmpVar))))); // C3
            argSorts.add(sort);
            Var tmpVar1 = tc.getFreshVar();
            vars.add(tmpVar1);
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, argSorts), Term.mkImp(Term.mkAnd(Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVars.get(1), tmpVar1)), Term.mkApp(aux, getList(boundVars, tmpVars.get(1), tmpVar, tmpVar1))), Term.mkApp(aux, getList(boundVars, tmpVars.get(0), tmpVar, tmpVar1))))); // C2
        }
        List<Var> finalArgs = new ArrayList<>();
        for (ExprVar bv : bve.boundVars) {
            env.remove(bv);
            finalArgs.add((Var) cterm(bv));
        }
        if (!c)
            return Term.mkOr(Term.mkApp(closureCache.get(func).name(), getList(finalArgs, envVars.get(e).get(0), envVars.get(e).get(1), envVars.get(e).get(1))), Term.mkEq(envVars.get(e).get(0), envVars.get(e).get(1)));
        envVars.put(e, List.of(envVars.get(e).get(0), tmpVar));
        t = cterm(e);
        envVars.remove(e);
        return Term.mkExists(tmpVar.of(sort), Term.mkAnd(t, Term.mkOr(Term.mkApp(closureCache.get(func).name(), getList(finalArgs, tmpVar, envVars.get(e).get(1), envVars.get(e).get(1))), Term.mkEq(tmpVar, envVars.get(e).get(1)))));
    }

    // Using Closure in Fortress
    // private Term closure(ExprUnary x, boolean c) {
    //     Term t = cterm(x.sub);
    //     if (!(t instanceof App)) {
    //         BoundVariableEliminator bve = new BoundVariableEliminator(x.sub);
    //         List<Term> args = new ArrayList<>(bve.boundVars.size()+2);
    //         if (!cache.has(x.sub)) {
    //             List<Var> vars = new ArrayList<>(bve.boundVars.size()+2);
    //             List<Sort> sorts = new ArrayList<>(bve.boundVars.size()+2);
    //             envVars.put(x.sub, getVars(2));
    //             t = cterm(x.sub);
    //             for (ExprVar bv : bve.boundVars) {
    //                 sorts.add(getSorts(bv).get(0));
    //                 vars.add(env.get(bv));
    //             }
    //             vars.addAll(envVars.get(x.sub));
    //             sorts.addAll(getSorts(x.sub));
    //             envVars.remove(x.sub);
    //             String funcName = getFreshFunc();
    //             cache.put(x.sub, frame.addFuncDecl(funcName, sorts, Sort.Bool()));
    //             frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkEq(Term.mkApp(funcName, vars), t)));
    //         }
    //         for (ExprVar bv : bve.boundVars) {
    //             env.remove(bv);
    //             args.add(env.get(bv));
    //         }
    //         args.addAll(envVars.get(x.sub));
    //         t = Term.mkApp(cache.get(x.sub).name(), args);
    //     }
    //     // look at order of variables in app and compare to envvars, if not introduce new function and add axiom, change t to new app
    //     envVars.remove(x.sub);
    //     App app = (App) t;
    //     List<Term> args = new ArrayList<>(app.getArguments());
    //     int idx1 = args.indexOf(envVars.get(x).get(0));
    //     int idx2 ;= args.indexOf(envVars.get(x).get(1));
    //     if (idx1 > idx2) {
    //         args.set(idx1, envVars.get(x).get(1));
    //         args.set(idx2, envVars.get(x).get(0));
    //         List<Sort> sorts = new ArrayList<>();
    //         for (Sort s : JavaConverters.asJavaIterable(frame.getFuncDecl(app.getFunctionName()).argSorts()))
    //             sorts.add(s);
    //         cache.put(x.sub, frame.addFuncDecl(getFreshFunc(), sorts, Sort.Bool()));
    //         List<Var> vars = args.stream().map(a -> (Var) a).collect(Collectors.toList());
    //         app = (App) Term.mkApp(cache.get(x.sub).name(), args);
    //         frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkEq(app, t)));
    //     }
    //     return c ? Term.mkClosure(app, envVars.get(x).get(0), envVars.get(x).get(1)) : Term.mkReflexiveClosure(app, envVars.get(x).get(0), envVars.get(x).get(1));    
    // }

    /* ============================ */
    /* Evaluates an ExprVar node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprVar x) throws Err {
        Var ans = env.get(x);
        if (ans == null) {
            if (!letMappings.has(x))
                throw new ErrorFatal(x.pos, "Variable \"" + x + "\" is not bound to a legal value during translation.\n");
            if (envVars.has(x))
                envVars.put(letMappings.get(x), envVars.get(x));
            Object o = visitThis(letMappings.get(x));
            envVars.remove(letMappings.get(x));
            return o;
        }
        if (envVars.has(x))
            return Term.mkEq(ans, envVars.get(x).get(0));
        return ans;
    }

    /* ========================= */
    /* Evaluates a Field node. */
    /* ========================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(Field x) throws Err {
        FuncDecl func = frame.a2f(x);
        if (func == null)
            throw new ErrorFatal(x.pos, "Sig \"" + x + "\" is not bound to a legal value during translation.\n");
        if (envVars.has(x)) {
            if (func.resultSort() != Sort.Bool()) {
                if (envVars.get(x).size() == 1)
                    return Term.mkApp(func.name(), envVars.get(x));
                List<Var> vars = new ArrayList<>(envVars.get(x));
                Var v = vars.remove(vars.size() - 1);
                return Term.mkEq(Term.mkApp(func.name(), vars), v);
            }
            return Term.mkApp(func.name(), envVars.get(x));
        }
        return func;
    }

    /* ======================= */
    /* Evaluates a Sig node. */
    /* ======================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(Sig x) throws Err {
        if (frame.a2s(x) != null)
            return Term.mkTop();
        FuncDecl func = frame.a2f(x);
        if (func == null) {
            AnnotatedVar v = frame.a2c(x);
            if (v == null)
                throw new ErrorFatal(x.pos, "Sig \"" + x + "\" is not bound to a legal value during translation.\n");
            if (envVars.has(x)) {
                Term t = Term.mkEq(v.variable(), envVars.get(x).get(0));
                return tc.notPred.contains(x) ? Term.mkNot(t) : t;
            }
            return v.variable();
        }
        if (envVars.has(x)) {
            Term t = Term.mkApp(func.name(), envVars.get(x));
            return tc.notPred.contains(x) ? Term.mkNot(t) : t;
        }
        return func;
    }

    /* ============================= */
    /* Evaluates an ExprCall node. */
    /* ============================= */

    private void createPrevsFunction(Sig s) {
        Sort sort = cfunc(s).argSorts().head();
        FuncDecl func = frame.addFuncDecl(s.label + ".prevs", List.of(sort, sort), Sort.Bool());
        for (int i = 0; i < frame.getScope(sort); i++)
            for (int j = 0; j < frame.getScope(sort); j++)
                if (i > j)
                    frame.addAxiom(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort))));
                else
                    frame.addAxiom(Term.mkNot(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort)))));
    }

    private void createNextsFunction(Sig s) {
        Sort sort = cfunc(s).argSorts().head();
        FuncDecl func = frame.addFuncDecl(s.label + ".nexts", List.of(sort, sort), Sort.Bool());
        for (int i = 0; i < frame.getScope(sort); i++)
            for (int j = 0; j < frame.getScope(sort); j++)
                if (i < j)
                    frame.addAxiom(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort))));
                else
                    frame.addAxiom(Term.mkNot(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort)))));
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprCall x) throws Err {
        final Func f = x.fun;
        if (opt.orderingModule) {
            String[] tmp = f.label.split("/");
            if (tmp[1].equals("first")) {
                Sort sort = cfunc(f.returnDecl.type().fold().get(0).get(0)).argSorts().head();
                return Term.mkEq(Term.mkDomainElement(1, sort), envVars.get(x).get(0));
            } else if (tmp[1].equals("last")) {
                Sort sort = cfunc(f.returnDecl.type().fold().get(0).get(0)).argSorts().head();
                return Term.mkEq(Term.mkDomainElement(frame.getScope(sort), sort), envVars.get(x).get(0));
            } else if (tmp[1].equals("next")) {
                Sig s = f.returnDecl.type().fold().get(0).get(0);
                if (!frame.hasFunctionWithName(s.label + ".next")) {
                    Sort sort = cfunc(s).argSorts().head();
                    FuncDecl func = frame.addFuncDecl(s.label + ".next", List.of(sort, sort), Sort.Bool());
                    for (int i = 0; i < frame.getScope(sort); i++)
                        for (int j = 0; j < frame.getScope(sort); j++)
                            if (i+1 == j)
                                frame.addAxiom(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort))));
                            else
                                frame.addAxiom(Term.mkNot(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort)))));
                }
                return Term.mkApp(s.label + ".next", envVars.get(x));
            } else if (tmp[1].equals("prev")) {
                Sig s = f.returnDecl.type().fold().get(0).get(0);
                if (!frame.hasFunctionWithName(s.label + ".prev")) {
                    Sort sort = cfunc(s).argSorts().head();
                    FuncDecl func = frame.addFuncDecl(s.label + ".prev", List.of(sort, sort), Sort.Bool());
                    for (int i = 0; i < frame.getScope(sort); i++)
                        for (int j = 0; j < frame.getScope(sort); j++)
                            if (i == j+1)
                                frame.addAxiom(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort))));
                            else
                                frame.addAxiom(Term.mkNot(Term.mkApp(func.name(), List.of(Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort)))));
                }
                return Term.mkApp(s.label + ".prev", envVars.get(x));
            } else if (tmp[1].equals("prevs")) {
                Sig s = f.returnDecl.type().fold().get(0).get(0);
                Sort sort = cfunc(s).argSorts().head();
                if (!frame.hasFunctionWithName(s.label + ".prevs")) {
                    createPrevsFunction(s);
                }
                Var v = tc.getFreshVar();
                envVars.put(x.args.get(0), List.of(v));
                Term t = Term.mkExists(v.of(sort), Term.mkAnd(cterm(x.args.get(0)), Term.mkApp(s.label + ".prevs", List.of(v, envVars.get(x).get(0)))));
                envVars.remove(x.args.get(0));
                return t;
            } else if (tmp[1].equals("nexts")) {
                Sig s = f.returnDecl.type().fold().get(0).get(0);
                Sort sort = cfunc(s).argSorts().head();
                if (!frame.hasFunctionWithName(s.label + ".nexts")) {
                    createNextsFunction(s);
                }
                Var v = tc.getFreshVar();
                envVars.put(x.args.get(0), List.of(v));
                Term t = Term.mkExists(v.of(sort), Term.mkAnd(cterm(x.args.get(0)), Term.mkApp(s.label + ".nexts", List.of(v, envVars.get(x).get(0)))));
                envVars.remove(x.args.get(0));
                return t;
            } else if (tmp[1].equals("lt")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("gt")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("lte")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("gte")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("larger")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("smaller")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("max")) {
                throw new RuntimeException("Not implemented yet!");
            } else if (tmp[1].equals("min")) {
                Sig s = f.returnDecl.type().fold().get(0).get(0);
                Sort sort = cfunc(s).argSorts().head();
                envVars.put(x.args.get(0), envVars.get(x));
                Term t = cterm(x.args.get(0));
                envVars.remove(x.args.get(0));
                if (!frame.hasFunctionWithName(s.label + ".nexts")) {
                    createNextsFunction(s);
                }
                Var v = tc.getFreshVar();
                envVars.put(x.args.get(0), List.of(v));
                t = Term.mkAnd(t, Term.mkNot(Term.mkExists(v.of(sort), Term.mkAnd(cterm(x.args.get(0)), Term.mkApp(s.label + ".nexts", v, envVars.get(x).get(0))))));
                envVars.remove(x.args.get(0));
                return t;
            }
        }
        final Expr body = f.getBody();
        if (body.type().arity() < 0 || body.type().arity() != f.returnDecl.type().arity())
            throw new ErrorType(body.span(), "Function return value not fully resolved.");
        Env<ExprVar, Var> newenv = new Env<ExprVar, Var>();
        List<ExprVar> exprList = new ArrayList<>();
        for (int i = 0; i < f.count(); i++) {
            if (isExprVar(x.args.get(i)))
                newenv.put(f.get(i), (Var) visitThis(x.args.get(i)));
            else {
                Expr e = getLetMappingIfAny(x.args.get(i));
                BoundVariableEliminator bve = new BoundVariableEliminator(e);
                for (ExprVar bv : bve.boundVars) {
                    env.remove(bv);
                    newenv.put(bv, env.get(bv));
                }
                letMappings.put(f.get(i), e);
                exprList.add(f.get(i));
            }
        }
        Env<ExprVar, Var> oldenv = env;
        env = newenv;
        current_function.add(f);
        if (envVars.has(x))
            envVars.put(body, envVars.get(x));
        Object ans = visitThis(body);
        for (ExprVar ev : exprList)
            letMappings.remove(ev);
        envVars.remove(body);
        env = oldenv;
        current_function.remove(current_function.size() - 1);
        return ans;
    }

    /* ================================ */
    /* Evaluates an ExprList node. */
    /* ================================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprList x) throws Err {
        if (x.op == ExprList.Op.AND || x.op == ExprList.Op.OR) {
            if (x.args.size() == 0)
                return (x.op == ExprList.Op.AND) ? Term.mkTop() : Term.mkBottom();
            return getSingleFormula(x.op == ExprList.Op.AND, 1, x.args);
        }
        if (x.op == ExprList.Op.TOTALORDER) {
            Expr elem = x.args.get(0);
            ExprBinary first = (ExprBinary) x.args.get(1), next = (ExprBinary) x.args.get(2);
            FuncDecl elm = cfunc(elem);
            FuncDecl fst = cfunc(first.right);
            FuncDecl nxt = cfunc(next.right);
            Sort ord = cfunc(first.left).argSorts().head();
            Sort sort = elm.argSorts().head();
            Var v1 = tc.getFreshVar();
            Var v2 = tc.getFreshVar();
            Var v3 = tc.getFreshVar();
            // elem in first.*next
            Term t1 = Term.mkApp(fst.name(), Term.mkDomainElement(1, ord), v2);
            Term t2 = Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v2, v1);
            frame.addAxiom(Term.mkForall(v1.of(sort), Term.mkImp(Term.mkApp(elm.name(), v1), Term.mkExists(v2.of(sort), Term.mkAnd(t1, Term.mkReflexiveClosure((App) t2, v2, v1))))));
            // no next.first
            t2 = Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v1, v2);
            frame.addAxiom(Term.mkForall(v1.of(sort), Term.mkNot(Term.mkExists(v2.of(sort), Term.mkAnd(t2, t1)))));
            // v2 = first || one next.v2
            frame.addAxiom(Term.mkForall(v2.of(sort), Term.mkOr(t1, Term.mkAnd(Term.mkExists(v1.of(sort), t2), Term.mkForall(v1.of(sort), Term.mkImp(t2, Term.mkForall(v3.of(sort), Term.mkImp(Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v3, v2), Term.mkEq(v1, v3)))))))));
            // v2 = elem - next.elem || one v2.next
            frame.addAxiom(Term.mkForall(v1.of(sort), Term.mkOr(Term.mkForall(v2.of(sort), Term.mkEq(Term.mkEq(v1, v2), Term.mkAnd(Term.mkApp(elm.name(), v2), Term.mkNot(Term.mkExists(v3.of(sort), Term.mkAnd(Term.mkApp(elm.name(), v3), Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v2, v3))))))), Term.mkAnd(Term.mkExists(v2.of(sort), t2), Term.mkForall(v2.of(sort), Term.mkImp(t2, Term.mkForall(v3.of(sort), Term.mkImp(Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v1, v3), Term.mkEq(v2, v3)))))))));
            // !(v2 in v2.^next)
            return Term.mkForall(v2.of(sort), Term.mkNot(Term.mkClosure((App) Term.mkApp(nxt.name(), Term.mkDomainElement(1, ord), v2, v2), v2, v2)));
        }
        List<Term> terms = new ArrayList<>();
        for (int i = 0; i < x.args.size(); i++)
            terms.add(cterm(x.args.get(i)));
        return Term.mkDistinct(terms);
    }

    private Term getSingleFormula(boolean isConjunct, int i, List<Expr> formulas) throws Err {
        int n = formulas.size();
        if (n == 0)
            return isConjunct ? Term.mkTop() : Term.mkBottom();
        Term me = cterm(formulas.get(i - 1)), other;
        int child1 = i + i, child2 = child1 + 1;
        if (child1 < i || child1 > n)
            return me;
        other = getSingleFormula(isConjunct, child1, formulas);
        if (isConjunct)
            me = Term.mkAnd(me, other);
        else
            me = Term.mkOr(me, other);
        if (child2 < 1 || child2 > n)
            return me;
        other = getSingleFormula(isConjunct, child2, formulas);
        if (isConjunct)
            me = Term.mkAnd(me, other);
        else
            me = Term.mkOr(me, other);
        return me;
    }

    // /* =============================== */
    // /* Evaluates an ExprBinary node. */
    // /* =============================== */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprBinary x) throws Err {
        Expr a = x.left, b = x.right;
        switch (x.op) {
            case IMPLIES :
                return Term.mkOr(Term.mkNot(cterm(a)), cterm(b));
            case IN :
                return isIn(a, b, false);
            case NOT_IN : 
                return Term.mkNot(isIn(a, b, false));
            case JOIN :
                return join(x);
            case LT :
            case LTE :
            case GT :
            case GTE :
            case EQUALS :
                return helperComparison(a, b, x.op);
            case NOT_LT :
                return Term.mkNot(helperComparison(a, b, ExprBinary.Op.LT));
            case NOT_LTE :
                return Term.mkNot(helperComparison(a, b, ExprBinary.Op.LTE));
            case NOT_GT :
                return Term.mkNot(helperComparison(a, b, ExprBinary.Op.GT));
            case NOT_GTE :
                return Term.mkNot(helperComparison(a, b, ExprBinary.Op.GTE));
            case NOT_EQUALS :
                return Term.mkNot(helperComparison(a, b, ExprBinary.Op.EQUALS));
            case PLUS :
            case MINUS :
            case INTERSECT :
                if (envVars.has(x)) {
                    envVars.put(a, envVars.get(x));
                    envVars.put(b, envVars.get(x));
                }
                return helperBinary(x);
            case ANY_ARROW_SOME :
            case ANY_ARROW_ONE :
            case ANY_ARROW_LONE :
            case SOME_ARROW_ANY :
            case SOME_ARROW_SOME :
            case SOME_ARROW_ONE :
            case SOME_ARROW_LONE :
            case ONE_ARROW_ANY :
            case ONE_ARROW_SOME :
            case ONE_ARROW_ONE :
            case ONE_ARROW_LONE :
            case LONE_ARROW_ANY :
            case LONE_ARROW_SOME :
            case LONE_ARROW_ONE :
            case LONE_ARROW_LONE :
            case ISSEQ_ARROW_LONE :
            case ARROW :
                envVars.put(a, envVars.get(x).subList(0, a.type().arity()));
                envVars.put(b, envVars.get(x).subList(a.type().arity(), envVars.get(x).size()));
                return helperBinary(x);
            case AND :
                return Term.mkAnd(cterm(a), cterm(b));
            case OR :
                return Term.mkOr(cterm(a), cterm(b));
            case IFF :
                return Term.mkEq(cterm(a), cterm(b));
            case PLUSPLUS :
                return plusplus(x);
            case MUL :
                return Term.mkMult(cterm(a), cterm(b));
            case DIV :
                return Term.mkDiv(cterm(a), cterm(b));
            case REM :
                return Term.mkMod(cterm(a), cterm(b));
            case SHL :
                throw new RuntimeException("Not implemented yet!");
            case SHR :
                throw new RuntimeException("Not implemented yet!");
            case SHA :
                throw new RuntimeException("Not implemented yet!");
            case IPLUS :
                return Term.mkPlus(cterm(a), cterm(b));
            case IMINUS :
                return Term.mkSub(cterm(a), cterm(b));
            case DOMAIN :
                throw new RuntimeException("Not implemented yet!");
            case RANGE :
                throw new RuntimeException("Not implemented yet!");
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprBinary.accept()");
    }

    /**
     * Helper method that translates the formula "a in b" into a Fortress term.
     */
    private Term isIn(Expr left, Expr right, boolean field) throws Err {
        if (right instanceof ExprBinary && right.mult != 0 && ((ExprBinary) right).op.isArrow) {
            return isInBinary(left, (ExprBinary) right, field);
        }
        List<Var> vars = getVars(left.type().arity());
        List<AnnotatedVar> avars = new ArrayList<>(getAnnotatedVars(vars, getSorts(left)));
        Term t = null;
        switch (right.mult()) {
            case EXACTLYOF :
                t = cterm(left);
                Term r = cterm(right);
                envVars.remove(left);
                envVars.remove(right);
                if (t instanceof Eq && r instanceof Eq) {
                    avars.remove(avars.size()-1);
                    return helperForall(avars, Term.mkEq(((Eq) t).left(), ((Eq) r).left()));
                }
                return Term.mkForall(avars, Term.mkEq(t, r));
            case ONEOF :
                if (field && opt.useFunctions)
                    return Term.mkTop();
                t = one(left);
                break;
            case LONEOF :
                t = lone(left);
                break;
            case SOMEOF :
                t = some(left);
                break;
            default :
                if (field)
                    return Term.mkTop();
        }
        envVars.put(left, vars);
        envVars.put(right, vars);
        Term l = cterm(left), r = cterm(right);
        envVars.remove(left);
        envVars.remove(right);
        Term tmp = Term.mkForall(avars, Term.mkImp(l, r));
        if (l instanceof Eq) {
            if (r instanceof Eq) {
                avars.remove(avars.size()-1);
                tmp = helperForall(avars, Term.mkEq(((Eq) l).left(), ((Eq) r).left()));
            } else if (isApp(r)) {
                avars.remove(avars.size()-1);
                tmp = helperForall(avars, helperEqApp((Eq) l, r));
            }
        }
        if (r instanceof Eq && (isApp(l))) {
            tmp = helperEqApp((Eq) r, l);
        }
        return (t == null) ? tmp : Term.mkAnd(t, tmp);
    }

    /**
     * Helper method that translates the formula "r in (a ?->? b)" into a Fortress term
     */
    private Term isInBinary(Expr r, ExprBinary ab, boolean field) throws Err {
        Term t, t2;
        Expr a = r;
        List<Var> vars = getVars(ab.left.type().arity());
        envVars.put(ab.left, vars);
        Term tmp = cterm(ab.left);
        envVars.remove(ab.left);
        Type.ProductType it = ab.left.type().iterator().next();
        List<ExprVar> evars = new ArrayList<>();
        for (int i = 0; i < it.arity(); i++) {
            ExprVar ev = ExprVar.make(Pos.UNKNOWN, vars.get(i).getName(), it.get(i).type());
            evars.add(ev);
            env.put(ev, vars.get(i));
            a = ev.join(a); 
        }
        t = isIn(a, ab.right, field);
        switch (ab.op) {
            case ISSEQ_ARROW_LONE :
            case ANY_ARROW_LONE :
            case SOME_ARROW_LONE :
            case ONE_ARROW_LONE :
            case LONE_ARROW_LONE :
                t = Term.mkAnd(t, lone(a));
                break;
            case ANY_ARROW_ONE :
            case SOME_ARROW_ONE :
            case ONE_ARROW_ONE :
            case LONE_ARROW_ONE :
                if (!field || !opt.useFunctions)
                    t = Term.mkAnd(t, one(a));
                break;
            case ANY_ARROW_SOME :
            case SOME_ARROW_SOME :
            case ONE_ARROW_SOME :
            case LONE_ARROW_SOME :
                t = Term.mkAnd(t, some(a));
                break;
        }
        List<Sort> sorts = getSorts(ab.left);
        if (t != Term.mkTop()) {
            if (tmp != Term.mkTop() || !(tmp instanceof App && sorts.get(0).name().equals(((App) tmp).getFunctionName().split("/")[1])))
                t = Term.mkImp(tmp, t);
            t = Term.mkForall(getAnnotatedVars(vars, sorts), t);
        }
        vars = getVars(ab.right.type().arity());
        envVars.put(ab.right, vars);
        tmp = cterm(ab.right);
        envVars.remove(ab.right);
        it = ab.right.type().iterator().next();
        for (int i = it.arity() - 1; i >= 0; i--) {
            ExprVar ev = ExprVar.make(Pos.UNKNOWN, vars.get(i).getName(), it.get(i).type());
            evars.add(ev);
            env.put(ev, vars.get(i));
            r = r.join(ev); 
        }
        t2 = isIn(r, ab.left, field);
        switch (ab.op) {
            case LONE_ARROW_ANY :
            case LONE_ARROW_SOME :
            case LONE_ARROW_ONE :
            case LONE_ARROW_LONE :
                t2 = Term.mkAnd(t2, lone(r));
                break;
            case ONE_ARROW_ANY :
            case ONE_ARROW_SOME :
            case ONE_ARROW_ONE :
            case ONE_ARROW_LONE :
                t2 = Term.mkAnd(t2, one(r));
                break;
            case SOME_ARROW_ANY :
            case SOME_ARROW_SOME :
            case SOME_ARROW_ONE :
            case SOME_ARROW_LONE :
                t2 = Term.mkAnd(t2, some(r));
                break;
        }
        sorts = getSorts(ab.right);
        for (ExprVar ev : evars)
            env.remove(ev);
        if (t2 != Term.mkTop()) {
            if (tmp != Term.mkTop()  || !(tmp instanceof App && sorts.get(0).name().equals(((App) tmp).getFunctionName().split("/")[1])))
                t2 = Term.mkImp(tmp, t2);
            if (t != Term.mkTop())
                return Term.mkAnd(Term.mkForall(getAnnotatedVars(vars, sorts), t2), t);
            return Term.mkForall(getAnnotatedVars(vars, sorts), t2);
        }
        return t;
    }

    private Object join(ExprBinary e) {
        Expr a = e.left, b = e.right;
        List<Var> vars = new ArrayList<>();
        Term t;
        if (isExprVar(a)) {
            vars.add((Var) cterm(a));
            if (envVars.has(e))
                vars.addAll(envVars.get(e)); 
            envVars.put(b, vars);
            t = cterm(b);
            envVars.remove(b);
            return t;
        }
        if (isExprVar(b)) {
            vars.addAll(envVars.get(e));
            vars.add((Var) cterm(b)); 
            envVars.put(a, vars);
            t = cterm(a);
            envVars.remove(a);
            return t;
        }
        vars.add(tc.getFreshVar());
        List<Var> lVars = new ArrayList(envVars.get(e).subList(0, a.type().arity()-1));
        lVars.addAll(vars);
        List<Var> rVars = new ArrayList(vars);
        rVars.addAll(envVars.get(e).subList(a.type().arity()-1, e.type().arity()));
        envVars.put(a, lVars);
        envVars.put(b, rVars);
        Term l = cterm(a), r = cterm(b);
        envVars.remove(a);
        envVars.remove(b);
        if (l instanceof Eq) {
            if (isApp(r))
                return helperEqApp((Eq) l, r);
        }
        if (r instanceof Eq && ((Eq) r).left() instanceof Var) {
            if (isApp(l))
                return helperEqApp((Eq) r, l);
            else if (l instanceof Eq)
                return Term.mkEq(((Eq) l).left(), ((Eq) r).left());
        }
        return Term.mkExists(getAnnotatedVars(vars, List.of(getSorts(b).get(0))), Term.mkAnd(l, r));
    }

    // private Term domain(ExprBinary e) {
    //     Expr a = e.left, b = e.right;
    //     Var lVar = tc.getFreshVar();
    //     List<Var> rVars = new ArrayList(lVar);
    //     rVars.add()
    //     rVars.addAll(envVars.get(e));
    //     envVars.put(a, List.of(lVar));
    //     envVars.put(b, rVars);
    //     Term l = cterm(a), r = cterm(b);
    //     envVars.remove(a);
    //     envVars.remove(b);
    //     return Term.mkExists(lVar.of(getSorts(a).get(0)), Term.mkAnd(l, r));
    // }

    // private Term range(ExprBinary e) {
    //     Expr a = e.left, b = e.right;
    //     List<Var> rVars = tc.getFreshVar();
    //     List<Var> lVars = new ArrayList(envVars.get(e));
    //     lVars.addAll(rVars);
    //     envVars.put(a, lVars);
    //     envVars.put(b, rVars);
    //     Term l = cterm(a), r = cterm(b);
    //     envVars.remove(a);
    //     envVars.remove(b);
    //     if (l instanceof Eq) {
    //         if (r instanceof App)
    //             return Term.mkApp(((App) r).getFunctionName(), ((Eq) l).left());
    //     }
    //     return Term.mkExists(getAnnotatedVars(rVars, getSorts(b)), Term.mkAnd(l, r));
    // }

    private boolean isCardinality(Expr e) {
        return e instanceof ExprUnary && ((ExprUnary) e).op == ExprUnary.Op.CARDINALITY;
    }

    private boolean isNumber(Expr e) {
        return e instanceof ExprConstant && ((ExprConstant) e).op == ExprConstant.Op.NUMBER;
    }

    private Term getAndList(List<Var> vars1, List<Var> vars2) {
        Term term = Term.mkEq(vars1.get(0), vars2.get(0));
        for (int i = 1; i < vars1.size(); i++)
            term = Term.mkAnd(term, Term.mkEq(vars1.get(i), vars2.get(i)));
        return term;
    }

    private Term getOrList(List<Var> vars1, List<Var> vars2) {
        Term term = Term.mkNot(Term.mkEq(vars1.get(0), vars2.get(0)));
        for (int i = 1; i < vars1.size(); i++)
            term = Term.mkOr(term, Term.mkNot(Term.mkEq(vars1.get(i), vars2.get(i))));
        return term;
    }

    private Term atmostN(Expr a, int num) {
        List<List<Var>> vars = new ArrayList<>();
        List<AnnotatedVar> avars = new ArrayList<>();
        List<Term> andList = new ArrayList<>(), orList = new ArrayList<>();
        List<Sort> sorts = getSorts(a);
        int arity = sorts.size();
        for (int i = 0; i <= num; i++) {
            List<Var> varList = new ArrayList<>();
            for (int j = 0; j < arity; j++) {
                Var v = tc.getFreshVar();
                varList.add(v);
                avars.add(v.of(sorts.get(j)));
            }
            for (List<Var> vv : vars) {
                orList.add(getAndList(varList, vv));
            }
            vars.add(varList);
            envVars.put(a, varList);
            andList.add(cterm(a));
            envVars.remove(a);
        }
        return Term.mkForall(avars, Term.mkImp(Term.mkAnd(andList), Term.mkOr(orList)));
    }

    private Term atleastN(Expr a, int num) {
        List<List<Var>> vars = new ArrayList<>();
        List<AnnotatedVar> avars = new ArrayList<>();
        List<Term> andList = new ArrayList<>();
        List<Sort> sorts = getSorts(a);
        int arity = sorts.size();
        for (int i = 0; i < num; i++) {
            List<Var> varList = new ArrayList<>();
            for (int j = 0; j < arity; j++) {
                Var v = tc.getFreshVar();
                varList.add(v);
                avars.add(v.of(sorts.get(j)));
            }
            for (List<Var> vv : vars) {
                andList.add(getOrList(varList, vv));
            }
            vars.add(varList);
            envVars.put(a, varList);
            andList.add(cterm(a));
            envVars.remove(a);
        }
        return Term.mkExists(avars, Term.mkAnd(andList));
    }

    private Term exactlyN(Expr a, int num) {
        List<List<Var>> vars = new ArrayList<>();
        List<AnnotatedVar> exists = new ArrayList<>();
        List<Term> andList = new ArrayList<>(), orList = new ArrayList<>();
        List<Sort> sorts = getSorts(a);
        int arity = sorts.size();
        for (int i = 0; i < num; i++) {
            List<Var> varList = new ArrayList<>();
            for (int j = 0; j < arity; j++) {
                Var v = tc.getFreshVar();
                varList.add(v);
                exists.add(v.of(sorts.get(j)));
            }
            for (List<Var> vv : vars) {
                andList.add(getOrList(varList, vv));
            }
            vars.add(varList);
        }
        List<AnnotatedVar> forall = new ArrayList<>();
        List<Var> varList2 = new ArrayList<>();
        for (int i = 0; i < arity; i++) {
            Var v = tc.getFreshVar();
            varList2.add(v);
            forall.add(v.of(sorts.get(i)));
        }
        for (List<Var> vv : vars) {
            orList.add(getAndList(varList2, vv));
        }
        envVars.put(a, varList2);
        andList.add(Term.mkEq(cterm(a), Term.mkOr(orList)));
        envVars.remove(a);
        return Term.mkExists(exists, Term.mkForall(forall, Term.mkAnd(andList)));
    }

    private Term helperComparison(Expr a, Expr b, ExprBinary.Op op) {
        if (opt.cardinality) {
            if (isCardinality(a) && isNumber(b)) {
                Expr r = ((ExprUnary) a).sub;
                int n = ((ExprConstant) b).num;
                switch(op) {
                    case LT:
                        return atmostN(r, n-1);
                    case LTE :
                        return atmostN(r, n);
                    case GT :
                        return atleastN(r, n+1);
                    case GTE :
                        return atleastN(r, n);
                    case EQUALS :
                        return exactlyN(r, n);
                }
            } else if (isCardinality(b) && isNumber(a)) {
                Expr r = ((ExprUnary) b).sub;
                int n = ((ExprConstant) a).num;
                switch (op) {
                    case LT:
                        return atleastN(r, n+1);
                    case LTE :
                        return atleastN(r, n);
                    case GT :
                        return atmostN(r, n-1);
                    case GTE :
                        return atmostN(r, n);
                    case EQUALS :
                        return exactlyN(r, n);
                }
            }
        }
        switch (op) {
            case LT:
                return Term.mkLT(cterm(a), cterm(b));
            case LTE :
                return Term.mkLE(cterm(a), cterm(b));
            case GT :
                return Term.mkGT(cterm(a), cterm(b));
            case GTE :
                return Term.mkGE(cterm(a), cterm(b));
            case EQUALS :
                return equals(a, b);
        }
        throw new ErrorFatal(Pos.UNKNOWN, "Unsupported operator (" + op + ") encountered during ExprBinary.accept()");
    }

    private Term helperBinary(ExprBinary e) {
        Term l = cterm(e.left), r = cterm(e.right);
        envVars.remove(e.left);
        envVars.remove(e.right);
        if (e.op == ExprBinary.Op.PLUS)
            return Term.mkOr(l, r);
        if (e.op == ExprBinary.Op.MINUS)
            return Term.mkAnd(l, Term.mkNot(r));
        return Term.mkAnd(l, r);
    }

    private Term equalsVar(Expr e, Expr b) {
        Term t;
        if (!isExprVar(b)) {
            Var v = tc.getFreshVar();
            envVars.put(b, List.of(v));
            t = cterm(b);
            envVars.remove(b);
            if (t instanceof Eq)
                return Term.mkEq(((Eq) t).left(), (Var) visitThis(e));
            envVars.put(e, List.of(v));
            t = Term.mkForall(v.of(getSorts(b).get(0)), Term.mkEq(cterm(e), t));
            envVars.remove(e);
        } else {
            envVars.put(b, List.of((Var) visitThis(e)));
            t = cterm(b);
            envVars.remove(b);
        }
        return t;
    }

    private Term equals(Expr a, Expr b) {
        if (isExprVar(a))
            return equalsVar(a, b);
        if (isExprVar(b))
            return equalsVar(b, a);
        if (a.type().is_int())
            return Term.mkEq(cterm(a), cterm(b));
        List<Sort> sorts = getSorts(a);
        List<Var> vars = getVars(sorts.size());
        List<AnnotatedVar> avars = new ArrayList<>(getAnnotatedVars(vars, sorts));
        envVars.put(a, vars);
        envVars.put(b, vars);
        Term l = cterm(a), r = cterm(b);
        envVars.remove(a);
        envVars.remove(b);
        if (l instanceof Eq && r instanceof Eq) {
            avars.remove(avars.size()-1);
            return helperForall(avars, Term.mkEq(((Eq) l).left(), ((Eq) r).left()));
        }
        return Term.mkForall(avars, Term.mkEq(l, r));
    }

    private Term plusplus(ExprBinary e) {
        envVars.put(e.right, envVars.get(e));
        Term r = cterm(e.right);
        envVars.remove(e.right);
        envVars.put(e.left, envVars.get(e));
        Term l = cterm(e.left);
        envVars.remove(e.left);
        List<Var> vars = new ArrayList<>();
        vars.add(envVars.get(e).get(0));
        vars.addAll(getVars(e.type().arity() - 1));
        List<Sort> sorts = getSorts(e);
        sorts = sorts.subList(1, sorts.size());
        envVars.put(e.right, vars);
        Term t = Term.mkExists(getAnnotatedVars(vars.subList(1, vars.size()), sorts), cterm(e.right));
        envVars.remove(e.right);
        return Term.mkAnd(Term.mkImp(t, r), Term.mkImp(Term.mkNot(t), l));
    }

    /* =========================== */
    /* Evaluates an ExprQt node. */
    /* =========================== */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprQt x) throws Err {
        Expr xx = x.desugar();
        if (xx instanceof ExprQt)
            x = (ExprQt) xx;
        else
            return visitThis(xx);
        if (envVars.has(x))
            envVars.put(x.sub, envVars.get(x));
        Object o = visit_qt(x.op, x.decls, x.sub);
        envVars.remove(x.sub);
        return o;
    }

    /**
     * Helper method that translates the quantification expression "op vars | sub"
     */
    private Object visit_qt(final ExprQt.Op op, final ConstList<Decl> xvars, final Expr sub) throws Err {
        if (op == ExprQt.Op.NO)
            return visit_qt(ExprQt.Op.ALL, xvars, sub.not());
        if (op == ExprQt.Op.ONE)
            return Term.mkAnd((Term) visit_qt(ExprQt.Op.LONE, xvars, sub), (Term) visit_qt(ExprQt.Op.SOME, xvars, sub));
        if (op == ExprQt.Op.LONE) {
            Forall t1 = (Forall) visit_qt(ExprQt.Op.ALL, xvars, sub), t2 = (Forall) visit_qt(ExprQt.Op.ALL, xvars, sub);
            List<AnnotatedVar> avars = new ArrayList<>(t1.varsJava());
            List<Term> andList = new ArrayList<>(avars.size()), termList = new ArrayList<>();
            avars.addAll(t2.varsJava());
            for (int i = 0; i < t1.varsJava().size(); i++)
                andList.add(Term.mkEq(t1.varsJava().get(i).variable(), t2.varsJava().get(i).variable()));
            Term body = Term.mkAnd(t1.body(), t2.body());
            if (t1.body() instanceof Implication) {
                Implication i1 = (Implication) t1.body();
                Implication i2 = (Implication) t2.body();
                termList.add(i1.left());
                termList.add(i2.left());
                body = Term.mkAnd(i1.right(), i2.right());
            }
            Term t = andList.size() > 1 ? Term.mkImp(body, Term.mkAnd(andList)) : Term.mkImp(body, andList.get(0));
            return getQtTerm(false, avars, termList, t);
        }
        if (op == ExprQt.Op.COMPREHENSION) 
            return comprehension(xvars, sub);
        List<AnnotatedVar> avarList = new ArrayList<>();
        List<Term> termList = new ArrayList<>();
        for (Decl dep : xvars) {
            final Expr dexexpr = addOne(dep.expr);
            Sort sort = getSorts(dexexpr).get(0);
            for (ExprHasName dex : dep.names) {
                if (dex.type().arity() != 1) {
                    throw new RuntimeException("Not implemented yet!");
                } else {
                    String label = skolem(dex.label);
                    final Var v = Term.mkVar(nameGenerator.freshName(label));
                    env.put((ExprVar) dex, v);
                    envVars.put(dexexpr, List.of(v));
                    Term tmp = cterm(dexexpr);
                    if (tmp != Term.mkTop())
                        termList.add(tmp);
                    envVars.remove(dexexpr);
                    switch (dexexpr.mult()) {
                        case SETOF :
                            throw new RuntimeException("Not implemented yet!");
                        case SOMEOF :
                            throw new RuntimeException("Not implemented yet!");
                        case LONEOF :
                            throw new RuntimeException("Not implemented yet!");
                        default :
                            avarList.add(v.of(sort));
                            frame.addDecl(v.of(sort), new Pair<String, Type>(label, dexexpr.type()));
                    }
                }
            }
        }
        final Term term = cterm(sub);
        for (Decl d : xvars)
            for (ExprHasName v : d.names)
                env.remove((ExprVar) v);
        if (op == ExprQt.Op.SUM)
            throw new RuntimeException("Not implemented yet!");
        return getQtTerm(op == ExprQt.Op.SOME, avarList, termList, term);
    }

    /**
     * Helper method that translates the comprehension expression "{vars | sub}"
     */
    private Object comprehension(final ConstList<Decl> xvars, final Expr sub) throws Err {
        BoundVariableEliminator bve = null;
        List<ExprVar> bvars = new ArrayList<>();
        List<ExprVar> exprVars = new ArrayList<>();
        List<Term> termList = new ArrayList<>(), args = new ArrayList<>();
        for (Decl dep : xvars) {
            final Expr dexexpr = addOne(dep.expr);
            Sort sort = getSorts(dexexpr).get(0);
            for (ExprHasName dex : dep.names) {
                if (dex.type().arity() != 1) {
                    throw new RuntimeException("Not implemented yet!");
                } else {
                    final Var v = Term.mkVar(skolem(dex.label));
                    env.put((ExprVar) dex, v);
                    envVars.put(dexexpr, List.of(v));
                    bve = new BoundVariableEliminator(bvars, dexexpr);
                    Term tmp = cterm(dexexpr);
                    bvars.addAll(bve.boundVars);
                    if (tmp != Term.mkTop() || !(tmp instanceof App && sort.name().equals(((App) tmp).getFunctionName().split("/")[1])))
                        termList.add(tmp);
                    envVars.remove(dexexpr);
                    switch (dexexpr.mult()) {
                        case SETOF :
                            throw new RuntimeException("Not implemented yet!");
                        case SOMEOF :
                            throw new RuntimeException("Not implemented yet!");
                        case LONEOF :
                            throw new RuntimeException("Not implemented yet!");
                        default :
                            exprVars.add((ExprVar) dex);
                    }
                }
            }
        }
        int varSize = exprVars.size();
        exprVars.addAll(bvars);
        bve = new BoundVariableEliminator(exprVars, sub);
        Term term = cterm(sub);
        if (!cache.containsKey(sub)) {
            List<Var> vars = new ArrayList<>(bve.boundVars.size());
            List<Sort> sorts = new ArrayList<>(bve.boundVars.size());
            for (ExprVar bv : bve.boundVars.subList(varSize, bve.boundVars.size())) {
                vars.add(env.get(bv));
                sorts.add(getSorts(bv).get(0));
            }
            for (ExprVar bv : bve.boundVars.subList(0, varSize)) {
                vars.add(env.get(bv));
                sorts.add(getSorts(bv).get(0));
            }
            String funcName = getFreshFunc();
            cache.put(sub, frame.addFuncDecl(funcName, sorts, Sort.Bool()));
            frame.addAxiom(getQtTerm(false, getAnnotatedVars(vars, sorts), termList, Term.mkEq(Term.mkApp(funcName, vars), term)));
        }
        for (ExprVar bv : bve.boundVars)
            env.remove(bv);
        for (ExprVar bv : bve.boundVars.subList(varSize, bve.boundVars.size()))
            args.add(env.get(bv));
        if (envVars.has(sub))
            args.addAll(envVars.get(sub));
        return args.size() > 0 ? Term.mkApp(cache.get(sub).name(), args) : cache.get(sub);
    }

    /**
     * Adds a "one of" in front of X if X is unary and does not have a declared
     * multiplicity.
     */
    private static Expr addOne(Expr x) {
        Expr save = x;
        while (x instanceof ExprUnary) {
            switch (((ExprUnary) x).op) {
                case EXACTLYOF :
                case SETOF :
                case ONEOF :
                case LONEOF :
                case SOMEOF :
                    return save;
                case NOOP :
                    x = ((ExprUnary) x).sub;
                    continue;
                default :
                    break;
            }
        }
        return (x.type().arity() != 1) ? x : ExprUnary.Op.ONEOF.make(x.span(), x);
    }

    // Get appropriate formula given a list of annotated variables, subset sig term and translated term
    private Term getQtTerm(boolean op, List<AnnotatedVar> avars, List<Term> termList, Term t) {
        if (termList.size() > 0) {
            Term terms = termList.size() > 1 ? Term.mkAnd(termList) : termList.get(0);
            t = op ? Term.mkAnd(terms, t) : Term.mkImp(terms, t);
        }
        return op ? Term.mkExists(avars, t) : Term.mkForall(avars, t);
    }
}