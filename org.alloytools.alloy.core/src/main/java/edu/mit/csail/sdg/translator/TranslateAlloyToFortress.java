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
import java.util.List;
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
import fortress.msfol.Forall;
import fortress.msfol.FuncDecl;
import fortress.msfol.Implication;
import fortress.msfol.IntegerLiteral;
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

    /** The unique name generator. */
    private final NameGenerator               nameGenerator; 

    private final List<Func>                  current_function = new ArrayList<Func>();

    private Env<ExprVar, Var>                 env              = new Env<ExprVar, Var>();

    private Env<ExprVar, Expr>                letMappings      = new Env<ExprVar, Expr>();

    private Env<Expr, FuncDecl>               cache            = new Env<Expr, FuncDecl>(); 

    private Env<Expr, List<Var>>              envVars          = new Env<Expr, List<Var>>();

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
        this.nameGenerator = TheoryComputer.compute(rep, frame, sigs, sc, opt);
    }

    /**
     * Conjoin the constraints for "field declarations" and "fact" paragraphs
     */
    private void makeFacts(Expr facts, Iterable<Sig> sigs) throws Err {
        // add the field facts and appended facts
        for (Sig s : sigs) {
            for (Decl d : s.getFieldDecls()) {
                for (ExprHasName n : d.names) {
                    Field f = (Field) n;
                    Expr form = s.decl.get().join(f).in(d.expr);
                    if (s.isOne != null)
                        throw new RuntimeException("Not implemented yet!");
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

    private List<Sort> getSorts(Expr e) {
        Type.ProductType it = removeRClosure(e).type().iterator().next();
        List<Sort> sorts = new ArrayList<>(it.arity());
        for (int i = 0; i < it.arity(); i++)
            sorts.add(JavaConverters.asJavaIterable(cfunc(it.get(i)).argSorts()).iterator().next());
        return sorts;
    }

    private List<Var> getVars(int numVars) {
        List<Var> vars = new ArrayList<>();
        for (int i = 0; i < numVars; i++)
            vars.add(Term.mkVar(nameGenerator.freshName("var")));
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

    private boolean isExprVar(Expr a) {
        if (a instanceof ExprVar)
            return !letMappings.has((ExprVar) a);
        if (a instanceof ExprUnary && ((ExprUnary) a).sub instanceof ExprVar)
            return !letMappings.has((ExprVar) ((ExprUnary) a).sub);
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
                env.put(x, Term.mkVar(nameGenerator.freshName("var")));
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
                // check scope of x.sub and add all values
                throw new RuntimeException("Not implemented yet!");
            case RCLOSURE :
                if (envVars.get(x).size() != 2)
                    throw new ErrorFatal(x.pos, "Two rclosure variables (" + x + ") not provided!");
                return closure(x, false);
            case CLOSURE :
                if (envVars.get(x).size() != 2)
                    throw new ErrorFatal(x.pos, "Two closure variables (" + x + ") not provided!");
                return closure(x, true);
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprUnary.visit()");
    }

    private Term lone(Expr e) {
        List<Sort> sorts = getSorts(e);
        List<Var> vars = getVars(sorts.size());
        envVars.put(e, vars);
        Term t = cterm(e);
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
        List<Var> vars2 = getVars(sorts.size());
        envVars.put(e, vars2);
        t = Term.mkAnd(Term.mkExists(getAnnotatedVars(vars, sorts), t), Term.mkForall(getAnnotatedVars(vars2, sorts), Term.mkImp(cterm(e), Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkImp(t, compareVars(vars, vars2))))));
        envVars.remove(e);
        return t;
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
        List<Sort> sorts = getSorts(e);
        List<List<Term>> domainValues = new ArrayList<>();
        if (!cache.has(e)) {
            List<Sort> argSorts = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            List<Var> vars = new ArrayList<>(e.type().arity()+bve.boundVars.size());
            envVars.put(e, getVars(e.type().arity()));
            Term t = cterm(e);
            for (ExprVar bv : bve.boundVars) {
                argSorts.add(getSorts(bv).get(0));
                vars.add(env.get(bv));
            }
            vars.addAll(envVars.get(e));
            argSorts.addAll(sorts);
            envVars.remove(e);
            String funcName = nameGenerator.freshName("func");
            cache.put(e, frame.addFuncDecl(funcName, argSorts, Sort.Int()));
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
        Term term = Term.mkApp(cache.get(e).name(), appValues.get(0));
        for (int i = 1; i < appValues.size(); i++)
            term = Term.mkPlus(term, Term.mkApp(cache.get(e).name(), appValues.get(i)));
        return term;
    }

    private Term closure(ExprUnary x, boolean c) {
        Term t = cterm(x.sub);
        if (!(t instanceof App)) {
            BoundVariableEliminator bve = new BoundVariableEliminator(x.sub);
            List<Term> args = new ArrayList<>(bve.boundVars.size()+2);
            if (!cache.has(x.sub)) {
                List<Var> vars = new ArrayList<>(bve.boundVars.size()+2);
                List<Sort> sorts = new ArrayList<>(bve.boundVars.size()+2);
                envVars.put(x.sub, getVars(2));
                t = cterm(x.sub);
                for (ExprVar bv : bve.boundVars) {
                    sorts.add(getSorts(bv).get(0));
                    vars.add(env.get(bv));
                }
                vars.addAll(envVars.get(x.sub));
                sorts.addAll(getSorts(x.sub));
                envVars.remove(x.sub);
                String funcName = nameGenerator.freshName("func");
                cache.put(x.sub, frame.addFuncDecl(funcName, sorts, Sort.Bool()));
                frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkIff(Term.mkApp(funcName, vars), t)));
            }
            for (ExprVar bv : bve.boundVars) {
                env.remove(bv);
                args.add(env.get(bv));
            }
            args.addAll(envVars.get(x.sub));
            t = Term.mkApp(cache.get(x.sub).name(), args);
        }
        // look at order of variables in app and compare to envvars, if not introduce new function and add axiom, change t to new app
        envVars.remove(x.sub);
        App app = (App) t;
        List<Term> args = new ArrayList<>(app.getArguments());
        int idx1 = args.indexOf(envVars.get(x).get(0));
        int idx2 = args.indexOf(envVars.get(x).get(1));
        if (idx1 > idx2) {
            args.set(idx1, envVars.get(x).get(1));
            args.set(idx2, envVars.get(x).get(0));
            List<Sort> sorts = new ArrayList<>();
            for (Sort s : JavaConverters.asJavaIterable(frame.getFuncDecl(app.getFunctionName()).argSorts()))
                sorts.add(s);
            cache.put(x.sub, frame.addFuncDecl(nameGenerator.freshName("func"), sorts, Sort.Bool()));
            List<Var> vars = args.stream().map(a -> (Var) a).collect(Collectors.toList());
            app = (App) Term.mkApp(cache.get(x.sub).name(), args);
            frame.addAxiom(Term.mkForall(getAnnotatedVars(vars, sorts), Term.mkIff(app, t)));
        }
        return c ? Term.mkClosure(app, envVars.get(x).get(0), envVars.get(x).get(1)) : Term.mkReflexiveClosure(app, envVars.get(x).get(0), envVars.get(x).get(1));    
    }

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
            return Term.mkEq(envVars.get(x).get(0), ans);
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
        FuncDecl func = frame.a2f(x);
        if (func == null) {
            Var v = frame.a2c(x);
            if (v == null)
                throw new ErrorFatal(x.pos, "Sig \"" + x + "\" is not bound to a legal value during translation.\n");
            return Term.mkEq(envVars.get(x).get(0), v);
        }
        if (envVars.has(x))
            return Term.mkApp(func.name(), envVars.get(x));
        return func;
    }

    /* ============================= */
    /* Evaluates an ExprCall node. */
    /* ============================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprCall x) throws Err {
        final Func f = x.fun;
        final Expr body = f.getBody();
        if (body.type().arity() < 0 || body.type().arity() != f.returnDecl.type().arity())
            throw new ErrorType(body.span(), "Function return value not fully resolved.");
        final int n = f.count();
        int maxRecursion = opt.unrolls;
        for (Func ff : current_function)
            if (ff == f) {
                if (maxRecursion < 0) {
                    throw new ErrorSyntax(x.span(), "" + f + " cannot call itself recursively!");
                }
                if (maxRecursion == 0) {
                    Type t = f.returnDecl.type();
                    if (t.is_bool)
                        return Term.mkBottom();
                    if (t.is_int())
                        return new IntegerLiteral(0);
                    return Term.mkTop();
                }
                maxRecursion--;
            }
        Env<ExprVar, Var> newenv = new Env<ExprVar, Var>();
        List<ExprVar> exprList = new ArrayList<>();
        for (int i = 0; i < n; i++) {
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
            Sort sort = getSorts(elem).get(0);
            Sort ord = JavaConverters.asJavaIterable(cfunc(first.left).argSorts()).iterator().next();
            FuncDecl fst = cfunc(first.right);
            FuncDecl nxt = cfunc(next.right);
            for (int i = 1; i < frame.getScope(sort); i++)
                frame.addAxiom(Term.mkNot(Term.mkApp(fst.name(), List.of(Term.mkDomainElement(1, ord), Term.mkDomainElement(i+1, sort)))));
            for (int i = 0; i < frame.getScope(sort); i++)
                for (int j = 0; j < frame.getScope(sort); j++)
                    if (i+1 == j)
                        frame.addAxiom(Term.mkApp(nxt.name(), List.of(Term.mkDomainElement(1, ord), Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort))));
                    else
                        frame.addAxiom(Term.mkNot(Term.mkApp(nxt.name(), List.of(Term.mkDomainElement(1, ord), Term.mkDomainElement(i+1, sort), Term.mkDomainElement(j+1, sort)))));
            return Term.mkApp(fst.name(), List.of(Term.mkDomainElement(1, ord), Term.mkDomainElement(1, sort)));
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
                return Term.mkLT(cterm(a), cterm(b));
            case LTE :
                return Term.mkLE(cterm(a), cterm(b));
            case GT :
                return Term.mkGT(cterm(a), cterm(b));
            case GTE :
                return Term.mkGE(cterm(a), cterm(b));
            case NOT_LT :
                return Term.mkNot(Term.mkLT(cterm(a), cterm(b)));
            case NOT_LTE :
                return Term.mkNot(Term.mkLE(cterm(a), cterm(b)));
            case NOT_GT :
                return Term.mkNot(Term.mkGT(cterm(a), cterm(b)));
            case NOT_GTE :
                return Term.mkNot(Term.mkGE(cterm(a), cterm(b)));
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
            case EQUALS :
                return equals(a, b);
            case NOT_EQUALS :
                return Term.mkNot(equals(a, b));
            case AND :
                return Term.mkAnd(cterm(a), cterm(b));
            case OR :
                return Term.mkOr(cterm(a), cterm(b));
            case IFF :
                return Term.mkIff(cterm(a), cterm(b));
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
                return domain(x);
            case RANGE :
                return range(x);
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
        envVars.put(left, vars);
        envVars.put(right, vars);
        Term t;
        switch (right.mult()) {
            case EXACTLYOF :
                t = Term.mkIff(cterm(left), cterm(right));
                envVars.remove(left);
                envVars.remove(right);
                return Term.mkForall(getAnnotatedVars(vars, getSorts(left)), t);
            case ONEOF :
                if (field && opt.useFunctions)
                    return Term.mkTop();
                t = Term.mkImp(cterm(left), cterm(right));
                envVars.remove(left);
                envVars.remove(right);
                return Term.mkAnd(one(left), Term.mkForall(getAnnotatedVars(vars, getSorts(left)), t));
            case LONEOF :
                t = Term.mkImp(cterm(left), cterm(right));
                envVars.remove(left);
                envVars.remove(right);
                return Term.mkAnd(lone(left), Term.mkForall(getAnnotatedVars(vars, getSorts(left)), t));
            case SOMEOF :
                t = Term.mkImp(cterm(left), cterm(right));
                envVars.remove(left);
                envVars.remove(right);
                return Term.mkAnd(some(left), Term.mkForall(getAnnotatedVars(vars, getSorts(left)), t));
            default :
                if (field)
                    return Term.mkTop();
                t = Term.mkImp(cterm(left), cterm(right));
                envVars.remove(left);
                envVars.remove(right);
                return Term.mkForall(getAnnotatedVars(vars, getSorts(left)), t);
        }
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
            if (!(tmp instanceof App && sorts.size() == 1 && sorts.get(0).name().equals(((App) tmp).getFunctionName().split("/")[1])))
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
            if (!(tmp instanceof App && sorts.size() == 1 && sorts.get(0).name().equals(((App) tmp).getFunctionName().split("/")[1])))
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
        vars.addAll(getVars(1));
        List<Var> lVars = new ArrayList(envVars.get(e).subList(0, a.type().arity()-1));
        lVars.addAll(vars);
        List<Var> rVars = new ArrayList(vars);
        rVars.addAll(envVars.get(e).subList(a.type().arity()-1, e.type().arity()));
        envVars.put(a, lVars);
        envVars.put(b, rVars);
        Term l = cterm(a), r = cterm(b);
        envVars.remove(a);
        envVars.remove(b);
        return Term.mkExists(getAnnotatedVars(vars, List.of(getSorts(b).get(0))), Term.mkAnd(l, r));
    }

    private Term domain(ExprBinary e) {
        Expr a = e.left, b = e.right;
        List<Var> lVars = getVars(1);
        List<Var> rVars = new ArrayList(lVars);
        rVars.addAll(envVars.get(e));
        envVars.put(a, lVars);
        envVars.put(b, rVars);
        Term l = cterm(a), r = cterm(b);
        envVars.remove(a);
        envVars.remove(b);
        return Term.mkExists(getAnnotatedVars(lVars, getSorts(a)), Term.mkAnd(l, r));
    }

    private Term range(ExprBinary e) {
        Expr a = e.left, b = e.right;
        List<Var> rVars = getVars(1);
        List<Var> lVars = new ArrayList(envVars.get(e));
        lVars.addAll(rVars);
        envVars.put(a, lVars);
        envVars.put(b, rVars);
        Term l = cterm(a), r = cterm(b);
        envVars.remove(a);
        envVars.remove(b);
        return Term.mkExists(getAnnotatedVars(rVars, getSorts(b)), Term.mkAnd(l, r));
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
            List<Var> vars = getVars(1);
            envVars.put(b, List.of(vars.get(0)));
            t = cterm(b);
            envVars.remove(b);
            envVars.put(e, List.of(vars.get(0)));
            t = Term.mkForall(getAnnotatedVars(vars, getSorts(e)), Term.mkIff(cterm(e), t));
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
        List<Sort> sorts = getSorts(b);
        List<Var> vars = getVars(sorts.size());
        envVars.put(a, vars);
        envVars.put(b, vars);
        Term t = Term.mkIff(cterm(a), cterm(b));
        envVars.remove(a);
        envVars.remove(b);
        return Term.mkForall(getAnnotatedVars(vars, sorts), t);
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
                    if (!(tmp instanceof App && sort.name().equals(((App) tmp).getFunctionName().split("/")[1])))
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
        if (!cache.has(sub)) {
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
            String funcName = nameGenerator.freshName("func");
            cache.put(sub, frame.addFuncDecl(funcName, sorts, Sort.Bool()));
            frame.addAxiom(getQtTerm(false, getAnnotatedVars(vars, sorts), termList, Term.mkIff(Term.mkApp(funcName, vars), term)));
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