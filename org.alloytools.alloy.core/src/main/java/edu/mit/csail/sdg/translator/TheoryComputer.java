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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Type;
import fortress.data.NameGenerator;
import fortress.data.IntSuffixNameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import kodkod.instance.Bounds;

/**
 * Immutable; this class assigns each sig and field to some Fortress sort or function, then sets the scope.
 */

final class TheoryComputer {

    // It calls these A4Solution methods...
    // a2k(), a2f(), addSort(), addSig(), addFuncDecl(), addTupleMapping(), addAxiom(), getBounds()

    /**
     * Stores the reporter that will receive diagnostic messages.
     */
    private final A4Reporter        rep;

    /**
     * Stores the scope, bounds, and other settings necessary for performing a
     * solve.
     */
    private final A4Solution        sol;

    private final ScopeComputer     sc;

    /**
     * Stores the bounds created by Kodkod
     */
    private final Bounds            bounds;

    private final A4Options         opt;

    /** Keeps track of all sort/function/var names */
    private final NameGenerator nameGenerator;

    public List<Sig>                notPred;

    public int                      cnt;

    // ==============================================================================================================//

    NameGenerator nameGenerator() {
        return nameGenerator;
    }

    public Var getFreshVar() {
        cnt++;
        return Term.mkVar("var_"+cnt); 
    }

    private Term getTerm(Sig s, Var arg) {
        return notPred.contains(s) ? Term.mkNot(Term.mkApp(sol.a2f(s).name(), arg)) : Term.mkApp(s.label, arg);
    }

    // ==============================================================================================================//

    private void allocatePrimSig(PrimSig sig) {
        String sortName = "_"+sig.label;
        nameGenerator.forbidName(sortName);
        Sort sort = sol.addSort(sortName, sc.sig2scope(sig));
        // Recursively add all functions, and form the union of them
        nameGenerator.forbidName(sig.label);
        if (opt.useScalars && sc.isExact(sig) && sc.sig2scope(sig) == 1) {
            Var c = Term.mkVar(sig.label);
            sol.addSig(sig, c.of(sort));
        } else {
            if (sc.isExact(sig) && opt.exactScopes)
                sol.addSig(sig, sort);
            else {
                FuncDecl func = sol.addFuncDecl(sig.label, List.of(sort), Sort.Bool());
                sol.addSig(sig, func);
                if (sc.isExact(sig)) {
                    Var v = getFreshVar();
                    sol.addAxiom(Term.mkForall(v.of(sort), Term.mkApp(sig.label, v)));
                }
            }
        }
        allocateSubsetSig(sig, sort);
    }

    private void allocateSubsetSig(PrimSig sig, Sort sort) {
        Var v = getFreshVar();
        Term sum = null;
        List<Var> constants = new ArrayList<>();
        List<FuncDecl> funcs = new ArrayList<>();
        List<Term> terms = new ArrayList<>();
        boolean isExact = sol.a2s(sig) != null;
        boolean applyOpt = opt.sigHeirarchy && sig.isTopLevel() && sc.isExact(sig) && sig.isAbstract != null && sig.children().size() == 2;
        for (PrimSig child : sig.children()) {
            if (applyOpt && sum != null) {
                sol.addSig(child, sol.a2f(sig.children().get(0)));
                notPred.add(child);
                sum = null;
                allocateSubsetSig(child, sort);
            } else {
                nameGenerator.forbidName(child.label);
                boolean check = false;
                if (opt.useScalars && sc.isExact(child) && sc.sig2scope(child) == 1) {
                    Var c = Term.mkVar(child.label);
                    sol.addSig(child, c.of(sort));
                    if (!isExact)
                        sol.addAxiom(getTerm(sig, sol.a2c(child).variable()));
                    constants.add(c);
                    check = true;
                } else {
                    FuncDecl func = sol.addFuncDecl(child.label, List.of(sort), Sort.Bool());
                    sol.addSig(child, func);
                    if (!isExact)
                        sol.addAxiom(Term.mkForall(v.of(sort), Term.mkImp(Term.mkApp(child.label, v), getTerm(sig, v))));
                    funcs.add(func);
                    if (sc.isExact(child))
                        sol.addAxiom(exactlyN(func, sc.sig2scope(child)));
                    if (sc.sig2scope(sig) != sc.sig2scope(child) && !sc.isExact(child))
                        sol.addAxiom(atMostN(func, sc.sig2scope(child)));
                }
                allocateSubsetSig(child, sort);
                if (sum == null) {
                    sum = check ? Term.mkEq(v, sol.a2c(child).variable()) : Term.mkApp(child.label, v);
                    continue;
                }
                Term childTerm = check ? Term.mkEq(v, sol.a2c(child).variable()) : Term.mkApp(child.label, v);
                // subsigs are disjoint
                terms.add(Term.mkForall(v.of(sort), Term.mkNot(Term.mkAnd(sum, childTerm))));
                sum = Term.mkOr(sum, childTerm);
            }
        }
        if (constants.size() > 1)
            sol.addAxiom(Term.mkDistinct(constants));
        if (constants.isEmpty())
            for (Term t : terms)
                sol.addAxiom(t);
        for (FuncDecl f : funcs)
            for (Var c : constants)
                sol.addAxiom(Term.mkNot(Term.mkApp(f.name(), c)));
        if (sig.isAbstract != null && sum != null)
            if (isExact)
                sol.addAxiom(Term.mkForall(v.of(sort), sum));
            else
                sol.addAxiom(Term.mkForall(v.of(sort), Term.mkImp(getTerm(sig, v), sum)));
    }

    private Term atMostN(FuncDecl f, int n) {
        List<Var> vars = new ArrayList<>();
        List<AnnotatedVar> avars = new ArrayList<>();
        List<Term> andList = new ArrayList<>(), orList = new ArrayList<>();
        Sort sort = f.argSorts().head();
        for (int i = 0; i <= n; i++) {
            Var v = getFreshVar();
            for (Var vv : vars) {
                orList.add(Term.mkEq(v, vv));
            }
            vars.add(v);
            avars.add(v.of(sort));
            andList.add(Term.mkApp(f.name(), v));
        }
        return Term.mkForall(avars, Term.mkImp(Term.mkAnd(andList), Term.mkOr(orList)));
    }

    private Term exactlyN(FuncDecl f, int n) {
        List<Var> vars = new ArrayList<>();
        List<AnnotatedVar> avars = new ArrayList<>();
        List<Term> andList = new ArrayList<>(), orList = new ArrayList<>();
        Sort sort = f.argSorts().head();
        for (int i = 0; i < n; i++) {
            Var v = getFreshVar();
            for (Var vv : vars) {
                andList.add(Term.mkNot(Term.mkEq(v, vv)));
            }
            vars.add(v);
            avars.add(v.of(sort));
        }
        Var v = getFreshVar();
        for (Var vv : vars) {
            orList.add(Term.mkEq(v, vv));
        }
        andList.add(Term.mkImp(Term.mkApp(f.name(), v), Term.mkOr(orList)));
        return Term.mkExists(avars, Term.mkForall(v.of(sort), Term.mkAnd(andList)));
    }

    // ==============================================================================================================//

    /**
     * Computes the theory for sigs/fields, then construct a TheoryComputer object
     * that you can query.
     */
    private TheoryComputer(A4Reporter rep, A4Solution sol, Iterable<Sig> sigs, ScopeComputer sc, A4Options opt) {
        this.rep = rep;
        this.sol = sol;
        this.sc = sc;
        this.opt = opt;
        this.bounds = sol.getBounds();
        this.nameGenerator = new IntSuffixNameGenerator(scala.collection.immutable.Set$.MODULE$.<String>empty(), 0);
        this.notPred = new ArrayList<>();
        this.cnt = 0;
        // Bound the sigs and fields
        for (Sig s : sigs)
            if (!s.builtin && s.isTopLevel() && !(opt.orderingModule && s.label.split("/")[1].equals("Ord")))
                allocatePrimSig((PrimSig) s);
        for (Sig s : sigs) {
            if (s.builtin || (opt.orderingModule && s.label.split("/")[1].equals("Ord")))
                continue;
            for (Field f : s.getFields()) {
                Type t = f.type();
                List<Sort> args = new ArrayList<>(t.arity());
                List<Var> vars = new ArrayList<>(t.arity());
                List<AnnotatedVar> avars = new ArrayList<>(t.arity());
                List<Term> sum = new ArrayList<>();
                for (PrimSig p : t.fold().get(0)) {
                    Sort tmp = sol.a2s(p);
                    Sort sort = tmp != null ? tmp : sol.a2f(p).argSorts().head();
                    args.add(sort);
                    Var v = getFreshVar();
                    vars.add(v);
                    avars.add(v.of(sort));
                    if (tmp == null)
                        sum.add(getTerm(p, v));
                }
                boolean isFunc = false;
                if (opt.useFunctions) {
                    Expr expr = f.decl().expr, prev = expr;
                    while (expr instanceof ExprBinary && expr.mult != 0 && ((ExprBinary) expr).op.isArrow) {
                        prev = expr;
                        expr = ((ExprBinary) expr).right;
                    }
                    if (prev.mult == 1) {
                        if (((ExprUnary) prev).op == ExprUnary.Op.ONEOF)
                            isFunc = true;
                    } else if (prev.mult == 2) {
                        switch (((ExprBinary) prev).op) {
                            case ANY_ARROW_ONE :
                            case SOME_ARROW_ONE :
                            case ONE_ARROW_ONE :
                            case LONE_ARROW_ONE :
                                isFunc = true;
                        }
                    }
                    if (isFunc) {
                        Sort returnType = args.remove(args.size() - 1);
                        Var returnVar = vars.remove(vars.size() - 1);
                        FuncDecl func = sol.addFuncDecl(s.label + "." + f.label, args, returnType);
                        sol.addField(f, func);
                        if (sum.size() > 0)
                            sol.addAxiom(Term.mkForall(avars, Term.mkImp(Term.mkEq(Term.mkApp(s.label + "." + f.label, vars), returnVar), Term.mkAnd(sum))));
                    }
                }
                if (!opt.useFunctions || !isFunc) {
                    FuncDecl func = sol.addFuncDecl(s.label + "." + f.label, args, Sort.Bool());
                    sol.addField(f, func);
                    if (sum.size() > 0)
                        sol.addAxiom(Term.mkForall(avars, Term.mkImp(Term.mkApp(s.label + "." + f.label, vars), Term.mkAnd(sum))));
                }
            }
            // Add any additional SIZE constraints
            // if (s.isOne != null && sol.a2c(s) == null) {
            //     Var v1 = Term.mkVar(nameGenerator.freshName("var"));
            //     Var v2 = Term.mkVar(nameGenerator.freshName("var"));
            //     Sort sort = sol.a2f(s).argSorts().head();
            //     sol.addAxiom(Term.mkAnd(Term.mkExists(v1.of(sort), getTerm(s, v1)), Term.mkForall(v1.of(sort), Term.mkImp(getTerm(s, v1), Term.mkForall(v2.of(sort), Term.mkImp(getTerm(s, v2), Term.mkEq(v1, v2)))))));
            // } else if (s.isSome != null && !sig2sort.containsKey(s)) {
            //     Var v = Term.mkVar(nameGenerator.freshName("var"));
            //     Sort sort = sol.a2f(s).argSorts().head();
            //     sol.addAxiom(Term.mkExists(v.of(sort), getTerm(s, v)));
            // } else if (s.isLone != null && !sig2sort.containsKey(s)) {
            //     Var v1 = Term.mkVar(nameGenerator.freshName("var"));
            //     Var v2 = Term.mkVar(nameGenerator.freshName("var"));
            //     Sort sort = sol.a2f(s).argSorts().head();
            //     sol.addAxiom(Term.mkForall(v1.of(sort), Term.mkImp(getTerm(s, v1), Term.mkForall(v2.of(sort), Term.mkImp(getTerm(s, v2), Term.mkEq(v1, v2))))));
            // }
        }
    }

    // ==============================================================================================================//

    /**
     * Assign each sig and field to some Kodkod relation or expression, then set the
     * bounds.
     */
    static TheoryComputer compute(A4Reporter rep, A4Solution sol, Iterable<Sig> sigs, ScopeComputer sc, A4Options opt) {
        TheoryComputer tc = new TheoryComputer(rep, sol, sigs, sc, opt);
        return tc;
    }
}