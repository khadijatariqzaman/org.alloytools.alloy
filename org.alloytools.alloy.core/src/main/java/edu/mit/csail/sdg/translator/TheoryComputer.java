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
import scala.collection.JavaConverters;

import edu.mit.csail.sdg.alloy4.A4Reporter;
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

    /** Keeps track of all sort/function/var names */
    private final NameGenerator nameGenerator;

    // ==============================================================================================================//

    NameGenerator getNameGenerator() {
        return nameGenerator;
    }

    // ==============================================================================================================//

    private void allocatePrimSig(PrimSig sig) {
        String sortName = "sort"+sig.label;
        nameGenerator.forbidName(sortName);
        Sort sort = sol.addSort(sortName, sc.sig2scope(sig));
        // Recursively add all functions, and form the union of them
        allocateSubsetSig(sig, sort);
    }

    private FuncDecl allocateSubsetSig(PrimSig sig, Sort sort) {
        nameGenerator.forbidName(sig.label);
        FuncDecl func = sol.addFuncDecl(sig.label, List.of(sort), Sort.Bool());
        sol.addSig(sig, func);
        Var v = Term.mkVar(nameGenerator.freshName("var"));
        if (sc.isExact(sig))
            sol.addAxiom(exactlyN(func, sc.sig2scope(sig)));
        Term sum = null;
        for (PrimSig child : sig.children()) {
            FuncDecl f = allocateSubsetSig(child, sort);
            sol.addAxiom(Term.mkForall(v.of(sort), Term.mkImp(Term.mkApp(child.label, v), Term.mkApp(sig.label, v))));
            if (sum == null) {
                sum = Term.mkApp(child.label, v);
                continue;
            }
            Term childTerm = Term.mkApp(child.label, v);
            // subsigs are disjoint
            sol.addAxiom(Term.mkForall(v.of(sort), Term.mkNot(Term.mkAnd(sum, childTerm))));
            sum = Term.mkOr(sum, childTerm);
            if (sc.sig2scope(sig) != sc.sig2scope(child) && !sc.isExact(child))
                sol.addAxiom(atMostN(func, sc.sig2scope(sig)));
        }
        if (sig.isAbstract != null && sum != null)
            sol.addAxiom(Term.mkForall(v.of(sort), Term.mkImp(Term.mkApp(sig.label, v), sum)));
        return func;
    }

    private Term atMostN(FuncDecl f, int n) {
        List<Var> vars = new ArrayList<>();
        List<AnnotatedVar> avars = new ArrayList<>();
        List<Term> andList = new ArrayList<>(), orList = new ArrayList<>();
        Sort sort = JavaConverters.asJavaIterable(f.argSorts()).iterator().next();
        for (int i = 0; i <= n; i++) {
            Var v = Term.mkVar(nameGenerator.freshName("var"));
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
        Sort sort = JavaConverters.asJavaIterable(f.argSorts()).iterator().next();
        for (int i = 0; i < n; i++) {
            Var v = Term.mkVar(nameGenerator.freshName("var"));
            for (Var vv : vars) {
                andList.add(Term.mkNot(Term.mkEq(v, vv)));
            }
            vars.add(v);
            avars.add(v.of(sort));
            andList.add(Term.mkApp(f.name(), v));
        }
        Var v = Term.mkVar(nameGenerator.freshName("var"));
        for (Var vv : vars) {
            orList.add(Term.mkEq(v, vv));
        }
        andList.add(Term.mkForall(v.of(sort), Term.mkImp(Term.mkApp(f.name(), v), Term.mkOr(orList))));
        return Term.mkExists(avars, Term.mkAnd(andList));
    }

    // ==============================================================================================================//

    /**
     * Computes the theory for sigs/fields, then construct a TheoryComputer object
     * that you can query.
     */
    private TheoryComputer(A4Reporter rep, A4Solution sol, Iterable<Sig> sigs, ScopeComputer sc) {
        this.rep = rep;
        this.sol = sol;
        this.sc = sc;
        this.bounds = sol.getBounds();
        this.nameGenerator = new IntSuffixNameGenerator(scala.collection.immutable.Set$.MODULE$.<String>empty(), 0);
        // Bound the sigs
        for (Sig s : sigs)
            if (!s.builtin && s.isTopLevel())
                allocatePrimSig((PrimSig) s);
        // TODO: total ordering
        // Bound the fields
        for (Sig s : sigs) {
            for (Field f : s.getFields()) {
                Type t = f.type();
                List<Sort> args = new ArrayList<>(t.arity());
                List<Var> vars = new ArrayList<>(t.arity());
                List<AnnotatedVar> avars = new ArrayList<>(t.arity());
                Term sum = null;
                for (PrimSig p : t.fold().get(0)) {
                    Sort sort = JavaConverters.asJavaIterable(sol.a2f(p).argSorts()).iterator().next();
                    args.add(sort);
                    Var v = Term.mkVar(nameGenerator.freshName("var"));
                    vars.add(v);
                    avars.add(v.of(sort));
                    if (sum == null)
                        sum = Term.mkApp(p.label, v);
                    else
                        sum = Term.mkAnd(sum, Term.mkApp(p.label, v));
                }
                FuncDecl func = sol.addFuncDecl(s.label + "." + f.label, args, Sort.Bool());
                sol.addField(f, func);
                sol.addAxiom(Term.mkForall(avars, Term.mkImp(Term.mkApp(s.label + "." + f.label, vars), sum)));
            }
        }
        // TODO: Add any additional SIZE constraints
    }

    // ==============================================================================================================//

    /**
     * Assign each sig and field to some Kodkod relation or expression, then set the
     * bounds.
     */
    static NameGenerator compute(A4Reporter rep, A4Solution sol, Iterable<Sig> sigs, ScopeComputer sc) {
        TheoryComputer tc = new TheoryComputer(rep, sol, sigs, sc);
        return tc.getNameGenerator();
    }
}