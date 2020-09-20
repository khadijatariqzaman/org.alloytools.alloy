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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;

import fortress.msfol.AndList;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.App;
import fortress.msfol.BitVectorLiteral;
import fortress.msfol.BuiltinApp;
import fortress.msfol.Closure;
import fortress.msfol.Distinct;
import fortress.msfol.DomainElement;
import fortress.msfol.EnumValue;
import fortress.msfol.Eq;
import fortress.msfol.Exists;
import fortress.msfol.Forall;
import fortress.msfol.FuncDecl;
import fortress.msfol.Iff;
import fortress.msfol.IfThenElse;
import fortress.msfol.IntDiv$;
import fortress.msfol.IntGE$;
import fortress.msfol.IntGT$;
import fortress.msfol.IntLE$;
import fortress.msfol.IntLT$;
import fortress.msfol.IntMod$;
import fortress.msfol.IntMult$;
import fortress.msfol.IntNeg$;
import fortress.msfol.IntPlus$;
import fortress.msfol.IntSub$;
import fortress.msfol.Implication;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Not;
import fortress.msfol.OrList;
import fortress.msfol.ReflexiveClosure;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.TermVisitor;
import fortress.msfol.Theory;
import fortress.msfol.Var;

import scala.collection.Iterator;
import scala.collection.JavaConverters;
import scala.collection.immutable.Seq;

/**
 * Translate a Fortress theory to an equivalent Java program that solves the
 * axioms in the theory.
 */

public final class TranslateFortressToJava implements TermVisitor<String> {
    public static String convert(Theory theory, Map<Sort, Integer> sortScopes) {
        StringWriter string = new StringWriter();
        PrintWriter file = new PrintWriter(string);
        new TranslateFortressToJava(theory, sortScopes, file);
        if (file.checkError()) {
            return "";
        } else {
            return string.toString();
        }
    }

    /** The PrintWriter that is receiving the text. */
    private final PrintWriter file;

    /** This caches terms that we have already generated. */
    private final HashMap<String, String> map = new HashMap<>();

        /**
     * Given a sort, return its name (if no name has been chosen, then make a new
     * name)
     */
        private String makename(String s) {
            if (map.containsKey(s))
                return null;
            String name = "x" + (map.size());
            map.put(s, name);
            return name;
        }

    /**
     * Constructor is private, so that the only way to access this class is via the
     * static convert() method.
     */
    private TranslateFortressToJava(Theory theory, Map<Sort, Integer> sortScopes, PrintWriter pw) {
        file = pw;
        file.printf("import fortress.msfol.*;%n");
        file.printf("import fortress.modelfind.*;%n%n");
        file.printf("import java.util.List;%n%n");

        file.printf("public final class Test {%n%n");
        file.printf("public static void main(String[] args) throws Exception {%n");
        file.printf("%nTheory theory = Theory.empty();");
        map.put(Sort.Bool().toString(), "Sort.Bool()");
        map.put(Sort.Int().toString(), "Sort.Int()");
        for (Sort sort : theory.sortsJava()) {
            String name = makename(sort.toString());
            if (!sort.isBuiltin()) {
                file.printf("%nSort %s = Sort.mkSortConst(\"%s\");", name, sort.name());
                file.printf("%ntheory = theory.withSort(%s);%n", name);
            }
        }
        Map<Sort, Seq<EnumValue>> enumConstantsMap = JavaConverters.mapAsJavaMap(theory.enumConstants());
        for (Sort sort : enumConstantsMap.keySet()) {
            String name = makename(sort.toString());
            if (!sort.isBuiltin()) {
                file.printf("%nSort %s = Sort.mkSortConst(\"%s\");", name, sort.name());
                file.printf("%ntheory = theory.withEnumSort(%s, List.of(", name);
                boolean check = false;
                for (EnumValue eval : JavaConverters.asJavaIterable(enumConstantsMap.get(sort))) {
                    if (check) { file.printf(","); }
                    file.printf("Term.mkEnumValue(\"%s\")", eval.toString());
                    check = true;
                }
                file.printf("));%n");
            }
        }
        for (FuncDecl func : JavaConverters.asJavaIterable(theory.functionDeclarations())) {
            file.printf("%ntheory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl(\"%s\", ", func.name());
            for (Sort sort : JavaConverters.asJavaIterable(func.argSorts())) {
                file.printf("%s, ", map.get(sort.toString()));
            }
            file.printf("%s));%n", map.get(func.resultSort().toString()));
        }
        Iterator<Term> it = theory.axioms().iterator();
        while (it.hasNext()) {
            String result = it.next().accept(this);
            file.printf("%ntheory = theory.withAxiom(%s);%n", result);
        }
        file.printf("%nModelFinder finder = ModelFinder.createDefault();");
        file.printf("%nfinder.setTheory(theory);");
        for (Sort sort : sortScopes.keySet()) {
            file.printf("%nfinder.setAnalysisScope(%s, %d);", map.get(sort.toString()), sortScopes.get(sort));
        }
        file.printf("%ntry{");
        file.printf("%nModelFinderResult res = finder.checkSat();");
        file.printf("%nif (res.equals(ModelFinderResult.Sat())) { System.out.println(finder.viewModel()); }");
        file.printf("%n} catch (Exception e) { e.printStackTrace(); }");
        file.printf("%nSystem.out.println(\"*************************FINISH*****************************\");");
        file.printf("%n}}%n");
        file.close();
    }

    @Override
    public String visitTop() {
        return "Term.mkTop()";
    }

    @Override
    public String visitBottom() {
        return "Term.mkBottom()";
    }

    @Override
    public String visitVar(Var var) {
        String newname = makename(var.toString());
        if (newname == null)
            return map.get(var.toString());
        file.printf("%nVar %s = Term.mkVar(\"%s\");", newname, var.getName());
        return newname;
    }

    @Override
    public String visitEnumValue(EnumValue eval) {
        String newname = makename(eval.toString());
        if (newname == null)
            return map.get(eval.toString());
        file.printf("%nTerm %s = Term.mkEnumValue(%s);", newname, eval.name());
        return newname;
    }

    @Override
    public String visitDomainElement(DomainElement de) {
        String newname = makename(de.toString());
        if (newname == null)
            return map.get(de.toString());
        file.printf("%nTerm %s = Term.mkDomainElement(%d, %s);", newname, de.index(), map.get(de.sort().name()));
        return newname;
    }

    @Override
    public String visitNot(Not not) {
        String newname = makename(not.toString());
        if (newname == null)
            return map.get(not.toString());
        String body = not.body().accept(this);
        file.printf("%nTerm %s = Term.mkNot(%s);", newname, body);
        return newname;
    }

    @Override
    public String visitAndList(AndList and) {
        String newname = makename(and.toString());
        if (newname == null)
            return map.get(and.toString());
        List<String> list = new ArrayList<>();
        for (Term arg : JavaConverters.asJavaIterable(and.arguments()))
            list.add(arg.accept(this));
        file.printf("%nTerm %s = Term.mkAnd(", newname);
        writeToFile(list);
        file.printf(");");
        return newname;
    }

    @Override
    public String visitOrList(OrList or) {
        String newname = makename(or.toString());
        if (newname == null)
            return map.get(or.toString());
        List<String> list = new ArrayList<>();
        for (Term arg : JavaConverters.asJavaIterable(or.arguments()))
            list.add(arg.accept(this));
        file.printf("%nTerm %s = Term.mkOr(", newname);
        writeToFile(list);
        file.printf(");");
        return newname;
    }

    @Override
    public String visitDistinct(Distinct dist) {
        String newname = makename(dist.toString());
        if (newname == null)
            return map.get(dist.toString());
        List<String> list = new ArrayList<>();
        for (Term arg : JavaConverters.asJavaIterable(dist.arguments()))
            list.add(arg.accept(this));
        file.printf("%nTerm %s = Term.mkDistinct(", newname);
        writeToFile(list);
        file.printf(");");
        return newname;
    }

    @Override
    public String visitImplication(Implication imp) {
        String newname = makename(imp.toString());
        if (newname == null)
            return map.get(imp.toString());
        String left = imp.left().accept(this);
        String right = imp.right().accept(this);
        file.printf("%nTerm %s = Term.mkImp(%s, %s);", newname, left, right);
        return newname;
    }

    @Override
    public String visitIff(Iff iff) {
        String newname = makename(iff.toString());
        if (newname == null)
            return map.get(iff.toString());
        String left = iff.left().accept(this);
        String right = iff.right().accept(this);
        file.printf("%nTerm %s = Term.mkIff(%s, %s);", newname, left, right);
        return newname;
    }

    @Override
    public String visitEq(Eq eq) {
        String newname = makename(eq.toString());
        if (newname == null)
            return map.get(eq.toString());
        String left = eq.left().accept(this);
        String right = eq.right().accept(this);
        file.printf("%nTerm %s = Term.mkEq(%s, %s);", newname, left, right);
        return newname;
    }

    @Override
    public String visitApp(App app) {
        String newname = makename(app.toString());
        if (newname == null)
            return map.get(app.toString());
        List<String> list = new ArrayList<>();
        for (Term t : JavaConverters.asJavaIterable(app.arguments()))
            list.add(t.accept(this));
        file.printf("%nTerm %s = Term.mkApp(\"%s\", ", newname, app.functionName());
        writeToFile(list);
        file.printf(");");
        return newname;
    }

    @Override
    public String visitBuiltinApp(BuiltinApp app) {
        String newname = makename(app.toString());
        if (newname == null)
            return map.get(app.toString());
        List<String> list = new ArrayList<>();
        for (Term t : JavaConverters.asJavaIterable(app.arguments()))
            list.add(t.accept(this));
        if (app.function() == IntPlus$.MODULE$)
            file.printf("%nTerm %s = Term.mkPlus(", newname);
        else if (app.function() == IntNeg$.MODULE$)
            file.printf("%nTerm %s = Term.mkNeg(", newname);
        else if (app.function() == IntSub$.MODULE$)
            file.printf("%nTerm %s = Term.mkSub(", newname);
        else if (app.function() == IntMult$.MODULE$)
            file.printf("%nTerm %s = Term.mkMult(", newname);
        else if (app.function() == IntDiv$.MODULE$)
            file.printf("%nTerm %s = Term.mkDiv(", newname);
        else if (app.function() == IntMod$.MODULE$)
            file.printf("%nTerm %s = Term.mkMod(", newname);
        else if (app.function() == IntLE$.MODULE$)
            file.printf("%nTerm %s = Term.mkLE(", newname);
        else if (app.function() == IntLT$.MODULE$)
            file.printf("%nTerm %s = Term.mkLT(", newname);
        else if (app.function() == IntGE$.MODULE$)
            file.printf("%nTerm %s = Term.mkGE(", newname);
        else if (app.function() == IntGT$.MODULE$)
            file.printf("%nTerm %s = Term.mkGT(", newname);
        writeToFile(list);
        file.printf(");");
        return newname;
    }

    @Override
    public String visitClosure(Closure closure) {
        String newname = makename(closure.toString());
        if (newname == null)
            return map.get(closure.toString());
        List<String> list = new ArrayList<>();
        for (Term t : JavaConverters.asJavaIterable(closure.arguments()))
            list.add(t.accept(this));
        file.printf("%nTerm %s = Term.mkClosure((App) Term.mkApp(\"%s\", ", newname, closure.functionName());
        writeToFile(list);
        file.printf("), %s, %s);", map.get(closure.arg1().toString()), map.get(closure.arg2().toString()));
        return newname;
    }

    @Override
    public String visitReflexiveClosure(ReflexiveClosure closure) {
        String newname = makename(closure.toString());
        if (newname == null)
            return map.get(closure.toString());
        List<String> list = new ArrayList<>();
        for (Term t : JavaConverters.asJavaIterable(closure.arguments()))
            list.add(t.accept(this));
        file.printf("%nTerm %s = Term.mkReflexiveClosure((App) Term.mkApp(\"%s\", ", newname, closure.functionName());
        writeToFile(list);
        file.printf("), %s, %s);", map.get(closure.arg1().toString()), map.get(closure.arg2().toString()));
        return newname;
    }

    @Override
    public String visitExists(Exists exists) {
        String newname = makename(exists.toString());
        if (newname == null)
            return map.get(exists.toString());
        List<String> list = new ArrayList<>();
        for (AnnotatedVar avar : JavaConverters.asJavaIterable(exists.vars()))
            list.add(String.format("%s.of(%s)", avar.variable().accept(this), map.get(avar.sort().name())));
        String body = exists.body().accept(this);
        file.printf("%nTerm %s = Term.mkExists(List.of(", newname);
        writeToFile(list);
        file.printf("), %s);", body);
        return newname;
    }

    @Override
    public String visitForall(Forall forall) {
        String newname = makename(forall.toString());
        if (newname == null)
            return map.get(forall.toString());
        List<String> list = new ArrayList<>();
        for (AnnotatedVar avar : JavaConverters.asJavaIterable(forall.vars()))
            list.add(String.format("%s.of(%s)", avar.variable().accept(this), map.get(avar.sort().name())));
        String body = forall.body().accept(this);
        file.printf("%nTerm %s = Term.mkForall(List.of(", newname);
        writeToFile(list);
        file.printf("), %s);", body);
        return newname;
    }

    @Override
    public String visitIntegerLiteral(IntegerLiteral literal) {
        String newname = makename(literal.toString());
        if (newname == null)
            return map.get(literal.toString());
        file.printf("%nTerm %s = new IntegerLiteral(%d);", newname, literal.value());
        return newname;
    }

    @Override
    public String visitBitVectorLiteral(BitVectorLiteral literal) {
        String newname = makename(literal.toString());
        if (newname == null)
            return map.get(literal.toString());
        file.printf("%nTerm %s = new BitVectorLiteral(%d, %d);", newname, literal.value(), literal.bitwidth());
        return newname;
    }

    @Override
    public String visitIfThenElse(IfThenElse ite) {
        String newname = makename(ite.toString());
        if (newname == null)
            return map.get(ite.toString());
        file.printf("%nTerm %s = Term.mkIfThenElse(%s, %s, %s);", newname, ite.condition().accept(this), ite.ifTrue().accept(this), ite.ifFalse().accept(this));
        return newname;
    }

    void writeToFile(List<String> list) {
        boolean check = false;
        for (String t : list) {
            if (check) file.printf(", ");
            file.printf("%s", t);
            check = true;
        }
    }
}