/**
 * ConjunctionOfNormalizedAtomicExpressions.java
 * ---------------------------------
 * Copyright (c) 2015
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.rewriteprover.absyn.*;
import edu.clemson.cs.r2jt.typeandpopulate.MTFunction;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;

import java.util.*;

/**
 * Created by mike on 4/3/2014.
 */
public class ConjunctionOfNormalizedAtomicExpressions {

    private final Registry m_registry;
    protected final List<NormalizedAtomicExpressionMapImpl> m_exprList;
    protected long m_timeToEnd = -1;
    protected boolean m_evaluates_to_false = false;
    private int f_num = 0;
    private String m_current_justification = "";
    private final Map<Integer, Set<NormalizedAtomicExpressionMapImpl>> m_useMap;
    protected final boolean m_forVC_flag;

    /**
     * @param registry the Registry symbols contained in the conjunction will
     *                 reference. This class will add entries to the registry if needed.
     */
    public ConjunctionOfNormalizedAtomicExpressions(Registry registry,
            boolean for_VC) {
        m_registry = registry;
        // Array list is much slower than LinkedList for this application
        m_exprList = new LinkedList<NormalizedAtomicExpressionMapImpl>();
        m_useMap =
                new HashMap<Integer, Set<NormalizedAtomicExpressionMapImpl>>();
        m_forVC_flag = for_VC;
    }

    protected int size() {
        return m_exprList.size();
    }

    protected void clear() {
        m_exprList.clear();
    }

    protected NormalizedAtomicExpressionMapImpl getExprAtPosition(int position) {
        return m_exprList.get(position);
    }

    protected String addExpression(PExp expression, long timeToEnd) {
        m_timeToEnd = timeToEnd;
        return addExpression(expression);
    }

    protected String addExpressionAndTrackChanges(PExp expression,
            long timeToEnd, String justification) {
        m_timeToEnd = timeToEnd;
        m_timeToEnd = Long.MAX_VALUE;
        m_current_justification = justification;
        String rString = "";
        /*boolean haPart = false;
        for (String eS : expression.getSymbolNames()) {
            String root = m_registry.getRootSymbolForSymbol(eS);
            if (m_registry.m_partTypes.contains(root)) {
                haPart = true;
                break;
            }
        }
        if (haPart) {
            List<PExp> frs = makeFRestr(expression);
            for (PExp pf : frs) {
                rString += "[forced] " + pf.toString() + "\n\t" + addExpression(pf);
                System.err.println(pf.toString());
            }
        }*/
        rString += addExpression(expression);
        m_current_justification = "";
        updateUseMap();
        return rString;
    }

    private List<PExp> makeFRestr(PExp pf) {
        ArrayList<PExp> rList = new ArrayList<PExp>();
        if (!pf.getTopLevelOperation().equals("="))
            return rList;
        PExp lhs = pf.getSubExpressions().get(0);
        PExp rhs = pf.getSubExpressions().get(1);
        if (!(lhs.getSubExpressions().size() == 1 && rhs.getSubExpressions()
                .size() == 1))
            return rList;
        PExp lhsArg = lhs.getSubExpressions().get(0);
        PExp rhsArg = rhs.getSubExpressions().get(0);
        if (!lhsArg.toString().equals(rhsArg.toString()))
            return rList;
        if (!m_registry.m_partTypes.contains(m_registry
                .getRootSymbolForSymbol(lhsArg.getTopLevelOperation())))
            return rList;
        ArrayList<PExp> args = new ArrayList<PExp>();
        args.add(new PSymbol(lhs.getType(), lhs.getTypeValue(), lhs
                .getTopLevelOperation()));
        args.add(lhsArg);
        PExp fr1 =
                new PSymbol(m_registry.m_typeGraph.BOOLEAN, null, "FRestr",
                        args);
        args.clear();
        args.add(new PSymbol(lhs.getType(), rhs.getTypeValue(), rhs
                .getTopLevelOperation()));
        args.add(rhsArg);
        PExp fr2 =
                new PSymbol(m_registry.m_typeGraph.BOOLEAN, null, "FRestr",
                        args);
        args.clear();
        args.add(fr1);
        args.add(fr2);
        rList.add(new PSymbol(m_registry.m_typeGraph.BOOLEAN, null, "=", args));
        return rList;
    }

    // Top level
    protected String addExpression(PExp expression) {
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return "";
        }
        String name = expression.getTopLevelOperation();

        if (expression.isEquality()) {
            int lhs = addFormula(expression.getSubExpressions().get(0));
            int rhs = addFormula(expression.getSubExpressions().get(1));
            return mergeOperators(lhs, rhs);
        }
        else if (name.equals("and")) {
            String r = "";
            r += addExpression(expression.getSubExpressions().get(0));
            r += addExpression(expression.getSubExpressions().get(1));
            return r;
        }
        else {
            MTType type = expression.getType();
            PSymbol asPsymbol = (PSymbol) expression;
            int intRepOfOp = addPsymbol(asPsymbol);
            int root = addFormula(expression);
            if (type.isBoolean()) {
                return mergeOperators(m_registry.getIndexForSymbol("true"),
                        root);
            }
        }
        return "";
    }

    // adds a particular symbol to the registry
    protected int addPsymbol(PSymbol ps) {
        String name = ps.getTopLevelOperation();
        MTType type = ps.getType();
        Registry.Usage usage = Registry.Usage.SINGULAR_VARIABLE;
        if (ps.isLiteral()) {
            usage = Registry.Usage.LITERAL;
        }
        else if (ps.isFunction()
                || ps.getType().getClass().getSimpleName().equals("MTFunction")) {
            if (ps.quantification.equals(PSymbol.Quantification.FOR_ALL)) {
                usage = Registry.Usage.HASARGS_FORALL;
            }
            else {
                usage = Registry.Usage.HASARGS_SINGULAR;
            }

        }
        else if (ps.quantification.equals(PSymbol.Quantification.FOR_ALL)) {
            usage = Registry.Usage.FORALL;
        }
        // The type stored with expressions is actually the range type
        // Ex: (S = T):B.
        // However, I need to store types for functions/relations.
        // Building these here.
        // It would be far better to handle this upstream.
        // Currently PExps from theorems have correct type set already
        if (ps.getSubExpressions().size() > 0
                && !type.getClass().getSimpleName().equals("MTFunction")) {
            List<MTType> paramList = new ArrayList<MTType>();
            for (PExp pParam : ps.getSubExpressions()) {
                paramList.add(pParam.getType());
            }
            type = new MTFunction(m_registry.m_typeGraph, type, paramList);
        }
        return m_registry.addSymbol(name, type, usage);
    }

    /* experimentally handling =
     i.e.: (|?S| = 0) = (?S = Empty_String))
     is broken down by addExpression so (|?S| = 0) is an argument
     should return int for true if known to be equal, otherwise return root representative. 
     */
    protected int addFormula(PExp formula) {
        if (formula.isEquality()) {
            int lhs = addFormula(formula.getSubExpressions().get(0));
            PExp r = formula.getSubExpressions().get(1);
            int rhs = addFormula(r);
            lhs = m_registry.findAndCompress(lhs);
            rhs = m_registry.findAndCompress(rhs);
            // This prevents matching of (i=i)=true, which is not built in
            /*if (lhs == rhs) {
                return m_registry.getIndexForSymbol("true");
            }
            else {*/
            // insert =(lhs,rhs) = someNewRoot
            int questEq = m_registry.getIndexForSymbol("=");
            NormalizedAtomicExpressionMapImpl pred =
                    new NormalizedAtomicExpressionMapImpl();
            pred.writeOnto(questEq, 0);
            pred.writeOnto(lhs, 1);
            pred.writeOnto(rhs, 2);
            return addAtomicFormula(pred);
            // }
        }
        PSymbol asPsymbol;
        if (!(formula instanceof PSymbol)) {
            System.err.println("unhandled PExp: " + formula.toString());
            throw new RuntimeException();

        }
        else
            asPsymbol = (PSymbol) formula;
        int intRepOfOp = addPsymbol(asPsymbol);
        // base case
        if (formula.isVariable()) {
            return intRepOfOp;
        }

        NormalizedAtomicExpressionMapImpl newExpr =
                new NormalizedAtomicExpressionMapImpl();
        newExpr.writeOnto(intRepOfOp, 0);
        int pos = 0;
        PExpSubexpressionIterator it = formula.getSubExpressionIterator();
        while (it.hasNext()) {
            PExp p = it.next();
            pos++;
            int root = addFormula(p);
            assert newExpr != null;
            newExpr.writeOnto(root, pos);
        }
        mergeArgsOfEqualityPredicateIfRootIsTrue();
        return addAtomicFormula(newExpr);
    }

    /**
     * @param atomicFormula one sided expression. (= new root) is appended and
     *                      expression is inserted if no match of the side is found. Otherwise
     *                      current root is returned.
     * @return current integer value of root symbol that represents the input.
     */
    private int addAtomicFormula(NormalizedAtomicExpressionMapImpl atomicFormula) {
        // Order terms if operator is commutative
        if (m_registry.isCommutative(atomicFormula.readPosition(0))) {
            atomicFormula = atomicFormula.withOrderedArguments();
        }
        int posIfFound = Collections.binarySearch(m_exprList, atomicFormula);
        if (posIfFound >= 0) {
            return m_exprList.get(posIfFound).readRoot();
        }
        // no such formula exists
        int indexToInsert = -(posIfFound + 1);
        MTType typeOfFormula =
                m_registry.getTypeByIndex(atomicFormula.readPosition(0));
        // this is the full type and is necessarily a function type

        MTType rangeType = ((MTFunction) typeOfFormula).getRange();
        String symName =
                m_registry.getSymbolForIndex(atomicFormula.readPosition(0));
        assert rangeType != null : symName + " has null type";
        // if any of the symbols in atomicFormula are variables (FORALL) make created symbol a variable
        boolean isVar = false;
        for (Integer is : atomicFormula.getKeys()) {
            String s = m_registry.getSymbolForIndex(is);
            if (s.startsWith("¢v")) {
                isVar = true;
                break;
            }
            Registry.Usage us = m_registry.getUsage(s);
            if (us == Registry.Usage.FORALL
                    || us == Registry.Usage.HASARGS_FORALL) {
                isVar = true;
                break;
            }
        }
        int rhs = m_registry.makeSymbol(rangeType, isVar);
        atomicFormula.writeToRoot(rhs);
        m_exprList.add(indexToInsert, atomicFormula);
        return rhs;
    }

    protected String mergeOperators(int a, int b) {
        String rString = "";
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return rString;
        }
        a = m_registry.findAndCompress(a);
        b = m_registry.findAndCompress(b);
        if (a == b)
            return "";
        Stack<Integer> holdingTank = new Stack<Integer>();
        holdingTank.push(a);
        holdingTank.push(b);

        while (holdingTank != null && !holdingTank.empty()) {
            if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
                return rString;
            }
            int opA = m_registry.findAndCompress(holdingTank.pop());
            int opB = m_registry.findAndCompress(holdingTank.pop());
            // Want to replace quantified vars with constant if it is equal to the constant
            int keeper = chooseSymbolToKeep(opA, opB);
            if (keeper == opB) {
                int temp = opA;
                opA = opB;
                opB = temp;
            }
            rString +=
                    m_registry.getSymbolForIndex(opA) + "/"
                            + m_registry.getSymbolForIndex(opB) + ",";
            Stack<Integer> mResult = mergeOnlyArgumentOperators(opA, opB);

            if (mResult != null)
                holdingTank.addAll(mResult);

        }
        return rString;
    }

    // need to choose literals over vars for theorem matching purposes
    // i.e. the theorem expression should keep the literals
    protected int chooseSymbolToKeep(int a, int b) {
        String s = m_registry.m_indexToSymbol.get(a);
        if (s.contains("¢"))
            return b;
        if (m_registry.getUsage(s).equals(Registry.Usage.FORALL))
            return b;
        return a;
    }

    // look for =(x,y)=true in list.  If found call merge(x,y).
    //  = will always be at top of list.
    // These expression will not be removed by this function,
    // but can be removed by merge().
    protected void mergeArgsOfEqualityPredicateIfRootIsTrue() {
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return;
        }
        // loop until end, function op is not =, or =(x,y)=true
        // when found do merge, start again.
        int eqQ = m_registry.getIndexForSymbol("=");
        for (int i = 0; i < m_exprList.size(); ++i) {
            NormalizedAtomicExpressionMapImpl cur = m_exprList.get(i);
            int f = cur.readPosition(0);
            if (f != eqQ) {
                return;
            }
            int t = m_registry.getIndexForSymbol("true");
            int root = cur.readRoot();
            int op1 = cur.readPosition(1);
            int op2 = cur.readPosition(2);
            if (root == t && op1 != op2) {
                mergeOperators(cur.readPosition(1), cur.readPosition(2));
                // mergeOperators will do any other merges that arise.
                i = 0;
            }
        }
    }

    // Return list of modified predicates by their position. Only these can cause new merges.
    // b is replaced by a
    protected Stack<Integer> mergeOnlyArgumentOperators(int a, int b) {
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return null;
        }

        Iterator<NormalizedAtomicExpressionMapImpl> it = m_exprList.iterator();
        Stack<NormalizedAtomicExpressionMapImpl> modifiedEntries =
                new Stack<NormalizedAtomicExpressionMapImpl>();
        Stack<Integer> coincidentalMergeHoldingTank = new Stack<Integer>();
        while (it.hasNext()) {
            NormalizedAtomicExpressionMapImpl curr = it.next();
            if (curr.replaceOperator(b, a)) {
                if (m_registry.isCommutative(curr.readPosition(0))) {
                    curr = curr.withOrderedArguments();
                }
                modifiedEntries.push(curr);
                it.remove();
            }
        }
        while (!modifiedEntries.empty()) {
            int indexToInsert =
                    Collections
                            .binarySearch(m_exprList, modifiedEntries.peek());
            // If the modified one is already there, don't put it back
            if (indexToInsert < 0) {
                indexToInsert = -(indexToInsert + 1);
                // root of modified expression depends on the changed arg
                //String fordebug = modifiedEntries.peek().toHumanReadableString(m_registry);
                int rootOfChangedExpression = modifiedEntries.peek().readRoot();
                m_registry.addDependency(rootOfChangedExpression,
                        m_current_justification, false);
                m_exprList.add(indexToInsert, modifiedEntries.pop());
            }
            else {
                // the expr is in the list, but are the roots different?
                int rootA = modifiedEntries.pop().readRoot();
                int rootB = m_exprList.get(indexToInsert).readRoot();
                if (rootA != rootB) {
                    coincidentalMergeHoldingTank.push(rootA);
                    coincidentalMergeHoldingTank.push(rootB);
                }
            }
        }
        //System.err.println(m_registry.getSymbolForIndex(a) + "/" + m_registry.getSymbolForIndex(b));
        m_registry.addDependency(a, m_current_justification, true);
        m_registry.substitute(a, b);
        return coincidentalMergeHoldingTank;
    }

    protected void updateUseMap() {
        m_useMap.clear();
        assert m_useMap.size() == 0;
        for (NormalizedAtomicExpressionMapImpl e : m_exprList) {
            for (Integer k : e.getKeys()) {
                assert m_registry.findAndCompress(k) == k : "child symbol in conj";
                if (m_useMap.containsKey(k))
                    m_useMap.get(k).add(e);
                else {
                    HashSet<NormalizedAtomicExpressionMapImpl> nm =
                            new HashSet<NormalizedAtomicExpressionMapImpl>();
                    nm.add(e);
                    m_useMap.put(k, nm);
                }
            }
        }
        // for debug
        /*String s = "";
        for(Integer k : m_useMap.keySet()){
            s += m_registry.getSymbolForIndex(k) + "\n";
            for(NormalizedAtomicExpressionMapImpl nm : m_useMap.get(k)){
                s += nm.toHumanReadableString(m_registry) + "\n";
            }
            s += "\n";
        }
        System.err.println(s);*/
        for (Integer k : m_useMap.keySet()) {
            assert !m_useMap.get(k).isEmpty();
            assert m_useMap.get(k).size() != 0;
        }
    }

    protected Set<NormalizedAtomicExpressionMapImpl> multiKeyUseMapSearch(
            Set<String> keys) {

        Set<NormalizedAtomicExpressionMapImpl> resultSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        boolean firstkey = true;
        for (String k : keys) {
            int rKey = m_registry.getIndexForSymbol(k);
            if (!m_useMap.containsKey(rKey)) {
                return null;
            }
            Set<NormalizedAtomicExpressionMapImpl> tResults =
                    new HashSet<NormalizedAtomicExpressionMapImpl>(m_useMap
                            .get(rKey));
            if (tResults == null || tResults.isEmpty())
                return null;
            if (firstkey) {
                resultSet = tResults;
                firstkey = false;
            }
            else { // result is intersection
                resultSet.retainAll(tResults);
            }
        }
        return resultSet;
    }

    protected Set<java.util.Map<String, String>> getMatchesForOverideSet(
            NormalizedAtomicExpressionMapImpl expr, Registry exprReg,
            Set<Map<String, String>> foreignSymbolOverideSet) {
        Set<java.util.Map<String, String>> rSet =
                new HashSet<Map<String, String>>();
        for (Map<String, String> fs_m : foreignSymbolOverideSet) {
            Set<java.util.Map<String, String>> results =
                    getMatchesForEq(expr, exprReg, fs_m);
            if (results != null && results.size() != 0)
                rSet.addAll(results);
        }
        return rSet;
    }

    protected Set<Map<String, String>> getMatchesForEq(
            NormalizedAtomicExpressionMapImpl expr, Registry exprReg,
            Map<String, String> foreignSymbolOveride) {
        // Identify the literals.
        Set<String> literalsInexpr = new HashSet<String>();
        Map<String, Integer> exprMMap =
                expr.getEquationOperatorsAsStrings(exprReg);
        for (String s : exprMMap.keySet()) {
            String lit = "";
            if (!foreignSymbolOveride.containsKey(s)) {
                lit = s;
            }
            else if (!foreignSymbolOveride.get(s).equals("")) {
                // wildcard may have been bound in search for another expression
                lit = foreignSymbolOveride.get(s);
            }
            if (!lit.equals("")) {
                if (!m_registry.m_symbolToIndex.containsKey(lit))
                    return null;
                literalsInexpr.add(lit);
            }

        }

        Set<NormalizedAtomicExpressionMapImpl> vCNaemlsWithAllLiterals =
                multiKeyUseMapSearch(literalsInexpr);
        String deleteme = toString();
        if (vCNaemlsWithAllLiterals == null)
            return null;

        Set<NormalizedAtomicExpressionMapImpl> filtered_vcNaemlsWithAllLiterals;
        // std filter. opnum -> bitcode. means opnum must be used at each position indicated by the bitcode
        NormalizedAtomicExpressionMapImpl filter =
                new NormalizedAtomicExpressionMapImpl();
        for (String s : literalsInexpr) {
            // all literals in the search expr have to already be in the Vc.
            // find all positions
            int allPositionsLitIsUsedInSearchExpr = 0;
            int vcInt = m_registry.getIndexForSymbol(s);
            assert vcInt >= 0 : s + " not in VC registry";
            if (exprReg.m_symbolToIndex.containsKey(s)) {
                int sInt = exprReg.getIndexForSymbol(s);
                filter.overwriteEntry(vcInt, expr.readOperator(sInt));
            }
            else {
                for (String baseMapK : foreignSymbolOveride.keySet()) {
                    if (foreignSymbolOveride.get(baseMapK).equals(s)) {
                        allPositionsLitIsUsedInSearchExpr |=
                                expr.readOperator(exprReg
                                        .getIndexForSymbol(baseMapK));
                    }
                }
                filter.overwriteEntry(vcInt, allPositionsLitIsUsedInSearchExpr);
            }

        }

        boolean isCommutOp = exprReg.isCommutative(expr.readPosition(0));

        if (!isCommutOp) {
            filtered_vcNaemlsWithAllLiterals =
                    nonCommutativeFilter(vCNaemlsWithAllLiterals, filter);
            if (filtered_vcNaemlsWithAllLiterals.isEmpty())
                return null;
            return getBindings_NonCommutative(filtered_vcNaemlsWithAllLiterals,
                    foreignSymbolOveride, expr, exprReg);
        }
        else {
            filtered_vcNaemlsWithAllLiterals =
                    commutativeFilter(vCNaemlsWithAllLiterals, filter);
            if (filtered_vcNaemlsWithAllLiterals.isEmpty())
                return null;
            return getBindings_Commutative(filtered_vcNaemlsWithAllLiterals,
                    foreignSymbolOveride, expr, exprReg);
        }
    }

    Set<Map<String, String>> getBindings_Commutative(
            Set<NormalizedAtomicExpressionMapImpl> vcEquations,
            Map<String, String> basemap,
            NormalizedAtomicExpressionMapImpl searchExpr, Registry searchReg) {
        // Argument sets
        Map<String, Integer> thArgs =
                searchExpr.getArgumentsAsStrings(searchReg);
        Map<String, Integer> thOps =
                searchExpr.getEquationOperatorsAsStrings(searchReg);
        Set<Map<String, String>> bindings = new HashSet<Map<String, String>>();
        bindToAVCEquation: for (NormalizedAtomicExpressionMapImpl vc_r : vcEquations) {
            Map<String, String> currentBind =
                    new HashMap<String, String>(basemap);
            Map<String, Integer> vcArgs =
                    vc_r.getArgumentsAsStrings(m_registry);
            for (String thOp : thOps.keySet()) {
                if (!basemap.containsKey(thOp) || !basemap.get(thOp).equals("")) {
                    // This is a literal
                    // Remove num uses as arg from arg count
                    if (basemap.containsKey(thOp) && thArgs.containsKey(thOp)) {
                        // Wildcard argument has already been bound
                        int numUses = thArgs.get(thOp);
                        String lit = basemap.get(thOp);
                        // May be in commutative section
                        if (vcArgs.containsKey(lit)) {
                            vcArgs.put(lit, vcArgs.get(lit) - numUses);
                        }
                        else { // lit is arg of theorem, but not arg of vcEq
                            continue bindToAVCEquation;
                        }
                    }
                    else if (thArgs.containsKey(thOp)) {
                        // arg literal that exists in both places, not ever was wildcard
                        int numUses = thArgs.get(thOp);
                        if (vcArgs.containsKey(thOp)) {
                            vcArgs.put(thOp, vcArgs.get(thOp) - numUses);
                        }
                        else {
                            continue bindToAVCEquation;
                        }
                    }
                    continue; // go to next op
                }
                // thOp must be a wildcard
                String wild = thOp;
                int wildOpCode = searchReg.getIndexForSymbol(wild);
                int wildPosBitCode = searchExpr.readOperator(wildOpCode);
                // Basemap is used over a set of equations; ie wild may not even be used in this one
                if (wildPosBitCode <= 0)
                    continue;
                String localToBindTo = "";

                boolean isRoot = searchExpr.readRoot() == wildOpCode;
                boolean isFSymb = searchExpr.readPosition(0) == wildOpCode;
                if (isRoot || isFSymb) {
                    if ((wildPosBitCode & (wildPosBitCode - 1)) == 0) { // Single use and is func symbol or root
                        localToBindTo =
                                m_registry.getSymbolForIndex(vc_r
                                        .readPositionBitcode(wildPosBitCode));
                    }
                    else {// used as (root or func symb) and as arg(s) in search
                        // so reject if same not true of vcr
                        String loc = "";
                        if (isRoot && isFSymb) {
                            if (vc_r.readPosition(0) == vc_r.readRoot()) {
                                loc =
                                        m_registry.getSymbolForIndex(vc_r
                                                .readRoot());
                            }
                        }
                        else if (isFSymb) {
                            loc =
                                    m_registry.getSymbolForIndex(vc_r
                                            .readPosition(0));
                        }
                        else if (isRoot) {
                            loc = m_registry.getSymbolForIndex(vc_r.readRoot());
                        }
                        if (!loc.equals("")) {
                            int thC = thArgs.get(wild);
                            int vcC = vcArgs.get(loc);
                            if (thC <= vcC) {
                                vcArgs.put(loc, vcC - thC);
                                localToBindTo = loc;
                            }
                            else
                                continue bindToAVCEquation;
                        }
                        else
                            continue bindToAVCEquation;
                    }
                }
                // Only use is in arg list
                else {
                    int thC = thArgs.get(wild);
                    // Choose the first that has the min no. of uses.  (Going to potentially miss some matches)
                    for (String vcA : vcArgs.keySet()) {
                        int vcACnt = vcArgs.get(vcA);
                        if (thC <= vcACnt) {
                            localToBindTo = vcA;
                            vcArgs.put(localToBindTo, vcACnt - thC);
                            break;
                        }
                    }
                }
                if (!localToBindTo.equals("")) {
                    MTType wildType =
                            searchReg.getTypeByIndex(searchReg
                                    .getIndexForSymbol(wild));
                    MTType localType =
                            m_registry.getTypeByIndex(m_registry
                                    .getIndexForSymbol(localToBindTo));
                    if (!localType.isSubtypeOf(wildType))
                        continue bindToAVCEquation;
                    currentBind.put(wild, localToBindTo);
                }
                else
                    continue bindToAVCEquation;

            }
            bindings.add(currentBind);
        }
        return bindings;
    }

    Set<Map<String, String>> getBindings_NonCommutative(
            Set<NormalizedAtomicExpressionMapImpl> vcEquations,
            Map<String, String> basemap,
            NormalizedAtomicExpressionMapImpl searchExpr, Registry searchReg) {
        Set<Map<String, String>> bindings = new HashSet<Map<String, String>>();
        bindToAVCEquation: for (NormalizedAtomicExpressionMapImpl vc_r : vcEquations) {
            Map<String, String> currentBind =
                    new HashMap<String, String>(basemap);
            for (String wild : basemap.keySet()) {
                String wildVal = basemap.get(wild);
                if (wildVal.equals("")) {
                    int wildInt = searchReg.getIndexForSymbol(wild);
                    int wildP_BitCode = searchExpr.readOperator(wildInt);
                    if (wildP_BitCode <= 0)
                        continue; // wild not used in this eq.
                    int vc_eq_op = vc_r.readPositionBitcode(wildP_BitCode);
                    if (vc_eq_op == -1)
                        continue bindToAVCEquation; // non matching due to wildcard symbol used more places than found
                    String localToBindTo =
                            m_registry.getSymbolForIndex(vc_eq_op);
                    MTType wildType =
                            searchReg.getTypeByIndex(searchReg
                                    .getIndexForSymbol(wild));
                    MTType localType =
                            m_registry.getTypeByIndex(m_registry
                                    .getIndexForSymbol(localToBindTo));
                    if (!localType.isSubtypeOf(wildType))
                        continue bindToAVCEquation;
                    currentBind.put(wild, localToBindTo);
                }
            }
            bindings.add(currentBind);
        }
        return bindings;
    }

    protected Set<NormalizedAtomicExpressionMapImpl> commutativeFilter(
            Set<NormalizedAtomicExpressionMapImpl> raw,
            NormalizedAtomicExpressionMapImpl filter_criteria) {
        Set<NormalizedAtomicExpressionMapImpl> filteredSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        Map<String, Integer> filterLitArgs =
                filter_criteria.getArgumentsAsStrings(m_registry);
        nextExpr: for (NormalizedAtomicExpressionMapImpl r_n : raw) {
            if ((filter_criteria.readPosition(0) != -1 && filter_criteria
                    .readPosition(0) != r_n.readPosition(0))
                    || (filter_criteria.readRoot() != -1 && filter_criteria
                            .readRoot() != r_n.readRoot()))
                continue nextExpr;
            Map<String, Integer> r_n_litArgs =
                    r_n.getArgumentsAsStrings(m_registry);
            for (String arg : filterLitArgs.keySet()) {
                if (!r_n_litArgs.containsKey(arg))
                    continue nextExpr;
                if (filterLitArgs.get(arg) > r_n_litArgs.get(arg))
                    continue nextExpr;
            }
            filteredSet.add(r_n);
        }
        return filteredSet;
    }

    protected Set<NormalizedAtomicExpressionMapImpl> nonCommutativeFilter(
            Set<NormalizedAtomicExpressionMapImpl> raw,
            NormalizedAtomicExpressionMapImpl filter_criteria) {
        Set<NormalizedAtomicExpressionMapImpl> filteredSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        for (NormalizedAtomicExpressionMapImpl r_n : raw) {
            // r_n & filter_criteria ex. 1111 & 1001
            boolean matches = true;
            for (int litOp : filter_criteria.getKeys()) {
                int vcBitCodeForLitOp = r_n.readOperator(litOp);
                int filterBitCodeForLitOp = filter_criteria.readOperator(litOp);
                if ((vcBitCodeForLitOp & filterBitCodeForLitOp) != filterBitCodeForLitOp) {
                    matches = false;
                    break;
                }
            }
            if (matches)
                filteredSet.add(r_n);
        }
        return filteredSet;
    }

    // return map is expr Symbol -> this Symbol
    // returns null if no match found;
    // foreignSymbolOveride is expr Symbol -> this Symbol
    protected Set<java.util.Map<String, String>> getMatches(
            NormalizedAtomicExpressionMapImpl expr, Registry exprReg,
            Map<String, String> foreignSymbolOveride) {
        Set<NormalizedAtomicExpressionMapImpl> candidates =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        boolean firstKey = true;
        String funSymb = exprReg.getSymbolForIndex(expr.readPosition(0));
        boolean orderOfArgsMatters = !m_registry.isCommutative(funSymb);
        orderOfArgsMatters = true;
        Map<String, Integer> expCounts =
                expr.getEquationOperatorsAsStrings(exprReg);
        Map<String, Integer> foundSearchTerms = new HashMap<String, Integer>();
        for (Integer k : expr.getKeys()) {
            String eSymb = exprReg.getSymbolForIndex(k);
            // String equals does not work for ""
            int exprKeyCount = 0;
            boolean isWild =
                    foreignSymbolOveride.containsKey(eSymb)
                            && foreignSymbolOveride.get(eSymb).length() == 0;
            if (isWild)
                continue; // if it is wild, no point in looking for it here, go to next key
            exprKeyCount = expCounts.get(eSymb);
            if (foreignSymbolOveride.containsKey(eSymb))
                eSymb = foreignSymbolOveride.get(eSymb);
            // Early return for case where no possible match can occur
            if (!m_registry.m_symbolToIndex.containsKey(eSymb)) {
                return null;
            }
            eSymb = m_registry.getRootSymbolForSymbol(eSymb);
            // Either the symbol is a previously matched wildcard or it is a literal
            int symbolInConj = m_registry.getIndexForSymbol(eSymb);
            // Literal is in the registry, but it may not be in an expression. Some symbols added by default.
            if (!m_useMap.containsKey(symbolInConj)) {
                return null;
            }
            // ALIAS alert!!!!!
            Set<NormalizedAtomicExpressionMapImpl> results =
                    new HashSet<NormalizedAtomicExpressionMapImpl>(m_useMap
                            .get(symbolInConj));
            // early return for no matches.
            if (results == null || results.isEmpty())
                return null;
            foundSearchTerms.put(eSymb, exprKeyCount); // Mark these as used for search so that we know not to bind a wild to them
            Set<NormalizedAtomicExpressionMapImpl> removalSet =
                    new HashSet<NormalizedAtomicExpressionMapImpl>();
            // remove equations with non matching length
            // remove equations from the result set if they do not have the literal we just searched for where they occur
            // in the search expression.  They may occur elsewhere, in which case they will be dealt with at another
            // loop iteration (is another literal of the search expr in the same pos?) or in the binding phase.
            // 0101 expPos
            // 1111 r_n     Is OK
            // 1011 r_n     Is NOT ok
            int exprPositions = expr.readOperator(k); // this is the bit code, 1 if used, 0 if not
            for (NormalizedAtomicExpressionMapImpl r_n : results) {
                int conjPos = r_n.readOperator(symbolInConj);
                if (r_n.numOperators() != expr.numOperators()) {
                    removalSet.add(r_n);
                }
                else if (orderOfArgsMatters) {
                    if ((conjPos & exprPositions) != exprPositions) {
                        removalSet.add(r_n);
                    }
                }
                else {
                    // It is commut. We do not care about position, but about the number of uses
                    if (exprKeyCount > r_n.getEquationOperatorsAsStrings(
                            m_registry).get(eSymb)) { // eSymb should be a root
                        // remove if we have more uses of the literal in the search terms than what is found
                        removalSet.add(r_n);
                    }

                    // also: opName and RHS are not commut;
                    // throw out if those positions don't match if we were looking for those
                    else if (expr.readRoot() == k
                            && !eSymb.equals(m_registry.getSymbolForIndex(r_n
                                    .readRoot()))) {
                        removalSet.add(r_n);
                    }
                    else if (expr.readPosition(0) == k
                            && !eSymb.equals(m_registry.getSymbolForIndex(r_n
                                    .readPosition(0)))) {
                        removalSet.add(r_n);
                    }
                }

            }
            results.removeAll(removalSet);
            if (firstKey)
                candidates = results;
            else {
                // candidates = candidates intersect results
                candidates.retainAll(results);
                if (candidates.isEmpty())
                    return null;
            }
            firstKey = false;
        }
        // early return for case where no result due to non matching literal positions
        if (candidates.isEmpty())
            return null;

        // At this point candidates is a set of all expressions that syntactically match,
        // also considering the wildcards already defined
        // For commut's, all candidates have the min num of matching literals.
        // ex. CO(1,1,0) is a candidate for CO(1,x,x)
        // Create collection of bindings to return
        Set<Map<String, String>> rSet = new HashSet<Map<String, String>>();
        String rootSymb = exprReg.getSymbolForIndex(expr.readRoot());

        for (NormalizedAtomicExpressionMapImpl c_n : candidates) {
            // If a symbol in c_n is an undefined key in the overide map, define that key
            HashMap<String, String> binding =
                    new HashMap<String, String>(foreignSymbolOveride);
            boolean rhsToBeBound =
                    binding.containsKey(rootSymb)
                            && binding.get(rootSymb).equals("");
            boolean validBinding = true;
            Map<String, Integer> comArgs;
            if (!orderOfArgsMatters) {
                comArgs = c_n.getEquationOperatorsAsStrings(m_registry);
                // mark as used the terms we searched for
                for (String sKey : foundSearchTerms.keySet()) {
                    int remaining =
                            comArgs.get(sKey) - foundSearchTerms.get(sKey);
                    if (remaining < 0) {
                        throw new RuntimeException("Invalid arg count");
                    }
                    comArgs.put(sKey, remaining);
                }
            }
            else {
                comArgs = null;

            }

            for (String exprKey : binding.keySet()) {

                boolean isRHS = (rootSymb.equals(exprKey));
                if (binding.get(exprKey).length() == 0) {
                    // We have found a wildcard
                    int posInSearchExpr =
                            expr.readOperator(exprReg
                                    .getIndexForSymbol(exprKey));
                    if (posInSearchExpr == 0)
                        continue; // meaning the wildcard is not a part of the equation
                    int localSymbolIndex =
                            c_n.readPositionBitcode(posInSearchExpr);

                    if (orderOfArgsMatters && localSymbolIndex == -1) {
                        // Occurs when wildcard used in multiple positions, but different symbols in matched expr.
                        // Throw it out.
                        validBinding = false;
                        break;

                    }
                    String localSymbol = "";
                    if (orderOfArgsMatters)
                        localSymbol =
                                m_registry.getSymbolForIndex(localSymbolIndex);
                    else {
                        // choose the first one that type checks (discounting those that matched due to search keys)
                        if (isRHS) { // A wildcard is used as the RHS.  It may also be used in other postions.  0 + j = j
                            int numUses =
                                    expr.getEquationOperatorsAsStrings(exprReg)
                                            .get(exprKey);
                            localSymbol =
                                    m_registry
                                            .getSymbolForIndex(c_n.readRoot());
                            int pc = comArgs.get(localSymbol);
                            comArgs.put(localSymbol, pc - numUses);
                            rhsToBeBound = false;
                        }
                        else {
                            for (String l : comArgs.keySet()) {
                                int c = comArgs.get(l);
                                // Dont use if the only use is rhs
                                if (c > 0) {
                                    if (!(m_registry.getSymbolForIndex(
                                            c_n.readRoot()).equals(l)
                                            && c == 1 && rhsToBeBound)) {
                                        localSymbol = l;
                                        comArgs.put(l, --c);
                                        break;
                                    }
                                }
                            }
                        }
                        if (localSymbol == "") {
                            throw new RuntimeException("Symbol count error");
                        }

                    }
                    // Type check here.  Incompatible types should invalidate the whole binding
                    MTType theoremSymbolType =
                            exprReg.getTypeByIndex(exprReg
                                    .getIndexForSymbol(exprKey));
                    MTType localSymbolType =
                            m_registry.getTypeByIndex(localSymbolIndex);
                    if (!localSymbolType.isSubtypeOf(theoremSymbolType)) {
                        validBinding = false;
                        break;
                    }
                    binding.put(exprKey, localSymbol);
                }

            }
            if (validBinding) {
                // At this point we have bound all the wildcards for a particular candidate
                rSet.add(binding);
            }

        }
        return rSet;
    }

    protected Map<String, Integer> getSymbolProximity(Set<String> symbols) {
        boolean done = false;
        Map<Integer, Integer> relatedKeys = new HashMap<Integer, Integer>();
        for (String s : symbols) {
            relatedKeys.put(m_registry.getIndexForSymbol(s), 0);
        }
        int closeness = 0;
        Set<Integer> relatedSet = new HashSet<Integer>();

        while (!done) {
            closeness++;
            int startSize = relatedKeys.size();
            HashMap<Integer, Integer> relatedKeys2 =
                    new HashMap<Integer, Integer>();
            for (int i = 0; i < m_exprList.size(); ++i) {
                if (relatedSet.contains(i))
                    continue;
                Set<Integer> intersection =
                        new HashSet<Integer>(m_exprList.get(i).getKeys());
                intersection.retainAll(relatedKeys.keySet());
                if (!intersection.isEmpty()) {
                    relatedSet.add(i);
                    for (Integer k : m_exprList.get(i).getKeys()) {
                        if (!relatedKeys.containsKey(k)) {
                            relatedKeys2.put(k, closeness);
                        }
                    }
                }
            }
            relatedKeys.putAll(relatedKeys2);
            if (startSize == relatedKeys.size()) {
                done = true;
            }
        }

        Map<String, Integer> rMap =
                new HashMap<String, Integer>(relatedKeys.size());
        for (Integer i : relatedKeys.keySet()) {
            rMap.put(m_registry.getSymbolForIndex(i), relatedKeys.get(i));
        }

        return rMap;
    }

    @Override
    public String toString() {
        String r = "";
        if (m_evaluates_to_false)
            r += "Conjunction evaluates to false" + "\n";
        /*for (MTType key : m_registry.m_typeToSetOfOperators.keySet()) {
            r += key.toString() + ":\n";
            r += m_registry.m_typeToSetOfOperators.get(key) + "\n\n";
        }*/
        for (NormalizedAtomicExpressionMapImpl cur : m_exprList) {
            r += cur.toHumanReadableString(m_registry) + "\n";
        }
        return r;
    }

}
