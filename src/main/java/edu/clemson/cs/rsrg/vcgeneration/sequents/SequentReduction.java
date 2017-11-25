/*
 * SequentReduction.java
 * ---------------------------------
 * Copyright (c) 2017
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.rsrg.vcgeneration.sequents;

import edu.clemson.cs.rsrg.absyn.expressions.Exp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.BetweenExp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.InfixExp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.PrefixExp;
import edu.clemson.cs.rsrg.statushandling.exception.MiscErrorException;
import edu.clemson.cs.rsrg.vcgeneration.sequents.reductionrules.ReductionRuleApplication;
import edu.clemson.cs.rsrg.vcgeneration.sequents.reductionrules.leftrules.*;
import edu.clemson.cs.rsrg.vcgeneration.sequents.reductionrules.rightrules.*;
import java.util.*;
import org.jgrapht.DirectedGraph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;

/**
 * <p>This class contains logic for reducing a {@link Sequent}.</p>
 *
 * @see <a href="https://en.wikipedia.org/wiki/Sequent_calculus">Sequent Calculus</a>
 *
 * @author Yu-Shan Sun
 * @version 1.0
 */
public class SequentReduction {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /** <p>The incoming {@link Sequent} we are trying to reduce.</p> */
    private final Sequent myOriginalSequent;

    /** <p>A resulting list containing the reduced {@link Sequent Sequent(s)}.</p> */
    private final List<Sequent> myResultingSequents;

    /** <p>The reduction tree generated by applying the reduction rules.</p> */
    private final DirectedGraph<Sequent, DefaultEdge> myReductionTree;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>This creates an object that helps reduce a
     * {@link Sequent}.</p>
     *
     * @param sequent A {@link Sequent} to be reduced.
     */
    public SequentReduction(Sequent sequent) {
        myOriginalSequent = sequent;
        myReductionTree = new DefaultDirectedGraph<>(DefaultEdge.class);
        myResultingSequents = new ArrayList<>();

        // Add the originalSequent as our root node
        myReductionTree.addVertex(myOriginalSequent);
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>This method applies the various different sequent reduction
     * rules until we can't reduce any further.</p>
     *
     * @return A list of {@link Sequent Sequents}.
     */
    public final List<Sequent> applyReduction() {
        Deque<Sequent> sequentsToBeReduced = new LinkedList<>();
        List<Sequent> reducedSequents = new ArrayList<>();

        // Add the original sequent to the sequentsToBeReduced
        // and begin reducing it!
        sequentsToBeReduced.add(myOriginalSequent);
        while (!sequentsToBeReduced.isEmpty()) {
            Sequent seq = sequentsToBeReduced.removeFirst();

            // Check to see if have a sequent with atomic formulas.
            // If we do, then we are done reducing the sequent!
            if (seq.consistOfAtomicFormulas()) {
                reducedSequents.add(seq);
            }
            // Otherwise, apply the left and/or right reduction
            // rules to reduce it!
            else {
                // Try to apply the left reduction rules
                Deque<Sequent> leftReductionSeqs = applyLeftReductionRules(seq);

                // It is an error if we don't get any sequents back.
                if (leftReductionSeqs.isEmpty()) {
                    throw new MiscErrorException("Error encountered during reduction. Sequent: "
                            + seq
                            + " either contains atomic formulas or one of the reduction rules is wrong!",
                            new IllegalStateException());
                }
                else if (leftReductionSeqs.size() == 1) {
                    Sequent resultSequent = leftReductionSeqs.getFirst();

                    // YS: Probably can do equality check here, but it is the same
                    // as checking to see if we have an edge between "seq" and "resultSequent"
                    // If there is an edge, then it means that we have done some kind of
                    // reduction and we need to add it back to "sequentsToBeReduced" for
                    // potentially more reductions.
                    if (myReductionTree.containsEdge(seq, resultSequent)) {
                        leftReductionSeqs.addAll(sequentsToBeReduced);
                        sequentsToBeReduced = leftReductionSeqs;
                    }
                    // Otherwise, we need to check our right reduction rules and see if there is any
                    // reduction to be applied.
                    else {
                        Deque<Sequent> rightReductionSeqs = applyRightReductionRules(resultSequent);

                        // It is an error if we don't get any sequents back.
                        if (rightReductionSeqs.isEmpty()) {
                            throw new MiscErrorException("Error encountered during reduction. Sequent: "
                                    + resultSequent
                                    + " either contains atomic formulas or one of the reduction rules is wrong!",
                                    new IllegalStateException());
                        }
                        else if (rightReductionSeqs.size() == 1) {
                            resultSequent = rightReductionSeqs.getFirst();

                            // We must have done some kind of reduction.
                            if (myReductionTree.containsEdge(seq, resultSequent)) {
                                rightReductionSeqs.addAll(sequentsToBeReduced);
                                sequentsToBeReduced = rightReductionSeqs;
                            }
                            // If we didn't, then it is an error. We must have incorrectly
                            // identified this as a sequent that didn't contain atomic formulas
                            // or one of the reduction rules is wrong.
                            else {
                                throw new MiscErrorException("Error encountered during reduction. Sequent: "
                                        + resultSequent
                                        + " either contains atomic formulas or one of the reduction rules is wrong!",
                                        new IllegalStateException());
                            }
                        }
                        // We definitely did some reduction because it generated more sequents,
                        // so add it back to "sequentsToBeReduced" for potentially more reductions.
                        else {
                            rightReductionSeqs.addAll(sequentsToBeReduced);
                            sequentsToBeReduced = rightReductionSeqs;
                        }
                    }
                }
                // We definitely did some reduction because it generated more sequents,
                // so add it back to "sequentsToBeReduced" for potentially more reductions.
                else {
                    leftReductionSeqs.addAll(sequentsToBeReduced);
                    sequentsToBeReduced = leftReductionSeqs;
                }
            }
        }

        myResultingSequents.addAll(reducedSequents);

        return myResultingSequents;
    }

    /**
     * <p>This method overrides the default {@code equals} method implementation.</p>
     *
     * @param o Object to be compared.
     *
     * @return {@code true} if all the fields are equal, {@code false} otherwise.
     */
    @Override
    public final boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        SequentReduction that = (SequentReduction) o;

        return myOriginalSequent.equals(that.myOriginalSequent)
                && myResultingSequents.equals(that.myResultingSequents)
                && myReductionTree.equals(that.myReductionTree);
    }

    /**
     * <p>This method returns a graph containing the steps taken to reduce
     * the {@link Sequent}.</p>
     *
     * @return A {@link DirectedGraph} representing a reduction tree.
     */
    public final DirectedGraph<Sequent, DefaultEdge> getReductionTree() {
        return myReductionTree;
    }

    /**
     * <p>This method overrides the default {@code hashCode} method implementation.</p>
     *
     * @return The hash code associated with the object.
     */
    @Override
    public final int hashCode() {
        int result = myOriginalSequent.hashCode();
        result = 31 * result + myResultingSequents.hashCode();
        result = 31 * result + myReductionTree.hashCode();
        return result;
    }

    // ===========================================================
    // Private Methods
    // ===========================================================

    /**
     * <p>An helper method that calls a reduction rule and adds the
     * appropriate nodes and edges to the reduction tree.</p>
     *
     * @param sequent The {@link Sequent} being reduced.
     * @param ruleApplication The {@link ReductionRuleApplication} to be applied.
     *
     * @return A list of resulting {@link Sequent Sequents} from the rule
     * application.
     */
    private List<Sequent> applyAndAddToReductionTree(Sequent sequent,
            ReductionRuleApplication ruleApplication) {
        List<Sequent> ruleResultingSeqs = ruleApplication.applyRule();

        // Add a vertex for the new sequent. Also add an edge from
        // the original sequent to each sequent generated by
        // the reduction rules.
        for (Sequent resultSeq : ruleResultingSeqs) {
            myReductionTree.addVertex(resultSeq);
            myReductionTree.addEdge(sequent, resultSeq);
        }

        return ruleResultingSeqs;
    }

    // -----------------------------------------------------------
    // Left Rules
    // -----------------------------------------------------------

    /**
     * <p>This method attempts to apply the left reduction rules
     * to {@code sequent}.</p>
     *
     * @param sequent The sequent to be reduced.
     *
     * @return A {@link Deque} containing the reduced {@link Sequent Sequents}.
     */
    private Deque<Sequent> applyLeftReductionRules(Sequent sequent) {
        Deque<Sequent> resultingSeq = new LinkedList<>();

        // Loop until we find an antecedent expression that
        // can be reduced and call the associated reduction rule.
        boolean doneReduction = false;
        Iterator<Exp> antecedentsIt = sequent.getAntecedents().iterator();
        while (antecedentsIt.hasNext() && !doneReduction) {
            ReductionRuleApplication ruleApplication = null;
            Exp exp = antecedentsIt.next();

            if (exp instanceof BetweenExp) {
                // BetweenExp are joined together by the "and" operator.
                ruleApplication = new LeftAndRule(sequent, exp);
            }
            else if (exp instanceof InfixExp) {
                // Use the operator to determine which rule to call.
                String operator = ((InfixExp) exp).getOperatorAsString();
                switch (operator) {
                    case "and":
                        ruleApplication = new LeftAndRule(sequent, exp);
                        break;
                    case "or":
                        ruleApplication = new LeftOrRule(sequent, exp);
                        break;
                    case "implies":
                        ruleApplication = new LeftImpliesRule(sequent, exp);
                        break;
                }
            }
            // Only call the not reduction rule if the operator is "not"
            else if (exp instanceof PrefixExp &&
                    ((PrefixExp) exp).getOperatorAsString().equals("not")) {
                ruleApplication = new LeftNotRule(sequent, exp);
            }

            // Apply the reduction rule and add it to the reduction tree
            // if we generated a reduction rule application.
            if (ruleApplication != null) {
                // Add all the sequents that resulted from the rule
                // to the deque we are returning.
                resultingSeq.addAll(applyAndAddToReductionTree(sequent, ruleApplication));
                doneReduction = true;
            }
        }

        // If we didn't do any kind of reduction, it is OK.
        // The formula that needs to be reduced could be in the
        // consequent, so we simply add the sequent back to resultingSeq
        if (!doneReduction) {
            resultingSeq.add(sequent);
        }

        return resultingSeq;
    }

    // -----------------------------------------------------------
    // Right Rules
    // -----------------------------------------------------------

    /**
     * <p>This method attempts to apply the right reduction rules
     * to {@code sequent}.</p>
     *
     * @param sequent The sequent to be reduced.
     *
     * @return A {@link Deque} containing the reduced {@link Sequent Sequents}.
     */
    private Deque<Sequent> applyRightReductionRules(Sequent sequent) {
        Deque<Sequent> resultingSeq = new LinkedList<>();

        // Loop until we find an consequent expression that
        // can be reduced and call the associated reduction rule.
        boolean doneReduction = false;
        Iterator<Exp> consequentIt = sequent.getConcequents().iterator();
        while (consequentIt.hasNext() && !doneReduction) {
            ReductionRuleApplication ruleApplication = null;
            Exp exp = consequentIt.next();

            if (exp instanceof InfixExp) {
                // Use the operator to determine which rule to call.
                String operator = ((InfixExp) exp).getOperatorAsString();
                switch (operator) {
                    case "and":
                        ruleApplication = new RightAndRule(sequent, exp);
                        break;
                    case "or":
                        ruleApplication = new RightOrRule(sequent, exp);
                        break;
                    case "implies":
                        ruleApplication = new RightImpliesRule(sequent, exp);
                        break;
                }
            }
            // Only call the not reduction rule if the operator is "not"
            else if (exp instanceof PrefixExp &&
                    ((PrefixExp) exp).getOperatorAsString().equals("not")) {
                ruleApplication = new RightNotRule(sequent, exp);
            }

            // Apply the reduction rule and add it to the reduction tree
            // if we generated a reduction rule application.
            if (ruleApplication != null) {
                // Add all the sequents that resulted from the rule
                // to the deque we are returning.
                resultingSeq.addAll(applyAndAddToReductionTree(sequent, ruleApplication));
                doneReduction = true;
            }
        }

        // If we didn't do any kind of reduction after visiting all
        // the consequents, it is an error. However, rather than dealing
        // with the error here, it is best to leave all that to the caller
        // for this method.
        return resultingSeq;
    }
}