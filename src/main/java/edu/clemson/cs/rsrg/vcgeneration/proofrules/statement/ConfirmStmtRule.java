/*
 * ConfirmStmtRule.java
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
package edu.clemson.cs.rsrg.vcgeneration.proofrules.statement;

import edu.clemson.cs.rsrg.absyn.expressions.Exp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.VarExp;
import edu.clemson.cs.rsrg.absyn.statements.ConfirmStmt;
import edu.clemson.cs.rsrg.parsing.data.LocationDetailModel;
import edu.clemson.cs.rsrg.vcgeneration.proofrules.AbstractProofRuleApplication;
import edu.clemson.cs.rsrg.vcgeneration.proofrules.ProofRuleApplication;
import edu.clemson.cs.rsrg.vcgeneration.sequents.Sequent;
import edu.clemson.cs.rsrg.vcgeneration.sequents.SequentReduction;
import edu.clemson.cs.rsrg.vcgeneration.sequents.reductiontree.ReductionTreeDotExporter;
import edu.clemson.cs.rsrg.vcgeneration.sequents.reductiontree.ReductionTreeExporter;
import edu.clemson.cs.rsrg.vcgeneration.utilities.AssertiveCodeBlock;
import edu.clemson.cs.rsrg.vcgeneration.utilities.VerificationCondition;
import edu.clemson.cs.rsrg.vcgeneration.utilities.VerificationContext;
import java.util.*;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;

/**
 * <p>This class contains the logic for applying the {@code confirm}
 * rule to a {@link ConfirmStmt}.</p>
 *
 * @author Yu-Shan Sun
 * @version 1.0
 */
public class ConfirmStmtRule extends AbstractProofRuleApplication
        implements
            ProofRuleApplication {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /** <p>The {@link ConfirmStmt} we are applying the rule to.</p> */
    private final ConfirmStmt myConfirmStmt;

    /**
     * <p>A map that indicates if a particular {@link Sequent} had
     * an impacting reduction.</p>
     */
    private final Map<Sequent, Boolean> myImpactingReducedSequentMap;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>This creates a new application of the {@code confirm}
     * rule.</p>
     *
     * @param confirmStmt The {@link ConfirmStmt} we are applying
     *                    the rule to.
     * @param block The assertive code block that the subclasses are
     *              applying the rule to.
     * @param context The verification context that contains all
     *                the information we have collected so far.
     * @param stGroup The string template group we will be using.
     * @param blockModel The model associated with {@code block}.
     */
    public ConfirmStmtRule(ConfirmStmt confirmStmt, AssertiveCodeBlock block,
            VerificationContext context, STGroup stGroup, ST blockModel) {
        super(block, context, stGroup, blockModel);
        myConfirmStmt = confirmStmt;
        myImpactingReducedSequentMap = new LinkedHashMap<>();
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>This method applies the {@code Proof Rule}.</p>
     */
    @Override
    public final void applyRule() {
        ST stepModel = mySTGroup.getInstanceOf("outputVCGenStep");

        // Check to see if this confirm can be simplified or not.
        if (myConfirmStmt.getSimplify() && VarExp.isLiteralTrue(myConfirmStmt.getAssertion())) {
            // Add the different details to the various different output models
            stepModel.add("proofRuleName", getRuleDescription() + " and Simplified")
                    .add("currentStateOfBlock", myCurrentAssertiveCodeBlock);
        }
        else {
            // Build the new list of VCs
            // YS: Since we are backward sweeping, the VCs generated by
            //     the latest ConfirmStmt should come before all the VCs
            //     in the current assertive code block.
            List<VerificationCondition> newVCs = new ArrayList<>();
            newVCs.addAll(buildNewVCs(stepModel));
            newVCs.addAll(myCurrentAssertiveCodeBlock.getVCs());

            // Set this as our new list of vcs
            myCurrentAssertiveCodeBlock.setVCs(newVCs);

            stepModel.add("proofRuleName", getRuleDescription())
                    .add("currentStateOfBlock", myCurrentAssertiveCodeBlock);
        }

        // Add the different details to the various different output models
        myBlockModel.add("vcGenSteps", stepModel.render());
    }

    /**
     * <p>This method returns a description associated with
     * the {@code Proof Rule}.</p>
     *
     * @return A string.
     */
    @Override
    public final String getRuleDescription() {
        return "Confirm Rule";
    }

    // ===========================================================
    // Private Methods
    // ===========================================================

    /**
     * <p>An helper method that builds a list of new {@code VCs}.</p>
     *
     * @param stepModel The model associated with this step.
     *
     * @return A list of {@link VerificationCondition VCs}.
     */
    private List<VerificationCondition> buildNewVCs(ST stepModel) {
        // Apply the various sequent reduction rules to the expressions
        // in the confirm statement.
        Sequent sequentToBeReduced =
                new Sequent(myConfirmStmt.getLocation(), new ArrayList<Exp>(),
                        Collections.singletonList(myConfirmStmt.getAssertion()));
        SequentReduction reduction =
                new SequentReduction(sequentToBeReduced);
        List<Sequent> resultSequents = reduction.applyReduction();
        Graph<Sequent, DefaultEdge> reductionTree = reduction.getReductionTree();

        // Store the map of impacting reductions
        myImpactingReducedSequentMap.putAll(reduction
                .getImpactingReducedSequentMap());

        // YS: The confirm statement always generate new VCs.
        List<VerificationCondition> vcs = new ArrayList<>();
        for (Sequent s : resultSequents) {
            // Check to see if the sequent has an impacting reduction and
            // create the VC appropriately.
            vcs.add(new VerificationCondition(myConfirmStmt.getLocation().clone(),
                    s.clone(), myImpactingReducedSequentMap.get(s),
                    findLocationDetailModel(s)));
        }

        // Output the reduction tree as a dot file to the step model
        // only if we did some kind of reduction.
        if (!reductionTree.edgeSet().isEmpty()) {
            ReductionTreeExporter treeExporter = new ReductionTreeDotExporter();
            stepModel.add("reductionTrees", treeExporter.output(reductionTree));
        }

        return vcs;
    }

    /**
     * <p>This method finds the location details that will be associated
     * with a {@code VC}.</p>
     *
     * @param sequent A {@link Sequent}.
     *
     * @return A {@link LocationDetailModel}.
     */
    private LocationDetailModel findLocationDetailModel(Sequent sequent) {
        // YS: All the expressions inside the consequent should have a
        //     LocationDetailModel. We simply return the first one we
        //     find.
        LocationDetailModel model = null;

        // First check to see if we have any consequent. If yes, we simply
        // return the first one we find.
        Iterator<Exp> consequentExpIt = sequent.getConcequents().iterator();
        while (consequentExpIt.hasNext() && model == null) {
            Exp exp = consequentExpIt.next();
            if (exp.getLocationDetailModel() != null) {
                model = exp.getLocationDetailModel();
            }
        }

        // Second if we still didn't find it, we must have done some kind of
        // sequent reduction and ended up putting the consequent in the antecedent
        // as a negation. We simply return the first one we find.
        Iterator<Exp> antecedentIt = sequent.getAntecedents().iterator();
        while (antecedentIt.hasNext() && model == null) {
            Exp exp = antecedentIt.next();
            if (exp.getLocationDetailModel() != null) {
                model = exp.getLocationDetailModel();
            }
        }

        return model;
    }
}