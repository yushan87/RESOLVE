/*
 * RightNotRule.java
 * ---------------------------------
 * Copyright (c) 2024
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.rsrg.vcgeneration.sequents.reductionrules.rightrules;

import edu.clemson.rsrg.absyn.expressions.Exp;
import edu.clemson.rsrg.absyn.expressions.mathexpr.PrefixExp;
import edu.clemson.rsrg.vcgeneration.sequents.Sequent;
import edu.clemson.rsrg.vcgeneration.sequents.reductionrules.AbstractReductionRuleApplication;
import edu.clemson.rsrg.vcgeneration.sequents.reductionrules.ReductionRuleApplication;
import java.util.ArrayList;
import java.util.List;

/**
 * <p>
 * This class contains the logic for applying the {@code right not} rule.
 * </p>
 *
 * @author Yu-Shan Sun
 *
 * @version 1.0
 */
public class RightNotRule extends AbstractReductionRuleApplication implements ReductionRuleApplication {

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>
     * This creates a new application of the {@code right not} rule.
     * </p>
     *
     * @param originalSequent
     *            The original {@link Sequent} that contains the expression to be reduced.
     * @param originalExp
     *            The {@link Exp} to be reduced.
     */
    public RightNotRule(Sequent originalSequent, Exp originalExp) {
        super(originalSequent, originalExp);
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>
     * This method applies the {@code Sequent Reduction Rule}.
     * </p>
     *
     * @return A list of {@link Sequent Sequents} that resulted from applying the rule.
     */
    @Override
    public final List<Sequent> applyRule() {
        if (myOriginalExp instanceof PrefixExp) {
            PrefixExp originalExpAsPrefixExp = (PrefixExp) myOriginalExp;
            List<Exp> newAntecedents = copyExpList(myOriginalSequent.getAntecedents(), null);
            List<Exp> newConsequents = new ArrayList<>();
            for (Exp exp : myOriginalSequent.getConcequents()) {
                if (exp.equals(originalExpAsPrefixExp)) {
                    // Add the expression inside the "not" to the consequent.
                    if (originalExpAsPrefixExp.getOperatorAsString().equals("not")) {
                        // Copy the entire PrefixExp so we get a new copy of
                        // the LocationDetailModel if it exists.
                        PrefixExp copyExp = (PrefixExp) originalExpAsPrefixExp.clone();
                        Exp argumentExp = copyExp.getArgument();
                        argumentExp.setLocationDetailModel(copyExp.getLocationDetailModel());

                        // Add this modified argumentExp
                        newAntecedents.add(argumentExp);
                    }
                    // This must be an error!
                    else {
                        unexpectedExp();
                    }
                }
                // Don't do anything to the other expressions.
                else {
                    newConsequents.add(exp.clone());
                }
            }

            // Construct a new sequent
            Sequent resultingSequent = new Sequent(myOriginalSequent.getLocation(), newAntecedents, newConsequents);
            myResultingSequents.add(resultingSequent);

            // Indicate that this is an impacting reduction
            myIsImpactingReductionFlag = true;
        }
        // This must be an error!
        else {
            unexpectedExp();
        }

        return myResultingSequents;
    }

    /**
     * <p>
     * This method returns a description associated with the {@code Sequent Reduction Rule}.
     * </p>
     *
     * @return A string.
     */
    @Override
    public final String getRuleDescription() {
        return "Right Not Rule";
    }

}
