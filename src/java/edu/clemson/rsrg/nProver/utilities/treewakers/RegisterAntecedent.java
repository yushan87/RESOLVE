/*
 * RegisterAntecedent.java
 * ---------------------------------
 * Copyright (c) 2022
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.rsrg.nProver.utilities.treewakers;

import edu.clemson.rsrg.absyn.expressions.Exp;
import edu.clemson.rsrg.absyn.expressions.mathexpr.*;
import edu.clemson.rsrg.nProver.registry.CongruenceClassRegistry;
import edu.clemson.rsrg.treewalk.TreeWalkerStackVisitor;
import java.util.BitSet;
import java.util.Map;

/**
 * <p>
 * This class registers each antecedent expression. This visitor logic is implemented as a
 * {@link TreeWalkerStackVisitor}.
 * </p>
 *
 * @author Yu-Shan Sun
 * @author Nicodemus Msafiri J. M.
 *
 * @version 1.0
 */
public class RegisterAntecedent extends AbstractRegisterSequent {

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>
     * This creates an object that labels all relevant {@link Exp} in the antecedents with a number and registers them.
     * </p>
     *
     * @param registry
     *            The registry that will contain the target sequent VC to be proved.
     * @param expLabels
     *            A mapping between expressions and its associated integer number.
     * @param nextLabel
     *            The number to be assigned initially as a label.
     */
    public RegisterAntecedent(CongruenceClassRegistry<Integer, String, String, String> registry,
            Map<String, Integer> expLabels, int nextLabel) {
        super(registry, expLabels, nextLabel);
    }

    // ===========================================================
    // Visitor Methods
    // ===========================================================

    // -----------------------------------------------------------
    // Math Expression-Related
    // -----------------------------------------------------------

    /**
     * <p>
     * Code that gets executed after visiting a {@link InfixExp}.
     * </p>
     *
     * @param exp
     *            An infix expression.
     */
    @Override
    public final void postInfixExp(InfixExp exp) {
        super.postInfixExp(exp);
        int operatorNumber = myExpLabels.get(exp.getOperatorAsString());

        // Logic for handling infix expressions in the antecedent
        if (operatorNumber == OP_EQUALS) { // if it is antecedent equal
            myRegistry.makeCongruent(myArgumentsCache.remove(exp.getLeft()), myArgumentsCache.remove(exp.getRight()));
        } else {
            // append arguments usable in registering the infix operator
            myRegistry.appendToClusterArgList(myArgumentsCache.remove(exp.getLeft()));
            myRegistry.appendToClusterArgList(myArgumentsCache.remove(exp.getRight()));

            // check if registered, no duplicates allowed
            if (myRegistry.checkIfRegistered(operatorNumber)) {
                myArgumentsCache.put(exp, myRegistry.getAccessorFor(operatorNumber));
            } else {
                // register if new, and make it an argument for the next higher level operator
                int accessor = myRegistry.registerCluster(operatorNumber);

                // if exp is ultimate i.e., at root
                if (super.getAncestorSize() == 1) {
                    BitSet attb = new BitSet();
                    attb.set(0);// set the class antecedent
                    attb.set(2);// set the class ultimate
                    myRegistry.updateClassAttributes(accessor, attb);
                } else {
                    // only non-ultimate classes can be used as arguments in clusters
                    myArgumentsCache.put(exp, accessor);
                }
            }
        }
    }

    /**
     * <p>
     * Code that gets executed after visiting a {@link OutfixExp}.
     * </p>
     *
     * @param exp
     *            An outfix expression.
     */
    @Override
    public final void postOutfixExp(OutfixExp exp) {
        super.postOutfixExp(exp);
        int operatorNumber = myExpLabels.get(exp.getOperatorAsString());

        // Logic for handling outfix expressions in the antecedent
        // has only one argument, should run once
        myRegistry.appendToClusterArgList(myArgumentsCache.remove(exp.getArgument()));

        // check if registered, no duplicates allowed
        if (myRegistry.checkIfRegistered(operatorNumber)) {
            myArgumentsCache.put(exp, myRegistry.getAccessorFor(operatorNumber));
        } else {
            // register if new, and make it an argument for the next higher level operator
            int accessor = myRegistry.registerCluster(operatorNumber);

            // if exp is ultimate i.e., at root
            if (super.getAncestorSize() == 1) {
                BitSet attb = new BitSet();
                attb.set(0);// set the class antecedent
                attb.set(2);// set the class ultimate
                myRegistry.updateClassAttributes(accessor, attb);
            } else {
                // only non-ultimate classes can be used as arguments in clusters
                myArgumentsCache.put(exp, accessor);
            }
        }
    }

}