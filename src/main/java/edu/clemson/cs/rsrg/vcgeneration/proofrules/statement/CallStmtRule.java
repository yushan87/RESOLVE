/*
 * CallStmtRule.java
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

import edu.clemson.cs.r2jt.rewriteprover.immutableadts.ImmutableList;
import edu.clemson.cs.rsrg.absyn.clauses.AssertionClause;
import edu.clemson.cs.rsrg.absyn.declarations.operationdecl.OperationDec;
import edu.clemson.cs.rsrg.absyn.declarations.typedecl.AbstractTypeRepresentationDec;
import edu.clemson.cs.rsrg.absyn.declarations.typedecl.TypeFamilyDec;
import edu.clemson.cs.rsrg.absyn.declarations.variabledecl.ParameterVarDec;
import edu.clemson.cs.rsrg.absyn.expressions.Exp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.*;
import edu.clemson.cs.rsrg.absyn.expressions.programexpr.ProgramExp;
import edu.clemson.cs.rsrg.absyn.expressions.programexpr.ProgramFunctionExp;
import edu.clemson.cs.rsrg.absyn.rawtypes.NameTy;
import edu.clemson.cs.rsrg.absyn.statements.AssumeStmt;
import edu.clemson.cs.rsrg.absyn.statements.CallStmt;
import edu.clemson.cs.rsrg.absyn.statements.ConfirmStmt;
import edu.clemson.cs.rsrg.parsing.data.Location;
import edu.clemson.cs.rsrg.parsing.data.LocationDetailModel;
import edu.clemson.cs.rsrg.parsing.data.PosSymbol;
import edu.clemson.cs.rsrg.treewalk.TreeWalker;
import edu.clemson.cs.rsrg.typeandpopulate.entry.OperationEntry;
import edu.clemson.cs.rsrg.typeandpopulate.entry.ProgramParameterEntry;
import edu.clemson.cs.rsrg.typeandpopulate.entry.ProgramParameterEntry.ParameterMode;
import edu.clemson.cs.rsrg.typeandpopulate.entry.ProgramTypeEntry;
import edu.clemson.cs.rsrg.typeandpopulate.entry.SymbolTableEntry;
import edu.clemson.cs.rsrg.typeandpopulate.symboltables.MathSymbolTableBuilder;
import edu.clemson.cs.rsrg.typeandpopulate.symboltables.ModuleScope;
import edu.clemson.cs.rsrg.typeandpopulate.typereasoning.TypeGraph;
import edu.clemson.cs.rsrg.vcgeneration.proofrules.AbstractProofRuleApplication;
import edu.clemson.cs.rsrg.vcgeneration.proofrules.ProofRuleApplication;
import edu.clemson.cs.rsrg.vcgeneration.utilities.AssertiveCodeBlock;
import edu.clemson.cs.rsrg.vcgeneration.utilities.Utilities;
import edu.clemson.cs.rsrg.vcgeneration.utilities.VerificationCondition;
import edu.clemson.cs.rsrg.vcgeneration.utilities.formaltoactual.InstantiatedFacilityDecl;
import edu.clemson.cs.rsrg.vcgeneration.utilities.treewalkers.ProgramFunctionExpWalker;
import java.util.*;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;

/**
 * <p>This class contains the logic for applying the {@code call}
 * rule.</p>
 *
 * @author Yu-Shan Sun
 * @version 1.0
 */
public class CallStmtRule extends AbstractProofRuleApplication
        implements
            ProofRuleApplication {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /** <p>The {@link CallStmt} we are applying the rule to.</p> */
    private final CallStmt myCallStmt;

    /**
     * <p>This contains all the types declared by the {@code Concept}
     * associated with the current module. Note that if we are in a
     * {@code Facility}, this list will be empty.</p>
     */
    private final List<TypeFamilyDec> myCurrentConceptDeclaredTypes;

    /**
     * <p>The module scope for the file we are generating
     * {@code VCs} for.</p>
     */
    private final ModuleScope myCurrentModuleScope;

    /**
     * <p>If we are in a {@code Procedure} and it is an recursive
     * operation implementation, then this stores the decreasing clause
     * expression.</p>
     */
    private final Exp myCurrentProcedureDecreasingExp;

    /**
     * <p>The {@link OperationEntry} associated with this {@code If}
     * statement if we are inside a {@code ProcedureDec}.</p>
     */
    private final OperationEntry myCurrentProcedureOperationEntry;

    /**
     * <p>If our current module scope allows us to introduce new type implementations,
     * this will contain all the {@link AbstractTypeRepresentationDec}. Otherwise,
     * this list will be empty.</p>
     */
    private final List<AbstractTypeRepresentationDec> myLocalRepresentationTypeDecs;

    /** <p>The list of processed {@link InstantiatedFacilityDecl}. </p> */
    private final List<InstantiatedFacilityDecl> myProcessedInstFacilityDecls;

    /**
     * <p>This is the math type graph that indicates relationship
     * between different math types.</p>
     */
    private final TypeGraph myTypeGraph;

    // -----------------------------------------------------------
    // Nested Function Expression-Related
    // -----------------------------------------------------------

    /**
     * <p>The list of {@link ConfirmStmt ConfirmStmts} generated by some nested function in
     * our {@link CallStmt} argument list.</p>
     */
    private final List<ConfirmStmt> myNestedTerminationConfirmStmts;

    /**
     * <p>The list of {@code requires} clauses generated by some nested function in
     * our {@link CallStmt} argument list.</p>
     */
    private final List<Exp> myNestedRequiresClauses;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>This creates a new application of the {@code assume}
     * rule.</p>
     *
     * @param callStmt The {@link CallStmt} we are applying
     *                 the rule to.
     * param currentProcedureOpEntry An {@link OperationEntry} with a {@code Procedure},
     *                                if {@code ifStmt} is inside one. Otherwise it should
     *                                be left as {@code null}.
     * @param currentProcedureDecreasingExp If we are in a {@code Procedure} and it is recursive,
     *                                      this is its {@code decreasing} clause expression.
     *                                      Otherwise it should be left as {@code null}.
     * @param typeFamilyDecs List of abstract types we are implementing or extending.
     * @param localRepresentationTypeDecs List of local representation types.
     * @param processedInstFacDecs The list of processed {@link InstantiatedFacilityDecl}.
     * @param symbolTableBuilder The current symbol table.
     * @param moduleScope The current module scope we are visiting.
     * @param block The assertive code block that the subclasses are
     *              applying the rule to.
     * @param stGroup The string template group we will be using.
     * @param blockModel The model associated with {@code block}.
     */
    public CallStmtRule(CallStmt callStmt,
            OperationEntry currentProcedureOpEntry,
            Exp currentProcedureDecreasingExp,
            List<TypeFamilyDec> typeFamilyDecs,
            List<AbstractTypeRepresentationDec> localRepresentationTypeDecs,
            List<InstantiatedFacilityDecl> processedInstFacDecs,
            MathSymbolTableBuilder symbolTableBuilder, ModuleScope moduleScope,
            AssertiveCodeBlock block, STGroup stGroup, ST blockModel) {
        super(block, stGroup, blockModel);
        myCallStmt = callStmt;
        myCurrentConceptDeclaredTypes = typeFamilyDecs;
        myCurrentModuleScope = moduleScope;
        myCurrentProcedureDecreasingExp = currentProcedureDecreasingExp;
        myCurrentProcedureOperationEntry = currentProcedureOpEntry;
        myLocalRepresentationTypeDecs = localRepresentationTypeDecs;
        myNestedRequiresClauses = new LinkedList<>();
        myNestedTerminationConfirmStmts = new LinkedList<>();
        myProcessedInstFacilityDecls = processedInstFacDecs;
        myTypeGraph = symbolTableBuilder.getTypeGraph();
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>This method applies the {@code Proof Rule}.</p>
     */
    @Override
    public final void applyRule() {
        ProgramFunctionExp functionExp = myCallStmt.getFunctionExp();

        // Call a method to locate the operation entry for this call
        OperationEntry operationEntry =
                Utilities.getOperationEntry(functionExp, myCurrentModuleScope);
        OperationDec operationDec =
                (OperationDec) operationEntry.getDefiningElement();

        // Find all the replacements that needs to happen to the requires
        // and ensures clauses
        List<ProgramExp> callArgs = functionExp.getArguments();
        List<Exp> modifiedArguments = modifyArgumentList(callArgs);

        // Convert the formal operation parameters in VarExps for
        // substitution purposes.
        List<VarExp> operationParamAsVarExps =
                Utilities.createOperationParamExpList(operationDec
                        .getParameters());

        // 1) Confirm any nested function's invoking condition, recursive termination clauses
        //    and the modified requires clause of this calling statement.
        //    ( Confirm Invk_Cond(exp) and Pre[ Pre_Subs ] )
        Exp requiresExp =
                createModifiedReqExp(operationEntry, operationParamAsVarExps,
                        modifiedArguments);
        ConfirmStmt confirmStmt =
                new ConfirmStmt(myCallStmt.getLocation().clone(), requiresExp,
                        VarExp.isLiteralTrue(requiresExp));
        myCurrentAssertiveCodeBlock.addStatement(confirmStmt);

        // 2) Assume any ensures clause and ensures clauses generated by the parameter modes.
        //    ( Assume Implicit_Post[ Post_Subs ] and T6.Constraint(g) and T7.Is_Initial( NQV(RS, h) ) )
        Exp ensuresExp =
                createModifiedEnsExp(operationEntry, modifiedArguments);
        AssumeStmt assumeStmt =
                new AssumeStmt(myCallStmt.getLocation().clone(), ensuresExp,
                        false);
        myCurrentAssertiveCodeBlock.addStatement(assumeStmt);

        // Add the different details to the various different output models
        ST stepModel = mySTGroup.getInstanceOf("outputVCGenStep");
        stepModel.add("proofRuleName", getRuleDescription()).add(
                "currentStateOfBlock", myCurrentAssertiveCodeBlock);
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
        return "Call Rule";
    }

    // ===========================================================
    // Private Methods
    // ===========================================================

    /**
     * TODO: Add duration
     */
    private void createDurationEnsExp() {
    /*
    // NY YS
    // Duration for CallStmt
    if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
        Location loc = (Location) stmt.getLocation().clone();
        ConfirmStmt finalConfirm = myCurrentAssertiveCode.getFinalConfirm();
        Exp finalConfirmExp = finalConfirm.getAssertion();

        // Obtain the corresponding OperationProfileEntry
        OperationProfileEntry ope =
                Utilities.searchOperationProfile(loc, stmt.getQualifier(),
                        stmt.getName(), argTypes, myCurrentModuleScope);

        // Add the profile ensures as additional assume
        Exp profileEnsures = ope.getEnsuresClause();
        if (profileEnsures != null) {
            profileEnsures =
                    replaceFormalWithActualEns(profileEnsures, opDec
                                    .getParameters(), opDec.getStateVars(),
                            replaceArgs, false);

            // Obtain the current location
            if (stmt.getName().getLocation() != null) {
                // Set the details of the current location
                Location ensuresLoc = (Location) loc.clone();
                ensuresLoc.setDetails("Ensures Clause of "
                        + opDec.getName() + " from Profile "
                        + ope.getName());
                Utilities.setLocation(profileEnsures, ensuresLoc);
            }

            ensures = myTypeGraph.formConjunct(ensures, profileEnsures);
        }

        // Construct the Duration Clause
        Exp opDur = Exp.copy(ope.getDurationClause());

        // Replace PostCondition variables in the duration clause
        opDur =
                replaceFormalWithActualEns(opDur, opDec.getParameters(),
                        opDec.getStateVars(), replaceArgs, false);

        VarExp cumDur =
                Utilities.createVarExp((Location) loc.clone(), null,
                        Utilities.createPosSymbol(Utilities
                                .getCumDur(finalConfirmExp)),
                        myTypeGraph.R, null);
        Exp durCallExp =
                Utilities.createDurCallExp((Location) loc.clone(), Integer
                                .toString(opDec.getParameters().size()), Z,
                        myTypeGraph.R);
        InfixExp sumEvalDur =
                new InfixExp((Location) loc.clone(), opDur, Utilities
                        .createPosSymbol("+"), durCallExp);
        sumEvalDur.setMathType(myTypeGraph.R);
        sumEvalDur =
                new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                        Utilities.createPosSymbol("+"), sumEvalDur);
        sumEvalDur.setMathType(myTypeGraph.R);

        // For any evaluates mode expression, we need to finalize the variable
        edu.clemson.cs.r2jt.collections.List<ProgramExp> assignExpList =
                stmt.getArguments();
        for (int i = 0; i < assignExpList.size(); i++) {
            ParameterVarDec p = opDec.getParameters().get(i);
            VariableExp pExp = (VariableExp) assignExpList.get(i);
            if (p.getMode() == Mode.EVALUATES) {
                VarDec v =
                        new VarDec(Utilities.getVarName(pExp), p.getTy());
                FunctionExp finalDur =
                        Utilities.createFinalizAnyDur(v, myTypeGraph.R);
                sumEvalDur =
                        new InfixExp((Location) loc.clone(), sumEvalDur,
                                Utilities.createPosSymbol("+"), finalDur);
                sumEvalDur.setMathType(myTypeGraph.R);
            }
        }

        // Replace Cum_Dur in our final ensures clause
        finalConfirmExp =
                Utilities.replace(finalConfirmExp, cumDur, sumEvalDur);
        myCurrentAssertiveCode.setFinalConfirm(finalConfirmExp,
                finalConfirm.getSimplify());
    } */
    }

    /**
     * <p>An helper method for creating the modified {@code ensures} clause
     * that contains the modified {@code ensures} clause from the call statement as
     * well as any parameter {@code ensures} clauses.</p>
     *
     * <p>Note that this helper method also does all the appropriate substitutions to
     * the {@code VCs} in the assertive code block.</p>
     *
     * @param operationEntry Calling statement's {@link OperationEntry}.
     * @param modifiedArguments List of modified calling arguments.
     *
     * @return The modified {@code ensures} clause expression.
     */
    private Exp createModifiedEnsExp(OperationEntry operationEntry, List<Exp> modifiedArguments) {
        OperationDec operationDec =
                (OperationDec) operationEntry.getDefiningElement();

        // Get the ensures clause for this operation and
        // store it's associated location detail.
        AssertionClause ensuresClause = operationEntry.getEnsuresClause();
        Exp ensuresExp = Utilities.formConjunct(ensuresClause.getLocation(),
                null, ensuresClause, new LocationDetailModel(
                        ensuresClause.getLocation().clone(), myCallStmt.getLocation().clone(),
                        "Ensures Clause of " + operationDec.getName()));

        // Loop through each of the parameters in the operation entry.
        Map<Exp, Exp> substitutionsForSeq = new HashMap<>();
        Map<Exp, Exp> substitutions = new HashMap<>();
        Exp parameterEnsures = null;
        Iterator<Exp> it = modifiedArguments.iterator();
        ImmutableList<ProgramParameterEntry> entries = operationEntry.getParameters();
        for (ProgramParameterEntry entry : entries) {
            ParameterVarDec parameterVarDec =
                    (ParameterVarDec) entry.getDefiningElement();
            ParameterMode parameterMode = entry.getParameterMode();
            NameTy nameTy = (NameTy) parameterVarDec.getTy();
            Location loc = parameterVarDec.getLocation();
            Exp argument = it.next();

            // TODO: Add the other parameter mode logic
            if (parameterMode == ParameterMode.UPDATES) {
                // Parameter variable and incoming parameter variable and NQV(parameterExp)
                VarExp parameterExp = Utilities.createVarExp(loc.clone(), null,
                        parameterVarDec.getName().clone(), nameTy.getMathTypeValue(), null);
                OldExp oldParameterExp = new OldExp(loc.clone(), parameterExp.clone());
                oldParameterExp.setMathType(nameTy.getMathTypeValue());
                VCVarExp nqvParameterExp = Utilities.createVCVarExp(myCurrentAssertiveCodeBlock, parameterExp);
                myCurrentAssertiveCodeBlock.addFreeVar(nqvParameterExp);

                // Add these to our substitutions map
                substitutions.put(parameterExp, nqvParameterExp);
                substitutions.put(oldParameterExp, Utilities.convertExp(argument, myCurrentModuleScope));

                // Add this as something to substitute in our sequents
                substitutionsForSeq.put(parameterExp.clone(), nqvParameterExp.clone());

                // Query for the type entry in the symbol table
                SymbolTableEntry ste =
                        Utilities.searchProgramType(parameterVarDec.getLocation(), nameTy.getQualifier(),
                                nameTy.getName(), myCurrentModuleScope);

                ProgramTypeEntry typeEntry;
                if (ste instanceof ProgramTypeEntry) {
                    typeEntry = ste.toProgramTypeEntry(nameTy.getLocation());
                } else {
                    typeEntry =
                            ste.toTypeRepresentationEntry(nameTy.getLocation())
                                    .getDefiningTypeEntry();
                }

                AssertionClause modifiedConstraint = null;
                if (typeEntry.getDefiningElement() instanceof TypeFamilyDec) {
                    // Parameter variable with known program type
                    TypeFamilyDec type =
                            (TypeFamilyDec) typeEntry.getDefiningElement();
                    AssertionClause constraint = type.getConstraint();
                    modifiedConstraint =
                            Utilities.getTypeConstraintClause(constraint,
                                    loc.clone(), null,
                                    parameterVarDec.getName(), type.getExemplar(),
                                    typeEntry.getModelType(), null);
                }
                else {
                    Utilities.notAType(typeEntry, parameterVarDec.getLocation());
                }

                if (!VarExp.isLiteralTrue(modifiedConstraint.getAssertionExp())) {
                    // Form a conjunct with the modified constraint clause and add
                    // the location detail associated with it.
                    Location constraintLoc =
                            modifiedConstraint.getAssertionExp()
                                    .getLocation();
                    parameterEnsures = Utilities.formConjunct(myCallStmt.getLocation(),
                            parameterEnsures, modifiedConstraint, new LocationDetailModel(
                                    constraintLoc.clone(), constraintLoc.clone(),
                                    "Constraint Clause of " + parameterVarDec.getName()));
                }
            }
        }

        // Apply any replacements if it isn't just "ensures true;"
        if (!VarExp.isLiteralTrue(ensuresExp)) {
            // Replace any facility declaration instantiation arguments
            // in the ensures clause.
            ensuresExp =
                    Utilities.replaceFacilityFormalWithActual(ensuresExp,
                            operationDec.getParameters(), myCurrentModuleScope
                                    .getDefiningElement().getName(),
                            myCurrentConceptDeclaredTypes,
                            myLocalRepresentationTypeDecs,
                            myProcessedInstFacilityDecls);
        }

        // Form the final conjunct ensures clause expression
        if (parameterEnsures != null) {
            if (VarExp.isLiteralTrue(ensuresExp)) {
                ensuresExp = parameterEnsures;
            }
            else {
                ensuresExp =
                        MathExp.formConjunct(myCallStmt.getLocation().clone(),
                                parameterEnsures, ensuresExp);
            }
        }

        // Apply substitutions
        ensuresExp = ensuresExp.substitute(substitutions);

        // Retrieve the list of VCs and use the sequent
        // substitution map to do replacements.
        List<VerificationCondition> newVCs =
                createReplacementVCs(myCurrentAssertiveCodeBlock.getVCs(), substitutionsForSeq);

        // Store the new list of vcs
        myCurrentAssertiveCodeBlock.setVCs(newVCs);

        return ensuresExp;
    }

    /**
     * <p>An helper method for creating the modified {@code requires} clause
     * that contains all invoking conditions for nested function calls as well as
     * the modified {@code requires} clause from the call statement.</p>
     *
     * <p>Note that if any of the function or regular calls happen to be recursive,
     * then this will also generate the appropriate termination clauses and add it
     * to our current {@link AssertiveCodeBlock}.</p>
     *
     * @param operationEntry Calling statement's {@link OperationEntry}.
     * @param operationParamAsVarExps List of operation parameters as {@link VarExp VarExps}.
     * @param modifiedArguments List of modified calling arguments.
     *
     * @return The modified {@code requires} clause expression.
     */
    private Exp createModifiedReqExp(OperationEntry operationEntry,
            List<VarExp> operationParamAsVarExps, List<Exp> modifiedArguments) {
        OperationDec operationDec =
                (OperationDec) operationEntry.getDefiningElement();

        // Get the requires assertion for this operation and
        // store it's associated location detail.
        // YS: We don't need confirm it's which_entails clause,
        //     that has been taken care of already. Maybe add it as
        //     as something we can assume?
        AssertionClause requiresClause = operationDec.getRequires();
        Exp requiresExp = requiresClause.getAssertionExp().clone();
        requiresExp.setLocationDetailModel(new LocationDetailModel(
                requiresClause.getLocation().clone(), myCallStmt.getLocation()
                        .clone(), "Requires Clause of "
                        + operationDec.getName()));

        // Apply any replacements if it isn't just "requires true;"
        if (!VarExp.isLiteralTrue(requiresExp)) {
            // Replace formals in the original requires clause with the
            // actuals from the call statement.
            requiresExp =
                    Utilities.replaceFormalWithActual(requiresExp,
                            operationParamAsVarExps, modifiedArguments);

            // Replace any facility declaration instantiation arguments
            // in the requires clause.
            requiresExp =
                    Utilities.replaceFacilityFormalWithActual(requiresExp,
                            operationDec.getParameters(), myCurrentModuleScope
                                    .getDefiningElement().getName(),
                            myCurrentConceptDeclaredTypes,
                            myLocalRepresentationTypeDecs,
                            myProcessedInstFacilityDecls);
        }

        // Add any nested termination clauses to our current assertive code block.
        for (ConfirmStmt confirmStmt : myNestedTerminationConfirmStmts) {
            myCurrentAssertiveCodeBlock.addStatement(confirmStmt);
        }

        // Check to see if we are recursively calling ourselves. If yes,
        // generate a termination confirm clause and add it to our current
        // assertive code block.
        Exp terminationExp =
                VarExp.getTrueVarExp(myCallStmt.getLocation(), myTypeGraph);
        if (myCurrentProcedureOperationEntry.equals(operationEntry)
                && myCurrentProcedureDecreasingExp != null) {
            terminationExp = createTerminationReqExp();
        }

        if (!VarExp.isLiteralTrue(terminationExp)) {
            myCurrentAssertiveCodeBlock
                    .addStatement(new ConfirmStmt(terminationExp.getLocation()
                            .clone(), terminationExp, false));
        }

        // Form the final conjunct requires clause expression
        Exp conjunctRequiresExp =
                VarExp.getTrueVarExp(myCallStmt.getLocation().clone(),
                        myTypeGraph);
        for (Exp innerRequiresExp : myNestedRequiresClauses) {
            if (VarExp.isLiteralTrue(conjunctRequiresExp)) {
                conjunctRequiresExp = innerRequiresExp.clone();
            }
            else {
                conjunctRequiresExp =
                        MathExp.formConjunct(myCallStmt.getLocation().clone(),
                                conjunctRequiresExp, innerRequiresExp.clone());
            }
        }

        if (VarExp.isLiteralTrue(conjunctRequiresExp)) {
            conjunctRequiresExp = requiresExp;
        }
        else {
            conjunctRequiresExp =
                    MathExp.formConjunct(myCallStmt.getLocation().clone(),
                            conjunctRequiresExp, requiresExp);
        }

        return conjunctRequiresExp;
    }

    /**
     * <p>An helper method for generating a termination clause if our current
     * {@link CallStmt} is a recursive call to our current recursive {@code procedure}.</p>
     *
     * @return An {@link Exp} that contains the termination clause.
     */
    private Exp createTerminationReqExp() {
        // Create a new NQV(RS, P_Val)
        VCVarExp nqvPValExp =
                Utilities.createVCVarExp(myCurrentAssertiveCodeBlock, Utilities
                        .createPValExp(myCurrentProcedureDecreasingExp
                                .getLocation().clone(), myCurrentModuleScope));

        // Generate the termination of recursive call: 1 + P_Exp <= NQV(RS, P_Val)
        IntegerExp oneExp =
                new IntegerExp(myCurrentProcedureDecreasingExp.getLocation()
                        .clone(), null, 1);
        oneExp.setMathType(myCurrentProcedureDecreasingExp.getMathType());

        InfixExp sumExp =
                new InfixExp(myCurrentProcedureDecreasingExp.getLocation()
                        .clone(), oneExp, null, new PosSymbol(
                        myCurrentProcedureDecreasingExp.getLocation().clone(),
                        "+"), myCurrentProcedureDecreasingExp.clone());
        sumExp.setMathType(myCurrentProcedureDecreasingExp.getMathType());

        InfixExp terminationExp =
                new InfixExp(myCurrentProcedureDecreasingExp.getLocation()
                        .clone(), sumExp, null, new PosSymbol(
                        myCurrentProcedureDecreasingExp.getLocation().clone(),
                        "<="), nqvPValExp.clone());
        terminationExp.setMathType(myTypeGraph.BOOLEAN);

        // Store the location detail for the recursive function call's
        // termination expression.
        terminationExp.setLocationDetailModel(new LocationDetailModel(
                myCurrentProcedureDecreasingExp.getLocation().clone(),
                myCallStmt.getFunctionExp().getLocation().clone(),
                "Termination of Recursive Call"));

        return terminationExp;
    }

    /**
     * <p>An helper method for modifying the argument expression list
     * if we have a nested function call.</p>
     *
     * @param callArgs The original list of arguments.
     *
     * @return The modified list of arguments.
     */
    private List<Exp> modifyArgumentList(List<ProgramExp> callArgs) {
        // Find all the replacements that needs to happen to the requires
        // and ensures clauses
        List<Exp> replaceArgs = new ArrayList<>();
        for (ProgramExp exp : callArgs) {
            // If our argument is a ProgramFunctionExp, then we will
            // need to use the ProgramFunctionExpWalker to extract all
            // relevant information.
            if (exp instanceof ProgramFunctionExp) {
                // Use the walker to convert to mathematical expression
                ProgramFunctionExp expAsProgramFunctionexp = (ProgramFunctionExp) exp;
                ProgramFunctionExpWalker walker;
                if (myCurrentProcedureOperationEntry == null) {
                    walker =
                            new ProgramFunctionExpWalker(
                                    myCurrentAssertiveCodeBlock,
                                    myCurrentConceptDeclaredTypes,
                                    myLocalRepresentationTypeDecs,
                                    myProcessedInstFacilityDecls,
                                    myCurrentModuleScope, myTypeGraph);
                }
                else {
                    walker =
                            new ProgramFunctionExpWalker(
                                    myCurrentProcedureOperationEntry,
                                    myCurrentProcedureDecreasingExp,
                                    myCurrentAssertiveCodeBlock,
                                    myCurrentConceptDeclaredTypes,
                                    myLocalRepresentationTypeDecs,
                                    myProcessedInstFacilityDecls,
                                    myCurrentModuleScope, myTypeGraph);
                }
                TreeWalker.visit(walker, expAsProgramFunctionexp);

                // Retrieve the various pieces of information from the walker
                Exp generatedRequires =
                        walker.getRequiresClause(expAsProgramFunctionexp.
                                getLocation().clone());
                Exp generatedEnsures =
                        walker.getEnsuresClause(expAsProgramFunctionexp);
                List<Exp> restoresParamExps =
                        walker.getRestoresParamEnsuresClauses();
                List<ConfirmStmt> terminationConfirms =
                        walker.getTerminationConfirmStmts();

                // Form a conjunct using the restoresParamExps
                Exp restoresParamEnsures =
                        VarExp.getTrueVarExp(expAsProgramFunctionexp
                                .getLocation(), myTypeGraph);
                for (Exp restoresExp : restoresParamExps) {
                    if (VarExp.isLiteralTrue(restoresParamEnsures)) {
                        restoresParamEnsures = restoresExp;
                    }
                    else {
                        restoresParamEnsures =
                                MathExp.formConjunct(expAsProgramFunctionexp.getLocation().clone(),
                                        restoresParamEnsures, exp);
                    }
                }

                // 1) If the argument expression contains recursive calls,
                //    we need to add all the termination confirm statements.
                myNestedTerminationConfirmStmts.addAll(terminationConfirms);

                // 2) If the argument expression has any requires clauses,
                //    we need to add it as something we will need to confirm.
                if (!VarExp.isLiteralTrue(generatedRequires)) {
                    myNestedRequiresClauses.add(generatedRequires.clone());
                }

                // Add the modified ensures clause as the new expression we want
                // to replace in the CallStmt's ensures clause.
                replaceArgs.add(generatedEnsures.clone());
            }
            // For all other types of arguments, simply add it to the list to be replaced
            else {
                replaceArgs.add(exp);
            }
        }

        return replaceArgs;
    }
}