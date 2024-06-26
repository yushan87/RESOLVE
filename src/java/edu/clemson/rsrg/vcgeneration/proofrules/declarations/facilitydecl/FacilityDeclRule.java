/*
 * FacilityDeclRule.java
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
package edu.clemson.rsrg.vcgeneration.proofrules.declarations.facilitydecl;

import edu.clemson.rsrg.absyn.declarations.Dec;
import edu.clemson.rsrg.absyn.declarations.facilitydecl.FacilityDec;
import edu.clemson.rsrg.absyn.declarations.moduledecl.*;
import edu.clemson.rsrg.absyn.declarations.operationdecl.OperationDec;
import edu.clemson.rsrg.absyn.declarations.paramdecl.ModuleParameterDec;
import edu.clemson.rsrg.absyn.declarations.sharedstatedecl.SharedStateDec;
import edu.clemson.rsrg.absyn.declarations.typedecl.TypeFamilyDec;
import edu.clemson.rsrg.absyn.expressions.Exp;
import edu.clemson.rsrg.absyn.expressions.mathexpr.InfixExp;
import edu.clemson.rsrg.absyn.expressions.mathexpr.MathExp;
import edu.clemson.rsrg.absyn.expressions.mathexpr.VarExp;
import edu.clemson.rsrg.absyn.expressions.programexpr.*;
import edu.clemson.rsrg.absyn.items.programitems.EnhancementSpecRealizItem;
import edu.clemson.rsrg.absyn.items.programitems.ModuleArgumentItem;
import edu.clemson.rsrg.absyn.statements.ConfirmStmt;
import edu.clemson.rsrg.parsing.data.Location;
import edu.clemson.rsrg.parsing.data.LocationDetailModel;
import edu.clemson.rsrg.parsing.data.PosSymbol;
import edu.clemson.rsrg.treewalk.TreeWalker;
import edu.clemson.rsrg.typeandpopulate.entry.OperationEntry;
import edu.clemson.rsrg.typeandpopulate.exception.DuplicateSymbolException;
import edu.clemson.rsrg.typeandpopulate.exception.NoSuchSymbolException;
import edu.clemson.rsrg.typeandpopulate.query.NameQuery;
import edu.clemson.rsrg.typeandpopulate.symboltables.MathSymbolTable;
import edu.clemson.rsrg.typeandpopulate.symboltables.MathSymbolTableBuilder;
import edu.clemson.rsrg.typeandpopulate.symboltables.ModuleScope;
import edu.clemson.rsrg.typeandpopulate.typereasoning.TypeGraph;
import edu.clemson.rsrg.typeandpopulate.utilities.ModuleIdentifier;
import edu.clemson.rsrg.vcgeneration.proofrules.AbstractProofRuleApplication;
import edu.clemson.rsrg.vcgeneration.proofrules.ProofRuleApplication;
import edu.clemson.rsrg.vcgeneration.utilities.AssertiveCodeBlock;
import edu.clemson.rsrg.vcgeneration.utilities.Utilities;
import edu.clemson.rsrg.vcgeneration.utilities.VerificationContext;
import edu.clemson.rsrg.vcgeneration.utilities.formaltoactual.*;
import edu.clemson.rsrg.vcgeneration.utilities.treewalkers.ConceptSharedStateExtractor;
import edu.clemson.rsrg.vcgeneration.utilities.treewalkers.ConceptTypeExtractor;
import edu.clemson.rsrg.vcgeneration.utilities.treewalkers.ProgramFunctionExpWalker;
import java.util.*;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;

/**
 * <p>
 * This class contains the logic for a {@code facility} declaration rule.
 * </p>
 *
 * @author Yu-Shan Sun
 *
 * @version 1.0
 */
public class FacilityDeclRule extends AbstractProofRuleApplication implements ProofRuleApplication {

    // ===========================================================
    // Member Fields
    // ===========================================================

    // -----------------------------------------------------------
    // General
    // -----------------------------------------------------------

    /**
     * <p>
     * The module scope for the file we are generating {@code VCs} for.
     * </p>
     */
    private final ModuleScope myCurrentModuleScope;

    /**
     * <p>
     * The {@code facility} declaration we are applying the rule to.
     * </p>
     */
    private final FacilityDec myFacilityDec;

    /**
     * <p>
     * A flag that indicates if this is a local facility declaration or not.
     * </p>
     */
    private final boolean myIsLocalFacilityDec;

    /**
     * <p>
     * The symbol table we are currently building.
     * </p>
     */
    private final MathSymbolTableBuilder mySymbolTable;

    /**
     * <p>
     * This is the math type graph that indicates relationship between different math types.
     * </p>
     */
    private final TypeGraph myTypeGraph;

    // -----------------------------------------------------------
    // InstantiatedFacilityDecl - Related
    // -----------------------------------------------------------

    /**
     * <p>
     * A list that will be populated with the arguments used to instantiate the {@code Concept}.
     * </p>
     */
    private final List<Exp> myConceptActualArgList;

    /**
     * <p>
     * This contains all the types declared by the instantiated {@code Concept}.
     * </p>
     */
    private final List<TypeFamilyDec> myConceptDeclaredTypes;

    /**
     * <p>
     * A list that will be populated with the instantiating {@code Concept}'s formal parameters.
     * </p>
     */
    private final List<VarExp> myConceptFormalParamList;

    /**
     * <p>
     * A list that will be populated with the arguments used to instantiate the {@code Concept Realization}.
     * </p>
     */
    private final List<Exp> myConceptRealizActualArgList;

    /**
     * <p>
     * A list that will be populated with the instantiating {@code Concept Realization}'s formal parameters.
     * </p>
     */
    private final List<VarExp> myConceptRealizFormalParamList;

    /**
     * <p>
     * This contains all the shared state declared by the {@code Concept}.
     * </p>
     */
    private final List<SharedStateDec> myConceptSharedStates;

    /**
     * <p>
     * A list that contains the {@code Enhancement} and {@code Enhancement Realization}'s formal arguments to the
     * instantiated actual arguments.
     * </p>
     */
    private final List<InstantiatedEnhSpecRealizItem> myInstantiatedEnhSpecRealizItems;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>
     * This creates a new application for a {@code facility} declaration rule.
     * </p>
     *
     * @param facilityDec
     *            The {@code facility} declaration we are applying the rule to.
     * @param isLocalFacDec
     *            A flag that indicates if this is a local {@link FacilityDec}.
     * @param symbolTableBuilder
     *            The current symbol table.
     * @param moduleScope
     *            The current module scope we are visiting.
     * @param block
     *            The assertive code block that the subclasses are applying the rule to.
     * @param context
     *            The verification context that contains all the information we have collected so far.
     * @param stGroup
     *            The string template group we will be using.
     * @param blockModel
     *            The model associated with {@code block}.
     */
    public FacilityDeclRule(FacilityDec facilityDec, boolean isLocalFacDec, MathSymbolTableBuilder symbolTableBuilder,
            ModuleScope moduleScope, AssertiveCodeBlock block, VerificationContext context, STGroup stGroup,
            ST blockModel) {
        super(block, context, stGroup, blockModel);
        myCurrentModuleScope = moduleScope;
        myFacilityDec = facilityDec;
        myIsLocalFacilityDec = isLocalFacDec;
        mySymbolTable = symbolTableBuilder;
        myTypeGraph = symbolTableBuilder.getTypeGraph();

        // Objects needed to create a new InstantiatedFacilityDecl
        myConceptActualArgList = new ArrayList<>();
        myConceptDeclaredTypes = new LinkedList<>();
        myConceptFormalParamList = new ArrayList<>();
        myConceptRealizActualArgList = new ArrayList<>();
        myConceptRealizFormalParamList = new ArrayList<>();
        myConceptSharedStates = new LinkedList<>();
        myInstantiatedEnhSpecRealizItems = new LinkedList<>();
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>
     * This method applies the {@code Proof Rule}.
     * </p>
     */
    @Override
    public final void applyRule() {
        // Apply the part of the rule that deals with the facility
        // concept and its associated realization.
        Exp confirmExp = applyConceptRelatedPart();

        // Apply the part of the rule that deals with the facility
        // enhancements and its associated realizations.
        for (EnhancementSpecRealizItem specRealizItem : myFacilityDec.getEnhancementRealizPairs()) {
            Exp enhancementRelatedPart = applyEnhancementRelatedPart(specRealizItem);

            if (VarExp.isLiteralTrue(confirmExp)) {
                confirmExp = enhancementRelatedPart;
            } else {
                if (!VarExp.isLiteralTrue(enhancementRelatedPart)) {
                    confirmExp = InfixExp.formConjunct(myFacilityDec.getLocation().clone(), confirmExp,
                            enhancementRelatedPart);
                }
            }
        }

        // YS - This class is used by any importing facility declarations as well as
        // any local facility declarations. We really don't need to generate VCs
        // or display anything to our models if it isn't local.
        if (myIsLocalFacilityDec) {
            myCurrentAssertiveCodeBlock.addStatement(new ConfirmStmt(confirmExp.getLocation(), confirmExp, true));

            // Add the different details to the various different output models
            ST stepModel = mySTGroup.getInstanceOf("outputVCGenStep");
            stepModel.add("proofRuleName", getRuleDescription()).add("currentStateOfBlock",
                    myCurrentAssertiveCodeBlock);
            myBlockModel.add("vcGenSteps", stepModel.render());
        }
    }

    /**
     * <p>
     * This method returns an object that records all relevant information for the instantiated {@code Facility}.
     * </p>
     *
     * @return A {@link InstantiatedFacilityDecl} containing all the information.
     */
    public final InstantiatedFacilityDecl getInstantiatedFacilityDecl() {
        return new InstantiatedFacilityDecl(myFacilityDec, myConceptSharedStates, myConceptDeclaredTypes,
                myConceptFormalParamList, myConceptActualArgList, myConceptRealizFormalParamList,
                myConceptRealizActualArgList, myInstantiatedEnhSpecRealizItems, myIsLocalFacilityDec);
    }

    /**
     * <p>
     * This method returns a description associated with the {@code Proof Rule}.
     * </p>
     *
     * @return A string.
     */
    @Override
    public final String getRuleDescription() {
        return "Facility Instantiation Rule";
    }

    // ===========================================================
    // Private Methods
    // ===========================================================

    // -----------------------------------------------------------
    // General
    // -----------------------------------------------------------

    /**
     * <p>
     * An helper method that creates a list of {@link Exp Exps} representing each of the {@link ModuleArgumentItem
     * ModuleArgumentItems}. It is possible that the passed in programming expression contains nested function calls,
     * therefore we will need to deal with it appropriately.
     * </p>
     *
     * @param actualArgs
     *            List of module instantiated arguments.
     *
     * @return A list containing the {@link Exp Exps} representing each actual argument.
     */
    private List<Exp> createModuleArgExpList(List<ModuleArgumentItem> actualArgs) {
        List<Exp> retExpList = new ArrayList<>();

        for (ModuleArgumentItem item : actualArgs) {
            // Convert the module argument items into the equivalent
            // mathematical expression.
            ProgramExp moduleArgumentExp = item.getArgumentExp();
            Exp moduleArgumentAsExp;
            if (moduleArgumentExp instanceof ProgramFunctionExp) {
                // Use the walker to retrieve the ensures clause.
                ProgramFunctionExpWalker walker = new ProgramFunctionExpWalker(myCurrentVerificationContext,
                        myCurrentModuleScope, myTypeGraph);
                TreeWalker.visit(walker, moduleArgumentExp);

                // Retrieve the various pieces of information from the walker
                moduleArgumentAsExp = walker.getEnsuresClause((ProgramFunctionExp) moduleArgumentExp);
            } else {
                // Simply convert to the math equivalent expression
                moduleArgumentAsExp = Utilities.convertExp(moduleArgumentExp, myCurrentModuleScope);
            }

            // Add this to our return list
            retExpList.add(moduleArgumentAsExp);
        }

        return retExpList;
    }

    /**
     * <p>
     * An helper method that creates a list of {@link VarExp VarExps} representing each of the {@link ModuleParameterDec
     * ModuleParameterDecs}.
     * </p>
     *
     * @param formalParams
     *            List of module formal parameters.
     *
     * @return A list containing the {@link VarExp VarExps} representing each formal parameter.
     */
    private List<VarExp> createModuleParamExpList(List<ModuleParameterDec> formalParams) {
        List<VarExp> retExpList = new ArrayList<>(formalParams.size());

        // Create a VarExp representing each of the module parameters
        for (ModuleParameterDec dec : formalParams) {
            // Use the wrapped declaration name and type to create a VarExp.
            Dec wrappedDec = dec.getWrappedDec();
            retExpList.add(Utilities.createVarExp(wrappedDec.getLocation(), null, wrappedDec.getName(),
                    wrappedDec.getMathType(), null));
        }

        return retExpList;
    }

    /**
     * <p>
     * An helper method that searches for an {@link OperationEntry} using the provided qualifier and name.
     * </p>
     *
     * @param loc
     *            The location in the AST that we are currently visiting.
     * @param qualifier
     *            The qualifier of the operation.
     * @param name
     *            The name of the operation.
     *
     * @return An {@link OperationEntry} from the symbol table.
     */
    private OperationEntry searchOperation(Location loc, PosSymbol qualifier, PosSymbol name) {
        // Query for the corresponding operation
        OperationEntry op = null;
        try {
            op = myCurrentModuleScope
                    .queryForOne(new NameQuery(qualifier, name, MathSymbolTable.ImportStrategy.IMPORT_NAMED,
                            MathSymbolTable.FacilityStrategy.FACILITY_INSTANTIATE, true))
                    .toOperationEntry(loc);
        } catch (NoSuchSymbolException nsse) {
            Utilities.noSuchSymbol(qualifier, name.getName(), loc);
        } catch (DuplicateSymbolException dse) {
            // This should be caught earlier, when the duplicate operation is
            // created
            throw new RuntimeException(dse);
        }

        return op;
    }

    // -----------------------------------------------------------
    // Proof Rule - Related
    // -----------------------------------------------------------

    /**
     * <p>
     * An helper method that applies the part of the rule that deals with {@code Concept} and
     * {@code Concept Realizations}.
     * </p>
     *
     * @return An {@link Exp} that contains the {@code Concept}'s and {@code Concept Realization}'s modified requires
     *         clauses and any passed-in operations requires clauses and ensures clause.
     */
    private Exp applyConceptRelatedPart() {
        Exp retExp = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);
        try {
            // Obtain the concept module for the facility
            ConceptModuleDec facConceptDec = (ConceptModuleDec) mySymbolTable
                    .getModuleScope(new ModuleIdentifier(myFacilityDec.getConceptName().getName()))
                    .getDefiningElement();

            // Extract the concept's shared state variables
            ConceptSharedStateExtractor sharedStateExtractor = new ConceptSharedStateExtractor();
            TreeWalker.visit(sharedStateExtractor, facConceptDec);
            myConceptSharedStates.addAll(sharedStateExtractor.getSharedStateDecs());

            // Extract the concept's type declarations
            ConceptTypeExtractor typeExtractor = new ConceptTypeExtractor();
            TreeWalker.visit(typeExtractor, facConceptDec);
            myConceptDeclaredTypes.addAll(typeExtractor.getTypeFamilyDecs());

            // Obtain the concept's requires clause
            Exp conceptReq = facConceptDec.getRequires().getAssertionExp().clone();

            // Convert the concept's module parameters and the instantiated
            // concept's arguments into the appropriate mathematical expressions.
            // Note that any nested function calls will be dealt with appropriately.
            myConceptFormalParamList.addAll(createModuleParamExpList(facConceptDec.getParameterDecs()));
            myConceptActualArgList.addAll(createModuleArgExpList(myFacilityDec.getConceptParams()));

            // Note: Only to this step if we don't have an external realization
            Exp conceptRealizReq = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);
            Exp conceptRealizOperationPart = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);
            if (!myFacilityDec.getExternallyRealizedFlag()) {
                try {
                    // Obtain the concept realization module for the facility
                    ConceptRealizModuleDec facConceptRealizDec = (ConceptRealizModuleDec) mySymbolTable
                            .getModuleScope(new ModuleIdentifier(myFacilityDec.getConceptRealizName().getName()))
                            .getDefiningElement();

                    // Obtain the concept realization's requires clause
                    conceptRealizReq = facConceptRealizDec.getRequires().getAssertionExp().clone();

                    // Convert the concept realization's module parameters and the instantiated
                    // realization's arguments into the appropriate mathematical expressions.
                    // Note that any nested function calls will be dealt with appropriately.
                    myConceptRealizFormalParamList
                            .addAll(createModuleParamExpList(facConceptRealizDec.getParameterDecs()));
                    myConceptRealizActualArgList.addAll(createModuleArgExpList(myFacilityDec.getConceptRealizParams()));

                    // Replace the formal with the actual (if conceptRealizReq /= true)
                    if (!MathExp.isLiteralTrue(conceptRealizReq)) {
                        // Step 1a: Substitute concept realization's formal parameters with
                        // actual instantiation arguments for the concept realization's
                        // requires clause.
                        // ( RPC[ rn~>rn_exp, RR~>IRR ] )
                        conceptRealizReq = Utilities.replaceFormalWithActual(conceptRealizReq,
                                myConceptRealizFormalParamList, myConceptRealizActualArgList);

                        // Step 1b: Substitute concept's formal parameters with actual
                        // instantiation arguments for the concept realization's
                        // requires clause.
                        // ( ( RPC[ rn~>rn_exp, RR~>IRR ] ∧ CPC )[ n~>n_exp, R~>IR ] )
                        //
                        // YS: This isn't exactly what the rule says, but it makes it easier
                        // to record the location details for displaying purposes. Doing
                        // the substitution first and then forming the conjunct is the same
                        // as forming the conjunct first and then doing the substitution.
                        conceptRealizReq = Utilities.replaceFormalWithActual(conceptRealizReq, myConceptFormalParamList,
                                myConceptActualArgList);

                        // Store the location detail for this requires clause
                        Location conceptRealizReqLoc = conceptRealizReq.getLocation();
                        conceptRealizReq.setLocationDetailModel(new LocationDetailModel(conceptRealizReqLoc.clone(),
                                myFacilityDec.getConceptRealizName().getLocation().clone(), "Requires Clause for "
                                        + facConceptRealizDec.getName().getName() + " in " + getRuleDescription()));
                    }

                    // Iterate through searching for any operations being passed as parameters.
                    Iterator<ModuleParameterDec> realizFormalParams = facConceptRealizDec.getParameterDecs().iterator();
                    Iterator<ModuleArgumentItem> realizActualArgs = myFacilityDec.getConceptRealizParams().iterator();
                    while (realizFormalParams.hasNext()) {
                        ModuleParameterDec moduleParameterDec = realizFormalParams.next();
                        ModuleArgumentItem moduleArgumentItem = realizActualArgs.next();

                        // Only care about OperationDecs
                        if (moduleParameterDec.getWrappedDec() instanceof OperationDec) {
                            // Formal operation defined in the specifications and
                            // the operation being passed as argument
                            OperationDec formalOperationDec = (OperationDec) moduleParameterDec.getWrappedDec();

                            ProgramVariableNameExp operationNameExp = (ProgramVariableNameExp) moduleArgumentItem
                                    .getArgumentExp();
                            OperationEntry actualOperationEntry = searchOperation(moduleArgumentItem.getLocation(),
                                    operationNameExp.getQualifier(), operationNameExp.getName());
                            OperationDec actualOperationDec = actualOperationEntry.getOperationDec();

                            // Step 2: Substitute any operations's requires and ensures clauses
                            // passed to the concept realization instantiation.
                            // ( preRP[ rn~>rn_exp, rx~>irx ] => preIRP ) ∧
                            // ( postIRP => postRP[ rn~>rn_exp, #rx~>#irx, rx~>irx ] )
                            Exp processedOperationPart = applyOperationRelatedPart(
                                    moduleArgumentItem.getLocation().clone(), formalOperationDec,
                                    operationNameExp.getQualifier(), actualOperationDec, new ArrayList<VarExp>(),
                                    new ArrayList<Exp>(), myConceptRealizFormalParamList, myConceptRealizActualArgList);
                            if (VarExp.isLiteralTrue(conceptRealizOperationPart)) {
                                conceptRealizOperationPart = processedOperationPart;
                            } else {
                                // YS - Don't need to form a conjunct if processed operation part is "true".
                                if (!VarExp.isLiteralTrue(processedOperationPart)) {
                                    conceptRealizOperationPart = InfixExp.formConjunct(
                                            myFacilityDec.getLocation().clone(), conceptRealizOperationPart,
                                            processedOperationPart);
                                }
                            }
                        }
                    }
                } catch (NoSuchSymbolException e) {
                    Utilities.noSuchModule(myFacilityDec.getConceptRealizName().getLocation());
                }
            }

            // Step 1c: Substitute concept's formal parameters with actual
            // instantiation arguments for the concept's requires clause.
            // ( ( RPC[ rn~>rn_exp, RR~>IRR ] ∧ CPC )[ n~>n_exp, R~>IR ] )
            //
            // YS: Replace the formal with the actual (if conceptReq /= true)
            if (!MathExp.isLiteralTrue(conceptReq)) {
                conceptReq = Utilities.replaceFormalWithActual(conceptReq, myConceptFormalParamList,
                        myConceptActualArgList);

                // Store the location detail for this requires clause
                Location conceptReqLoc = conceptReq.getLocation();
                conceptReq.setLocationDetailModel(new LocationDetailModel(conceptReqLoc.clone(),
                        myFacilityDec.getConceptName().getLocation().clone(),
                        "Requires Clause for " + facConceptDec.getName().getName() + " in " + getRuleDescription()));
            }

            // Results from applying steps 1a to 1c.
            Exp conceptRequiresConjuct;
            if (VarExp.isLiteralTrue(conceptRealizReq)) {
                conceptRequiresConjuct = conceptReq;
            } else {
                if (VarExp.isLiteralTrue(conceptReq)) {
                    conceptRequiresConjuct = conceptRealizReq;
                } else {
                    // YS: The rule does put the CPC in the second part of the conjunct,
                    // But I want the requires clause VC for concept to come before
                    // it's realizations.
                    conceptRequiresConjuct = InfixExp.formConjunct(myFacilityDec.getLocation().clone(), conceptReq,
                            conceptRealizReq);
                }
            }

            // Combine with any expressions generated by step 2.
            if (VarExp.isLiteralTrue(conceptRealizOperationPart)) {
                retExp = conceptRequiresConjuct;
            } else {
                if (VarExp.isLiteralTrue(conceptRequiresConjuct)) {
                    retExp = conceptRealizOperationPart;
                } else {
                    retExp = InfixExp.formConjunct(myFacilityDec.getLocation().clone(), conceptRequiresConjuct,
                            conceptRealizOperationPart);
                }
            }
        } catch (NoSuchSymbolException e) {
            Utilities.noSuchModule(myFacilityDec.getConceptName().getLocation());
        }

        return retExp;
    }

    /**
     * <p>
     * An helper method that applies the part of the rule that deals with {@code Enhancement} and
     * {@code Enhancement Realizations}.
     * </p>
     *
     * @param specRealizItem
     *            The {@code Enhancement} and {@code Enhancement Realizations} we are going to be dealing with.
     *
     * @return An {@link Exp} that contains the {@code Enhancement}'s and {@code Enhancement Realization}'s modified
     *         requires clauses and any passed-in operations requires clauses and ensures clause.
     */
    private Exp applyEnhancementRelatedPart(EnhancementSpecRealizItem specRealizItem) {
        Exp retExp = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);

        // Enhancement part of the rule
        List<VarExp> enhancementFormalParamList;
        List<Exp> enhancementActualArgList;
        try {
            // Obtain the enhancement module for the facility
            EnhancementModuleDec enhancementModuleDec = (EnhancementModuleDec) mySymbolTable
                    .getModuleScope(new ModuleIdentifier(specRealizItem.getEnhancementName().getName()))
                    .getDefiningElement();

            // Obtain the enhancement's requires clause
            Exp enhancementReq = enhancementModuleDec.getRequires().getAssertionExp().clone();

            // Convert the enhancement's module parameters and the instantiated
            // enhancement's arguments into the appropriate mathematical expressions.
            // Note that any nested function calls will be dealt with appropriately.
            enhancementFormalParamList = createModuleParamExpList(enhancementModuleDec.getParameterDecs());
            enhancementActualArgList = createModuleArgExpList(specRealizItem.getEnhancementParams());

            // Enhancement realization part of the rule
            Exp realizationReq = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);
            Exp realizOperationPart = VarExp.getTrueVarExp(myFacilityDec.getLocation().clone(), myTypeGraph);
            try {
                // Obtain the enhancement module for the facility
                EnhancementRealizModuleDec enhancementRealizModuleDec = (EnhancementRealizModuleDec) mySymbolTable
                        .getModuleScope(new ModuleIdentifier(specRealizItem.getEnhancementRealizName().getName()))
                        .getDefiningElement();

                // Obtain the enhancement realization's requires clause
                realizationReq = enhancementRealizModuleDec.getRequires().getAssertionExp().clone();

                // Convert the enhancement realization's module parameters and the instantiated
                // realization's arguments into the appropriate mathematical expressions.
                // Note that any nested function calls will be dealt with appropriately.
                List<VarExp> enhancementRealizFormalParamList = createModuleParamExpList(
                        enhancementRealizModuleDec.getParameterDecs());
                List<Exp> enhancementRealizActualArgList = createModuleArgExpList(
                        specRealizItem.getEnhancementRealizParams());

                // Replace the formal with the actual (if realizationReq /= true)
                if (!MathExp.isLiteralTrue(realizationReq)) {
                    // Step 1a: Substitute enhancement realization's formal parameters with
                    // actual instantiation arguments for the enhancement realization's
                    // requires clause.
                    // ( ERPC[ ern~>ern_exp ] )
                    realizationReq = Utilities.replaceFormalWithActual(realizationReq, enhancementRealizFormalParamList,
                            enhancementRealizActualArgList);

                    // Step 1b: Substitute enhancement's formal parameters with actual
                    // instantiation arguments for the enhancement realization's
                    // requires clause.
                    // ( ERPC[ ern~>ern_exp ] ∧ EPC )
                    //
                    // YS: This isn't exactly what the rule says, but it makes it easier
                    // to record the location details for displaying purposes. Doing
                    // the substitution first and then forming the conjunct is the same
                    // as forming the conjunct first and then doing the substitution.
                    realizationReq = Utilities.replaceFormalWithActual(realizationReq, enhancementFormalParamList,
                            enhancementActualArgList);

                    // Step 1c: Substitute concept's formal parameters with actual
                    // instantiation arguments for the enhancement realization's
                    // requires clause.
                    // ( ( ERPC[ ern~>ern_exp ] ∧ EPC )[ n~>n_exp, R~>IR ] )
                    //
                    // YS: This isn't exactly what the rule says, but it makes it easier
                    // to record the location details for displaying purposes. Doing
                    // the substitution first and then forming the conjunct is the same
                    // as forming the conjunct first and then doing the substitution.
                    realizationReq = Utilities.replaceFormalWithActual(realizationReq, myConceptFormalParamList,
                            myConceptActualArgList);

                    // Store the location detail for this requires clause
                    Location realizationLoc = realizationReq.getLocation();
                    realizationReq.setLocationDetailModel(new LocationDetailModel(realizationLoc.clone(),
                            specRealizItem.getEnhancementRealizName().getLocation().clone(), "Requires Clause for "
                                    + enhancementRealizModuleDec.getName().getName() + " in " + getRuleDescription()));
                }

                // Iterate through searching for any operations being passed as parameters.
                Iterator<ModuleParameterDec> realizFormalParams = enhancementRealizModuleDec.getParameterDecs()
                        .iterator();
                Iterator<ModuleArgumentItem> realizActualArgs = specRealizItem.getEnhancementRealizParams().iterator();
                while (realizFormalParams.hasNext()) {
                    ModuleParameterDec moduleParameterDec = realizFormalParams.next();
                    ModuleArgumentItem moduleArgumentItem = realizActualArgs.next();

                    // Only care about OperationDecs
                    if (moduleParameterDec.getWrappedDec() instanceof OperationDec) {
                        // Formal operation defined in the specifications and
                        // the operation being passed as argument
                        OperationDec formalOperationDec = (OperationDec) moduleParameterDec.getWrappedDec();

                        ProgramVariableNameExp operationNameExp = (ProgramVariableNameExp) moduleArgumentItem
                                .getArgumentExp();
                        OperationEntry actualOperationEntry = searchOperation(moduleArgumentItem.getLocation(),
                                operationNameExp.getQualifier(), operationNameExp.getName());
                        OperationDec actualOperationDec = actualOperationEntry.getOperationDec();

                        // Step 2: Substitute any operations's requires and ensures clauses
                        // passed to the enhancement realization instantiation.
                        // ( preERP[ ern~>ern_exp, erx~>ierx ] => preIERP ) ∧
                        // ( postIERP => postERP[ ern~>ern_exp, #erx~>#ierx, erx~>ierx ] )
                        Exp processedOperationPart = applyOperationRelatedPart(moduleArgumentItem.getLocation().clone(),
                                formalOperationDec, operationNameExp.getQualifier(), actualOperationDec,
                                enhancementFormalParamList, enhancementActualArgList, enhancementRealizFormalParamList,
                                enhancementRealizActualArgList);
                        if (VarExp.isLiteralTrue(realizOperationPart)) {
                            realizOperationPart = processedOperationPart;
                        } else {
                            // YS - Don't need to form a conjunct if processed operation part is "true".
                            if (!VarExp.isLiteralTrue(processedOperationPart)) {
                                realizOperationPart = InfixExp.formConjunct(myFacilityDec.getLocation().clone(),
                                        realizOperationPart, processedOperationPart);
                            }
                        }
                    }
                }

                // Store these inside a new InstantiatedEnhSpecRealizItem and
                // add it to our list.
                myInstantiatedEnhSpecRealizItems.add(new InstantiatedEnhSpecRealizItem(specRealizItem,
                        enhancementFormalParamList, enhancementActualArgList, enhancementRealizFormalParamList,
                        enhancementRealizActualArgList));
            } catch (NoSuchSymbolException e) {
                Utilities.noSuchModule(specRealizItem.getEnhancementRealizName().getLocation());
            }

            // YS: Replace the formal with the actual (if enhancementReq /= true)
            if (!MathExp.isLiteralTrue(enhancementReq)) {
                // Step 1d: Substitute enhancement's formal parameters with actual
                // instantiation arguments for the enhancement's
                // requires clause.
                // ( ERPC[ ern~>ern_exp ] ∧ EPC )
                //
                // YS: This isn't exactly what the rule says, but it makes it easier
                // to record the location details for displaying purposes. Doing
                // the substitution first and then forming the conjunct is the same
                // as forming the conjunct first and then doing the substitution.
                enhancementReq = Utilities.replaceFormalWithActual(enhancementReq, enhancementFormalParamList,
                        enhancementActualArgList);

                // Step 1e: Substitute concept's formal parameters with actual
                // instantiation arguments for the enhancement's
                // requires clause.
                // ( ( ERPC[ ern~>ern_exp ] ∧ EPC )[ n~>n_exp, R~>IR ] )
                //
                // YS: This isn't exactly what the rule says, but it makes it easier
                // to record the location details for displaying purposes. Doing
                // the substitution first and then forming the conjunct is the same
                // as forming the conjunct first and then doing the substitution.
                enhancementReq = Utilities.replaceFormalWithActual(enhancementReq, myConceptFormalParamList,
                        myConceptActualArgList);

                // Store the location detail for this requires clause
                Location enhancementReqLoc = enhancementReq.getLocation();
                enhancementReq.setLocationDetailModel(new LocationDetailModel(enhancementReqLoc.clone(),
                        specRealizItem.getEnhancementName().getLocation().clone(), "Requires Clause for "
                                + enhancementModuleDec.getName().getName() + " in " + getRuleDescription()));
            }

            // Results from applying steps 1a to 1e.
            Exp enhancementRequiresConjuct;
            if (VarExp.isLiteralTrue(realizationReq)) {
                enhancementRequiresConjuct = enhancementReq;
            } else {
                if (VarExp.isLiteralTrue(enhancementReq)) {
                    enhancementRequiresConjuct = realizationReq;
                } else {
                    // YS: The rule does put the ERPC in the second part of the conjunct,
                    // But I want the requires clause VC for enhancement to come before
                    // it's realizations.
                    enhancementRequiresConjuct = InfixExp.formConjunct(myFacilityDec.getLocation().clone(),
                            enhancementReq, realizationReq);
                }
            }

            // Combine with any expressions generated by step 2.
            if (VarExp.isLiteralTrue(realizOperationPart)) {
                retExp = enhancementRequiresConjuct;
            } else {
                if (VarExp.isLiteralTrue(enhancementRequiresConjuct)) {
                    retExp = realizOperationPart;
                } else {
                    retExp = InfixExp.formConjunct(myFacilityDec.getLocation().clone(), enhancementRequiresConjuct,
                            realizOperationPart);
                }
            }
        } catch (NoSuchSymbolException e) {
            Utilities.noSuchModule(specRealizItem.getEnhancementName().getLocation());
        }

        return retExp;
    }

    /**
     * <p>
     * An helper method that applies the part of the rule that deals with passing {@code Operations} as parameters.
     * </p>
     *
     * @param argLoc
     *            A {@link Location} object that indicates where the {@code Operation} is being passed as argument.
     * @param formalOpDec
     *            The formal {@link OperationDec} specified in the formal parameters.
     * @param actualOpQualifier
     *            The module qualifier indicating where the {@code actualOpDec} originated from.
     * @param actualOpDec
     *            The actual {@link OperationDec} being passed to the instantiation.
     * @param enhancementFormalParamList
     *            The list of {@code Enhancement} formal parameters. If we are processing {@code Concept Realizations},
     *            this list will be empty.
     * @param enhancementActualArgList
     *            The list of arguments instantiating the {@code Enhancement}. If we are processing
     *            {@code Concept Realizations}, this list will be empty.
     * @param realizFormalParamList
     *            The list of {@code Realization} formal parameters.
     * @param realizActualArgList
     *            The list of arguments instantiating the {@code Realization}.
     *
     * @return An {@link Exp} that contains the passed-in operations requires clauses and ensures clause that must be
     *         true to successfully pass the operation as parameter.
     */
    private Exp applyOperationRelatedPart(Location argLoc, OperationDec formalOpDec, PosSymbol actualOpQualifier,
            OperationDec actualOpDec, List<VarExp> enhancementFormalParamList, List<Exp> enhancementActualArgList,
            List<VarExp> realizFormalParamList, List<Exp> realizActualArgList) {
        Exp retExp = VarExp.getTrueVarExp(argLoc, myTypeGraph);

        // Replace concept/enhancement/realization formals with actual
        // instantiations in the formalOpRequires/formalOpEnsures clauses
        Exp formalOpRequires = formalOpDec.getRequires().getAssertionExp();
        Exp formalOpEnsures = formalOpDec.getEnsures().getAssertionExp();
        formalOpRequires = Utilities.replaceFormalWithActual(formalOpRequires, myConceptFormalParamList,
                myConceptActualArgList);
        formalOpRequires = Utilities.replaceFormalWithActual(formalOpRequires, enhancementFormalParamList,
                enhancementActualArgList);
        formalOpRequires = Utilities.replaceFormalWithActual(formalOpRequires, realizFormalParamList,
                realizActualArgList);

        formalOpEnsures = Utilities.replaceFormalWithActual(formalOpEnsures, myConceptFormalParamList,
                myConceptActualArgList);
        formalOpEnsures = Utilities.replaceFormalWithActual(formalOpEnsures, enhancementFormalParamList,
                enhancementActualArgList);
        formalOpEnsures = Utilities.replaceFormalWithActual(formalOpEnsures, realizFormalParamList,
                realizActualArgList);

        // Things related to actualOpDec
        Exp actualOpRequires = actualOpDec.getRequires().getAssertionExp();
        Exp actualOpEnsures = actualOpDec.getEnsures().getAssertionExp();

        // YS - We need to replace the requires/ensures clauses to include any
        // qualifiers to distinguish the operation from others with the same name.
        if (actualOpQualifier != null) {
            List<VarExp> actualOpParamsAsVarExp = Utilities.createOperationParamExpList(actualOpDec.getParameters());
            if (actualOpDec.getReturnTy() != null) {
                actualOpParamsAsVarExp.add(Utilities.createVarExp(actualOpDec.getReturnTy().getLocation(),
                        actualOpQualifier, actualOpDec.getName(), actualOpDec.getReturnTy().getMathType(), null));
            }

            Map<Exp, Exp> varExpReplacementMap = new HashMap<>(actualOpParamsAsVarExp.size());
            for (VarExp paramExp : actualOpParamsAsVarExp) {
                varExpReplacementMap.put(paramExp,
                        Utilities.createVarExp(paramExp.getLocation(), actualOpQualifier.clone(),
                                paramExp.getName().clone(), paramExp.getMathType(), paramExp.getMathTypeValue()));
            }

            // Apply the replacement for any outgoing variables
            actualOpRequires = actualOpRequires.substitute(varExpReplacementMap);
            actualOpEnsures = actualOpEnsures.substitute(varExpReplacementMap);
        }

        // Facility Decl Rule (Operations as Parameters Part 1):
        // preRP [ rn ~> rn_exp, rx ~> irx ] implies preIRP
        // YS - Only do this if preIRP isn't just true.
        if (!VarExp.isLiteralTrue(actualOpRequires)) {
            retExp = InfixExp.formImplies(actualOpRequires.getLocation(), formalOpRequires, actualOpRequires);

            // Store the location detail for this implication
            String message = "Requires Clause of " + formalOpDec.getName().getName()
                    + " implies the Requires Clause of ";
            if (actualOpQualifier != null) {
                message += (actualOpQualifier.getName() + "::");
            }
            retExp.setLocationDetailModel(new LocationDetailModel(actualOpRequires.getLocation().clone(),
                    argLoc.clone(), message + actualOpDec.getName().getName() + " in " + getRuleDescription()));
        }

        // Facility Decl Rule (Operations as Parameters Part 2):
        // postIRP implies postRP [ rn ~> rn_exp, #rx ~> #irx, rx ~> irx ]
        // YS - Only do this if postRP isn't just true.
        if (!VarExp.isLiteralTrue(formalOpEnsures)) {
            Exp impliesExp = InfixExp.formImplies(actualOpEnsures.getLocation(), actualOpEnsures, formalOpEnsures);

            // Store the location detail for this implication
            String message = "Ensures Clause of ";
            if (actualOpQualifier != null) {
                message += (actualOpQualifier.getName() + "::");
            }
            impliesExp.setLocationDetailModel(new LocationDetailModel(actualOpEnsures.getLocation().clone(),
                    argLoc.clone(), message + actualOpDec.getName().getName() + " implies the Ensures Clause of "
                            + formalOpDec.getName().getName() + " in " + getRuleDescription()));

            // Form a conjunct if needed
            if (!VarExp.isLiteralTrue(retExp)) {
                retExp = InfixExp.formConjunct(actualOpDec.getLocation(), retExp, impliesExp);
            } else {
                retExp = impliesExp;
            }
        }

        return retExp;
    }
}
