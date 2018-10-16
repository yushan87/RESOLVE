/*
 * PExpTest.java
 * ---------------------------------
 * Copyright (c) 2018
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.rsrg.prover.absyn;

import edu.clemson.cs.rsrg.absyn.ResolveConceptualElement;
import edu.clemson.cs.rsrg.absyn.declarations.variabledecl.MathVarDec;
import edu.clemson.cs.rsrg.absyn.expressions.Exp;
import edu.clemson.cs.rsrg.absyn.expressions.mathexpr.*;
import edu.clemson.cs.rsrg.absyn.rawtypes.NameTy;
import edu.clemson.cs.rsrg.init.CompileEnvironment;
import edu.clemson.cs.rsrg.init.ResolveCompiler;
import edu.clemson.cs.rsrg.init.file.ModuleType;
import edu.clemson.cs.rsrg.init.file.ResolveFile;
import edu.clemson.cs.rsrg.init.file.ResolveFileBasicInfo;
import edu.clemson.cs.rsrg.parsing.data.Location;
import edu.clemson.cs.rsrg.parsing.data.PosSymbol;
import edu.clemson.cs.rsrg.prover.absyn.expressions.PSymbol;
import edu.clemson.cs.rsrg.statushandling.SystemStdHandler;
import edu.clemson.cs.rsrg.statushandling.exception.MiscErrorException;
import edu.clemson.cs.rsrg.typeandpopulate.entry.SymbolTableEntry;
import edu.clemson.cs.rsrg.typeandpopulate.mathtypes.MTProper;
import edu.clemson.cs.rsrg.typeandpopulate.typereasoning.TypeGraph;
import edu.clemson.cs.rsrg.vcgeneration.utilities.Utilities;
import org.antlr.v4.runtime.UnbufferedCharStream;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import org.junit.Test;
import static org.junit.Assert.*;

/**
 * <p>Unit test for testing the RESOLVE compiler's sequent reduction rules.</p>
 *
 * @author Hampton Smith
 * @author Daniel Welch
 * @author Yu-Shan Sun
 * @version 2.0
 */
public class PExpTest {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /**
     * <p>A fake {@link Location} object to be used to create
     * {@link ResolveConceptualElement ResolveConceptualElements}.</p>
     */
    private final Location FAKE_LOCATION;

    /**
     * <p>A fake {@link TypeGraph} object that allows us to assign
     * types to expressions.</p>
     */
    private final TypeGraph FAKE_TYPEGRAPH;

    /** <p>A fake type {@code Z}.</p> */
    private final MTProper FAKE_Z;

    {
        try {
            FAKE_LOCATION =
                    new Location(new ResolveFile(new ResolveFileBasicInfo(
                            "PExpTest", ""), ModuleType.THEORY,
                            new UnbufferedCharStream(new StringReader("")),
                            null, new ArrayList<String>(), ""), 0, 0);

            // Create a fake typegraph
            // YS: We need to create a ResolveCompiler instance to instantiate
            // the flag manager...
            new ResolveCompiler(new String[0]);
            FAKE_TYPEGRAPH =
                    new TypeGraph(new CompileEnvironment(new String[0],
                            "TestCompiler", new SystemStdHandler()));

            FAKE_Z =
                    new MTProper(FAKE_TYPEGRAPH, FAKE_TYPEGRAPH.SSET, false,
                            "Z");
        }
        catch (IOException e) {
            throw new MiscErrorException("Error creating a fake location", e);
        }
    }

    // ===========================================================
    // Test Methods
    // ===========================================================

    /**
     * <p>This tests what happens when we use the method {@link PExp#buildPExp(TypeGraph, Exp)}}
     * to build simple prover expressions.</p>
     */
    @Test
    public final void testBuildSimplePExp() {
        // "T : SSet"
        Exp varTExp =
                Utilities.createVarExp(FAKE_LOCATION.clone(), null,
                        new PosSymbol(FAKE_LOCATION.clone(), "T"),
                        FAKE_TYPEGRAPH.SSET, null);

        // Make sure we built the proper PSymbol from varTExp
        PExp varTExpAsPExp = PExp.buildPExp(FAKE_TYPEGRAPH, varTExp);
        assertEquals(varTExpAsPExp.getClass(), PSymbol.class);
        assertEquals(varTExpAsPExp.getMathType(), FAKE_TYPEGRAPH.SSET);

        // Make sure that there are no quantified variables.
        assertEquals(varTExpAsPExp.getQuantifiedVariables(), Collections
                .<PSymbol> emptySet());
        assertEquals(((PSymbol) varTExpAsPExp).quantification,
                PSymbol.Quantification.NONE);

        // "0 : Z"
        Exp varZeroExp =
                Utilities
                        .createVarExp(FAKE_LOCATION.clone(), null,
                                new PosSymbol(FAKE_LOCATION.clone(), "0"),
                                FAKE_Z, null);

        // Make sure we built the proper PSymbol from varTExp
        PExp varZeroExpAsPExp = PExp.buildPExp(FAKE_TYPEGRAPH, varZeroExp);
        assertEquals(varZeroExpAsPExp.getClass(), PSymbol.class);
        assertEquals(varZeroExpAsPExp.getMathType(), FAKE_Z);

        // Make sure that there are no quantified variables.
        assertEquals(varZeroExpAsPExp.getQuantifiedVariables(), Collections
                .<PSymbol> emptySet());
        assertEquals(((PSymbol) varZeroExpAsPExp).quantification,
                PSymbol.Quantification.NONE);
    }

    /**
     * <p>This tests that we can build a simple {@code forall} expression
     * as a {@link PExp}.</p>
     */
    @Test
    public final void testSimpleForallPExp() {
        // "For all x : B"
        VarExp varExp =
                Utilities.createVarExp(FAKE_LOCATION.clone(), null,
                        new PosSymbol(FAKE_LOCATION.clone(), "x"),
                        FAKE_TYPEGRAPH.BOOLEAN, null);
        varExp.setQuantification(SymbolTableEntry.Quantification.UNIVERSAL);

        // Make sure we built the proper PSymbol from varExp
        PExp result = PExp.buildPExp(FAKE_TYPEGRAPH, varExp);
        assertEquals(result.getClass(), PSymbol.class);
        assertEquals(result.getMathType(), FAKE_TYPEGRAPH.BOOLEAN);

        // Make sure that the only quantified symbol is "x"
        assertEquals(result.getQuantifiedVariables(), Collections
                .singleton(PExp.buildPExp(FAKE_TYPEGRAPH, varExp)));
    }

    /**
     * <p>This tests that we can build a complex {@code forall} expression
     * as a {@link PExp}.</p>
     */
    @Test
    public final void testComplexForallPExp() {
        // "For all a : Z, A or P(a)"
        Exp varExp =
                Utilities
                        .createVarExp(FAKE_LOCATION.clone(), null,
                                new PosSymbol(FAKE_LOCATION.clone(), "a"),
                                FAKE_Z, null);
        Exp varAExp =
                Utilities.createVarExp(FAKE_LOCATION.clone(), null,
                        new PosSymbol(FAKE_LOCATION.clone(), "A"),
                        FAKE_TYPEGRAPH.BOOLEAN, null);
        FunctionExp functionExp =
                Utilities.createFunctionExp(FAKE_LOCATION.clone(), null,
                        new PosSymbol(FAKE_LOCATION.clone(), "P"), Collections
                                .singletonList(varExp.clone()),
                        FAKE_TYPEGRAPH.SSET_FUNCTION, FAKE_TYPEGRAPH.BOOLEAN);

        QuantExp quantExp =
                new QuantExp(FAKE_LOCATION.clone(),
                        SymbolTableEntry.Quantification.UNIVERSAL, Collections
                                .singletonList(new MathVarDec(new PosSymbol(
                                        FAKE_LOCATION.clone(), "a"),
                                        new NameTy(FAKE_LOCATION.clone(), null,
                                                new PosSymbol(FAKE_LOCATION
                                                        .clone(), "Z")))),
                        null, MathExp.formDisjunct(FAKE_LOCATION.clone(),
                                varAExp, functionExp));

        // Make sure we built the proper PSymbol from quantExp
        PExp result = PExp.buildPExp(FAKE_TYPEGRAPH, quantExp);
        assertEquals(result.getClass(), PSymbol.class);
        assertEquals(result.getMathType(), FAKE_TYPEGRAPH.BOOLEAN);

        // Make sure that the only quantified symbol is "a"
        assertEquals(result.getQuantifiedVariables(), Collections
                .singleton(PExp.buildPExp(FAKE_TYPEGRAPH, varExp)));
    }

}