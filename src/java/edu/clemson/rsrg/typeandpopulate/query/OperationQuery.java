/*
 * OperationQuery.java
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
package edu.clemson.rsrg.typeandpopulate.query;

import edu.clemson.rsrg.parsing.data.PosSymbol;
import edu.clemson.rsrg.typeandpopulate.entry.OperationEntry;
import edu.clemson.rsrg.typeandpopulate.programtypes.PTType;
import edu.clemson.rsrg.typeandpopulate.query.searcher.OperationSearcher;
import edu.clemson.rsrg.typeandpopulate.query.searchpath.PossiblyQualifiedPath;
import edu.clemson.rsrg.typeandpopulate.symboltables.MathSymbolTable.FacilityStrategy;
import edu.clemson.rsrg.typeandpopulate.symboltables.MathSymbolTable.ImportStrategy;
import java.util.List;

/**
 * <p>
 * An <code>OperationQuery</code> searched for a (possibly-qualified) operation. If a qualifier is provided, the named
 * facility or module is searched. Otherwise, the operation is searched for in any directly imported modules and in
 * instantiated versions of any available facilities.
 * </p>
 *
 * @version 2.0
 */
public class OperationQuery extends BaseSymbolQuery<OperationEntry> {

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>
     * This query searches for an operation entry that matches the provided arguments.
     * </p>
     *
     * @param qualifier
     *            A qualifier symbol that indicates the instantiating facility or module.
     * @param name
     *            An operation name to query for.
     * @param argumentTypes
     *            The list of program types for this operation.
     */
    public OperationQuery(PosSymbol qualifier, PosSymbol name, List<PTType> argumentTypes) {
        this(qualifier, name, argumentTypes, ImportStrategy.IMPORT_NAMED, FacilityStrategy.FACILITY_INSTANTIATE);
    }

    /**
     * <p>
     * This query searches for an operation entry that matches the provided arguments.
     * </p>
     *
     * @param qualifier
     *            A qualifier symbol that indicates the instantiating facility or module.
     * @param name
     *            An operation name to query for.
     * @param argumentTypes
     *            The list of program types for this operation.
     * @param importStrategy
     *            The import strategy to use.
     * @param facilityStrategy
     *            The facility strategy to use.
     */
    public OperationQuery(PosSymbol qualifier, PosSymbol name, List<PTType> argumentTypes,
            ImportStrategy importStrategy, FacilityStrategy facilityStrategy) {
        super(new PossiblyQualifiedPath(qualifier, importStrategy, facilityStrategy, false),
                new OperationSearcher(name, argumentTypes));
    }

}
