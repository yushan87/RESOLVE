/*
 * ModuleDec.java
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
package edu.clemson.rsrg.absyn.declarations.moduledecl;

import edu.clemson.rsrg.absyn.declarations.mathdecl.MathDefinitionDec;
import edu.clemson.rsrg.absyn.declarations.Dec;
import edu.clemson.rsrg.absyn.declarations.paramdecl.ModuleParameterDec;
import edu.clemson.rsrg.absyn.items.programitems.UsesItem;
import edu.clemson.rsrg.init.file.ResolveFileBasicInfo;
import edu.clemson.rsrg.parsing.data.Location;
import edu.clemson.rsrg.parsing.data.PosSymbol;
import edu.clemson.rsrg.statushandling.exception.MiscErrorException;
import java.util.*;

/**
 * <p>
 * This is the abstract base class for all the module declaration objects that the compiler builds using the ANTLR4 AST
 * nodes.
 * </p>
 *
 * @version 2.0
 */
public abstract class ModuleDec extends Dec {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /**
     * <p>
     * The current module's parameter declaration objects.
     * </p>
     */
    protected final List<ModuleParameterDec> myParameterDecs;

    /**
     * <p>
     * The current module's import objects.
     * </p>
     */
    protected final List<UsesItem> myUsesItems;

    /**
     * <p>
     * The current module's declaration objects.
     * </p>
     */
    protected final List<Dec> myDecs;

    /**
     * <p>
     * The current module's import objects.
     * </p>
     */
    protected final Map<ResolveFileBasicInfo, Boolean> myModuleDependencies;

    // ===========================================================
    // Constructor
    // ===========================================================

    /**
     * <p>
     * A helper constructor that allow us to store common member fields for objects created from a class that inherits
     * from {@code ModuleDec}.
     * </p>
     *
     * @param l
     *            A {@link Location} representation object.
     * @param name
     *            The name in {@link PosSymbol} format.
     * @param parameterDecs
     *            The list of {@link ModuleParameterDec} objects.
     * @param usesItems
     *            The list of {@link UsesItem} objects.
     * @param decs
     *            The list of {@link Dec} objects.
     * @param moduleDependencies
     *            A map of {@link ResolveFileBasicInfo} to externally realized flags that indicates all the modules that
     *            this module declaration depends on.
     */
    protected ModuleDec(Location l, PosSymbol name, List<ModuleParameterDec> parameterDecs, List<UsesItem> usesItems,
            List<Dec> decs, Map<ResolveFileBasicInfo, Boolean> moduleDependencies) {
        super(l, name);
        myParameterDecs = parameterDecs;
        myUsesItems = usesItems;
        myDecs = decs;
        myModuleDependencies = moduleDependencies;
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        if (!super.equals(o))
            return false;

        ModuleDec moduleDec = (ModuleDec) o;

        if (!myDecs.equals(moduleDec.myDecs))
            return false;
        if (!myParameterDecs.equals(moduleDec.myParameterDecs))
            return false;
        if (!myUsesItems.equals(moduleDec.myUsesItems))
            return false;
        return myModuleDependencies.equals(moduleDec.myModuleDependencies);
    }

    /**
     * <p>
     * This method gets all the object declarations associated with this module.
     * </p>
     *
     * @return A list of {@link Dec} objects.
     */
    public final List<Dec> getDecList() {
        return myDecs;
    }

    /**
     * <p>
     * This method returns all modules dependencies associated with this module.
     * </p>
     *
     * @return A list of {@link Dec} objects.
     */
    public final Map<ResolveFileBasicInfo, Boolean> getModuleDependencies() {
        return myModuleDependencies;
    }

    /**
     * <p>
     * This method gets all the object parameter declarations associated with this module.
     * </p>
     *
     * @return A list of {@link ModuleParameterDec} objects.
     */
    public final List<ModuleParameterDec> getParameterDecs() {
        return myParameterDecs;
    }

    /**
     * <p>
     * This method gets all the import objects associated with this module.
     * </p>
     *
     * @return A list of {@link UsesItem} objects.
     */
    public final List<UsesItem> getUsesItems() {
        return myUsesItems;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + myDecs.hashCode();
        result = 31 * result + myParameterDecs.hashCode();
        result = 31 * result + myUsesItems.hashCode();
        result = 31 * result + myModuleDependencies.hashCode();
        return result;
    }

    // ===========================================================
    // Protected Methods
    // ===========================================================

    /**
     * <p>
     * Implemented by concrete subclasses of {@link ModuleDec} to manufacture a copy of themselves.
     * </p>
     *
     * @return A new {@link ModuleDec} that is a deep copy of the original.
     */
    protected ModuleDec copy() {
        throw new MiscErrorException("Shouldn't be calling copy()!  Type: " + this.getClass(),
                new CloneNotSupportedException());
    }

    /**
     * <p>
     * An helper method that deep copies all the module dependencies.
     * </p>
     *
     * @return A new module dependencies map.
     */
    protected final Map<ResolveFileBasicInfo, Boolean> copyModuleDependencies() {
        Map<ResolveFileBasicInfo, Boolean> newModuleDependencies = new LinkedHashMap<>(myModuleDependencies.size());
        for (ResolveFileBasicInfo fileBasicInfo : myModuleDependencies.keySet()) {
            newModuleDependencies.put(
                    new ResolveFileBasicInfo(fileBasicInfo.getName(), fileBasicInfo.getParentDirName()),
                    myModuleDependencies.get(fileBasicInfo));
        }

        return newModuleDependencies;
    }

    /**
     * <p>
     * A helper method to form the string with the declaration list and the end of module.
     * </p>
     *
     * @param indentSize
     *            The base indentation to the first line of the text.
     * @param innerIndentInc
     *            The additional indentation increment for the subsequent lines.
     *
     * @return A formatted text string.
     */
    protected final String formDecEnd(int indentSize, int innerIndentInc) {
        StringBuffer sb = new StringBuffer();
        for (Dec d : myDecs) {
            sb.append(d.asString(indentSize + innerIndentInc, innerIndentInc));
            sb.append("\n\n");
        }
        sb.append("end ");
        sb.append(myName.asString(0, innerIndentInc));
        sb.append(";");

        return sb.toString();
    }

    /**
     * <p>
     * A helper method to form the string with the module's name and args.
     * </p>
     *
     * @param indentSize
     *            The base indentation to the first line of the text.
     * @param innerIndentInc
     *            The additional indentation increment for the subsequent lines.
     *
     * @return A formatted text string.
     */
    protected final String formNameArgs(int indentSize, int innerIndentInc) {
        StringBuffer sb = new StringBuffer();
        sb.append(myName.asString(indentSize, innerIndentInc));

        if (myParameterDecs.size() > 0) {
            sb.append("( ");
            Iterator<ModuleParameterDec> it = myParameterDecs.iterator();
            while (it.hasNext()) {
                ModuleParameterDec m = it.next();
                sb.append(m.asString(indentSize, innerIndentInc));

                if (it.hasNext()) {
                    if (!(m.getWrappedDec() instanceof MathDefinitionDec)) {
                        sb.append(";");
                    }
                    sb.append(" ");
                }
            }
            sb.append("\n )");
        }

        return sb.toString();
    }

    /**
     * <p>
     * A helper method to form the string with the module's uses items.
     * </p>
     *
     * @param indentSize
     *            The base indentation to the first line of the text.
     * @param innerIndentInc
     *            The additional indentation increment for the subsequent lines.
     *
     * @return A formatted text string.
     */
    protected final String formUses(int indentSize, int innerIndentInc) {
        StringBuffer sb = new StringBuffer();

        if (myUsesItems.size() > 0) {
            printSpace(indentSize + innerIndentInc, sb);
            sb.append("uses ");
            Iterator<UsesItem> it = myUsesItems.iterator();
            while (it.hasNext()) {
                UsesItem u = it.next();
                sb.append(u.asString(0, innerIndentInc));

                if (it.hasNext()) {
                    sb.append(", ");
                }
            }
            sb.append(";\n");
        }

        return sb.toString();
    }

}
