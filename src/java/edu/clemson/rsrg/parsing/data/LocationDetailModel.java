/*
 * LocationDetailModel.java
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
package edu.clemson.rsrg.parsing.data;

import edu.clemson.rsrg.absyn.expressions.Exp;
import edu.clemson.rsrg.vcgeneration.VCGenerator;

/**
 * <p>
 * This class is an helper class that stores both source and destination {@link Location Locations} as well as the
 * associated message of where an {@link Exp} got generated by the {@link VCGenerator}.
 * </p>
 *
 * @author Yu-Shan Sun
 *
 * @version 1.0
 */
public class LocationDetailModel implements Cloneable {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /**
     * <p>
     * The destination {@link Location} where we want the detail message to be displayed at.
     * </p>
     */
    private final Location myDestLoc;

    /**
     * <p>
     * Message to be displayed by the {@link VCGenerator}.
     * </p>
     */
    private final String myDetailMessage;

    /**
     * <p>
     * The source {@link Location} from an {@link Exp}.
     * </p>
     */
    private final Location mySrcLoc;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>
     * This creates an object that stores the source and destination locations that generated the associated
     * {@link Exp}. The message is used by the {@link VCGenerator} for displaying purposes.
     * </p>
     *
     * @param srcLoc
     *            A source {@link Location}.
     * @param destLoc
     *            A destination {@link Location}.
     * @param message
     *            The mssage associated with the {@link Exp}.
     */
    public LocationDetailModel(Location srcLoc, Location destLoc, String message) {
        myDestLoc = destLoc;
        myDetailMessage = message;
        mySrcLoc = srcLoc;
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>
     * This method overrides the default clone method implementation for the {@link LocationDetailModel} class.
     * </p>
     *
     * @return A deep copy of the object.
     */
    @Override
    public final LocationDetailModel clone() {
        return new LocationDetailModel(mySrcLoc, myDestLoc, myDetailMessage);
    }

    /**
     * <p>
     * This method overrides the default {@code equals} method implementation.
     * </p>
     *
     * @param o
     *            Object to be compared.
     *
     * @return {@code true} if all the fields are equal, {@code false} otherwise.
     */
    @Override
    public final boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        LocationDetailModel that = (LocationDetailModel) o;

        return myDestLoc.equals(that.myDestLoc) && myDetailMessage.equals(that.myDetailMessage)
                && mySrcLoc.equals(that.mySrcLoc);
    }

    /**
     * <p>
     * This method returns the location to be displayed by the {@link VCGenerator}.
     * </p>
     *
     * @return A {@link Location}.
     */
    public final Location getDestinationLoc() {
        return myDestLoc;
    }

    /**
     * <p>
     * This method returns the message associated with the destination {@link Location}.
     * </p>
     *
     * @return A string.
     */
    public final String getDetailMessage() {
        return myDetailMessage;
    }

    /**
     * <p>
     * This method returns the source location where an {@link Exp} originated from.
     * </p>
     *
     * @return A {@link Location}.
     */
    public final Location getSourceLoc() {
        return mySrcLoc;
    }

    /**
     * <p>
     * This method overrides the default {@code hashCode} method implementation.
     * </p>
     *
     * @return The hash code associated with the object.
     */
    @Override
    public final int hashCode() {
        int result = myDestLoc.hashCode();
        result = 31 * result + myDetailMessage.hashCode();
        result = 31 * result + mySrcLoc.hashCode();
        return result;
    }

}
