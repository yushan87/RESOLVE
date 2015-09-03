/**
 * PLambda.java
 * ---------------------------------
 * Copyright (c) 2015
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.r2jt.rewriteprover.absyn;

import edu.clemson.cs.r2jt.rewriteprover.immutableadts.ArrayBackedImmutableList;
import edu.clemson.cs.r2jt.rewriteprover.immutableadts.ImmutableList;
import edu.clemson.cs.r2jt.rewriteprover.immutableadts.SingletonImmutableList;
import edu.clemson.cs.r2jt.typeandpopulate.MTFunction;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;

import java.lang.reflect.Array;
import java.util.*;

public class PLambda extends PExp {

    public final ImmutableList<Parameter> parameters;
    private final PExp myBody;
    private static int f_num = 0;

    public PLambda(ImmutableList<Parameter> parameters, PExp body) {
        super(body.structureHash * 34, parameterHash(parameters),
                new MTFunction(body.getType().getTypeGraph(), body.getType(),
                        parameterTypes(parameters)), null);

        this.parameters = parameters;
        myBody = body;
    }

    private static List<MTType> parameterTypes(Iterable<Parameter> parameters) {
        List<MTType> result = new LinkedList<MTType>();

        for (Parameter p : parameters) {
            result.add(p.type);
        }

        return result;
    }

    public PExp getBody() {
        return myBody;
    }

    public List<PExp> getParameters() {
        ArrayList<PExp> rList = new ArrayList<PExp>();
        for (Parameter p : parameters) {
            rList.add(new PSymbol(p.type, null, p.name,
                    PSymbol.Quantification.FOR_ALL));
        }
        return rList;
    }

    private static int parameterHash(Iterable<Parameter> parameters) {
        int hash = 0;

        for (Parameter p : parameters) {
            if (p.name == null) {
                throw new IllegalArgumentException("Null parameter name.");
            }
            else if (p.type == null) {
                throw new IllegalArgumentException("Null parameter type.");
            }

            hash += p.name.hashCode() * 27 + p.type.hashCode();
            hash *= 49;
        }

        return hash;
    }

    @Override
    public void accept(PExpVisitor v) {
        v.beginPExp(this);
        v.beginPLambda(this);

        v.beginChildren(this);
        myBody.accept(v);
        v.endChildren(this);

        v.endPLambda(this);
        v.endPExp(this);
    }

    @Override
    public PLambda withTypeReplaced(MTType t) {
        throw new UnsupportedOperationException("Cannot set the type "
                + "value on a " + this.getClass() + ".");
    }

    @Override
    public PLambda withTypeValueReplaced(MTType t) {
        throw new UnsupportedOperationException("Cannot set the type "
                + "value on a " + this.getClass() + ".");
    }

    @Override
    public PLambda withSubExpressionReplaced(int i, PExp e) {
        if (i != 0) {
            throw new IndexOutOfBoundsException("" + i);
        }

        return new PLambda(parameters, e);
    }

    @Override
    public ImmutableList<PExp> getSubExpressions() {
        return new SingletonImmutableList<PExp>(myBody);
    }

    @Override
    public PExpSubexpressionIterator getSubExpressionIterator() {
        return new PLambdaBodyIterator();
    }

    @Override
    public boolean isObviouslyTrue() {
        return myBody.isObviouslyTrue();
    }

    @Override
    public String toSMTLIB(Map<String, MTType> typeMap) {
        return null;
    }

    @Override
    protected void splitIntoConjuncts(List<PExp> accumulator) {
        accumulator.add(this);
    }

    @Override
    public PExp flipQuantifiers() {
        return this;
    }

    @Override
    public String getTopLevelOperation() {
        return "lambda";
    }

    @Override
    public void bindTo(PExp target, Map<PExp, PExp> accumulator)
            throws BindingException {

        if (!(target instanceof PLambda) || !typeMatches(target)) {
            throw BINDING_EXCEPTION;
        }

        PLambda targetAsPLambda = (PLambda) target;

        targetAsPLambda = (PLambda) targetAsPLambda.substitute(accumulator);

        myBody.bindTo(targetAsPLambda.myBody, accumulator);
    }

    @Override
    public PExp substitute(Map<PExp, PExp> substitutions) {
        PExp retval;

        if (substitutions.containsKey(this)) {
            retval = substitutions.get(this);
        }
        else {

            // make new parameters if substitutions contains type variables

            retval = new PLambda(parameters, myBody.substitute(substitutions));
        }

        return retval;
    }

    @Override
    public boolean containsName(String name) {
        boolean result = false;
        Iterator<Parameter> parameterIter = parameters.iterator();
        while (!result && parameterIter.hasNext()) {
            result = parameterIter.next().name.equals(name);
        }
        return result || myBody.containsName(name);
    }

    @Override
    public Set<String> getSymbolNamesNoCache() {
        Set<String> bodyNames = new HashSet<String>(myBody.getSymbolNames());

        bodyNames.add("lambda");

        return bodyNames;
    }

    @Override
    public Set<PSymbol> getQuantifiedVariablesNoCache() {
        return myBody.getQuantifiedVariables();
    }

    @Override
    public List<PExp> getFunctionApplicationsNoCache() {
        List<PExp> bodyFunctions =
                new LinkedList<PExp>(myBody.getFunctionApplications());

        bodyFunctions.add(new PSymbol(getType(), null, "lambda"));

        return bodyFunctions;
    }

    @Override
    public boolean containsExistential() {
        return myBody.containsExistential();
    }

    @Override
    public boolean isEquality() {
        return false;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    public String toSMTLIB() {
        return "not implemented";
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    private class PLambdaBodyIterator implements PExpSubexpressionIterator {

        private boolean myReturnedBodyFlag = false;

        @Override
        public boolean hasNext() {
            return !myReturnedBodyFlag;
        }

        @Override
        public PExp next() {
            if (myReturnedBodyFlag) {
                throw new NoSuchElementException();
            }

            return myBody;
        }

        @Override
        public PExp replaceLast(PExp newExpression) {
            return new PLambda(parameters, myBody);
        }

    }

    public PLambda withNormalizedParameterNames() {
        List<PExp> plist = getParameters();
        HashMap<PExp, PExp> substMap = new HashMap<PExp, PExp>();
        int argNum = 0;
        ArrayList<Parameter> normParams = new ArrayList<Parameter>();
        for (PExp p : plist) {
            String name = p.getType().toString().toLowerCase() + argNum++;
            PExp norm =
                    new PSymbol(p.getType(), p.getTypeValue(), name,
                            PSymbol.Quantification.FOR_ALL);
            substMap.put(p, norm);
            normParams.add(new Parameter(name, p.getType()));
        }
        return new PLambda(new ArrayBackedImmutableList<Parameter>(normParams),
                myBody.substitute(substMap));
    }

    public static class Parameter {

        public final String name;
        public final MTType type;

        public Parameter(String name, MTType type) {
            if (name == null) {
                throw new IllegalArgumentException("Parameter name is null");
            }

            if (type == null) {
                throw new IllegalArgumentException("Parameter type is null");
            }

            this.name = name;
            this.type = type;
        }

        @Override
        public String toString() {
            return name + " : " + type;
        }

    }
}
