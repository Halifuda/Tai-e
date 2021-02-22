/*
 * Tai-e: A Program Analysis Framework for Java
 *
 * Copyright (C) 2020 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020 Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * This software is designed for the "Static Program Analysis" course at
 * Nanjing University, and it supports a subset of Java features.
 * Tai-e is only for educational and academic purposes, and any form of
 * commercial use is disallowed.
 */

package pascal.taie.pta.ir;

import pascal.taie.java.classes.JMethod;
import pascal.taie.java.types.Type;
import pascal.taie.util.HashUtils;
import soot.jimple.AssignStmt;

import java.util.Optional;

public class NormalObj extends AbstractObj {

    private final AssignStmt allocation;

    private final JMethod containerMethod;

    NormalObj(AssignStmt allocation, Type type, JMethod containerMethod) {
        super(type);
        this.allocation = allocation;
        this.containerMethod = containerMethod;
    }

    @Override
    public Kind getKind() {
        return Kind.NORMAL;
    }

    @Override
    public AssignStmt getAllocation() {
        return allocation;
    }

    @Override
    public Optional<JMethod> getContainerMethod() {
        return Optional.of(containerMethod);
    }

    @Override
    public Type getContainerType() {
        return containerMethod.getDeclaringClass().getType();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        NormalObj obj = (NormalObj) o;
        return allocation.equals(obj.allocation)
                && type.equals(obj.type);
    }

    @Override
    public int hashCode() {
        return HashUtils.hash(allocation, type);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (containerMethod != null) {
            sb.append(containerMethod).append('/');
        }
        sb.append("new ")
                .append(type)
                .append('/')
                .append(allocation.getJavaSourceStartLineNumber());
        return sb.toString();
    }
}
