/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.*;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        List<JMethod> worklist= new ArrayList<>();
        List<JMethod> rm=new ArrayList<>();
        worklist.add(entry);
        callGraph.addReachableMethod(entry);
        while (!worklist.isEmpty()){
            if (!rm.contains(worklist.get(0))){
                rm.add(worklist.get(0));
                List<Stmt> list=  worklist.get(0).getIR().getStmts().stream().filter(stmt -> stmt instanceof Invoke).toList();
                list.forEach(invoke -> {
                    Set<JMethod> methods=resolve((Invoke) invoke);
                    methods.forEach(method->{
                        if (method!=null){
                        callGraph.addEdge( new Edge(CallGraphs.getCallKind((Invoke) invoke),invoke,method));
                        worklist.add(method);
                        callGraph.addReachableMethod(method);}
                    });
                });
            }
            worklist.remove(0);

        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methods= new HashSet<>();
        Subsignature methodSubsignature=callSite.getMethodRef().getSubsignature();
        JClass jClass=callSite.getMethodRef().getDeclaringClass();
        CallKind kind=CallGraphs.getCallKind(callSite);
        if (kind.equals(CallKind.STATIC)){
                methods.add(jClass.getDeclaredMethod(methodSubsignature));
        }
        if (kind.equals(CallKind.SPECIAL)){
               methods.add(dispatch(jClass,methodSubsignature));
        }
        if (kind.equals(CallKind.VIRTUAL)||kind.equals(CallKind.INTERFACE)){
            JClass nowClass=jClass;
            List<JClass> worklist=new ArrayList();
            worklist.add(nowClass);
            while (!worklist.isEmpty()){
                if (nowClass.isInterface()){
                    worklist.addAll(hierarchy.getDirectImplementorsOf(nowClass));
                }
                else {
                    methods.add(dispatch(nowClass,methodSubsignature));
                    worklist.addAll(hierarchy.getDirectSubclassesOf(nowClass));
                }
                worklist.remove(0);
                if (!worklist.isEmpty())
                nowClass=worklist.get(0);
            }
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
       JMethod method=jclass.getDeclaredMethod(subsignature);
       if (method!=null&&!method.isAbstract()){
           return method;
       }
       else {
           JClass superClass=jclass.getSuperClass();
           if (superClass==null)
               return null;
           return dispatch(superClass,subsignature);
       }
    }
}
