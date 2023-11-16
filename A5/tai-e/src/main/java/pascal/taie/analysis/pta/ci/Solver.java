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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import soot.jimple.Stmt;

import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

class Solver {
    private Pointer ouerForinvokeProcess;
    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtVisitor<Void> stmtProcessor;

    private StmtVisitor<Void> stmtProcessorForAddRreachable;
    private ClassHierarchy hierarchy;

    private PointsToSet nowDiffObjs;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        stmtProcessorForAddRreachable=new StmtProcessorForAddRreachable();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     * 处理静态字段 loads/stores 和静态方法调用 assign new
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)){
            //不是抽象方法
            if (callGraph.addReachableMethod(method)){
                method.getIR().getStmts().forEach(stmt -> {
                    stmt.accept(stmtProcessorForAddRreachable);
                });
            }
        }


    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor extends StmtProcessorForAddRreachable {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            return null;
        }
        //x=y
        @Override
        public Void visit(Copy stmt) {
            return null;
        }
        @Override
        public Void visit(LoadArray stmt) {
            nowDiffObjs.forEach(obj -> {
                Pointer target=pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer source=pointerFlowGraph.getArrayIndex(obj);
                addPFGEdge(source,target);
            });
            return null;
        }
        //x[*]=y
        @Override
        public Void visit(StoreArray stmt) {
            //使用定义的全局差集
            nowDiffObjs.forEach(obj -> {
                Pointer source=pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer target=pointerFlowGraph.getArrayIndex(obj);
                addPFGEdge(source,target);
            });
            return null;
        }
        //y=x.f
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic())
                return null;
            //使用定义的全局差集
            nowDiffObjs.forEach(obj -> {
                Pointer target=pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer source=pointerFlowGraph.getInstanceField(obj,stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
            });
            return null;
        }

        //x.f=y
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic())
                return null;
            //使用定义的全局差集
            nowDiffObjs.forEach(obj -> {
                Pointer source=pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer target=pointerFlowGraph.getInstanceField(obj,stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
            });
            return null;
        }
        //l:r=x.k(a);
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
                return null;
            nowDiffObjs.forEach(obj -> {
                JMethod jMethod=resolveCallee(obj,stmt);
                Pointer thisPoint=pointerFlowGraph.getVarPtr(jMethod.getIR().getThis());
                addPFGEdge(ouerForinvokeProcess,thisPoint);
                //是否已经加入该方法
                if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),stmt,jMethod))){
                    //加入到可达集（方法加入可达集;处理assign new;扩展S集）
                    addReachable(jMethod);
                    //扩大PFG
                    //处理传参 l:r=x.m(a1,a2)
                    AtomicInteger atomicInteger=new AtomicInteger(0);
                    stmt.getInvokeExp().getArgs().forEach(arg->{
                        Pointer source=pointerFlowGraph.getVarPtr(arg);
                        Var calleePara=jMethod.getIR().getParam(atomicInteger.getAndIncrement());
                        Pointer target=pointerFlowGraph.getVarPtr(calleePara);
                        addPFGEdge(source,target);
                    });
                    //处理返回  l:r=x.m()
                    Var receiver=stmt.getLValue();
                    if(receiver!=null){
                    jMethod.getIR().getReturnVars().forEach(var -> {
                        Pointer target=pointerFlowGraph.getVarPtr(receiver);
                        Pointer source=pointerFlowGraph.getVarPtr(var);
                        addPFGEdge(source,target);
                    });}
                }

            });
            return null;
        }
    }

    private class StmtProcessorForAddRreachable implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Var v = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(obj));
            return null;
        }
        //x=y
        @Override
        public Void visit(Copy stmt) {
            Pointer source=pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer target=pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source,target);
            return null;
        }

        //y=X.f
        @Override
        public Void visit(LoadField stmt) {
            //y=X.f
            if (stmt.isStatic()){
                Pointer target=pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer source=pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
                return null;
            }
            return null;
        }

        //X.f=y
        @Override
        public Void visit(StoreField stmt) {
            //X.f=y
            if (stmt.isStatic()){
                Pointer source=pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer target=pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
                return null;
            }
            return null;
        }
        // l:r=X.k;
        @Override
        public Void visit(Invoke stmt) {
            //静态方法
            if (stmt.isStatic()){
                {
                    JMethod jMethod=stmt.getMethodRef().resolve();
                    //是否已经加入该方法
                    if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),stmt,jMethod))){
                        //加入到可达集（方法加入可达集;处理assign new;扩展S集）
                        addReachable(jMethod);
                        //扩大PFG
                        //处理传参
                        AtomicInteger atomicInteger=new AtomicInteger(0);
                        stmt.getInvokeExp().getArgs().forEach(arg->{
                            Pointer source=pointerFlowGraph.getVarPtr(arg);
                            Var calleeArg=jMethod.getIR().getParam(atomicInteger.getAndIncrement());
                            Pointer target=pointerFlowGraph.getVarPtr(calleeArg);
                            addPFGEdge(source,target);
                        });
                        //处理返回  l:r=x.m(a1,a2)
                        Var receiver=stmt.getLValue();
                        if (receiver!=null)
                        jMethod.getIR().getReturnVars().forEach(var -> {
                            Pointer target=pointerFlowGraph.getVarPtr(receiver);
                            Pointer source=pointerFlowGraph.getVarPtr(var);
                            addPFGEdge(source,target);
                        });
                    }

                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source,target)){
            if (!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()){
           WorkList.Entry entry= workList.pollEntry();
           Pointer p=entry.pointer();
           propagate(p,entry.pointsToSet());
           if (p instanceof VarPtr){
               ((VarPtr) p).getVar().getLoadArrays().forEach(stmt->{stmt.accept(stmtProcessor);});
               ((VarPtr) p).getVar().getStoreFields().forEach(stmt->{stmt.accept(stmtProcessor);});
               ((VarPtr) p).getVar().getLoadFields().forEach(stmt->{stmt.accept(stmtProcessor);});
               ((VarPtr) p).getVar().getStoreArrays().forEach(stmt->{stmt.accept(stmtProcessor);});
               ouerForinvokeProcess=p;
               ((VarPtr) p).getVar().getInvokes().forEach(stmt->{stmt.accept(stmtProcessor);});
           }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    //传入的不是差集
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        nowDiffObjs=resolveDiffSet(pointsToSet,pointer.getPointsToSet());
        if (!nowDiffObjs.isEmpty()){
        unionSet(nowDiffObjs,pointer.getPointsToSet());
        //求传递闭包
        pointerFlowGraph.getSuccsOf(pointer).forEach(succPoint->{
            workList.addEntry(succPoint,nowDiffObjs);
        });}
        return nowDiffObjs;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }

    private PointsToSet resolveDiffSet(PointsToSet minuend,PointsToSet sub){
            Stream<Obj> diffObjs=minuend.objects().filter(obj -> !(sub.contains(obj)));
            PointsToSet diffSet=new PointsToSet();
            diffObjs.forEach(diffSet::addObject);
            return diffSet;
    }

    /*set2+=set1*/
    private void unionSet(PointsToSet set1,PointsToSet set2){
        set1.forEach(set2::addObject);
    }

}
