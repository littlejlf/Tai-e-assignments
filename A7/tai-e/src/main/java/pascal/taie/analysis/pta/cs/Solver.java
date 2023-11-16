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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private PointsToSet nowDiffObjs;
    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;


    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod)){
            //不是抽象方法
            if (callGraph.addReachableMethod(csMethod)){
                csMethod.getMethod().getIR().getStmts().forEach(stmt -> {
                    stmt.accept(new StmtProcessorForAddReachable(csMethod));
                });
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessorForAddReachable implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessorForAddReachable(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        //x=new A();
        @Override
        public Void visit(New stmt) {
            Pointer pointer= csManager.getCSVar(context,stmt.getLValue());
            Obj obj= heapModel.getObj(stmt);
            CSObj csObj=csManager.getCSObj(contextSelector.selectHeapContext(csMethod,obj), obj);
            PointsToSet pointsToSet=PointsToSetFactory.make(csObj);
            workList.addEntry(pointer,pointsToSet );
            return StmtVisitor.super.visit(stmt);
        }
        //y=x
        @Override
        public Void visit(Copy stmt) {
            Pointer source= csManager.getCSVar(context,stmt.getRValue());
            Pointer target= csManager.getCSVar(context,stmt.getLValue());
            addPFGEdge(source,target);
            return StmtVisitor.super.visit(stmt);
        }

        //y=X.m(a1,a2)
        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic())
            return StmtVisitor.super.visit(stmt);
            //获取method 以及上下文
            JMethod method=stmt.getMethodRef().resolve();
            CSCallSite csCallSite=csManager.getCSCallSite(context,stmt);
            Context methodContext= contextSelector.selectContext(csCallSite,method);
            //加入可达集以及CG
            CSMethod csMethod=csManager.getCSMethod(methodContext,method);
            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),csCallSite,csMethod));
            addReachable(csManager.getCSMethod(methodContext,method));
            //处理传参
            AtomicInteger integer=new AtomicInteger(0);
            method.getIR().getParams().forEach(para->{
                Pointer argPonit= csManager.getCSVar(context,stmt.getInvokeExp().getArg(integer.getAndIncrement()));
                Pointer paraPonit= csManager.getCSVar(methodContext,para);
                addPFGEdge(argPonit,paraPonit);
            });
            //处理返回值
            if(stmt.getLValue()!=null){
                    method.getIR().getReturnVars().forEach(var -> {
                        Pointer target=csManager.getCSVar(context,stmt.getLValue());
                        Pointer source=csManager.getCSVar(methodContext,var);
                        addPFGEdge(source,target);
                    });
            }
            return null;
        }
    }


    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        //y=x[*]
        @Override
        public Void visit(LoadArray stmt) {
            nowDiffObjs.forEach(csobj -> {
                Pointer target=csManager.getCSVar(context,stmt.getLValue());
                Pointer source=csManager.getArrayIndex(csobj);
                addPFGEdge(source,target);
            });
            return null;
        }
        //x[*]=y
        @Override
        public Void visit(StoreArray stmt) {
            //使用定义的全局差集
            nowDiffObjs.forEach(csobj -> {
                Pointer source=csManager.getCSVar(context,stmt.getRValue());
                Pointer target=csManager.getArrayIndex(csobj);
                addPFGEdge(source,target);
            });
            return null;
        }
        //y=x.f
        @Override
        public Void visit(LoadField stmt) {
            nowDiffObjs.forEach(csobj -> {
                Pointer target=csManager.getCSVar(context,stmt.getLValue());
                Pointer source=csManager.getInstanceField(csobj,stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
            });
            return null;
        }
        //x.f=y
        @Override
        public Void visit(StoreField stmt) {
            //使用定义的全局差集
            nowDiffObjs.forEach(csobj -> {
                Pointer source=csManager.getCSVar(context,stmt.getRValue());
                Pointer target=csManager.getInstanceField(csobj,stmt.getFieldRef().resolve());
                addPFGEdge(source,target);
            });
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
            return StmtVisitor.super.visit(stmt);
            //y=x.m(a)
            nowDiffObjs.forEach(csobj -> {
                //获取method 以及上下文
                JMethod method=resolveCallee(csobj,stmt);
                CSCallSite csCallSite=csManager.getCSCallSite(context,stmt);
                Context methodContext= contextSelector.selectContext(csCallSite,csobj,method);
                //加入可达集以及CG
                CSMethod csMethod=csManager.getCSMethod(methodContext,method);
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),csCallSite,csMethod));
                addReachable(csManager.getCSMethod(methodContext,method));
                //处理传参
                AtomicInteger integer=new AtomicInteger(0);
                method.getIR().getParams().forEach(para->{
                    Pointer argPonit= csManager.getCSVar(context,stmt.getInvokeExp().getArg(integer.getAndIncrement()));
                    Pointer paraPonit= csManager.getCSVar(methodContext,para);
                    addPFGEdge(argPonit,paraPonit);
                });
                //处理返回值
                if(stmt.getLValue()!=null){
                    method.getIR().getReturnVars().forEach(var -> {
                        Pointer target=csManager.getCSVar(context,stmt.getLValue());
                        Pointer source=csManager.getCSVar(methodContext,var);
                        addPFGEdge(source,target);
                    });
                }
                //处理this
                Pointer thisPoint=csManager.getCSVar(methodContext,method.getIR().getThis());
                InvokeExp invokeExp= stmt.getInvokeExp();
                //循环执行v同一行语句 var应该不变 上下文变了 pts的精度和上下文的敏感度有关 pts中的obj要看它head的敏感度
                Var base=((InvokeInstanceExp) invokeExp).getBase();
                addPFGEdge(csManager.getCSVar(context,base), thisPoint);
            });
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
            if (p instanceof CSVar){
                CSMethod csMethod=csManager.getCSMethod(((CSVar) p).getContext(),((CSVar) p).getVar().getMethod());
                StmtProcessor stmtProcessor= new StmtProcessor(csMethod);
                ((CSVar) p).getVar().getLoadArrays().forEach(stmt->{stmt.accept(stmtProcessor);});
                ((CSVar) p).getVar().getStoreFields().forEach(stmt->{stmt.accept(stmtProcessor);});
                ((CSVar) p).getVar().getLoadFields().forEach(stmt->{stmt.accept(stmtProcessor);});
                ((CSVar) p).getVar().getStoreArrays().forEach(stmt->{stmt.accept(stmtProcessor);});
                ((CSVar) p).getVar().getInvokes().forEach(stmt->{stmt.accept(stmtProcessor);});
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        nowDiffObjs=resolveDiffSet(pointsToSet,pointer.getPointsToSet());
        if (!nowDiffObjs.isEmpty()){
            unionSet(nowDiffObjs,pointer.getPointsToSet());
            //求由x出发的传递闭包
            pointerFlowGraph.getSuccsOf(pointer).forEach(succPoint->{
                workList.addEntry(succPoint,nowDiffObjs);
            });}
        return nowDiffObjs;

    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
    private PointsToSet resolveDiffSet(PointsToSet minuend,PointsToSet sub){
        Stream<CSObj> diffObjs=minuend.objects().filter(obj -> !(sub.contains(obj)));
        PointsToSet diffSet=PointsToSetFactory.make();
        diffObjs.forEach(diffSet::addObject);
        return diffSet;
    }

    /*set2+=set1*/
    private void unionSet(PointsToSet set1,PointsToSet set2){
        set1.forEach(set2::addObject);
    }





}
