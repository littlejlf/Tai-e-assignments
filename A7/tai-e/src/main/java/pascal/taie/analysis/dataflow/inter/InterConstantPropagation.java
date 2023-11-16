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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {
    private Map<Obj,List<Pointer>> objToPoints;
    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<LoadField,List<StoreField>> loadFieldToStores=new HashMap<>();
    private Map<StoreField,List<LoadField>> storeFieldToLoads=new HashMap<>();
    private Map<LoadArray,List<StoreArray>> loadArrayToStores=new HashMap<>();
    private Map<StoreArray,List<LoadArray>> storeArrayToLoads=new HashMap<>();
    private List<LoadField> allLoadFields= new ArrayList<>();

    private List<StoreField> allStoreFields= new ArrayList<>();

    private List<LoadArray> allLoadArrays= new ArrayList<>();

    private List<StoreArray> allStoreArrays= new ArrayList<>();
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }
    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        objToPoints=new HashMap<>();
        //初始化
        for(Stmt stmt:icfg){
            if ( stmt instanceof LoadField loadField){
                loadFieldToStores.put(loadField,new ArrayList<>());
                allLoadFields.add(loadField);
            }
            else if (stmt instanceof StoreField storeField ){
                storeFieldToLoads.put(storeField,new ArrayList<>());
                allStoreFields.add(storeField);
            }
            else if ( stmt instanceof LoadArray loadArray){
                loadArrayToStores.put(loadArray,new ArrayList<>());
                allLoadArrays.add(loadArray);
            }
            else if (stmt instanceof StoreArray storeArray ){
                storeArrayToLoads.put(storeArray,new ArrayList<>());
                allStoreArrays.add(storeArray);
            }
        }
        //遍历填充
        for(StoreField storeField:allStoreFields){
            //X.f=y
            if (storeField.isStatic()){
                //filered 还是fieldAccess
                JField sfield=storeField.getFieldAccess().getFieldRef().resolve();
                for (LoadField loadField:allLoadFields) {
                    if (loadField.getFieldAccess().getFieldRef().resolve().equals(sfield)){
                        loadFieldToStores.get(loadField).add(storeField);
                        storeFieldToLoads.get(storeField).add(loadField);
                    }
                }
            }
            else {
                for (LoadField loadField:allLoadFields) {
                if (isAlis(pta,loadField,storeField)){
                    loadFieldToStores.get(loadField).add(storeField);
                    storeFieldToLoads.get(storeField).add(loadField);
                }
            }
            }
        }
        if (solver==null){
            System.out.printf("cmd");
        }
        for(StoreArray storeArray:allStoreArrays){
            for (LoadArray loadArray:allLoadArrays) {
                if (isAlis(pta,loadArray,storeArray)){
                    loadArrayToStores.get(loadArray).add(storeArray);
                    storeArrayToLoads.get(storeArray).add(loadArray);
                }
            }
        }
        System.out.printf("d");
    }
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof Invoke)
            return this.transferCallNode(stmt,in,out);
        return this.transferNonCallNode(stmt,in,out);
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact outOrigin = out.copy();
        out.clear();
        for (Var v : in.keySet()) {
            out.update(v, in.get(v));
        }
        return !outOrigin.equals(out);

    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish
        CPFact oldCF=out.copy();
        out.clear();
        for (Var v : in.keySet()) {
            out.update(v, in.get(v));
        }
        if (stmt instanceof LoadField loadField){
            Value value=Value.getUndef();
            if (ConstantPropagation.canHoldInt(loadField.getLValue())){
           for( StoreField storeField:loadFieldToStores.get(loadField)){
               //从store语句的fact得出而不是原本的fact得出更准确 IN还是out
              value=cp.meetValue(solver.getOutFact(storeField).get(storeField.getRValue()),value);
           }
           out.update(loadField.getLValue(),value);}
        }
        else if(stmt instanceof StoreField storeField&&!oldCF.equals(out)){
            //刷新相关load 但是可能只能影响store以下的句子这样好像更加精确
            solver.addNodeToWorkList(storeField);
        }
        else if (stmt instanceof LoadArray loadArray){
            Value value=Value.getUndef();
            if (ConstantPropagation.canHoldInt(loadArray.getLValue())){
                for( StoreArray storeField:loadArrayToStores.get(loadArray)){
                //从store语句的fact得出而不是原本的fact得出更准确 IN还是out
                value=cp.meetValue(solver.getInFact(storeField).get(storeField.getRValue()),value);
            }
            out.update(loadArray.getLValue(),value);
        }}
        else if(stmt instanceof StoreArray storeArray){
            //刷新相关load 但是可能只能影响store以下的句子这样好像更加精确
            solver.addNodeToWorkList(storeArray);
        }
        else if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue lv = definitionStmt.getLValue();
            RValue rv = definitionStmt.getRValue();

            if (lv instanceof Var && ConstantPropagation.canHoldInt((Var)lv)) {
                Value val = ConstantPropagation.evaluate(rv, in);
                out.update((Var)lv, val);
            }
        }

        return !out.equals(oldCF);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact cpFact=out.copy();
        Optional<LValue> optional=edge.getSource().getDef();
        if(optional.isPresent()&&optional.get()instanceof Var&& ConstantPropagation.canHoldInt((Var) optional.get()))
            cpFact.update((Var) optional.get(), Value.getUndef());
        return cpFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact cpFact=new CPFact();
        Invoke invoke=(Invoke) edge.getSource();
        JMethod method=edge.getCallee();
        List<Var> args=invoke.getInvokeExp().getArgs();
        AtomicInteger atomicInteger= new AtomicInteger(0);
        args.forEach(arg->{
            cpFact.update(method.getIR().getParam(atomicInteger.getAndIncrement()),callSiteOut.get(arg));
        });
        return cpFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact calleeOutFact = new CPFact();

        Stmt callSiteStmt = edge.getCallSite();
        if (callSiteStmt instanceof DefinitionStmt<?,?>) {
            LValue lv = ((DefinitionStmt<?, ?>) callSiteStmt).getLValue();
            if (lv instanceof Var returnVar && ConstantPropagation.canHoldInt((Var) lv)) {
                Value returnValue = Value.getUndef();

                for (Var rv : edge.getReturnVars()) {
                    returnValue = cp.meetValue(returnValue, returnOut.get(rv));
                }
                calleeOutFact.update(returnVar, returnValue);
            }
        }

        return calleeOutFact;
    }




/*    protected Value  resolveAlisForInstanceField(){
        List<Pointer> alis=new ArrayList<>();

    }*/
protected boolean isAlis(PointerAnalysisResult pta,LoadField loadField,StoreField storeField){
    JField loadJfile=loadField.getFieldRef().resolve();
    JField storeJfile=storeField.getFieldRef().resolve();
    Var lbase = ((InstanceFieldAccess) loadField.getRValue()).getBase();
    Var sbase = ((InstanceFieldAccess) storeField.getLValue()).getBase();
    Set setl=pta.getPointsToSet(lbase,loadJfile).stream().filter(e->1==1).collect(Collectors.toSet());
    Set sets=pta.getPointsToSet(sbase,storeJfile).stream().filter(e->1==1).collect(Collectors.toSet());
    return sets.retainAll(setl);
}


    protected boolean isAlis(PointerAnalysisResult pta,LoadArray loadArray,StoreArray storeArray){
    Var loadIndex=loadArray.getArrayAccess().getIndex();
    Var storeIndex=storeArray.getArrayAccess().getIndex();
    Var loadBase=loadArray.getArrayAccess().getBase();
    Var storeBase=storeArray.getArrayAccess().getBase();
    Set sets=pta.getPointsToSet(storeBase).stream().filter(e->1==1).collect(Collectors.toSet());
    Set setl=pta.getPointsToSet(loadBase).stream().filter(e->1==1).collect(Collectors.toSet());
    return sets.retainAll(setl)&&indexCheck(loadIndex,storeIndex,solver.getInFact(loadArray),solver.getInFact(storeArray));

    }

    private boolean indexCheck(Var loadIndex, Var storeIndex, CPFact loadFact, CPFact storeFact) {
    Value value1=loadFact.get(loadIndex);
    Value value2=storeFact.get(storeIndex);
    if (value1.isConstant()){
        if (value2.isConstant()&& value2.getConstant()==value1.getConstant()){
            return true;
        }
        if (value2.isNAC()){
            return true;
        }

    }
    else if(value1.isNAC()){
        if (!value2.isUndef())
            return true;
    }
    else {
        return false;
    }
    return false;
    }


}
