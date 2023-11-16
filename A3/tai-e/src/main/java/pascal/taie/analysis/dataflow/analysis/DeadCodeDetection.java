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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.ExcuteCondition;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {

        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        //control flow unreachable
        Set unreachableStmts=new HashSet();
        unreachableStmts.addAll(ir.getStmts());
        Set<Stmt> unreachableBranch=new HashSet<>();
        visit(cfg,unreachableStmts);
        //unreachable branch
        for (Stmt stmt :ir.getStmts())
            {
                //in or out
                CPFact fact=constants.getOutFact(stmt);
                if (stmt instanceof If){
                    ConditionExp.Op op=((If) stmt).getCondition().getOperator();
                    Var op1=((If) stmt).getCondition().getOperand1();
                    Var op2=((If) stmt).getCondition().getOperand2();
                    Value v1=fact.get(op1);
                    Value v2=fact.get(op2);
                    //先不考虑引用值
                    if (v1.isConstant()&&v2.isConstant()){
                        boolean result=ExcuteCondition.execute(op,v1,v2);
                        Stmt falseStmt=  cfg.getOutEdgesOf(stmt).stream().filter(elem->elem.getKind().equals(Edge.Kind.IF_FALSE)).collect(Collectors.toList()).get(0).getTarget();
                        Stmt trueStmt=  cfg.getOutEdgesOf(stmt).stream().filter(elem->elem.getKind().equals(Edge.Kind.IF_TRUE)).collect(Collectors.toList()).get(0).getTarget();
                        if (result){
                            unreachableBranch.add(falseStmt);
                            //控制流出度递归删除
                            Set s1=new HashSet<>();
                            Set s2=new HashSet<>();
                            deleteRecursion(trueStmt,cfg,s1,s2);
                            deleteRecursion(falseStmt,cfg,s2,s1);
                            s2.removeAll(s1);
                            unreachableBranch.addAll(s2);
                        }
                        else {
                            unreachableBranch.add(trueStmt);
                            Set s1=new HashSet<>();
                            Set s2=new HashSet<>();
                            deleteRecursion(falseStmt,cfg,s1,s2);
                            deleteRecursion(trueStmt,cfg,s2,s1);
                           // s2.removeAll(s1);
                            unreachableBranch.addAll(s2);
                        }
                    }

                }
                if (stmt instanceof SwitchStmt){
                    Var var=((SwitchStmt) stmt).getVar();
                    Value value=fact.get(var);
                    List needDelete=new ArrayList();
                    if (value.isConstant()){
                        //dead不能包含在match的路径里
                        Set s1=new HashSet<>();
                        Set s2=new HashSet<>();
                        List ints=((SwitchStmt) stmt).getCaseValues();
                        Stmt mactched;
                        Set<Stmt> unmatched;
                        //删除不匹配的
                        if (ints.contains(value.getConstant())){
                            mactched= ((SwitchStmt) stmt).getCaseTargets().stream().filter(i->i.first()==value.getConstant()).collect(Collectors.toList()).get(0).second();
                        }
                        //删除除了default
                        else {
                            mactched=((SwitchStmt) stmt).getDefaultTarget();
                        }
                        unmatched=new HashSet(((SwitchStmt) stmt).getTargets());
                        unmatched.add(((SwitchStmt) stmt).getDefaultTarget());
                        unmatched.remove(mactched);
                        deleteRecursion(mactched,cfg,s1,s2);
                        unmatched.forEach(s->{
                            deleteRecursion(s,cfg,s2,s1);
                        });
                        unreachableBranch.addAll(s2);
                        unreachableBranch.addAll(unmatched);
                    }
                }


            }


        //无效赋值
        Set<Stmt> deadAssign;
        Set<Stmt> assignStmts=ir.getStmts().stream().filter(stmt -> stmt instanceof AssignStmt).collect(Collectors.toSet());
        deadAssign=assignStmts.stream().filter(stmt->!liveVars.getInFact(stmt).contains( (Var) stmt.getDef().get()))
                .filter(stmt -> stmt.getUses().stream().anyMatch(e->DeadCodeDetection.hasNoSideEffect(e))).collect(Collectors.toSet());
/*       deadCode.addAll(deadAssign);*/
        deadCode.addAll(unreachableBranch);
/*
        deadCode.addAll(unreachableStmts);
*/
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
    //通过控制流图删除
    public void deleteRecursion(Stmt stmt,CFG<Stmt> cfg,Set dead,Set accBanch){
    List<Edge<Stmt>> outEs=new ArrayList<>(cfg.getOutEdgesOf(stmt));
    outEs.forEach(stmtEdge -> {
        Stmt target=stmtEdge.getTarget();
        //不能包含if和if not之后的汇合路径
        if (target!=null&&!accBanch.contains(target)){
            dead.add(target);
            deleteRecursion(target,cfg,dead,accBanch);
        }
    });

    }
    //广度遍历
    public <N> void visit(CFG<N> cfg, Set<Edge<N>> set){
        List<N> workList= new ArrayList();
        N entry=  cfg.getEntry();
        workList.add(entry);
        set.remove(entry);
        while (!workList.isEmpty()){
            for (Edge<N> e:cfg.getOutEdgesOf(workList.get(0)))
            {
                workList.add(e.getTarget());
                set.remove(e.getTarget());
            }
            workList.remove(0);
        }
    }
}
