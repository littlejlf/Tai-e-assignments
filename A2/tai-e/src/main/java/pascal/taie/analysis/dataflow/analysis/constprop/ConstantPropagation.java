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

package pascal.taie.analysis.dataflow.analysis.constprop;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundaryFact=new CPFact();
        for(Var param:cfg.getIR().getParams()){
            if (canHoldInt(param))
            boundaryFact.update(param,Value.getNAC());
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }
    //  target 传copy值
    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
       fact.forEach((k,v)->{
           target.update(k,meetValue(v,target.get(k)));
       });

        }


    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.equals(v2))
            return v1;
        else if(v1.isConstant()&&v2.isUndef())
            return v1;
        else if(v2.isConstant()&&v1.isUndef())
            return v2;
        else
            return  Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut=in.copy();
        if(stmt instanceof pascal.taie.ir.stmt.DefinitionStmt){
            if (stmt.getDef().isPresent()){
                LValue def=stmt.getDef().get();
                //LHS应该是变量
                if (def instanceof Var){
                    //如果是x=3或者是x=y这种类型，直接更新即可
                    List list=stmt.getUses();
                    RValue rValue=((DefinitionStmt) stmt).getRValue();
                    int size=stmt.getUses().size();
                    if(size==1){
                        RValue use=stmt.getUses().get(0);
                        //如果是常量
                        if(use instanceof IntLiteral){
                            IntLiteral cons=(IntLiteral) use;
                            newOut.update((Var) def,Value.makeConstant(cons.getValue()));
                        }
                        //如果是变量
                        else if(use instanceof Var){
                            Var useVar=(Var) use;
                            if (canHoldInt((Var) def))
                            newOut.update((Var) def,newOut.get(useVar));
                        }

                    }else {
                        //如果是二元表达式类型
                        DefinitionStmt definitionStmt=(DefinitionStmt) stmt;
                        if (definitionStmt.getRValue() instanceof BinaryExp){
                            BinaryExp binaryExp=(BinaryExp) definitionStmt.getRValue();
                            Value newVal=evaluate(binaryExp,newOut);
                            if (canHoldInt((Var) def))
                                newOut.update((Var) def,newVal);
                        }
                        //其他如函数调用 保守NAC
                        else {
                            if (canHoldInt((Var) def))
                                newOut.update((Var) def,Value.getNAC());
                        }

                    }
                }
            }

        }
        if (!newOut.equals(out)){
            out.copyFrom(newOut);
            return true;
        }
        return false;
    }


    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *解决op操作
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        BinaryExp binaryExp=(BinaryExp) exp;
        Var var1=binaryExp.getOperand1();
        Var var2=binaryExp.getOperand2();

        if(in.get(var1).isConstant()&&in.get(var2).isConstant()){
            int cons1=in.get(var1).getConstant();
            int cons2=in.get(var2).getConstant();
            if (binaryExp instanceof ArithmeticExp){
                ArithmeticExp arithmeticExp=(ArithmeticExp) binaryExp;
                switch (arithmeticExp.getOperator().toString()){
                    case "+":
                        return Value.makeConstant(cons1+cons2);
                    case  "-":
                        return Value.makeConstant(cons1-cons2);
                    case "*":
                        return Value.makeConstant(cons1*cons2);
                    case "/":
                        if (cons2==0){
                            return Value.getUndef();
                        }
                        return Value.makeConstant(cons1/cons2);
                    case "%":
                        if(cons2==0){
                            return Value.getUndef();
                        }
                        return Value.makeConstant(cons1%cons2);
                }
            }else if(binaryExp instanceof ConditionExp){
                ConditionExp conditionExp=(ConditionExp) binaryExp;
                switch (conditionExp.getOperator().toString()){
                    case "==":
                        return Value.makeConstant(cons1==cons2?1:0);
                    case "!=":
                        return Value.makeConstant(cons1!=cons2?1:0);
                    case "<":
                        return Value.makeConstant(cons1<cons2?1:0);
                    case ">":
                        return Value.makeConstant(cons1>cons2?1:0);
                    case "<=":
                        return Value.makeConstant(cons1<=cons2?1:0);
                    case ">=":
                        return Value.makeConstant(cons1>=cons2?1:0);

                }
            }else if(binaryExp instanceof ShiftExp){
                ShiftExp shiftExp=(ShiftExp) binaryExp;
                switch (shiftExp.getOperator().toString()){
                    case "<<":
                        return Value.makeConstant(cons1 << cons2);
                    case ">>":
                        return Value.makeConstant(cons1 >> cons2);
                    case ">>>":
                        return Value.makeConstant(cons1 >>> cons2);
                }
            }else if (binaryExp instanceof BitwiseExp){
                BitwiseExp bitwiseExp=(BitwiseExp) binaryExp;
                switch (bitwiseExp.getOperator().toString()){
                    case "|":
                        return Value.makeConstant(cons1|cons2);
                    case "&":
                        return Value.makeConstant(cons1&cons2);
                    case "^":
                        return Value.makeConstant(cons1^cons2);
                }
            }
        }else if (in.get(var1).isNAC()||in.get(var2).isNAC()){
            return Value.getNAC();
        }
        return Value.getUndef();
    }
}
