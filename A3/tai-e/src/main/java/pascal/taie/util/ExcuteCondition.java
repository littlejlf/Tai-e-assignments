package pascal.taie.util;

import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Var;

public class ExcuteCondition {
    public static boolean execute(ConditionExp.Op operate, Value op1, Value op2) {
        switch (operate) {
            case EQ:
                return op1.equals(op2);
            case NE:
                return !op1.equals(op2);
            case LT:
                return op1.getConstant() < op2.getConstant();
            case GT:
                return op1.getConstant() > op2.getConstant();
            case LE:
                return op1.getConstant() <= op2.getConstant();
            case GE:
                return op1.getConstant() >= op2.getConstant();
            default:
                throw new IllegalArgumentException("Unsupported operation: " + operate);
        }
    }
}