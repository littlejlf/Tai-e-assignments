
package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        Context parentContext = callSite.getContainer().getContext();

        int parentContextLength = parentContext.getLength();
        if (parentContextLength > 0) {
            Context c2=callSite.getContainer().getContext();
            return ListContext.make(parentContext.getElementAt(parentContextLength - 1), callSite.getCallSite());
        } else {
            return ListContext.make(callSite.getCallSite());
        }
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        return selectContext(callSite, callee); // 注意，这里的父上下文是看 callSite，而不是 recv的上下文
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        Context parentContext = method.getContext();
        int parentContextLength = parentContext.getLength();
        if (parentContextLength > 0) {
            return ListContext.make(parentContext.getElementAt(parentContextLength - 1));
        } else {
            return ListContext.make();
        }
    }
}
