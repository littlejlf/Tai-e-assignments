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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        List<Node> worklist=new ArrayList<>();
        //首先将所有的node都加入到worklist中
        for(Node node:cfg){
            worklist.add(node);
        }
        while (!worklist.isEmpty()){
            Node nowNode=worklist.get(0);
            if (!cfg.isEntry(nowNode)) {
                for (Node pred:cfg.getPredsOf(nowNode)){
                    analysis.meetInto(result.getOutFact(pred),result.getInFact(nowNode) );
                }
                if (analysis.transferNode(nowNode,result.getInFact(nowNode),result.getOutFact(nowNode))){
                    //如果out改变了，那么就后续节点加入worklist
                    for (Node succ:cfg.getSuccsOf(nowNode)){
                        worklist.add(succ);
                    }
                }
            }
            worklist.remove(0);
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        List<Node> worklist=new ArrayList<>();
        //首先将所有的node都加入到worklist中
        for(Node node:cfg){
            worklist.add(node);
        }
        Collections.reverse(worklist);
        while (!worklist.isEmpty()){
            Node nowNode=worklist.get(0);
            if (!cfg.isEntry(nowNode)) {
                for (Node succ:cfg.getSuccsOf(nowNode)){
                    analysis.meetInto(result.getInFact(succ),result.getOutFact(nowNode) );
                }
                Fact out=result.getOutFact(nowNode);
                if (analysis.transferNode(nowNode,result.getInFact(nowNode),out)){
                    //如果out改变了，那么就前节点加入worklist
                    for (Node pre:cfg.getPredsOf(nowNode)){
                        worklist.add(pre);
                    }
                }
            }
            worklist.remove(0);
        }
    }
}
