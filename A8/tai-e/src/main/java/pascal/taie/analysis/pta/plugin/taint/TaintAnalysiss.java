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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.graph.Edge;

import java.util.*;
import java.util.function.Consumer;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        Set<Source> sources = config.getSources();
        Set<TaintTransfer> transfers = config.getTransfers();
        Set<Sink> sinks = config.getSinks();
        CallGraph<CSCallSite, CSMethod> csCallGraph = result.getCSCallGraph();
        Consumer consumer = null;
        sources.forEach(source -> {
            JMethod method = source.method();
            Type type = source.type();
            csCallGraph.getNodes().stream().filter(csMethod -> csMethod.getMethod().equals(method)).forEach(csSourceMethod -> {

                transfers.addAll(visit(csCallGraph, consumer, source, csSourceMethod));
            });
        });
        return taintFlows;
    }

    private Set<TaintTransfer> visit(CallGraph<CSCallSite, CSMethod> csCallGraph, Consumer consumer, Source source, CSMethod csSourceMethod) {
        List<CSMethod> worklist = new ArrayList<>();
        worklist.add(csSourceMethod);
        while (!worklist.isEmpty()) {
            CSMethod node = worklist.get(0);
            if (!isSinkFunc(node)) {
                List<CSMethod> nodes = csCallGraph.getOutEdgesOf(node).stream().map(Edge::getTarget).filter(csMethod -> isTransFunc(csMethod) || isSinkFunc(csMethod)).toList();
                worklist.remove(0);
                worklist.addAll(nodes.stream().filter(elem->!worklist.contains(elem)).toList());
                consumer.accept(node);

            }

        }
    }

    private boolean isTransFunc(CSMethod csMethod) {
        return false;
    }

    private boolean isSinkFunc(CSMethod csMethod) {
        return false;
    }


}
