package pku;

import java.io.*;
import java.util.*;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.analysis.misc.IRDumper;
import pascal.taie.language.classes.*;
import pascal.taie.util.collection.HybridHashMap;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

public class PointerAnalysis extends PointerAnalysisTrivial {
    // Global
    public static final String ID = "pku-pta";
    private static final Logger logger = LogManager.getLogger(IRDumper.class);
    private final File dumpPath = new File("result.txt");
    // Benchmark info
    private final PreprocessResult preprocess = new PreprocessResult();
    // Context sensitivity
    private final int maxLevel = 10;

    public PointerAnalysis(AnalysisConfig config) {
        super(config);
    }

    private final CopyRel getBBCopyRel(IR ir, BasicBlock bb) {
        var copyRel = new CopyRel();
        for (var i = bb.from; i <= bb.to; i++) {
            var stmt = ir.getStmt(i);
            if (stmt instanceof Copy) {
                var copy = (Copy) stmt;
                var lhs = copy.getLValue();
                var rhs = copy.getRValue();
                copyRel.obj.put(lhs, new HashSet<>());
                copyRel.obj.get(lhs).add(rhs);
            }
        }
        return copyRel;
    }

    private final MethodResult visitMethod(JMethod mth, int level) {
        if (level >= maxLevel) {
            return new MethodResult();
        }
        var rep = " ".repeat(level);
        var ir = mth.getIR();
        logger.info("{}=====[IR@{}]=====", rep, mth.getName());
        for (var i = 0; i < ir.getStmts().size(); i++) {
            logger.info("{}{}: {}", rep, i, ir.getStmt(i));
        }
        logger.info("{}=====[BASIC BLOCK]=====", rep);
        var cfg = new SimpleCFG(ir);
        for (var i = 0; i < cfg.size(); i++) {
            var bb = cfg.bbs.get(i);
            logger.info("{}{}: [{},{}] <- {}", rep, i, bb.from, bb.to,
                    cfg.revEdges.get(i).toString());
        }
        logger.info("{}=====[BB INDIVIDUAL COPY]=====", rep);
        var rellist = new ArrayList<CopyRel>(cfg.size());
        for (var bb : cfg.bbs) {
            rellist.add(getBBCopyRel(ir, bb));
        }
        for (var i = 0; i < cfg.size(); i++) {
            logger.info("{}{}: {}", rep, i, rellist.get(i).obj.toString());
        }
        logger.info("{}=====[BB FLOW COPY]=====", rep);
        // TODO: use iterative calculation (currently only once)
        for (var i = 0; i < cfg.size(); i++) {
            var bb = cfg.bbs.get(i);
            var bbrel = rellist.get(i);
            var temp = new CopyRel();
            for (var prev : cfg.revEdges.get(i)) {
                var prevrel = rellist.get(prev);
                prevrel.obj.forEach((lhs, rhs) -> {
                    if (!bbrel.obj.containsKey(lhs)) {
                        var update = temp.obj.getOrDefault(lhs, new HashSet<>());
                        update.addAll(rhs);
                        temp.obj.put(lhs, update);
                    }
                });
            }
            bbrel.obj.putAll(temp.obj);
        }
        for (var i = 0; i < cfg.size(); i++) {
            logger.info("{}{}: {}", rep, i, rellist.get(i).obj.toString());
        }
        logger.info("{}=====[NEW LOCATIONS]=====", rep);
        var newloc = new NewLoc();
        for (var stmt : ir.getStmts()) {
            if (stmt instanceof New) {
                var newStmt = (New) stmt;
                var id = preprocess.getObjIdAt(newStmt);
                var lva = newStmt.getLValue();
                // Somehow IR only uses temp value to store
                // new, so we donot need to check the newloc
                // for if there is already the same lva.
                var set = new TreeSet<Integer>();
                set.add(id);
                newloc.obj.put(lva, set);
            }
        }
        logger.info("{}{}", rep, newloc.obj.toString());
        logger.info("{}=====[SPREAD NEW THROUGH COPY]=====", rep);
        var outbbrel = rellist.get(cfg.size() - 1);
        var clone = new CopyRel(outbbrel.obj);
        while (!outbbrel.obj.isEmpty()) {
            var kdel = new HashSet<Var>();
            for (var lhs : outbbrel.obj.keySet()) {
                var vdel = new HashSet<Var>();
                for (var rhs : outbbrel.obj.get(lhs)) {
                    // For each `lhs = rhs`, and we know `rhs = new X`,
                    // add `X` to `lhs`.
                    if (newloc.obj.containsKey(rhs)) {
                        var locset = newloc.obj.getOrDefault(lhs, new TreeSet<>());
                        locset.addAll(newloc.obj.get(rhs));
                        newloc.obj.put(lhs, locset);
                        vdel.add(rhs);
                    }
                }
                // Delete updated in copyrel
                outbbrel.obj.get(lhs).removeAll(vdel);
                if (outbbrel.obj.get(lhs).isEmpty()) {
                    kdel.add(lhs);
                }
            }
            kdel.forEach(k -> outbbrel.obj.remove(k));
        }
        logger.info("{}{}", rep, newloc.obj.toString());
        return new MethodResult(newloc, clone);
    }

    @Override
    public PointerAnalysisResult analyze() {
        var result = new PointerAnalysisResult();
        var world = World.get();
        var classes = world.getClassHierarchy().applicationClasses();
        var main = world.getMainMethod();
        // Preprocess
        classes.forEach(jclass -> {
            logger.info("Preprocessing class {}...", jclass.getName());
            jclass.getDeclaredMethods().forEach(method -> {
                if (!method.isAbstract())
                    preprocess.analysis(method.getIR());
            });
        });
        // Analysis
        var res = visitMethod(main, 0);
        // Collect
        preprocess.test_pts.forEach((test_id, pt) -> {
            result.put(test_id, res.newloc.obj.get(pt));
        });
        dump(result);
        return result;
    }

    private final class MethodResult {
        public NewLoc newloc = new NewLoc();
        public CopyRel copyrel = new CopyRel();

        public MethodResult() {
        }

        public MethodResult(NewLoc newloc_, CopyRel lastbb) {
            newloc = newloc_;
            copyrel = lastbb;
        }
    }

    private final class NewLoc {
        public final HashMap<Var, TreeSet<Integer>> obj = new HashMap<>();
    }

    private final class CopyRel {
        public final HashMap<Var, HashSet<Var>> obj = new HashMap<>();

        public CopyRel() {
        }

        public CopyRel(HashMap<Var, HashSet<Var>> a) {
            obj.putAll(a);
        }
    }

    // Note: Belows are used for context sensitivity
    // I currently found this is complex, but if we are going to
    // do context-sensitive, these may be useful.
    private final class SimpleCFG {
        public final List<BasicBlock> bbs;
        public final List<Set<Integer>> edges;
        public final List<Set<Integer>> revEdges;

        public SimpleCFG(IR ir) {
            this.bbs = getBasicBlocks(ir);
            edges = new ArrayList<>();
            var n = bbs.size();
            for (var i = 0; i < n; i++) {
                edges.add(new HashSet<>());
                var bb = bbs.get(i);
                var stmt = ir.getStmts().get(bb.to);
                if (stmt instanceof If) {
                    var targets = ((JumpStmt) stmt).getTargets();
                    for (var t : targets) {
                        for (var j = 0; j < n; j++) {
                            var bb2 = bbs.get(j);
                            if (bb2.from == t.getIndex()) {
                                edges.get(i).add(j);
                            }
                        }
                    }
                    if (i + 1 < n) {
                        edges.get(i).add(i + 1);
                    }
                } else if (stmt instanceof Goto) {
                    var targets = ((JumpStmt) stmt).getTargets();
                    for (var t : targets) {
                        for (var j = 0; j < n; j++) {
                            var bb2 = bbs.get(j);
                            if (bb2.from == t.getIndex()) {
                                edges.get(i).add(j);
                            }
                        }
                    }
                } else {
                    if (i + 1 < n) {
                        edges.get(i).add(i + 1);
                    }
                }
            }
            revEdges = new ArrayList<>();
            for (var i = 0; i < n; i++) {
                revEdges.add(new HashSet<>());
                for (var j = 0; j < n; j++) {
                    if (edges.get(j).contains(i)) {
                        revEdges.get(i).add(j);
                    }
                }
            }
        }

        public final int size() {
            return bbs.size();
        }
    }

    private final List<BasicBlock> getBasicBlocks(IR ir) {
        // unique
        var starter = new TreeSet<Integer>();
        var stmts = ir.getStmts();
        var n = stmts.size();
        // 0 is a starter
        starter.add(0);
        for (var i = 0; i < n; i++) {
            var stmt = stmts.get(i);
            if (stmt instanceof JumpStmt) {
                // next stmt of a jump is a starter
                starter.add(stmt.getIndex() + 1);
                // every target is a starter
                var targets = ((JumpStmt) stmt).getTargets();
                targets.forEach(t -> starter.add(t.getIndex()));
            }
        }
        starter.add(n);
        var result = new ArrayList<BasicBlock>();
        var it = starter.stream().toList();
        for (var i = 0; i < it.size() - 1; i++) {
            // from starter to next starter form a basic block
            result.add(new BasicBlock(it.get(i), it.get(i + 1) - 1));
        }
        return result;
    }

    private final class BasicBlock {
        public final int from;
        public final int to;

        public BasicBlock(int from, int to) {
            this.from = from;
            this.to = to;
        }
    }

}
