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
    private final NewLoc pts = new NewLoc();
    // Context sensitivity
    private final int maxLevel = 10;

    public PointerAnalysis(AnalysisConfig config) {
        super(config);
    }

    // CONTENTS:
    // - ANALYZER: Methods performing actual analysis
    // - DATA STRUCTURES: Data structures used in analysis
    // - POINTER DEFS: Definitions of pointer types
    // - CFG: Simple control flow graph utils

    /* -------------------------------- ANALYZER -------------------------------- */

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
        preprocess.test_pts.forEach((test_id, var) -> {
            var pt = res.ptrlist.var2ptr(var);
            result.put(test_id, pts.obj.get(pt));
        });
        // Trivial complement
        var objs = new TreeSet<>(preprocess.obj_ids.values());
        preprocess.test_pts.forEach((test_id, pt) -> {
            if (!result.containsKey(test_id) || result.get(test_id).isEmpty()) {
                result.put(test_id, objs);
            }
        });
        dump(result);
        return result;
    }

    private final class VisitResult {
        public CopyRel copyrel = new CopyRel();
        public PtrList ptrlist = new PtrList();

        public VisitResult() {
        }

        public VisitResult(CopyRel copyrel, PtrList ptrlist) {
            this.copyrel = copyrel;
            this.ptrlist = ptrlist;
        }
    }

    private final VisitResult visitMethod(JMethod mth, int level) {
        if (level >= maxLevel) {
            return new VisitResult();
        }
        var rep = " ".repeat(level);
        logger.info("{}=====[IR@{}]=====", rep, mth.getName());
        var ir = mth.getIR();
        for (var i = 0; i < ir.getStmts().size(); i++) {
            logger.info("{}{}: {}", rep, i, ir.getStmt(i));
        }
        logger.info("{}=====[PTR LIST]=====", rep);
        var ptrlist = getPtrList(ir);
        logger.info("{}", ptrlist.ptrlist.toString());
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
            rellist.add(getBBCopyRel(ptrlist, ir, bb, level));
        }
        for (var i = 0; i < cfg.size(); i++) {
            logger.info("{}{}: {}", rep, i, rellist.get(i).tostr(ptrlist));
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
                    // avoid overwrite when merging control flow (functioning KILL)
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
            logger.info("{}{}: {}", rep, i, rellist.get(i).tostr(ptrlist));
        }
        logger.info("{}=====[NEW LOCATIONS]=====", rep);
        var newloc = new NewLoc();
        for (var stmt : ir.getStmts()) {
            if (stmt instanceof New) {
                var newStmt = (New) stmt;
                var id = preprocess.getObjIdAt(newStmt);
                var lva = ptrlist.var2ptr(newStmt.getLValue());
                // Somehow IR only uses temp value to store
                // new, so we donot need to check the newloc
                // for if there is already the same lva.
                var set = new TreeSet<Integer>();
                set.add(id);
                newloc.obj.put(lva, set);
            }
        }
        logger.info("{}{}", rep, newloc.tostr(ptrlist));
        logger.info("{}=====[SPREAD NEW THROUGH COPY]=====", rep);
        var outbbrel = rellist.get(cfg.size() - 1);
        var clone = new CopyRel(outbbrel.obj);
        while (!outbbrel.obj.isEmpty()) {
            var kdel = new HashSet<Integer>();
            for (var lhs : outbbrel.obj.keySet()) {
                var vdel = new HashSet<Integer>();
                for (var rhs : outbbrel.obj.get(lhs)) {
                    logger.debug("[CHECK] {}:{} ?= {}:{}, ?{}",
                            ptrlist.ptr2str(lhs), lhs, ptrlist.ptr2str(rhs), rhs,
                            newloc.obj.containsKey(rhs));
                    // For each `lhs = rhs`, and we know `rhs = new X`,
                    // add `X` to `lhs`.
                    if (newloc.obj.containsKey(rhs)) {
                        var locset = newloc.obj.getOrDefault(lhs, new TreeSet<>());
                        locset.addAll(newloc.obj.get(rhs));
                        newloc.obj.put(lhs, locset);
                        vdel.add(rhs);
                    }
                }
                for (var vd : vdel) {
                    logger.debug("[DEL] {} -> {}", ptrlist.ptr2str(lhs), ptrlist.ptr2str(vd));
                }
                // Delete updated in copyrel
                outbbrel.obj.get(lhs).removeAll(vdel);
                if (outbbrel.obj.get(lhs).isEmpty()) {
                    kdel.add(lhs);
                }
            }
            kdel.forEach(k -> outbbrel.obj.remove(k));
        }
        logger.info("{}{}", rep, newloc.tostr(ptrlist));
        pts.merge(newloc);
        return new VisitResult(clone, ptrlist);
    }

    private final PtrList getPtrList(IR ir) {
        var varlist = new HashSet<Var>();
        var sfieldlist = new HashSet<JField>();
        var ifieldlist = new HashMap<Var, HashSet<JField>>();
        var ptrlist = new PtrList();
        ir.getVars().forEach(varlist::add);
        ir.getParams().forEach(varlist::add);

        var cnt = 0;
        for (var v : varlist) {
            ptrlist.ptrlist.add(new VarPtr(v));
            ptrlist.varlist.put(v, cnt++);
        }
        for (var stmt : ir.getStmts()) {
            if ((stmt instanceof LoadField) || (stmt instanceof StoreField)) {
                FieldAccess fa = null;
                if (stmt instanceof LoadField) {
                    fa = ((LoadField) stmt).getRValue();
                } else {
                    fa = ((StoreField) stmt).getLValue();
                }
                if (fa instanceof StaticFieldAccess) {
                    var field = ((StaticFieldAccess) fa).getFieldRef().resolve();
                    sfieldlist.add(field);
                } else {
                    var field = ((InstanceFieldAccess) fa).getFieldRef().resolve();
                    var base = ((InstanceFieldAccess) fa).getBase();
                    if (!ifieldlist.containsKey(base)) {
                        ifieldlist.put(base, new HashSet<>());
                    }
                    ifieldlist.get(base).add(field);
                }
            }
        }

        for (var f : sfieldlist) {
            ptrlist.ptrlist.add(new StaticFieldPtr(f));
            ptrlist.sfieldlist.put(f, cnt++);
        }
        for (var base : ifieldlist.keySet()) {
            for (var f : ifieldlist.get(base)) {
                ptrlist.ptrlist.add(new InstanceFieldPtr(base, f));
                var inner = ptrlist.ifieldlist.getOrDefault(base, new HashMap<>());
                inner.put(f, cnt++);
                ptrlist.ifieldlist.put(base, inner);
            }
        }
        return ptrlist;
    }

    private final CopyRel getBBCopyRel(PtrList ptrlist, IR ir, BasicBlock bb, int level) {
        var copyRel = new CopyRel();
        var rep = " ".repeat(level);
        for (var i = bb.from; i <= bb.to; i++) {
            var stmt = ir.getStmt(i);
            if (stmt instanceof Copy) {
                var copy = (Copy) stmt;
                var lhs = ptrlist.var2ptr(copy.getLValue());
                var rhs = ptrlist.var2ptr(copy.getRValue());
                // overwrite the relationship on serialized control flow
                copyRel.obj.put(lhs, new HashSet<>());
                copyRel.obj.get(lhs).add(rhs);
            }
            if (stmt instanceof LoadField) {
                var load = (LoadField) stmt;
                var lhs = ptrlist.var2ptr(load.getLValue());
                var rhs = ptrlist.faccess2ptr(load.getRValue());
                copyRel.obj.put(lhs, new HashSet<>());
                copyRel.obj.get(lhs).add(rhs);
            }
            if (stmt instanceof StoreField) {
                var store = (StoreField) stmt;
                var lhs = ptrlist.faccess2ptr(store.getLValue());
                var rhs = ptrlist.var2ptr(store.getRValue());
                copyRel.obj.put(lhs, new HashSet<>());
                copyRel.obj.get(lhs).add(rhs);
            }
            if (stmt instanceof Invoke) {
                // TODO
            }
        }
        return copyRel;
    }

    /* ----------------------------- DATA STRUCTURES ---------------------------- */

    private final class PtrList {
        public final HashMap<Var, Integer> varlist = new HashMap<>();
        public final HashMap<JField, Integer> sfieldlist = new HashMap<>();
        public final HashMap<Var, HashMap<JField, Integer>> ifieldlist = new HashMap<>();
        public final ArrayList<Ptr> ptrlist = new ArrayList<>();

        public int var2ptr(Var var) {
            if (varlist.containsKey(var)) {
                return varlist.get(var);
            } else {
                return -1;
            }
        }

        public int sfield2ptr(JField field) {
            if (sfieldlist.containsKey(field)) {
                return sfieldlist.get(field);
            } else {
                return -1;
            }
        }

        public int faccess2ptr(FieldAccess fa) {
            if (fa instanceof StaticFieldAccess) {
                return sfield2ptr(((StaticFieldAccess) fa).getFieldRef().resolve());
            } else {
                var base = ((InstanceFieldAccess) fa).getBase();
                var field = ((InstanceFieldAccess) fa).getFieldRef().resolve();
                return ifield2ptr(base, field);
            }
        }

        public int ifield2ptr(Var base, JField field) {
            if (ifieldlist.containsKey(base) && ifieldlist.get(base).containsKey(field)) {
                return ifieldlist.get(base).get(field);
            } else {
                return -1;
            }
        }

        public String ptr2str(int i) {
            return ptrlist.get(i).toString();
        }
    }

    /**
     * Location of `new` statements for each Ptr (indexed in PtrList)
     */
    private final class NewLoc {
        public final HashMap<Integer, TreeSet<Integer>> obj = new HashMap<>();

        public void merge(NewLoc a) {
            a.obj.forEach((k, v) -> {
                var set = obj.getOrDefault(k, new TreeSet<>());
                set.addAll(v);
                obj.put(k, set);
            });
        }

        public String tostr(PtrList list) {
            var s = "{";
            for (var k : obj.keySet()) {
                var v = obj.get(k);
                s += list.ptr2str(k) + "=" + v.toString() + ", ";
            }
            return s + "}";
        }
    }

    /**
     * Copy relationship (a = b) for each Ptr (indexed in PtrList)
     */
    private final class CopyRel {
        public final HashMap<Integer, HashSet<Integer>> obj = new HashMap<>();

        public CopyRel() {
        }

        public CopyRel(HashMap<Integer, HashSet<Integer>> a) {
            obj.putAll(a);
        }

        public void merge(CopyRel a) {
            a.obj.forEach((k, v) -> {
                var set = obj.getOrDefault(k, new HashSet<>());
                set.addAll(v);
                obj.put(k, set);
            });
        }

        public String tostr(PtrList list) {
            var s = "{";
            for (var k : obj.keySet()) {
                var v = obj.get(k);
                s += list.ptr2str(k) + "=[";
                for (var i : v) {
                    s += list.ptr2str(i) + ", ";
                }
                s += "], ";
            }
            return s + "}";
        }
    }

    /* ------------------------------ POINTER DEFS ------------------------------ */

    private interface Ptr {
    }

    private class VarPtr implements Ptr {
        public final Var var;

        public VarPtr(Var var) {
            this.var = var;
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof VarPtr) {
                var other = (VarPtr) o;
                return var.equals(other.var);
            }
            return false;
        }

        @Override
        public String toString() {
            return var.toString();
        }
    }

    private class StaticFieldPtr implements Ptr {
        public final JField field;

        public StaticFieldPtr(StaticFieldAccess field) {
            this.field = field.getFieldRef().resolve();
        }

        public StaticFieldPtr(JField field) {
            this.field = field;
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof StaticFieldPtr) {
                var other = (StaticFieldPtr) o;
                return field.equals(other.field);
            }
            return false;
        }

        @Override
        public String toString() {
            return field.toString();
        }
    }

    private class InstanceFieldPtr implements Ptr {
        public final Var base;
        public final JField field;

        public InstanceFieldPtr(InstanceFieldAccess field) {
            this.base = field.getBase();
            this.field = field.getFieldRef().resolve();
        }

        public InstanceFieldPtr(Var base, JField field) {
            this.base = base;
            this.field = field;
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof InstanceFieldPtr) {
                var other = (InstanceFieldPtr) o;
                return field.equals(other.field) && base.equals(other.base);
            }
            return false;
        }

        @Override
        public String toString() {
            return base.toString() + "." + field.toString();
        }
    }

    private class ArrayPtr implements Ptr {
        // TODO
    }

    /* ----------------------------------- CFG ---------------------------------- */

    /**
     * Simple control flow graph, ignoring Invoke. We ignore Invoke to avoid
     * complex Call Graph.
     */
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
