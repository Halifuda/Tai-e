package pku;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.Set;
import java.util.TreeSet;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.misc.IRDumper;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.*;

public class PointerAnalysis extends PointerAnalysisTrivial {
    public PointerAnalysis(AnalysisConfig config) {
        super(config);
    }

    private class PtrID {
        public int i;

        public PtrID(int i) {
            this.i = i;
        }

        @Override
        public String toString() {
            return "P" + i;
        }
    }

    private final class PtrList {
        public final HashMap<Var, PtrID> varlist = new HashMap<>();
        public final HashMap<JField, PtrID> sfieldlist = new HashMap<>();
        public final HashMap<Var, HashMap<JField, PtrID>> ifieldlist = new HashMap<>();
        public final ArrayList<Ptr> ptrlist = new ArrayList<>();

        public Ptr ptr(PtrID id) {
            return ptrlist.get(id.i);
        }

        public PtrID var2ptr(Var var) {
            if (varlist.containsKey(var)) {
                return varlist.get(var);
            } else {
                return null;
            }
        }

        public PtrID sfield2ptr(JField field) {
            if (sfieldlist.containsKey(field)) {
                return sfieldlist.get(field);
            } else {
                return null;
            }
        }

        public PtrID ifield2ptr(Var base, JField field) {
            if (ifieldlist.containsKey(base) && ifieldlist.get(base).containsKey(field)) {
                return ifieldlist.get(base).get(field);
            } else {
                return null;
            }
        }

        public PtrID faccess2ptr(FieldAccess fa) {
            if (fa instanceof StaticFieldAccess) {
                return sfield2ptr(((StaticFieldAccess) fa).getFieldRef().resolve());
            } else {
                var base = ((InstanceFieldAccess) fa).getBase();
                var field = ((InstanceFieldAccess) fa).getFieldRef().resolve();
                return ifield2ptr(base, field);
            }
        }

        public void addVar(Var var) {
            if (!varlist.containsKey(var)) {
                varlist.put(var, new PtrID(ptrlist.size()));
                ptrlist.add(new VarPtr(var));
            }
        }

        public void addSField(JField field) {
            if (!sfieldlist.containsKey(field)) {
                sfieldlist.put(field, new PtrID(ptrlist.size()));
                ptrlist.add(new StaticFieldPtr(field));
            }
        }

        public void addIField(Var base, JField field) {
            if (!ifieldlist.containsKey(base)) {
                ifieldlist.put(base, new HashMap<>());
            }
            if (!ifieldlist.get(base).containsKey(field)) {
                ifieldlist.get(base).put(field, new PtrID(ptrlist.size()));
                ptrlist.add(new InstanceFieldPtr(base, field));
            }
        }

        public String ptr2str(PtrID id) {
            if (id == null) {
                return "null";
            }
            return ptrlist.get(id.i).toString();
        }

        @Override
        public String toString() {
            var s = "";
            for (var i = 0; i < ptrlist.size(); i++) {
                s += "P" + i + ": " + ptr2str(new PtrID(i)) + "\n";
            }
            return s;
        }
    }

    private final void initGlbPtrList(IR ir) {
        for (var v : ir.getVars()) {
            glbPtrList.addVar(v);
        }
        for (var v : ir.getParams()) {
            glbPtrList.addVar(v);
        }
        if (ir.getThis() != null) {
            glbPtrList.addVar(ir.getThis());
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
                    glbPtrList.addSField(field);
                } else {
                    var field = ((InstanceFieldAccess) fa).getFieldRef().resolve();
                    var base = ((InstanceFieldAccess) fa).getBase();
                    glbPtrList.addIField(base, field);
                }
            }
        }
    }

    private class PtrCopy {
        public PtrID lval;
        public PtrID rval;

        public PtrCopy(PtrID lval, PtrID rval) {
            this.lval = lval;
            this.rval = rval;
        }

        public PtrCopy(Var lval, Var rval) {
            this.lval = glbPtrList.var2ptr(lval);
            this.rval = glbPtrList.var2ptr(rval);
        }

        public PtrCopy(FieldAccess lval, Var rval) {
            this.lval = glbPtrList.faccess2ptr(lval);
            this.rval = glbPtrList.var2ptr(rval);
        }

        public PtrCopy(Var lval, FieldAccess rval) {
            this.lval = glbPtrList.var2ptr(lval);
            this.rval = glbPtrList.faccess2ptr(rval);
        }

        public PtrCopy(Copy stmt) {
            this.lval = glbPtrList.var2ptr(stmt.getLValue());
            this.rval = glbPtrList.var2ptr(stmt.getRValue());
        }

        public PtrCopy(StoreField stmt) {
            this.lval = glbPtrList.faccess2ptr(stmt.getLValue());
            this.rval = glbPtrList.var2ptr(stmt.getRValue());
        }

        public PtrCopy(LoadField stmt) {
            this.lval = glbPtrList.var2ptr(stmt.getLValue());
            this.rval = glbPtrList.faccess2ptr(stmt.getRValue());
        }

        public boolean isValid() {
            return lval != null && rval != null;
        }

        @Override
        public String toString() {
            return glbPtrList.ptr2str(lval) + " = " + glbPtrList.ptr2str(rval);
        }
    }

    private PtrCopy PtrCopyFromStmt(Stmt stmt, PtrID caller_recv) {
        PtrCopy result = null;
        if (stmt instanceof Copy) {
            result = new PtrCopy((Copy) stmt);
        } else if (stmt instanceof StoreField) {
            result = new PtrCopy((StoreField) stmt);
        } else if (stmt instanceof LoadField) {
            result = new PtrCopy((LoadField) stmt);
        } else if (stmt instanceof Return) {
            var ret = (Return) stmt;
            if (ret.getValue() != null && caller_recv != null) {
                result = new PtrCopy(caller_recv, glbPtrList.var2ptr(ret.getValue()));
            }
        }
        if (result != null && result.lval != null) {
            return result;
        } else {
            return null;
        }
    }

    private class BB {
        public ArrayList<PtrCopy> ir;
        public NewLoc out;

        public BB() {
            this.ir = new ArrayList<>();
            this.out = new NewLoc();
        }

        public BB(IR ir, int from, int to, PtrID caller_recv) {
            this.ir = new ArrayList<>();
            for (var i = from; i <= to; i++) {
                var stmt = ir.getStmts().get(i);
                var copy = PtrCopyFromStmt(stmt, caller_recv);
                if (copy != null) {
                    this.ir.add(copy);
                }
            }
            this.out = new NewLoc();
        }

        private List<PtrID> kill() {
            // TODO
            return null;
        }

        public NewLoc calcOut(List<NewLoc> in) {
            // TODO
            return null;
        }

        @Override
        public String toString() {
            var s = "";
            for (var i = 0; i < ir.size(); i++) {
                s += ir.get(i).toString() + "\n";
            }
            return s;
        }
    }

    private List<BB> BBsFromInvoke(Invoke stmt) {
        var call = new BB();
        var ret = new BB();

        var exp = stmt.getInvokeExp();
        var callee = exp.getMethodRef().resolve();
        var args = exp.getArgs();
        var params = callee.getIR().getParams();
        var recv = stmt.getLValue();
        var rets = callee.getIR().getReturnVars();
        var instance = (Var) null;
        if (exp instanceof InvokeInstanceExp) {
            instance = ((InvokeInstanceExp) exp).getBase();
        }
        var tis = callee.getIR().getThis();

        assert args.size() == params.size();
        for (int i = 0; i < args.size(); i++) {
            var arg = args.get(i);
            var param = params.get(i);
            call.ir.add(new PtrCopy(param, arg));
        }
        if (instance != null && tis != null) {
            call.ir.add(new PtrCopy(tis, instance));
        }
        if (recv != null && rets.size() > 0) {
            // NOTE: multiple return value is handled by
            // `Return` stmt. For example:
            // if `BB1 -> BB2(return x)`, `BB1 -> BB3(return y)`
            // we, being aware of `caller_recv`, add
            // `caller_recv = x` to `BB2` and
            // `caller_recv = y` to `BB3`.
            // Then, add `BB2 -> ret` and `BB3 -> ret`.
            // So `BB ret` need not to have any `PtrCopy`.
        }

        return List.of(call, ret);
    }

    private class CFG {
        public ArrayList<BB> bbs = new ArrayList<>();
        public Integer entry;
        public TreeSet<Integer> exits = new TreeSet<>();
        public TreeMap<Integer, TreeSet<Integer>> edges = new TreeMap<>();
        public TreeMap<Integer, TreeSet<Integer>> revEdges = new TreeMap<>();

        @Override
        public String toString() {
            var s = "";
            for (var i = 0; i < bbs.size(); i++) {
                s += i + ":\n" + bbs.get(i).toString() + "\n";
            }
            s += "Entry: " + entry + "\n";
            s += "Exits: " + exits.toString() + "\n";
            s += "Edges:\n";
            for (var i : edges.keySet()) {
                s += i + " -> " + edges.get(i).toString() + "\n";
            }
            return s;
        }
    }

    // List: entry, [exit1, exit2, ...]
    // Only build edges
    private List<Integer> buildCFGEdges(JMethod method, PtrID caller_recv) {
        var entry_exits = new ArrayList<Integer>();
        var ir = method.getIR();
        var ircfg = allMethods.get(method);
        var basecnt = glbCFG.bbs.size();
        ircfg.bbs.forEach(bb -> glbCFG.bbs.add(new BB(ir, bb.from, bb.to, caller_recv)));
        entry_exits.add(basecnt + ircfg.entry);

        for (var i = 0; i < ircfg.size(); i++) {
            if (ircfg.calls.containsKey(i)) {
                var mth = ircfg.calls.get(i);
                if (!mth.isAbstract()) {
                    var invoke = (Invoke) ir.getStmt(ircfg.bbs.get(i).to);
                    var recv = glbPtrList.var2ptr(invoke.getLValue());

                    var callee_bbs = buildCFGEdges(mth, recv);
                    var callee_entry = callee_bbs.get(0);
                    var callee_exits = callee_bbs.subList(1, callee_bbs.size());
                    glbCFG.bbs.addAll(BBsFromInvoke(invoke));
                    var call = glbCFG.bbs.size() - 2;
                    var ret = call + 1;
                    // this -> call -> callee_entry
                    var set = glbCFG.edges.getOrDefault(basecnt + i, new TreeSet<>());
                    set.add(call);
                    glbCFG.edges.put(basecnt + i, set);
                    set = glbCFG.edges.getOrDefault(call, new TreeSet<>());
                    set.add(callee_entry);
                    glbCFG.edges.put(call, set);
                    // [callee_exits] -> ret
                    for (var j : callee_exits) {
                        var set2 = glbCFG.edges.getOrDefault(j, new TreeSet<>());
                        set2.add(ret);
                        glbCFG.edges.put(j, set2);
                    }
                    // others -> this, remain unchanged
                    // this -> others => ret -> others
                    for (var j : ircfg.edges.get(i)) {
                        var set2 = glbCFG.edges.getOrDefault(ret, new TreeSet<>());
                        set2.add(basecnt + j);
                        glbCFG.edges.put(ret, set2);
                    }
                    if (ircfg.exits.contains(i)) {
                        entry_exits.add(ret);
                    }
                }
            } else {
                for (var j : ircfg.edges.get(i)) {
                    var set = glbCFG.edges.getOrDefault(basecnt + i, new TreeSet<>());
                    set.add(basecnt + j);
                    glbCFG.edges.put(basecnt + i, set);
                }
                if (ircfg.exits.contains(i)) {
                    entry_exits.add(basecnt + i);
                }
            }
        }
        return entry_exits;
    }

    private void completeGLbCFG(List<Integer> entry_exits) {
        // rev edges
        for (var i : glbCFG.edges.keySet()) {
            for (var j : glbCFG.edges.get(i)) {
                var set = glbCFG.revEdges.getOrDefault(j, new TreeSet<>());
                set.add(i);
                glbCFG.revEdges.put(j, set);
            }
        }
        // entry, exits
        glbCFG.entry = entry_exits.get(0);
        glbCFG.exits.addAll(entry_exits.subList(1, entry_exits.size()));
    }

    /**
     * Location of `new` statements for each Ptr (indexed in PtrList)
     */
    private final class NewLoc {
        public final HashMap<PtrID, TreeSet<Integer>> obj = new HashMap<>();

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

    private NewLoc getInitNewLoc() {
        var result = new NewLoc();
        for (var mth : allMethods.keySet()) {
            var ir = mth.getIR();
            for (var stmt : ir.getStmts()) {
                if (stmt instanceof New) {
                    var id = preprocess.obj_ids.get(stmt);
                    if (id != null) {
                        var ptr = glbPtrList.var2ptr(((New) stmt).getLValue());
                        if (ptr != null) {
                            var set = result.obj.getOrDefault(ptr, new TreeSet<>());
                            set.add(id);
                            result.obj.put(ptr, set);
                        }
                    }
                }
            }
        }
        return result;

    }

    public static final String ID = "pku-pta";
    private static final Logger logger = LogManager.getLogger(IRDumper.class);
    private final File dumpPath = new File("result.txt");
    private final PreprocessResult preprocess = new PreprocessResult();
    private final int maxLevel = 10;

    private final HashMap<JMethod, IRCFG> allMethods = new HashMap<>();
    private final PtrList glbPtrList = new PtrList();
    private final CFG glbCFG = new CFG();

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
                if (!method.isAbstract()) {
                    preprocess.analysis(method.getIR());
                    var className = method.getDeclaringClass().getName();
                    if (!(className.equals("benchmark.internal.Benchmark") ||
                            className.equals("benchmark.internal.BenchmarkN"))) {
                        allMethods.put(method, new IRCFG(method.getIR()));
                    }
                }
            });
        });
        // TODO: Init
        allMethods.keySet().forEach(method -> initGlbPtrList(method.getIR()));
        logger.info("PtrList:\n{}", glbPtrList.toString());
        var glbEntryExits = buildCFGEdges(main, null);
        completeGLbCFG(glbEntryExits);
        logger.info("CFG:\n{}", glbCFG.toString());
        var entry_out = getInitNewLoc();
        logger.info("Init NewLoc:\n{}", entry_out.tostr(glbPtrList));
        // TODO: Analysis
        // Trivial complement, avoid unsound
        var objs = new TreeSet<>(preprocess.obj_ids.values());
        preprocess.test_pts.forEach((test_id, pt) -> {
            if (!result.containsKey(test_id) || result.get(test_id).isEmpty()) {
                result.put(test_id, objs);
            }
        });
        dump(result);
        return result;
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
            return var.toString() + "@" + var.getMethod().getName();
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
            return base.toString() + "." + field.toString() + "@" + base.getMethod().getName();
        }
    }

    private class ArrayPtr implements Ptr {
        // TODO
    }

    /* ----------------------------------- CFG ---------------------------------- */

    private boolean isEssentialCall(String className, String mthName, int paramlen) {
        var is_benchmark = className.equals("benchmark.internal.Benchmark") ||
                className.equals("benchmark.internal.BenchmarkN");
        var is_test = is_benchmark && mthName.equals("test");
        // TODO: may be fault
        var is_no_param_init = mthName.equals("<init>") && paramlen == 0;
        return !is_test && !is_no_param_init;
    }

    private final class IRCFG {
        public final List<IRBB> bbs;
        public final Integer entry;
        public final TreeSet<Integer> exits;
        public final TreeMap<Integer, JMethod> calls;
        public final List<Set<Integer>> edges;
        public final List<Set<Integer>> revEdges;

        public IRCFG(IR ir) {
            bbs = getIRBBs(ir);
            entry = 0;
            exits = new TreeSet<>();
            calls = new TreeMap<>();
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
                } else if (stmt instanceof Invoke) {
                    var className = ((Invoke) stmt).getInvokeExp().getMethodRef().getDeclaringClass().getName();
                    var mthName = ((Invoke) stmt).getInvokeExp().getMethodRef().getName();
                    var paramlen = ((Invoke) stmt).getInvokeExp().getArgs().size();
                    if (isEssentialCall(className, mthName, paramlen)) {
                        // Only invoke of non-test, we mark as `call`
                        calls.put(i, ((Invoke) stmt).getInvokeExp().getMethodRef().resolve());
                    }
                    edges.get(i).add(i + 1);
                } else if (stmt instanceof Return) {
                    exits.add(i);
                } else {
                    edges.get(i).add(i + 1);
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

            logger.info("IRCFG @ {}", ir.getMethod().getName());
            for (var i = 0; i < n; i++) {
                logger.info("{}:", i);
                for (var j = bbs.get(i).from; j <= bbs.get(i).to; j++) {
                    logger.info("  {}", ir.getStmt(j));
                }
            }
            logger.info("Entry: {}", entry);
            logger.info("Exits: {}", exits.toString());
            logger.info("Calls: {}", calls.toString());
            for (var i = 0; i < n; i++) {
                logger.info("{} -> {}", i, edges.get(i).toString());
            }
            logger.info("\n");
        }

        public final int size() {
            return bbs.size();
        }

        @Override
        public String toString() {
            var s = "";
            for (var i = 0; i < bbs.size(); i++) {
                s += i + ": [" + bbs.get(i).from + "," + bbs.get(i).to
                        + "] <- " + revEdges.get(i).toString() + "\n";
            }
            return s;
        }
    }

    private final List<IRBB> getIRBBs(IR ir) {
        // unique
        var starter = new TreeSet<Integer>();
        var stmts = ir.getStmts();
        var n = stmts.size();
        // 0 is a starter
        starter.add(0);
        for (var i = 0; i < n; i++) {
            var stmt = stmts.get(i);
            if (stmt instanceof Return) {
                starter.add(i + 1);
            } else if (stmt instanceof JumpStmt) {
                // next stmt of a jump is a starter
                starter.add(i + 1);
                // every target is a starter
                var targets = ((JumpStmt) stmt).getTargets();
                targets.forEach(t -> starter.add(t.getIndex()));
            } else if (stmt instanceof Invoke) {
                var className = ((Invoke) stmt).getInvokeExp().getMethodRef().getDeclaringClass().getName();
                var mthName = ((Invoke) stmt).getInvokeExp().getMethodRef().getName();
                if ((className.equals("benchmark.internal.Benchmark") ||
                        className.equals("benchmark.internal.BenchmarkN"))
                        && mthName.equals("alloc")) {
                    // benchmark.alloc will not add starter
                    continue;
                }
                starter.add(i + 1);
            }
        }
        starter.add(n);
        var result = new ArrayList<IRBB>();
        var it = starter.stream().toList();
        for (var i = 0; i < it.size() - 1; i++) {
            // from starter to next starter form a basic block
            result.add(new IRBB(it.get(i), it.get(i + 1) - 1));
        }
        return result;
    }

    private final class IRBB {
        public final int from;
        public final int to;

        public IRBB(int from, int to) {
            this.from = from;
            this.to = to;
        }
    }

}
