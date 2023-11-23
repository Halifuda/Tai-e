package pku;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

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

    public static PtrList ptrList;
    public static NewLoc newLoc;
    
    public class PtrID extends Integer {
        public PtrID() {
            super();
        }
    }

    public class PtrCopy {
        public PtrID lval;
        public PtrID rval;
    }

    public class BB {
        public List<PtrCopy> ir;
        public NewLoc out;

        public BB(IR ir, int from, int to) {
        }

        public List<BB> invoke(LValue reciever, Var tis, RValue invokeExp) {
        }

        private List<PtrID> kill() {}

        public NewLoc calcOut(List<NewLoc> in) {}
        
        
    }

    public class CFG {
        public List<BB> bbs;
        public Map<Integer, List<Integer>> edges;
        public Map<Integer, List<Integer>> revEdges;

        public CFG(JMethod main) {
        }
    }

    // CONTENTS: (see readme-ayd.md)
    // - DATA STRUCTURES: helpers for analysis
    // - - MethodThings: method info
    // - - PtrList: list of pointers used in method
    // - - CopyRel: copy relationship between vars
    // - - Sumup: Method sumup
    // - - NewLoc: location of new statements
    //
    // - ANALYZER: analysis methods
    // - - analyze: main entry
    // - - collectTestResult: collect final result
    // from the MewLoc in each MethodThings
    // - - calcNewloc: calculate NewLoc in each method
    // by spreading through CopyRel
    // - - getPtrList: get PtrList of a method
    // - - sortMethods: sort methods in call order,
    // also do init work
    // - - analyzeMethod: analyze CopyRel in a method
    // by analyzing each BB, and merge them
    // - - analyzeBB: analyze CopyRel in a BB
    // - - mergeBB: merge CopyRel through control flow
    // - - sumupMethod: form sumup of a method
    // - - understandSumup: convert a Sumup in callee
    // to the corresponding CopyRel in caller
    // - - ptr_Callee2Caller: convert a ptr in callee
    // to the corresponding ptr in caller, HELPER
    // - - isNonLocal: check if a ptr is non-local, HELPER
    //
    // - POINTER DEFS: pointer definitions
    // - - Ptr: base class
    // - - VarPtr: individual var pointer
    // - - StaticFieldPtr: static field pointer
    // - - InstanceFieldPtr: instance field pointer
    // including its base var and field
    // - - ArrayPtr: array pointer (TODO)
    //
    // - CFG: control flow graph

    /* ----------------------------- DATA STRUCTURES ---------------------------- */

    private final HashMap<JMethod, Integer> methods = new HashMap<>();
    private final ArrayList<MethodThings> callOrder = new ArrayList<>();

    public MethodThings getThings(JMethod method) {
        if (methods.containsKey(method)) {
            return callOrder.get(methods.get(method));
        }
        return null;
    }

    private final class MethodThings {
        public boolean hasNew = false;
        public boolean hasTest = false;
        public IR ir = null;
        public Set<Var> returns = null;
        public SimpleCFG cfg = null;
        public PtrList ptrList = null;
        public Map<Integer, Integer> paramID = null;
        public ArrayList<CopyRel> copyList = null;
        public Sumup sumup = null;
        public NewLoc newloc = null;
    }

    private final class Sumup {
        // HashMap<Ptr, HashSet<Ptr>>
        // Note: we use -1 to represent local (anonymous) object
        public HashMap<Integer, HashSet<Integer>> obj = new HashMap<>();
    }

    private final class PtrList {
        public final HashMap<Var, Integer> varlist = new HashMap<>();
        public final HashMap<JField, Integer> sfieldlist = new HashMap<>();
        public final HashMap<Var, HashMap<JField, Integer>> ifieldlist = new HashMap<>();
        public final ArrayList<Ptr> ptrlist = new ArrayList<>();

        public Ptr ptr(int i) {
            return ptrlist.get(i);
        }

        /**
         * Convert a var to ptr index. -1 if not found.
         */
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

        public int ifield2ptr(Var base, JField field) {
            if (ifieldlist.containsKey(base) && ifieldlist.get(base).containsKey(field)) {
                return ifieldlist.get(base).get(field);
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

        public String ptr2str(int i) {
            return ptrlist.get(i).toString();
        }

        @Override
        public String toString() {
            var s = "";
            for (var i = 0; i < ptrlist.size(); i++) {
                s += i + ": " + ptr2str(i) + "\n";
            }
            return s;
        }
    }

    /**
     * Copy relationship (a = b) for each Ptr (indexed in PtrList)
     */
    private final class CopyRel {
        // Map<Ptr-ID-in-PtrList, Set<Ptr-ID-in-PtrList>>
        public final class Pair {
            public Integer first;
            public Integer second;
        }

        public List<Pair> copies; // 1:a=b, 2:a=c, 3:a=d, 4:d=e
        public Map<Ptr, HashSet<Integer>> copies_of_ptr; // a:[3], d:[4]

        public TreeSet<Stmt> a;
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
        // Analysis copy relationship
        sortMethods(main, 0);
        callOrder.forEach(this::analyzeMethod);
        // TODO: we need a global PtrList to handle cross-method benchmark
        callOrder.forEach(this::calcNewloc);
        // Calculate for each test
        callOrder.forEach(things -> collectTestResult(things, result));
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

    public void collectTestResult(MethodThings things, PointerAnalysisResult result) {
        // TODO: cross-method benchmark? i.e. alloc in A, test in B
        if (!things.hasTest) {
            return;
        }
        preprocess.test_pts.forEach((test_id, var) -> {
            var ptr = things.ptrList.var2ptr(var);
            if (ptr == -1)
                return;
            var set = things.newloc.obj.getOrDefault(ptr, new TreeSet<>());
            result.put(test_id, set);
        });
    }

    public void calcNewloc(MethodThings things) {
        // TODO: cross-method benchmark? i.e. alloc in A, test in B
        if (!things.hasNew) {
            return;
        }
        var newloc = new NewLoc();
        // Collect all benchmark alloc
        for (var stmt : things.ir.getStmts()) {
            if (stmt instanceof New) {
                var alloc = (New) stmt;
                if (!preprocess.obj_ids.containsKey(alloc))
                    continue;
                var id = preprocess.obj_ids.get(alloc);
                var ptr = things.ptrList.var2ptr(alloc.getLValue());
                if (ptr == -1)
                    continue;
                var set = newloc.obj.getOrDefault(ptr, new TreeSet<>());
                set.add(id);
                newloc.obj.put(ptr, set);
            }
        }
        if (newloc.obj.size() == 0) {
            return;
        }
        // Spread through copy relationship
        var copy = things.copyList.get(things.copyList.size() - 1);
        var modified = true;
        while (modified) {
            modified = false;
            for (var lhs : copy.obj.keySet()) {
                var rhs = copy.obj.get(lhs);
                var temp = new TreeSet<Integer>();
                for (var r : rhs) {
                    if (newloc.obj.containsKey(r)) {
                        var set = newloc.obj.get(r);
                        temp.addAll(set);
                    }
                }
                var set = newloc.obj.getOrDefault(lhs, new TreeSet<>());
                if (!set.containsAll(temp)) {
                    set.addAll(temp);
                    newloc.obj.put(lhs, set);
                    modified = true;
                }
            }
        }
        var sign = things.ir.getMethod().getName();
        logger.info("{}", "#".repeat(sign.length() + 13));
        logger.info("# NEWLOC @ {} #", sign);
        logger.info("{}", "#".repeat(sign.length() + 13));
        logger.info("{}", newloc.tostr(things.ptrList));
        logger.info("{}", "^".repeat(sign.length() + 13));
        things.newloc = newloc;
    }

    public void sortMethods(JMethod method, int level) {
        var things = new MethodThings();
        things.ir = method.getIR();
        things.returns = things.ir.getReturnVars().stream().collect(Collectors.toSet());
        things.cfg = new SimpleCFG(things.ir);
        things.ptrList = getPtrList(things.ir);
        things.paramID = new HashMap<>();
        var cnt = 0;
        for (var param : things.ir.getParams()) {
            things.paramID.put(things.ptrList.var2ptr(param), cnt++);
        }
        methods.put(method, 0);
        if (level < maxLevel) {
            // TODO: currently dynamic invoke is considered,
            // but the base var pointer of virtual invoke is not considered.
            var invokes = things.ir.invokes(true);
            invokes.forEach(invoke -> {
                var mth = invoke.getMethodRef().resolve();
                var className = mth.getDeclaringClass().getName();
                var methodName = mth.getName();
                // ignore benchmark invoke
                if (className.equals("benchmark.internal.Benchmark")
                        || className.equals("benchmark.internal.BenchmarkN")) {
                    if (methodName.equals("alloc")) {
                        things.hasNew = true;
                    } else if (methodName.equals("test")) {
                        things.hasTest = true;
                    }
                } else if (!methods.containsKey(mth)) {
                    sortMethods(mth, level + 1);
                }
            });
        }
        callOrder.add(things);
        methods.put(method, callOrder.size() - 1);
    }

    public void analyzeMethod(MethodThings things) {
        if (things == null) {
            return;
        }
        var ir = things.ir;
        var cfg = things.cfg;
        var ptrList = things.ptrList;

        var sign = ir.getMethod().getSignature();
        logger.info("{}", "#".repeat(sign.length() + 4));
        logger.info("# {} #", sign);
        logger.info("{}", "#".repeat(sign.length() + 4));
        logger.info("IR:");
        ir.stmts().forEach(stmt -> logger.info("{}: {}", stmt.getIndex(), stmt.toString()));
        logger.info("\nCFG: \n{}", cfg.toString());
        logger.info("PtrList: \n{}", ptrList.toString());

        var copyList = new ArrayList<CopyRel>(cfg.size());
        // Analyze each single BB
        cfg.bbs.forEach(bb -> copyList.add(analyzeBB(things, bb)));

        logger.info("Individual BB results:");
        for (var i = 0; i < cfg.size(); i++) {
            logger.info("BB{}: {}", i, copyList.get(i).tostr(ptrList));
        }
        logger.info("\n");

        // Merge copy relationship through control flow
        mergeBB(cfg, copyList);

        logger.info("Merged BB results:");
        for (var i = 0; i < cfg.size(); i++) {
            logger.info("BB{}: {}", i, copyList.get(i).tostr(ptrList));
        }

        logger.info("{}", "^".repeat(sign.length() + 4));

        things.copyList = copyList;
        // Form sumup
        things.sumup = sumupMethod(things);
    }

    /**
     * Is a pointer in a method is non-local, i.e. params, returns, %this
     * and all fields of these (including any static fields).
     */
    public boolean isNonLocal(int ptr, MethodThings things) {
        var pptr = things.ptrList.ptr(ptr);
        if (pptr instanceof VarPtr) {
            var inner = ((VarPtr) pptr).var;
            if (things.ir.isThisOrParam(inner) || things.returns.contains(inner)) {
                return true;
            }
        } else if (pptr instanceof InstanceFieldPtr) {
            var inner = ((InstanceFieldPtr) pptr).base;
            if (things.ir.isThisOrParam(inner) || things.returns.contains(inner)) {
                return true;
            }
        } else if (pptr instanceof StaticFieldPtr) {
            // Static is always non-local
            return true;
        }
        return false;
    }

    public Sumup sumupMethod(MethodThings things) {
        var sumup = new Sumup();
        // interest in the last BB (EXIT) only
        var copy = things.copyList.get(things.copyList.size() - 1).obj;
        copy.forEach((lhs, rhs) -> {
            if (isNonLocal(lhs, things)) {
                var set = sumup.obj.getOrDefault(lhs, new HashSet<>());
                for (var r : rhs) {
                    if (isNonLocal(r, things)) {
                        set.add(r);
                    } else {
                        // TODO: if benchmark is cross methods, may need change
                        // TODO: means, non-local should include benchmark.alloc
                        set.add(-1);
                    }
                }
                sumup.obj.put(lhs, set);
            }
        });
        return sumup;
    }

    public void mergeBB(SimpleCFG cfg, List<CopyRel> copyList) {
        // TODO: is this method correct?
        var modified = true;
        while (modified) {
            modified = false;
            for (var i = 0; i < cfg.size(); i++) {
                var bb = cfg.bbs.get(i);
                var copy = copyList.get(i);
                var temp = new CopyRel();
                for (var prevbb : cfg.revEdges.get(i)) {
                    var prevcopy = copyList.get(prevbb);
                    for (var lhs : prevcopy.obj.keySet()) {
                        var rhs = prevcopy.obj.get(lhs);
                        // avoid overwrite when merging control flow (functioning KILL)
                        if (!copy.obj.containsKey(lhs)) {
                            var update = temp.obj.getOrDefault(lhs, new HashSet<>());
                            update.addAll(rhs);
                            temp.obj.put(lhs, update);
                            modified = true;
                        }
                    }
                }
                copy.obj.putAll(temp.obj);
            }
        }

        // TODO: IN is not considered
        // BB1: a = b IN
        // BB2: a = c KILL, OUT
    }
    // We know all OUT
    public CopyRel analyzeBB(MethodThings things, BasicBlock bb) {
        var ir = things.ir;
        var ptrlist = things.ptrList;
        var copyRel = new CopyRel();
        for (var i = bb.from; i <= bb.to; i++) {
            var stmt = ir.getStmt(i);
            if (stmt instanceof Copy) {
                var copy = (Copy) stmt;
                var lhs = ptrlist.var2ptr(copy.getLValue());
                var rhs = ptrlist.var2ptr(copy.getRValue());
                // overwrite the relationship on serialized control flow
                if (!copy.getRValue().isConst()) {
                    var set = new HashSet<Integer>();
                    set.add(rhs);
                    copyRel.obj.put(lhs, set);
                }
            }

            if (stmt instanceof LoadField) {
                var load = (LoadField) stmt;
                var lhs = ptrlist.var2ptr(load.getLValue());
                var rhs = ptrlist.faccess2ptr(load.getRValue());
                var set = new HashSet<Integer>();
                set.add(rhs);
                copyRel.obj.put(lhs, set);
            }
            if (stmt instanceof StoreField) {
                var store = (StoreField) stmt;
                var lhs = ptrlist.faccess2ptr(store.getLValue());
                var rhs = ptrlist.var2ptr(store.getRValue());
                if (!store.getRValue().isConst()) {
                    var set = new HashSet<Integer>();
                    set.add(rhs);
                    copyRel.obj.put(lhs, set);
                }
            }
            if (stmt instanceof Invoke) {
                var invoke = (Invoke) stmt;
                var mth = invoke.getMethodRef().resolve();
                var callee = getThings(mth);
                if (callee == null) {
                    // not sumup yet, ignore
                    // TODO
                    continue;
                }

                var exp = invoke.getInvokeExp();
                var args = exp.getArgs();
                var recv = invoke.getLValue();
                var tis = (Var) null;
                if (exp instanceof InvokeInstanceExp) {
                    tis = ((InvokeInstanceExp) exp).getBase();
                }
                CopyRel sumup = understandSumup(args, tis, recv, things, callee);
                sumup.obj.forEach((lhs, rhs) -> {
                    // overwrite
                    copyRel.obj.put(lhs, rhs);
                });
            }
        }
        // Spread through field
        // If (1) a.f, b.f are all Ptr; (2) a.f is not recorded in copyRel,
        // i.e., there is no Stmt overwrites it; (3) we know a = b,
        // then, we add a.f = b.f.
        // TODO: here or after Copt Stmt?
        for (var a : things.ptrList.ifieldlist.keySet()) {
            for (var f : things.ptrList.ifieldlist.get(a).keySet()) {
                var aptr = things.ptrList.var2ptr(a);
                var afptr = things.ptrList.ifield2ptr(a, f);
                if (copyRel.obj.containsKey(aptr) && !copyRel.obj.containsKey(afptr)) {
                    var set = new HashSet<Integer>();
                    for (var bptr : copyRel.obj.get(aptr)) {
                        if (!(things.ptrList.ptr(bptr) instanceof VarPtr))
                            continue;
                        var b = ((VarPtr) things.ptrList.ptr(bptr)).var;
                        var bfptr = things.ptrList.ifield2ptr(b, f);
                        if (bfptr != -1) {
                            set.add(bfptr);
                        }
                    }
                    copyRel.obj.put(afptr, set);
                }

            }
        }
        // Spread through all ptr (iteratively)
        // TODO: order? e.g., (a = b, b = c, a != c)
        var modified = true;
        while (modified) {
            modified = false;
            for (var lhs : copyRel.obj.keySet()) {
                var rhs = copyRel.obj.get(lhs);
                var temp = new HashSet<Integer>();
                for (var r : rhs) {
                    if (copyRel.obj.containsKey(r)) {
                        temp.addAll(copyRel.obj.get(r));
                    }
                }
                if (!rhs.containsAll(temp)) {
                    rhs.addAll(temp);
                    copyRel.obj.put(lhs, rhs);
                    modified = true;
                }
            }
        }
        return copyRel;
    }

    /**
     * Convert a ptr in callee to the corresponding ptr in caller.
     * Only care about the param-return passing. If the callee-ptr
     * is none of param, return, %this or any field of these, return -1.
     * If the ptr is not in the caller, add it to the ptrList.
     */
    public Integer ptr_Callee2Caller(
            int ptr,
            List<Var> args, Var tis, Var recv, MethodThings caller, MethodThings callee) {
        if (ptr == -1)
            return -1;
        Ptr callee_ptr = callee.ptrList.ptr(ptr);
        Var base = null;
        JField field = null;
        if (callee_ptr instanceof VarPtr) {
            base = ((VarPtr) callee_ptr).var;
        } else if (callee_ptr instanceof InstanceFieldPtr) {
            base = ((InstanceFieldPtr) callee_ptr).base;
            field = ((InstanceFieldPtr) callee_ptr).field;
        } else if (callee_ptr instanceof StaticFieldPtr) {
            field = ((StaticFieldPtr) callee_ptr).field;
        }
        // Find if base exist
        Var caller_base = null;
        int caller_base_ptr = -1;
        if (callee.ir.isParam(base)) {
            int id = callee.paramID.get(callee.ptrList.var2ptr(base));
            caller_base = args.get(id);
            caller_base_ptr = caller.ptrList.var2ptr(caller_base);
        } else if (callee.ir.isThisOrParam(base)) {
            caller_base = tis;
            caller_base_ptr = tis != null ? caller.ptrList.var2ptr(tis) : -1;
        } else if (callee.returns.contains(base)) {
            caller_base = recv;
            caller_base_ptr = recv != null ? caller.ptrList.var2ptr(recv) : -1;
        }
        // return
        if (caller_base_ptr == -1 && field == null) {
            return -1;
        } else if (caller_base_ptr == -1) /* Static field */ {
            int sf = caller.ptrList.sfield2ptr(field);
            if (sf == -1) {
                caller.ptrList.ptrlist.add(new StaticFieldPtr(field));
                sf = caller.ptrList.ptrlist.size() - 1;
                caller.ptrList.sfieldlist.put(field, sf);
            }
            return sf;
        } else if (field == null) /* Var */ {
            return caller_base_ptr;
        } else /* Instance field */ {
            var fields = caller.ptrList.ifieldlist.getOrDefault(caller_base, new HashMap<>());
            int ifield = fields.getOrDefault(field, -1);
            if (ifield == -1) {
                /*
                 * if callee uses a.f, but caller doesnot use a.f explitly,
                 * then we add a Ptr of a.f to caller's PtrList
                 */
                caller.ptrList.ptrlist.add(new InstanceFieldPtr(caller_base, field));
                ifield = caller.ptrList.ptrlist.size() - 1;
                fields.put(field, ifield);
                caller.ptrList.ifieldlist.put(caller_base, fields);
            }
            return ifield;
        }
    }

    /**
     * Return a CopyRel of the param, return, %this and any field of these.
     * This is used for caller to understand the callee without recursivly invoke.
     */
    public CopyRel understandSumup(
            List<Var> args, Var tis, Var recv, MethodThings caller, MethodThings callee) {
        var copy = new CopyRel();
        var callee_sumup = callee.sumup;
        for (var lhs : callee_sumup.obj.keySet()) {
            var lhs_caller = ptr_Callee2Caller(lhs, args, tis, recv, caller, callee);
            if (lhs_caller == -1)
                continue;
            for (var r : callee_sumup.obj.get(lhs)) {
                var r_caller = ptr_Callee2Caller(r, args, tis, recv, caller, callee);
                if (r_caller == -1)
                    continue;
                var set = copy.obj.getOrDefault(lhs_caller, new HashSet<>());
                set.add(r_caller);
                copy.obj.put(lhs_caller, set);
            }
        }
        return copy;
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
            if (v.isConst())
                continue;
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
