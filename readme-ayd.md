# PKU-PTA

## step 1: 调用图

这里为了方便，上下文敏感不考虑循环调用（例如递归）的情况，这样调用图实际上可以变成调用树。从 `main` 开始，对所有 `Invoke` 进行后序遍历，可以得到调用树上的一个拓扑排序。

数据结构上，用一个 `Map<JMethod, Integer>` 保存所有已找到的方法，然后用一个 `List<MethodThings>` 保存拓扑排序和后续会用到的信息。map 建立了方法到排序的映射。

## step 2: 方法摘要（Sumup）

### step 2.1: 控制流图（CFG）

此处，为了应对一些流敏感的情况（主要是包括了多次对同一个指针赋值造成的覆盖），我们对方法建立控制流图。此处我们只考虑简单的控制流，即不考虑 `invoke` 带来的控制流变化。

### step 2.2: 拷贝关系（Copy relationship）

对每个方法都确定出是否存在指针间拷贝关系：`{a = [b, ...]}`，即 `a` 可能被 `[b, ...]` 赋值。

原理上来说，在每个控制流的基本块中，考察本基本块的 GEN 和 KILL，然后在基本块之间求解。

实际上为了简化实现，各基本块通过一次对 ir 的遍历确定，而基本块间则通过一个简单的迭代方法计算。

### step 2.3: 方法摘要

在某方法算出拷贝关系后，我们对 EXIT 处的，关于入参（包括 `this`）的拷贝关系进行摘要。所有与入参有关的拷贝关系（入参在左侧）会形成摘要表。

当在 step 2.2 的基本块中遇到 `Invoke` 时，直接使用拷贝关系，而不触发递归调用。通过 step 1 的调用图，我们可以确保在无循环引用的情况下，所有方法此时都已经获得摘要了。

## step 3: 指针分析

在 step 1 顺便记录哪些方法有 `benchmark`，此时直接将该方法的拷贝关系找出，然后通过迭代计算即可求解。


## 代码目录
- **数据结构**: 分析中用到的数据结构，记录信息用
- - `MethodThings`: 方法的所有信息
- - `PtrList`: 方法所使用到的所有指针（见下文），包括变量、静态 field 和实例 field
- - `CopyRel`: 一个方法中各个指针之间的拷贝关系，单向的（a=b 不代表 b=a）
- - `Sumup`: 方法的摘要，大约为从 `CopyRel` 中去除所有内部临时变量之后得到的情况，可以帮助外部调用者获得 `CopyRel`
- - `NewLoc`: 方法中每个指针的 alloc 位置，约等于分析结果
- **分析方法**: 一大堆方法，互相调用
- - `analyze`: 分析器的入口
- - `collectTestResult`: 从每个方法的 `NewLoc` 中获得分析结果
- - `calcNewloc`: 给每个方法计算 `NewLoc` （通过 `CopyRel`）
- - `getPtrList`: 获取每个方法的 `PtrList` ，初始化的一部分
- - `sortMethods`: 把方法按照调用树的后序遍历排序，并执行初始化
- - `analyzeMethod`: 分析出每个方法的 `CopyRel`
- - `analyzeBB`: 给每个基本块（BB）分析 `CopyRel`
- - `mergeBB`: 合并基本块之间的 `CopyRel`
- - `sumupMethod`: 给方法算出 `Sumup`
- - `understandSumup`: 在基本块中遇到 `Invoke` 时通过摘要计算 `CopyRel`
- - `ptr_Callee2Caller`: HELPER，把 Callee 的指针转成 Caller 的指针，如果没有就添加进去
- - `isNonLocal`: HELPER，确定一个 Callee 的指针不是内部临时变量
- **指针**:
- - `Ptr`: 基类
- - `VarPtr`: 变量
- - `StaticFieldPtr`: 静态字段（A::f1）
- - `InstanceFieldPtr`: 实例字段（a.f2），记录实例（a）和字段信息（f2）
- - `ArrayPtr`: 数组内部指针（TODO）
- **CFG**: 简易控制流图

## 数据结构解释

- `PtrList`:
- - 通常来说 `Ptr` 是用它在 `PtrList` 中的 ID 表示的，所以代码里通常是用 `Integer` 或者 `int`。只有当考虑到域敏感，需要区分究竟是变量还是域的时候，才会用到 `Ptr` 本身，然后用类似 `Ptr instanceof VarPtr` 这样的代码来 dispatch。
- - `HashMap<Var, Integer> varlist`: 纯变量。建立从 `Var` 到指针 ID 的映射。
- - `HashMap<JField, Integer> sfield`: 静态域。
- - `HashMap<Var, HashMap<JField, Integer>>`: 实例域。每个实例都可能有一些域是指针。

- `CopyRel`:
- - 指针之间的拷贝关系。具体有何作用见下文。
- - `HashMap<Integer, HashSet<Integer>> obj`: 拷贝关系，表示 `a = [b,c,...]`。这里的 `Integer` 都是 `PtrList` 中的指针 ID。

- `NewLoc`:
- - 记录每个指针是在何处分配的。
- - `HashMap<Integer, TreeSet<Integer>> obj`: 表示指针 `a` 可能在 `[1,2,...]` 处分配。第一个 `Integer` 是指针 ID，第二个是 `Benchmark.alloc` 的位置。

- `Sumup`:
- - 摘要。结构上约等于 `CopyRel`。
- - 指针 ID 用 -1 表示一个伪关系（用法见后文）。

- `MethodThings`:
- - `hasNew`: 方法里有 `Benchmark.alloc`。
- - `hasTest`: 有 `Benchmark.test`。
- - `IR ir`: 方法的 IR。
- - `Set<Var> returns`: 所有返回的变量。
- - `SimpleCFG cfg`: 控制流图。
- - `PtrList ptrList`: 方法用到的指针集合。
- - `Map<Integer, Integer> paramID`: 建立一个指针 ID 到参数位置的映射，方便 `understandSumup`。
- - `ArrayList<CopyRel> copyList`: 控制流图中每个基本块的 `CopyRel`。分析结束后，最后一个相当于方法的 OUT。
- - `Sumup sumup`: 摘要。
- - `NewLoc newloc`: 分配位置。

## 方法解释

- `HashMap<JMethod, Integer> methods`: 所有需要分析的方法。
- `ArrayList<MethodThings> callOrder`: 按照调用图拓扑排序好的所有方法。`methods` 保存了方法到排序的映射。

- `analyze`: 
- - 先进行预处理，参见 trivial 的实现，主要是把所有 benchmark alloc 和 test 找到。
- - 调用 `sortMethods`，把方法拓扑排序，这样，后被调用的方法先分析，就确保（无循环调用时），所有 `Invoke` 都可以获得可用的摘要，避免递归分析。当然这个方法也会做一些初始化。
- - 调用 `analyzeMethod`，给每个方法算出指针间的拷贝关系 `CopyRel`。
- - 调用 `calcNewloc`，给每个方法的指针算出其分配的位置 `NewLoc`。
- - 调用 `collectTestResult`，获得分析结果。
- - 通过 trivial 的方法把没分析出来但是测试到的都补齐防止 unsound。

- `sortMethods`:
- - 首先初始化一些 `MethodThings` 中无需在控制流图上分析的内容（例如所有指针的集合）。
- - 找到所有 `Invoke`。如果调用的方法此前没有遇到过，就递归地 sort。遇到过说明发生了循环调用，就不考虑了。

- `analyzeMethod`:
- - 通过控制流图，先用 `analyzeBB` 给每个基本块内部计算 `CopyRel`。
- - 再调用 `mregeBB`，通过数据流分析的标准方法把基本块之间的 `CopyRel` 沿控制流传递、合并。
- - 最后通过 `sumupMethod` 获得摘要。

- `analyzeBB`:
- - 遍历 BB 中 IR 的每个 `Stmt`，把 `Copy(a=b)`、`LoadField(a=b.f)`、`StoreField(a.f=b)` 三种语句构造的拷贝关系记录。
- - 沿着语句顺序，后面的语句会覆盖前面的语句（基本块内不考虑跳转）。
- - 遇到 `Invoke`，则通过 `understandSumup` 理解函数摘要，然后添加到拷贝关系里。特殊的，如果函数会修改一些不在 `ptrList` 里的内容（主要是各种没有在本方法用到的 field），就添加到 `ptrList` 里。
- - 这样计算完后，在 field 之间传递关系。对所有如下情况：(1) `a.f` 和 `b.f` 都是指针；(2) `a.f` 没有任何拷贝关系，即没有语句对它的拷贝关系进行覆盖；(3) `a=b` 已知。此时将 `a.f=b.f` 添加到拷贝关系里。
- - 这里不考虑 nested field （比如 `a.f=b.f.f`），因为这类语句在 IR 中会通过各种中间变量衔接。
- - 最后，在所有拷贝关系中传递。因为拷贝关系虽然不对称但是传递（`a=b, b=c => a=c`），所以这里用迭代的方式把关系全部传递。

- `mergeBB`:
- - 在控制流图上进行传递和合并。
- - 如果 BB1 -> BB2，就把 BB1 中存在，但 BB2 中不存在的关系放到 BB2 里。注意 BB2 会覆盖 BB1。
- - 对于合并控制流的情况，就把关系集合合并即可。
- - 经过 merge，每个方法的 OUT 关系就是最后一个 BB 的 `CopyRel`。

- `sumupMethod`:
- - 找到方法的 OUT （最后一个 BB 的 `CopyRel`）。
- - 对每一条关系 `a=b`，如果两个都不是局部临时变量，就保留这条关系。如果左边不是但右边是临时，就保留一个伪关系（`a=null`），表示左边被覆盖了。如果左边是临时变量，则删掉这条关系。
- - 最终得到 `Sumup`。

- `understandSumup`:
- - `analyzeBB` 遇到 `Invoke` 语句时就调用这个方法。
- - `analyzeBB` 会把函数调用的传参、this 指针和返回值接收者传递给此方法。通过 `Sumup` 中的关系，在这些值之间建立新的 `CopyRel`。
- - 通过 `ptr_Callee2Caller` 转换。如果某个关系中存在 field，例如 `a.f` ，而 `a` 属于 Caller 的指针，但 `a.f` 不属于 Caller 的指针（Caller 没有用到这个），为了域敏感，会把 `a.f` 添加到 Caller 的 `ptrList` 里。
