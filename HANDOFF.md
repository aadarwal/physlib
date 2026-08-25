# S6 lane handoff — signal-flow graphs and Mason's gain formula

Branch: `optics/s6-sfg-mason` (branched off `optics/development` at `fcc9b85d`, which carries the
merged S5 slices 1-4).
Home: `Physlib/Mathematics/SignalFlowGraph/` — neutral mathematics, **no** `Physlib/Optics`
import.
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s5-ztransform` (reused; the
`.lake/packages` symlink to the main repo is unchanged).

The conductor owns `optics/development`, `Physlib.lean`, `Physlib/Optics/API-map.yaml`,
`goal.md`, and `tbd.md`. This lane edits none of them.

The S6 exit theorem — agreement of Mason's gain with the N5 netlist semantics — is the
conductor's, not this lane's. Slice 5 leaves it a clean hook and attempts nothing beyond that.

---

## Slice status

| Slice | Content | Status |
|---|---|---|
| 1 | Structure and node-equation semantics; unique solvability; gain as an inverse entry | **done** |
| 2 | Paths, loops, non-touching loop families, the graph determinant and cofactors | **done** |
| 3 | Mason's theorem, and `Δ = det (1 - G)` | **done**, with the forward-path half of the numerator explicitly withheld |
| 4 | Regressions: single loop, two non-touching loops, the touching case, `Δ = 0` | **done**, delivered with slice 3 |
| 5 | `ofCoefficientMatrix` hook, plus the edge-indexed multigraph structure with `toMatrix` | **done** |
| 7 | Mason's formula in general | **done** in loop-family form |
| 7b | Forward-path repackaging of the numerator | **done** — Mason's rule closed in its classical form |
| 6 | Edge-based enumeration closing regression G-02 by proof | **done** |
| 8 | Reviewer fixes, distinguished terminals, definition-level G-01/G-03 regressions | **in progress** |

---

## Slice 1 — files

- `Physlib/Mathematics/SignalFlowGraph/Basic.lean` (174 lines)
- `Physlib/Mathematics/SignalFlowGraph/BasicRegression.lean` (119 lines)

### Registrations needed in `Physlib.lean`

```
public import Physlib.Mathematics.SignalFlowGraph.Basic
public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
```

### Slice 1 — declarations

`Physlib/Mathematics/SignalFlowGraph/Basic.lean`, namespace `Physlib.SignalFlowGraph`:

**A. The node equation** — `IsNodeSolution`, `systemMatrix`, `isNodeSolution_iff`,
`isNodeSolution_zero`.

**B. Unique solvability** — `nodeSolution`, `isNodeSolution_nodeSolution`, `eq_nodeSolution`,
`existsUnique_isNodeSolution`, `existsUnique_isNodeSolution_iff`.

**C. Gain between two nodes** — `gain`, `gain_eq_nodeSolution`, `nodeSolution_eq_sum_gain`.

`Physlib/Mathematics/SignalFlowGraph/BasicRegression.lean`, same namespace: `twoNodeLoop`,
`systemMatrix_twoNodeLoop`, `det_systemMatrix_twoNodeLoop`, `gain_twoNodeLoop`,
`det_systemMatrix_twoNodeLoop_one`, `not_existsUnique_twoNodeLoop_one`,
`isNodeSolution_twoNodeLoop_one_ones`.

### What slice 1 proves

- `existsUnique_isNodeSolution_iff` is an **iff**, both directions proved. Unique solvability for
  every input is exactly invertibility of `1 - G`. The reverse direction is the one that matters:
  a singular system matrix annihilates some nonzero vector, so the zero input already has two
  solutions. The criterion is therefore not merely sufficient, and every nonvanishing hypothesis
  in the later files is load-bearing rather than convenient.
- `gain G s t` is the `(t, s)` entry of `(1 - G)⁻¹`, and `gain_eq_nodeSolution` proves that this
  is the sink signal driven by a unit injection at the source, so the definition is not a
  convention.
- `nodeSolution_eq_sum_gain` is superposition: the response to an arbitrary input is the
  input-weighted sum of the pairwise gains.

The regression computes the two-node feedback gain `a / (1 - a * b)` **from the matrix inverse
alone**, deliberately not from Mason's formula. Slice 4 will derive the same value from paths and
loops, so the two routes can be compared rather than one restating the other. And
`not_existsUnique_twoNodeLoop_one` exhibits unit loop gain as a concrete failure of unique
solvability, with `isNodeSolution_twoNodeLoop_one_ones` naming the second solution explicitly.

### A gap in coverage that the controller should rule on

`goal.md` section H.4 S6 opens with "finite directed weighted **multigraph** with distinguished
input/output nodes and explicit edge identity, so parallel paths are not collapsed", requires the
topology to be "independent of whether a symbolic or evaluated edge weight happens to be zero",
and closes with "A simple digraph that collapses parallel edges does not meet this milestone".
Regression row G-02 of section I.3 is "distinct parallel branches remain distinct in compilation
and Mason enumeration".

A gain **matrix** does not meet that. `G i j` records only the total gain from `j` to `i`, so two
parallel edges are indistinguishable from one edge carrying their sum, and an edge whose gain
happens to be zero is indistinguishable from an absent edge.

I am proceeding with the matrix representation anyway, because the lane brief specifies it and
because slice 3's proof route — the Leibniz expansion of `det (1 - G)`, whose permutation cycle
decompositions are the vertex-disjoint loop families — is inherently a node-level and matrix-level
argument. The matrix layer is what satisfies the "node-equation semantics and adjacency matrix"
and "equality with the corresponding entry of `(1 - A)⁻¹`" bullets of S6, and it is what the later
Mason theorem is about. The non-claim is stated in the module doc rather than left implicit.

Closing the gap needs an **edge-indexed layer above this one**: a structure carrying
`source, target : E → ι` and `gain : E → ℂ` for a finite edge type `E`, with an adjacency map
summing parallel gains into this file's `G`. That layer would satisfy the multigraph and
zero-weight-independence bullets cheaply. Making the *enumeration* in slices 2 and 3 edge-based
rather than node-based, which is what regression G-02 actually demands, is a larger change and
would not compose with the determinant route.

**Decided by the controller on 2026-08-25.** The matrix route stays. Slice 5 adds the
edge-indexed structure with `toMatrix`, closing the representation and zero-weight-independence
bullets. A further optional slice 6 closes regression G-02 **by proof** rather than by
representation: edge-based enumeration of forward paths and simple loops over the multigraph,
where edge identity distinguishes parallel paths and loops, together with the theorem that the
edge-based sums equal the matrix-level ones. Mason then holds edge-based as a corollary of the
matrix theorem. Slice 6 is attempted only after 2-5 land cleanly; if disproportionate, the
representation ships and the G-02 residual is stated exactly.

---

## Slice 2 — files

- `Physlib/Mathematics/SignalFlowGraph/Combinatorics.lean` (273 lines)
- `Physlib/Mathematics/SignalFlowGraph/CombinatoricsRegression.lean` (124 lines)

### Registrations needed in `Physlib.lean` (cumulative, all four)

```
public import Physlib.Mathematics.SignalFlowGraph.Basic
public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Combinatorics
public import Physlib.Mathematics.SignalFlowGraph.CombinatoricsRegression
```

### Slice 2 — declarations

`Physlib/Mathematics/SignalFlowGraph/Combinatorics.lean`, namespace `Physlib.SignalFlowGraph`:

**A. Non-touching loop families** — `loopFamilies`, `mem_loopFamilies`, `one_mem_loopFamilies`,
`loopFamilies_empty`, `loopCount`, `loopCount_one`, `familyGain`, `familyGain_empty`.

**B. The graph determinant** — `graphDetOn`, `graphDet`, `graphDetOn_empty`.

**C. Forward paths** — `listsLen`, `mem_listsLen_iff`, `nodupLists`, `mem_nodupLists_iff`,
`forwardPaths`, `mem_forwardPaths_iff`, `singleton_mem_forwardPaths`,
`nil_notMem_forwardPaths`.

**D. Path gains, cofactors, and Mason's quotient** — `pathGain`, `pathGain_nil`,
`pathGain_singleton`, `pathGain_cons_cons`, `pathCofactor`, `masonNumerator`, `masonGain`.

`Physlib/Mathematics/SignalFlowGraph/CombinatoricsRegression.lean`, same namespace:
`forwardPaths_fin_three`, `forwardPaths_fin_two`, `forwardPaths_self_fin_two`,
`pathGain_fin_three`, `pathCofactor_spanning`, `pathCofactor_direct`,
`masonNumerator_twoNodeLoop`.

### The encoding choice that makes "non-touching" structural

A family of pairwise non-touching loops on a vertex set `T` is carried by a **permutation** of the
node type whose support is contained in `T`. This is exact, not merely convenient:

- the cycles of a permutation are automatically vertex-disjoint, so **"pairwise non-touching" is a
  property of the representation rather than a side condition anyone has to check**;
- the vertices of `T` that the permutation fixes are precisely the self-loops of the family;
- so `loopCount T σ = (T.card - σ.support.card) + Multiset.card σ.cycleType` counts self-loops
  plus nontrivial cycles.

Unwinding `graphDetOn` on a two-element vertex set gives `G i i * G j j - G j i * G i j`, that is
the product of two non-touching self-loop gains minus the two-cycle gain, which is the expected
second-order Mason term. This encoding is also what makes slice 3 provable: the Leibniz expansion
of `det (1 - G)` sums over permutations, and their cycle decompositions are exactly these
families.

### Executable enumeration, and a real obstacle overcome

`goal.md` section H.4 S6 demands "executable and proved-correct enumeration". The first attempt
enumerated each vertex subset's orderings with `Finset.toList` and `List.permutations`. That is
mathematically fine but **does not evaluate**: `Multiset.toList` is `noncomputable` in Mathlib, so
`decide` got stuck on it and no example could be settled by evaluation.

The shipped enumeration instead builds node lists by recursion on a length bound
(`listsLen`) and filters for repetition-freeness (`nodupLists`), using no choice. The length bound
loses nothing because a repetition-free list over a finite node type is no longer than the node
count (`List.Nodup.length_le_card`). `mem_listsLen_iff` and `mem_nodupLists_iff` prove the
enumeration correct, and the regression file settles `forwardPaths (0 : Fin 3) 2 = {[0,2],
[0,1,2]}` and its two-node analogues **by `decide`** — evaluation, not argument.

A consequence worth recording: the file no longer uses a blanket `noncomputable section`. The
complex-valued definitions carry `noncomputable` individually and the enumeration is left
computable, which is what makes `decide` available.

### Slice 2 — regressions and what each detects

- `forwardPaths_fin_three`, `forwardPaths_fin_two`, `forwardPaths_self_fin_two`: the enumeration
  evaluated. The self-path case pins that a node is joined to itself by the trivial one-node path
  alone, which is what gives the correct unit gain in Mason's formula.
- `pathGain_fin_three`: the two-hop gain is `G 1 0 * G 2 1`, which fixes the reading direction of
  each edge (from tail to head) and would fail under a transposed convention.
- `pathCofactor_spanning` and `pathCofactor_direct`: a path visiting every node has unit cofactor,
  and the direct hop on three nodes leaves exactly the middle vertex. Together these fix the
  **orientation** of the cofactor, which is otherwise easy to define as the determinant of the
  vertices the path *does* touch.
- `masonNumerator_twoNodeLoop`: the numerator for the two-node feedback graph is `a`. Slice 3 or 4
  divides it by the graph determinant and meets slice 1's independently computed
  `gain_twoNodeLoop = a / (1 - a * b)`.

### Slice 2 gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all four
files; the Batteries declaration linter set run module-scoped over all four modules passes; the
`module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal
(`Mathlib.GroupTheory.Perm.Cycle.Type` and `Mathlib.Data.Fintype.Card` were transitively
available through `Basic` and were dropped).

One linter finding was acted on rather than suppressed: `simpNF` reported that a
`loopCount_empty_one` simp lemma was derivable from `loopCount_one` and `Finset.card_empty`, so
the lemma was deleted and its single use inlined.

### Parity classification for slice 2

**Parity of coverage, with a representational difference, against ledger row IP-21.** FMICS'15
Definitions 1-4 (pp. 167-168) supply an SFG type, executable elementary-circuit and
forward-circuit enumeration, and Mason's gain as a quotient; SFG-TR'14 and NSV'16 Definition 6
(p. 37) do the same. This slice supplies the same objects with the same executability, and adds a
determinant defined directly as the alternating sum over families, which the sources define only
through their enumeration.

The representational difference is the one already recorded: the sources carry loops and paths as
**branch** lists, so parallel edges stay distinct; here they are node-level, so they do not.
Slices 5 and 6 address that, and until slice 6 lands regression row G-02 is **not** met. The
module doc says so.

---

## Slices 3 and 4 — files

- `Physlib/Mathematics/SignalFlowGraph/Mason.lean` (225 lines)
- `Physlib/Mathematics/SignalFlowGraph/MasonRegression.lean` (162 lines)

Slice 4 is delivered in the same commit as slice 3 because its regressions are what discharge the
part of Mason's formula that slice 3 does not prove in general.

### Registrations needed in `Physlib.lean` (cumulative, all six)

```
public import Physlib.Mathematics.SignalFlowGraph.Basic
public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Combinatorics
public import Physlib.Mathematics.SignalFlowGraph.CombinatoricsRegression
public import Physlib.Mathematics.SignalFlowGraph.Mason
public import Physlib.Mathematics.SignalFlowGraph.MasonRegression
```

### What is proved in general

**`graphDet_eq_det` : `graphDet G = (systemMatrix G).det`.** The alternating sum over families of
pairwise non-touching loops **is** `det (1 - G)`, for every finite node type and every gain
matrix. No hypothesis. This is the denominator half of Mason's formula and the "graph determinant"
bullet of `goal.md` section H.4 S6, and it is the theorem the whole lane is built to support.

The proof is the Leibniz expansion read correctly. Each factor of `∏ i, (1 - G) (σ i) i` splits
into an identity part and a gain part; `Fintype.prod_add` turns one permutation into a sum over
vertex sets; the identity part contributes `1` exactly when the permutation is supported inside
the chosen set (`prod_one_compl`) and `0` otherwise, so the surviving terms are precisely that
set's loop families. What remains is the sign count `neg_one_pow_card_mul_sign`: the Leibniz sign
is `(-1)` to the support size plus the cycle count, and multiplying by `(-1)` to the vertex-set
size converts it to `(-1)` to the loop count, because the two exponents differ by twice the
support size.

The slice-2 encoding is what made this work. Because a loop family **is** a permutation, the
objects being summed on the two sides are the same objects, and the theorem is a reindexing plus a
sign count rather than a construction.

**`gain_eq_adjugate_div_graphDet` : `gain G s t = adjugate (1 - G) t s / graphDet G`.** General,
no hypothesis. Together with `graphDet_eq_det` this gives a complete computational route from the
graph to the gain, and it is `goal.md` section H.4 S6's "equality with the corresponding entry of
`(1 - A)⁻¹`" bullet.

**`graphDet_ne_zero_iff`**: a nonvanishing graph determinant is exactly unique solvability of the
node equations, tying slice 1's criterion to the loop sum.

### What is withheld, and exactly what remains

The **forward-path form of the numerator is not proved in general**.
`gain_eq_masonGain_iff` reduces the entire remaining obligation to one identity:

```
masonNumerator G s t = (systemMatrix G).adjugate t s
```

and `gain_eq_masonGain` discharges Mason's formula from it. So the gap is a single named statement
rather than a vague shortfall.

The route is known and is written into the module doc so it can be picked up rather than
rediscovered. Expanding `Matrix.adjugate_apply` and the Leibniz sum for the updated row leaves the
permutations `σ` with `σ t = s`; expanding the remaining factors as in section A leaves a vertex
set `T` not containing `t` with `σ` supported in `T ∪ {t}`. For such `σ` the orbit of `t` is a
cycle through `s`, and deleting its edge from `t` back to `s` is exactly a forward path from `s`
to `t`, while the cycles off that orbit are a loop family on the untouched vertices. The
correspondence back is `σ = List.formPerm p * σ'`, with Mathlib's `List.formPerm` building the
cycle of a repetition-free list and `Equiv.Perm.toList` inverting it. What then remains is a sign
count of the same kind as `neg_one_pow_card_mul_sign` plus the factorisation of the family gain
along the orbit.

**Why it was not attempted now.** I estimate it at roughly 350 lines of `Equiv.Perm` cycle
bookkeeping: flattening both sides into `Finset.sigma` sums, the two maps and their
well-definedness, the mutual-inverse proofs, and the summand equality. That is a slice in its own
right, and shipping a half-finished attempt would have been worse than shipping a clean reduction
plus proved instances. I can take it as a further slice if wanted; it is independent of slices 5
and 6.

### Slices 3 and 4 — declarations

`Physlib/Mathematics/SignalFlowGraph/Mason.lean`, namespace `Physlib.SignalFlowGraph`:

**A. Expanding the Leibniz product** — `sum_loopFamilies`, `prod_one_compl`, `prod_neg_gain`,
`neg_one_pow_card_mul_sign`.

**B. The graph determinant is the system determinant** — `graphDet_eq_det`,
`graphDet_ne_zero_iff`.

**C. The gain as a cofactor quotient** — `gain_eq_adjugate_div_graphDet`,
`adjugate_systemMatrix_apply`, `gain_eq_masonGain_iff`, `gain_eq_masonGain`.

`Physlib/Mathematics/SignalFlowGraph/MasonRegression.lean`, same namespace:
`graphDet_twoNodeLoop`, `masonGain_twoNodeLoop`, `gain_eq_masonGain_twoNodeLoop`,
`masonNumerator_eq_adjugate_twoNodeLoop`, `diagThree`, `graphDet_diagThree`, `fullTwoNode`,
`graphDet_fullTwoNode`, `graphDet_twoNodeLoop_one`,
`not_existsUnique_of_graphDet_twoNodeLoop_one`.

### Slice 4 — regressions and what each detects

- **G-01 discharged on the single feedback loop.** `gain_eq_masonGain_twoNodeLoop` proves the
  matrix-inverse gain equals Mason's quotient. The two sides share no step: the left came from the
  adjugate of a two-by-two matrix in slice 1, the right from the `decide`-settled forward-path
  enumeration in slice 2 divided by the loop sum. Agreement is evidence, not restatement.
  `masonNumerator_eq_adjugate_twoNodeLoop` records the same fact in the form of the withheld
  general identity, so the withheld statement has at least one proved instance.
- **G-03 discharged on two audited graphs.** `graphDet_diagThree`: three disjoint self-loops give
  all three orders `1 - (c+d+e) + (cd+ce+de) - cde` with alternating signs.
  `graphDet_fullTwoNode`: a graph with two self-loops and a two-cycle has three first-order loops
  but only **one** second-order term, because the two-cycle touches both self-loops and pairs with
  neither. A development that summed over all pairs of loops rather than over non-touching pairs
  produces extra terms here and fails.
- **The `Δ = 0` case, from the loop side.** `graphDet_twoNodeLoop_one` and
  `not_existsUnique_of_graphDet_twoNodeLoop_one` connect a vanishing loop sum to the failure of
  unique solvability proved in slice 1, so the nonvanishing hypothesis is load-bearing on both
  sides of the identity.
- **G-02 is not addressed and cannot be here**, because loops and paths are node-level. It is
  slice 6. The regression module doc says so.

### Slices 3 and 4 gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all six files;
the Batteries declaration linter set run module-scoped over all six modules passes; the
`module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal.

### Parity classification for slices 3 and 4

**Physlib-original.** No fetched source relates Mason's graph determinant to a matrix
determinant. FMICS'15 Definition 4 (p. 168), SFG-TR'14, and NSV'16 Definition 6 (p. 37) all define
the determinant only through their executable enumeration of elementary circuits. Ledger row
IP-21's Mason's-gain content is matched at the level of the objects and their enumeration
(slice 2); the identification with `det (1 - G)` and with the inverse-matrix entry goes beyond
every source.

---

## Slice 5 — files

- `Physlib/Mathematics/SignalFlowGraph/Extraction.lean` (206 lines)
- `Physlib/Mathematics/SignalFlowGraph/ExtractionRegression.lean` (157 lines)

### Registrations needed in `Physlib.lean` (cumulative, all eight)

```
public import Physlib.Mathematics.SignalFlowGraph.Basic
public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Combinatorics
public import Physlib.Mathematics.SignalFlowGraph.CombinatoricsRegression
public import Physlib.Mathematics.SignalFlowGraph.Extraction
public import Physlib.Mathematics.SignalFlowGraph.ExtractionRegression
public import Physlib.Mathematics.SignalFlowGraph.Mason
public import Physlib.Mathematics.SignalFlowGraph.MasonRegression
```

Alphabetical order satisfies the dependency order.

### The extraction hook for the conductor

Two entry points, so a caller never has to guess which side of `1 - G` a matrix belongs on:

- `ofCoefficientMatrix` for a system already written `x = A x + b`; the matrix is the gain matrix
  as it stands, and `isNodeSolution_ofCoefficientMatrix` is the promised trivial lemma.
- `ofSystemMatrix` for a system written `M x = b`, which is the shape a solved netlist produces;
  the gain matrix is `1 - M`. Then `systemMatrix_ofSystemMatrix` is the round trip,
  `isNodeSolution_ofSystemMatrix` gives back the original linear system,
  `graphDet_ofSystemMatrix : graphDet (ofSystemMatrix M) = M.det`, and
  `gain_ofSystemMatrix : gain (ofSystemMatrix M) s t = M⁻¹ t s`.

The second is the one the conductor will want: it says the loop sum of the extracted graph is an
ordinary determinant and its gains are ordinary inverse entries, so the S6 exit theorem reduces to
matching the netlist's `M` with this `M`. **Nothing here asserts agreement with any netlist or
network semantics; that is the conductor's theorem, deliberately not attempted.**

### The multigraph layer, and why it is not decoration

`Multigraph ι E` carries `source, target : E → ι` and `gain : E → ℂ` on a separate edge type. That
gives both bullets of `goal.md` section H.4 S6 that a matrix cannot give:

- **parallel edges are distinct**, being distinct elements of `E`;
- **the topology does not depend on the gains**: `setGain_edgesBetween` proves the edges joining
  each ordered pair of nodes are unchanged when the gains are replaced, so an edge of gain zero is
  still an edge.

`Multigraph.toMatrix` sums the parallel edges into the gain matrix, connecting the layer to
everything already proved.

**The lossiness is proved, not asserted.** `toMatrix_parallelPair_eq_singleEdge`: two parallel
edges of gains `a` and `b` and one edge of gain `a + b` have the **same** gain matrix, while
`card_edgesBetween_parallelPair` and `card_edgesBetween_singleEdge` show the two multigraphs have
two edges and one edge respectively. So the residual gap in regression row G-02 is a fact about
the matrix layer rather than an oversight in it, and the multigraph layer demonstrably carries
information the matrix layer does not.

### Slice 5 — declarations

`Physlib/Mathematics/SignalFlowGraph/Extraction.lean`, namespace `Physlib.SignalFlowGraph`:

**A. Graphs from a linear system** — `ofCoefficientMatrix`, `isNodeSolution_ofCoefficientMatrix`,
`ofSystemMatrix`, `systemMatrix_ofSystemMatrix`, `isNodeSolution_ofSystemMatrix`,
`graphDet_ofSystemMatrix`, `gain_ofSystemMatrix`.

**B. Multigraphs with explicit edge identity** — `Multigraph`, `Multigraph.edgesBetween`,
`Multigraph.mem_edgesBetween`, `Multigraph.setGain`, `Multigraph.setGain_source`,
`Multigraph.setGain_target`, `Multigraph.setGain_edgesBetween`.

**C. The gain matrix of a multigraph** — `Multigraph.toMatrix`, `Multigraph.toMatrix_apply`,
`Multigraph.toMatrix_of_isEmpty`.

`Physlib/Mathematics/SignalFlowGraph/ExtractionRegression.lean`, same namespace: `parallelPair`,
`singleEdge`, `toMatrix_parallelPair`, `toMatrix_singleEdge`,
`toMatrix_parallelPair_eq_singleEdge`, `edgesBetween_parallelPair`, `edgesBetween_singleEdge`,
`card_edgesBetween_parallelPair`, `card_edgesBetween_singleEdge`, `edgesBetween_setGain_zero`,
`card_edgesBetween_setGain_zero`, `systemMatrix_ofSystemMatrix_twoNodeLoop`,
`graphDet_ofSystemMatrix_twoNodeLoop`.

### Slice 5 gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all eight
files; the Batteries declaration linter set run module-scoped over all eight modules passes; the
`module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal.

Two linter findings were acted on rather than suppressed. The first draft declared
`[DecidableEq ι]` on the multigraph definitions while a section variable already supplied it,
which `overlappingInstances` flagged; the file now scopes its `variable` blocks per section so
each declaration takes exactly the instances it uses. The first draft also proved three cardinality
facts by `decide`, which fails on statements containing free complex variables; they are now
proved by identifying the edge set with `Finset.univ`, which is both correct and general in the
gains.

### Parity classification for slice 5

**Physlib-original, with the multigraph a reformulation of the source representation.** The
sources carry a graph as a list of branches `ℕ × ℂ × ℕ` (FMICS'15 Definition 1, p. 167;
SFG-TR'14; NSV'16 Definition 1, p. 34). A separate edge type is the same idea with the branch
index made a first-class parameter rather than a list position, so section B should be classed as
parity of representation. Section A has no source counterpart: no fetched source extracts a
signal-flow graph from a linear system or relates it to a matrix inverse.

---

## Slice 7 — files

- `Physlib/Mathematics/SignalFlowGraph/Numerator.lean` (223 lines)
- `Physlib/Mathematics/SignalFlowGraph/NumeratorRegression.lean` (93 lines)

### Registrations needed in `Physlib.lean` (cumulative, all ten)

```
public import Physlib.Mathematics.SignalFlowGraph.Basic
public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Combinatorics
public import Physlib.Mathematics.SignalFlowGraph.CombinatoricsRegression
public import Physlib.Mathematics.SignalFlowGraph.Extraction
public import Physlib.Mathematics.SignalFlowGraph.ExtractionRegression
public import Physlib.Mathematics.SignalFlowGraph.Mason
public import Physlib.Mathematics.SignalFlowGraph.MasonRegression
public import Physlib.Mathematics.SignalFlowGraph.Numerator
public import Physlib.Mathematics.SignalFlowGraph.NumeratorRegression
```

### What slice 7 proves, and how it differs from what was asked

The obligation left open by slice 3 was `masonNumerator G s t = adjugate (1 - G) t s`, and the
plan was to close it by decomposing the orbit of the sink into a forward path. **That is not what
happened, and the outcome is better than the plan in one respect and short of it in another.**

Proved, in full generality, with no hypothesis:

```
cyclicNumerator_eq_adjugate :
  cyclicNumerator G s t = (systemMatrix G).adjugate t s

gain_eq_cyclicNumerator_div_graphDet :
  gain G s t = cyclicNumerator G s t / graphDet G
```

where `cyclicNumerator` is the alternating sum over the families of pairwise non-touching loops
whose loop through the sink sends it to the source, with the gain of that closing edge divided
out. **So Mason's gain formula is now a complete calculation theorem: the gain between two nodes
is a ratio of two explicit finite alternating sums over loop families, and both sums are proved
equal to the linear-algebra quantities they are supposed to compute.** That is the milestone
statement of `goal.md` section H.4 S6, "Mason gain formula under a nonzero graph determinant",
discharged in general.

**Why this route rather than the planned one.** The numerator turned out to be reachable by the
*same* expansion that proved `graphDet_eq_det`, with no cycle bookkeeping at all. Replacing one
row of the system matrix by a unit vector, as `Matrix.adjugate_apply` does, kills every
permutation that does not route the sink to the source; the survivors expand exactly as in
`Mason.lean`, except over the columns other than the sink; and adjoining the sink to each vertex
set turns those terms into loop families that close through it. The extra minus sign is the one
lost vertex in the exponent. `prod_updateRow` is the only genuinely new lemma. The whole file is
223 lines and cost no heartbeat fights, against an estimate of about 350 lines of `Equiv.Perm`
manipulation for the planned route.

**What is still open.** The numerator is in loop-family form, not forward-path form. The residual
obligation is now

```
masonNumerator G s t = cyclicNumerator G s t
```

which is a **repackaging of the same families, not new mathematical content**: the closing family
of `cyclicNumerator` is a permutation routing the sink to the source, and deleting its closing
edge from the orbit of the sink is exactly the forward path that `masonNumerator` sums over. The
route is unchanged from what was recorded in slice 3, namely `List.formPerm` in one direction and
`Equiv.Perm.toList` in the other, and the crux is the bridge lemma
`pathGain G p = familyGain G (p.toFinset.erase t) p.formPerm`.

`masonNumerator_eq_cyclicNumerator_twoNodeLoop` proves the open identity for the two-node feedback
graph, so it has a proved instance rather than only plausibility.

### Slice 7 — declarations

`Physlib/Mathematics/SignalFlowGraph/Numerator.lean`, namespace `Physlib.SignalFlowGraph`:

**A. Families that close through the sink** — `vertexSetsContaining`,
`mem_vertexSetsContaining`, `loopFamiliesRouting`, `mem_loopFamiliesRouting`,
`sum_loopFamiliesRouting`, `cyclicNumerator`.

**B. The replaced row** — `prod_updateRow`, `sdiff_erase_eq_compl_insert`.

**C. The numerator is the cofactor** — `cyclicNumerator_eq_adjugate`,
`gain_eq_cyclicNumerator_div_graphDet`.

`Physlib/Mathematics/SignalFlowGraph/NumeratorRegression.lean`, same namespace:
`cyclicNumerator_twoNodeLoop`, `gain_eq_cyclicNumerator_div_twoNodeLoop`,
`masonNumerator_eq_cyclicNumerator_twoNodeLoop`,
`masonGain_eq_cyclicNumerator_div_twoNodeLoop`.

### Slice 7 gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all ten files;
the Batteries declaration linter set run module-scoped over all ten modules passes; the
`module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal.

**Budget report, as requested.** 223 lines of theory plus 93 of regression, against a stop-limit
of about 500 lines; zero heartbeat fights. The budget was not exhausted, so there is room for the
forward-path repackaging or for slice 6, and that choice is the controller's.

### Parity classification for slice 7

**Physlib-original.** No fetched source relates Mason's numerator to a cofactor. FMICS'15
Definitions 3-4 (p. 168) and NSV'16 Definition 6 (p. 37) define it through the executable
enumeration of forward circuits, and neither states a determinant or inverse-matrix
identification.

---

## Slice 7b — files, and an honest stop

- `Physlib/Mathematics/SignalFlowGraph/PathCycle.lean` (263 lines)

Registration, appended to the cumulative list:

```
public import Physlib.Mathematics.SignalFlowGraph.PathCycle
```

### What is proved

Every piece of *mathematical content* in the correspondence between a forward path and the loop
family that closes through the sink:

- `pathGain_eq_familyGain`: the gain along a repetition-free path is the family gain of the cyclic
  permutation of its nodes, restricted to the nodes other than its last. This was the lemma named
  as the crux in the slice 7 report, and it is proved.
- `disjoint_formPerm`: a path cycle and a family supported off the path are disjoint
  permutations.
- `mul_apply_of_mem`, `mul_apply_of_notMem`: their product follows the path on the path and the
  family off it.
- `familyGain_union`: the family gain of a disjoint union splits into the two factors.
- `loopCount_mul`: the product has **exactly one loop more** than the family, in both the
  degenerate case where the path is a single node and the general case.
- Supporting: `eq_getLast_of_getLast?`, `mem_of_getLast?`, `formPerm_apply_last`,
  `formPerm_cons_apply`, `support_formPerm_toFinset`.

Every summand identity that the reindexing has to respect is therefore available.

### What is not proved, and why I stopped

`masonNumerator G s t = cyclicNumerator G s t` is **not proved**. What remains is exactly the
index bijection between

* triples of a forward path `p`, a vertex set `T'` disjoint from it, and a family `σ'` supported
  in `T'`; and
* pairs of a vertex set `T` containing the sink and a family `σ` supported in `T` with
  `σ t = s`,

given forwards by `T = p.toFinset ∪ T'` and `σ = p.formPerm * σ'`.

I stopped at the bijection rather than at the stop-limit, and the reason is a judgement rather
than an obstacle: the remaining work is index bookkeeping over a three-level and a two-level
`Finset.sigma`, which I estimate at 120 to 200 further lines with the highest iteration count of
anything in the lane, and the S6 batch is being held on this slice. Reporting the exact remaining
scope is worth more to the controller than continuing silently. Nothing is blocked; the work is
well defined.

**The route is now materially de-risked compared with the slice 3 write-up.** The inverse map
sends `σ` to the rotation of `Equiv.Perm.toList σ t`, and the earlier worry was a round trip
through `toList`. That round trip is **not needed**: `Equiv.Perm.formPerm_toList` together with
`List.formPerm_rotate_one` gives `p.formPerm = σ.cycleOf t` directly, and the support condition on
the residual family `σ' = (σ.cycleOf t)⁻¹ * σ` follows from `σ` agreeing with `σ.cycleOf t` on
that orbit. The degenerate case where the source equals the sink, in which the path is the single
node and the cycle is the identity, must be taken separately; `loopCount_mul` already handles that
split on the summand side.

### Slice 7b gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all eleven
files; the Batteries declaration linter set run module-scoped over all eleven modules passes; the
`module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal.

There is **no `sorry` anywhere**: the unproved identity is not stated as a declaration, only
described in the module doc. A reader of the file cannot mistake it for proved.

---

## Slice 7b — completed

- `Physlib/Mathematics/SignalFlowGraph/MasonPath.lean` (439 lines)
- `Physlib/Mathematics/SignalFlowGraph/MasonPathRegression.lean` (110 lines)

Registrations, appended to the cumulative list:

```
public import Physlib.Mathematics.SignalFlowGraph.MasonPath
public import Physlib.Mathematics.SignalFlowGraph.MasonPathRegression
```

### Mason's rule, closed in its classical form

```
masonGain_eq_gain :
  graphDet G ≠ 0 → masonGain G s t = gain G s t
```

The gain between two nodes is the sum, over the **forward paths** from source to sink, of the path
gain times the graph determinant of the nodes the path does not touch, divided by the graph
determinant of the whole graph. Also `masonNumerator_eq_adjugate`, unconditionally: the
forward-path sum **is** the cofactor of the system matrix. The obligation isolated in slice 3 and
narrowed in slice 7 is discharged; nothing about Mason's rule is now withheld.

### How the bijection went

`orbitPath σ t` is the orbit of the **source** under `σ`, listed from the source. That choice is
what made the proof short: the orbit ends at the sink because the sink is the source's
predecessor, so no rotation is needed, and Mathlib's
`Equiv.Perm.toList_formPerm_nontrivial` applies directly at the head. The earlier plan, which
started the list at the sink and rotated, would have needed a round trip through
`Equiv.Perm.toList` and an argument that two rotations of a repetition-free list with the same
last element are equal. Neither is needed.

`orbitPath_mul` is the recovery lemma: `orbitPath (p.formPerm * σ') t = p`. It is what makes the
correspondence a bijection rather than a surjection, and it is proved by showing the product and
the path cycle have the same cycle at the source (`Equiv.Perm.Disjoint.cycleOf_mul_distrib`) and
the same powers there, so their `toList`s agree entrywise.

The rest is index bookkeeping: `masonNumerator_eq_sum` and `cyclicNumerator_eq_sum` flatten each
side into a sum over a `Finset.sigma`, and `Finset.sum_nbij'` transports one to the other along
`⟨p, T', σ'⟩ ↦ ⟨p.toFinset ∪ T', p.formPerm * σ'⟩`. All five obligations use only lemmas proved in
`PathCycle.lean` and section B here.

### Sync with `optics/development`

Per the controller's rule, `optics/development` (`f66fb7d0`, including the conductor's review pass
`cd8af712`) was **merged** into this branch before the cutoff. The merge was clean: no conflicts.
The conductor's pass was mechanical — mostly `theorem` to `lemma`, doc and regression
clarifications, and a reformatted `nodeSolution` body — and none of it renamed a declaration, so
the new files needed no adaptation. Everything was rebuilt and every gate rerun after the merge.

`HANDOFF.md` is deleted on the integration branch, so the merge removed it here; it was restored
from the pre-merge commit and continues on this branch only.

**One discrepancy to reconcile.** The instruction was that the repo is `lemma`-only, and every
declaration in the two new files is a `lemma`. But the conductor's own merged files still carry
`theorem` on four headline results: `existsUnique_isNodeSolution_iff`, `graphDet_eq_det`,
`cyclicNumerator_eq_adjugate`, and `gain_eq_cyclicNumerator_div_graphDet`. So the effective
convention may be "`lemma` except for headline results" rather than "`lemma` only". If it is, then
`masonGain_eq_gain` — the milestone's headline statement — should be a `theorem` too. I followed
the instruction as given rather than guessing; the change is one keyword.

### Slice 7b gates

All rerun **after** the sync merge: build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true`
gives zero output on all thirteen files; the Batteries declaration linter set run module-scoped
over all thirteen modules passes; `module_doc_lint` and `style_lint` rules pass; no `sorry`,
`axiom`, `native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports
minimal.

### Parity classification

**Physlib-original.** FMICS'15 Definition 4 (p. 168) and NSV'16 Definition 6 (p. 37) *define* the
gain by Mason's formula. Here it is a **theorem** about the node equations, proved equal to the
entry of the inverse system matrix. No fetched source states that equality.

---

## Slice 6 — files

- `Physlib/Mathematics/SignalFlowGraph/EdgeEnumeration.lean` (231 lines)
- `Physlib/Mathematics/SignalFlowGraph/EdgeEnumerationRegression.lean` (114 lines)

Registrations, appended to the cumulative list:

```
public import Physlib.Mathematics.SignalFlowGraph.EdgeEnumeration
public import Physlib.Mathematics.SignalFlowGraph.EdgeEnumerationRegression
```

### G-02 closed by proof

The whole slice runs on one distributive law. An entry of the gain matrix is the sum of the gains
of the edges joining an ordered pair of nodes, so a **product** of entries is a **sum over choices
of one edge per factor**. `Finset.prod_sum` over `Finset.pi` is exactly that, and it gives:

- `familyGain_toMatrix`: a node-level family gain is the sum over its edge-level refinements;
- `pathGain_toMatrix`: a node-level path gain is the sum over the edge lists refining it.

From those, `edgeGraphDet_eq_det : edgeGraphDet Γ = (systemMatrix Γ.toMatrix).det` and
`edgeMasonGain_eq_gain : edgeMasonNumerator Γ s t / edgeGraphDet Γ = gain Γ.toMatrix s t` follow
as corollaries of the node-level theorems, not as new arguments. **Everything above the
enumeration is inherited.**

The regression then closes the row. `card_refiningEdgeLists_parallelPair = 2` and
`card_refiningEdgeLists_singleEdge = 1` on the very pair of multigraphs whose gain matrices slice 5
proved equal. So:

- the gain matrix **cannot** separate two parallel edges from one edge carrying their sum
  (slice 5, proved);
- the edge-level enumeration **does** separate them (this slice, proved);
- and every value computed from either enumeration agrees (`pathGain_toMatrix` instantiated).

That is exactly what `goal.md` section I.3 row G-02 asks for: distinct parallel branches remain
distinct **through the enumeration**, with nothing lost in what the enumeration computes. **G-02
is met.**

### Slice 6 — declarations

`Physlib/Mathematics/SignalFlowGraph/EdgeEnumeration.lean`, namespace `Physlib.SignalFlowGraph`:

**A. Edge refinements of a loop family** — `edgeChoices`, `edgeFamilyGain`, `familyGain_toMatrix`.

**B. The edge-level graph determinant** — `edgeGraphDetOn`, `edgeGraphDet`,
`edgeGraphDetOn_eq_graphDetOn`, `edgeGraphDet_eq_det`.

**C. Edge lists refining a node path** — `refiningEdgeLists`, `refiningEdgeLists_singleton`,
`refiningEdgeLists_pair`, `edgeListGain`, `edgeListGain_cons`, `pathGain_toMatrix`.

**D. Mason's formula at the edge level** — `edgeMasonNumerator`, `edgeMasonNumerator_eq`,
`edgeMasonGain_eq_gain`.

`Physlib/Mathematics/SignalFlowGraph/EdgeEnumerationRegression.lean`, same namespace:
`card_refiningEdgeLists_parallelPair`, `card_refiningEdgeLists_singleEdge`,
`refiningEdgeLists_ne`, `sum_edgeListGain_parallelPair`, `sum_edgeListGain_singleEdge`,
`edgeGraphDet_parallelPair_eq_singleEdge`.

### A note on what the refinement does and does not buy

The refinement is **exact on values**: no edge-level statement here is stronger than its
node-level counterpart. The gain is entirely in what the enumeration *distinguishes*, not in what
it *computes*, and the module doc says so. Claiming otherwise would misrepresent the slice.

### Slice 6 gates

Build clean; `lean -Dwarn.sorry=false -Dweak.says.verify=true` gives zero output on all fifteen
files; the Batteries declaration linter set run module-scoped over all fifteen modules passes; the
`module_doc_lint` and `style_lint` rules pass; no `sorry`, `axiom`, `native_decide`, or
`set_option maxHeartbeats`; no `Physlib.Optics` import; imports minimal. Every declaration is a
`lemma`, per the stated house convention.

The two cardinality regressions were first written with `decide`, which fails on statements
carrying free complex variables; they are proved instead by identifying the refinement set with an
image of the edge set, which is correct and general in the gains.

### Sync before the slice 6 cutoff

`optics/development` (`48015bbf`) was merged into this branch before the cutoff, per the standing
rule. Clean merge, no conflicts: the only incoming changes were new `Physlib/Optics/Rays` files
from another lane, and no `SignalFlowGraph` file was touched, so nothing needed adapting.
Everything was rebuilt and every gate rerun after the merge. `HANDOFF.md` survived this merge,
since the 7b batch that removes it downstream has not been merged yet.

### Parity classification for slice 6

**Physlib-original.** The sources carry branches as list entries and so distinguish parallel
branches by construction; see FMICS'15 Definitions 1-3 (pp. 167-168). No fetched source relates a
branch-level enumeration to a node-level one, which is the reduction proved here.

---

## Slice 8 — reviewer fixes, terminals, definition-level regressions

### The reviewer's five findings on `e3c79c09`

The verdict was NOT READY **on regressions and prose, not on the mathematics**; the reviewer
confirmed `masonGain_eq_gain` is the classical statement with the advertised hypothesis and that
G-02 is implemented beyond representation level. The five findings are handled as follows.

**1. No-teeth value regression — fixed.** `EdgeEnumerationRegression` claimed to have "evaluated"
the refinement sum to `a + b` but in fact restated `pathGain_toMatrix` twice and routed the
determinant comparison through `toMatrix`. The file now proves `sum_refining_parallelPair` and
`sum_refining_singleEdge` **from the enumeration itself** — identifying the refinement set with an
image of the edge set and taking the gain of a one-edge list — with no appeal to
`pathGain_toMatrix` or `toMatrix_parallelPair_eq_singleEdge`. Only afterwards does
`pathGain_toMatrix_parallelPair` show the hand-expanded value meets the general theorem, so the
two routes to `a + b` share no step. A swapped gain, an omitted branch, or a wrong edge-list
product now fails the file. The module doc was rewritten to describe what is actually proved.

**2. Prose bug — fixed.** The old `refiningEdgeLists_ne` quantified an arbitrary `c` while its
docstring claimed the two gain matrices were equal, which holds only at `c = a + b`. The statement
is now specialised to `c = a + b` and renamed `card_refiningEdgeLists_ne`, and the docstring names
the lemma that supplies the matrix equality.

**3. Overstated independence — fixed.** `orbitPath_swap` was advertised as checked "by
computation" but was proved by invoking `orbitPath_mul`, the recovery lemma it exists to exercise.
It is now proved `by decide`, and a separate `orbitPath_swap_eq_recovery` records that the
recovery lemma delivers the same list, so the two are compared rather than conflated.

**4. Empty regression — removed.** `masonNumerator_eq_adjugate_twoNodeLoop'` was a bare
specialisation of the general lemma with no regression content. Deleted.

**5. Long lines — not applicable, with evidence.** The five flagged lines are 92 to 100
**characters** but 101 to 104 **bytes**. The repo's `longLineLinter` tests `l.length`, which in
Lean 4 counts codepoints, not bytes. Empirically the merged tree contains 48 lines that are at
most 100 characters and more than 100 bytes, and the maximum **character** length across merged
`Physlib/Optics` files is exactly 100. So the operative rule is characters and these lines comply;
the finding appears to come from a byte-based measurement. Nothing was changed, because a
cosmetic edit here would imply a rule that the repo does not enforce. If the intent is a stricter
byte budget, say so and I will reflow them.

### Distinguished terminals

`Physlib/Mathematics/SignalFlowGraph/Terminated.lean`. `TerminatedGraph` packages a gain matrix
with a distinguished `input` and `output`, and `transfer` is the gain between them. The packaging
is thin on purpose and the module doc says so: every result is an instance of one already proved.
What the terminals buy is that the same number can be named four ways without repeating the two
nodes — `transfer_eq_nodeSolution` (the output signal under a unit injection at the input),
`transfer_eq_inv` (an entry of the inverse system matrix), `transfer_eq_masonGain` (Mason's
quotient over forward paths), and `transfer_eq_cyclicNumerator_div` (the loop-family quotient).
`Multigraph.terminate` terminates a multigraph, and
`Multigraph.transfer_terminate_eq_edgeMason` computes its transfer function by the edge-level
enumeration in which parallel edges stay distinct.

This is **parity of representation** with the sources: FMICS'15 Definition 1 (p. 167) carries the
input and output node numbers in its graph record. The four identifications have no source
counterpart.

### Definition-level G-01 and G-03

`Physlib/Mathematics/SignalFlowGraph/DefinitionRegression.lean`. The existing regressions compute
a determinant through `graphDet_eq_det` and a gain through the adjugate, so they exercise the
theorems but not the definitions those theorems are about. This file reaches the same values by
routes that do not pass through them.

- The loop families on two nodes are **enumerated and settled by evaluation**:
  `univ_finset_fin_two`, `loopFamilies_fin_two_empty/_zero/_one/_univ`,
  `loopCount_fin_two_univ_one`, `loopCount_fin_two_univ_swap`.
- `graphDet_fin_two` expands the graph determinant on two nodes **directly from the alternating
  sum**, giving `1 - G 0 0 - G 1 1 + G 0 0 * G 1 1 - G 1 0 * G 0 1`.
- `graphDet_fin_two_eq_det` then shows that expansion equals `det (1 - G)`. That is a **second,
  independent proof of the general identity restricted to two nodes**: an error inside
  `graphDet_eq_det` would be caught here.
- `graphDet_twoNodeLoop_direct` and `graphDet_fullTwoNode_direct` give the audited G-03 values
  from the definition, meeting the values obtained elsewhere through `det`.
- For G-01, `isNodeSolution_twoNodeLoop_explicit` exhibits an explicit signal vector and verifies
  it satisfies the node equations under a unit injection; uniqueness then forces
  `gain_twoNodeLoop_direct : gain (twoNodeLoop a b) 0 1 = a / (1 - a * b)` **from the semantics,
  with no matrix inverse involved**. The same value was obtained elsewhere from a two-by-two
  adjugate.

### Files in slice 8

New:

- `Physlib/Mathematics/SignalFlowGraph/Terminated.lean` (     164 lines)
- `Physlib/Mathematics/SignalFlowGraph/DefinitionRegression.lean` (     191 lines)

Edited for the reviewer's findings:

- `Physlib/Mathematics/SignalFlowGraph/EdgeEnumerationRegression.lean` (     144 lines) — findings 1, 2
- `Physlib/Mathematics/SignalFlowGraph/MasonPathRegression.lean` (     101 lines) — findings 3, 4

Registrations, appended to the cumulative list:

```
public import Physlib.Mathematics.SignalFlowGraph.Terminated
public import Physlib.Mathematics.SignalFlowGraph.DefinitionRegression
```

### Parity classification for slice 8

**Parity of representation** for `TerminatedGraph`: FMICS'15 Definition 1 (p. 167) carries the
input and output node numbers inside the graph record, so a terminated graph is the source's own
object. The four identifications of `transfer` — node solution, inverse entry, Mason quotient,
loop-family quotient — have no source counterpart and are **Physlib-original**.

`DefinitionRegression` is **test material, not a parity row**. Its one mathematically substantive
entry is `graphDet_fin_two_eq_det`, an independent second proof of the general identity restricted
to two nodes, which is **stronger** than anything in the sources only in that the sources have no
determinant identity at all.

### Slice 8 gates

- `lake-lock build` of all seventeen modules — clean.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true <file>` on each of the seventeen —
  zero output.
- Module-scoped Batteries declaration linters over all seventeen modules — passed.
- `module_doc_lint` and `style_lint` rules run locally on all seventeen — clean. One genuine
  101-character line in `Terminated.lean` was found and reflowed; see finding 5 above for why the
  five lines the reviewer flagged are not in this category.
- No `sorry`, `axiom`, `native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import.
- Every new declaration in both new files is a `lemma`, per the house convention.

## Slice 8b — three claim/semantics corrections

Reviewer verdict D on `ac23a99c` was NOT READY on three points, all of them about what the code
was *claimed* to show rather than about what it proves. The four earlier fixes passed. These three
are corrected as follows.

**1. The gain audit was not inverse-free, and now says so.** The module doc claimed the two-node
gain was confirmed "with no matrix inverse involved". That was wrong. `gain` is *defined* as an
entry of the totalized inverse system matrix, and the old proof reached it through
`gain_eq_nodeSolution` and `eq_nodeSolution`, both proved by multiplying by that inverse. What the
proof actually avoided was expanding the two-by-two inverse in closed form — a weaker thing.

The fix supplies the statement that *is* inverse-free.
`output_of_isNodeSolution_twoNodeLoop` shows that **every** signal vector satisfying the node
equations under a unit injection has output component `a / (1 - a * b)`, by eliminating the input
component between the two scalar equations. No inverse, no adjugate, and no uniqueness lemma
appears in it. The old corollary is renamed `gain_twoNodeLoop_via_nodeSolution`, and both its
docstring and the module doc now state that it carries the inverse bridge and why that is
unavoidable for a statement about `gain`. The unsupported word "causal" is gone: nothing in this
file involves a causality notion, which belongs to the Z-transform lane.

**2. Terminated.lean no longer overstates the singular case.** Three related overstatements are
corrected. The doc called `transfer` "the output signal produced by a unit injection"
unconditionally, but `transfer` and `nodeSolution` are totalized inverse expressions;
`Basic.lean` is careful about this and the new file had lost that care. The references section
also said the transfer function is "not defined when the graph determinant vanishes", which
contradicts its own definition — it *is* defined everywhere, since Mathlib's inverse is totalized.

Now: the unconditional identities are labelled as identities between totalized expressions, and
the file states that a response reading requires invertibility. Rather than leave that as prose,
`TerminatedGraph.transfer_eq_of_isNodeSolution` puts the boundary in Lean — under
`IsUnit (systemMatrix _).det`, the transfer function is the output component of a solution of the
node equations, and since solutions are unique there, that is the response reading. It is the only
identity in the file that asserts one.

**3. The parity claim is corrected, and a structure is added that earns it.** The file claimed
parity of representation with FMICS'15 Definition 1, but `TerminatedGraph` stores only a matrix
and two terminals, while the source record is a *branch list* with a node count and two terminals.
Since `toMatrix` has already summed parallel edges, the branch list has no counterpart — which is
exactly the representation divergence already recorded as ledger row IP-21. The claim as written
contradicted the ledger.

Bundling turned out to be cheap, so rather than only narrowing the claim the file now contains
both halves honestly:

- `TerminatedMultigraph` bundles the edge-indexed `Multigraph` with the two terminals. This
  **does** match Definition 1's shape — branch list to `Multigraph` (parallel edges distinct
  exactly as distinct branches are), node count to the `Fintype` instance, terminals to the two
  fields. Parity of representation is claimed here, and only here. It carries `transfer`,
  `transfer_eq_edgeMason`, `transfer_eq_of_isNodeSolution`, and
  `toTerminatedGraph`/`transfer_toTerminatedGraph` recording that forgetting edges leaves the
  value alone — the content of retaining edges is in the enumeration, not in the number.
- `TerminatedGraph` keeps the narrowed claim: parity of the distinguished-terminal fields only,
  and only when composed with a separate `Multigraph`. `Multigraph.terminate` is documented as
  forgetting edge identity.

### Files in slice 8b

- `Physlib/Mathematics/SignalFlowGraph/Terminated.lean` — fixes 2 and 3
- `Physlib/Mathematics/SignalFlowGraph/DefinitionRegression.lean` — fix 1

No new modules, so the registration list is unchanged from slice 8.

### Slice 8b gates

- `lake-lock build` of all seventeen modules — clean.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true` on each of the seventeen — zero
  output.
- Module-scoped Batteries declaration linters over all seventeen — passed.
- `module_doc_lint` and `style_lint` — clean.
- No `sorry`, `axiom`, `native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import.
- All new declarations are `lemma`, per the house convention.

## Slice 8c — two prose corrections in `Terminated.lean`

Reviewer verdict D2 closed all three of the slice 8b findings. Two prose blockers remained. Both
are documentation-only; the diff touches no declaration, no statement and no proof.

**1. The hypothesis split was miscounted.** The overview listed four descriptions of the transfer
function and said three of them were unconditional. Both halves were wrong. The list of four
silently omitted `transfer_eq_cyclicNumerator_div`, and of the four it did list, two are
unconditional rather than three. The file now states the split exactly, and the correct shape is
five descriptions, three plus two:

- Unconditional: `transfer_eq_inv`, `transfer_eq_nodeSolution`,
  `transfer_eq_cyclicNumerator_div`.
- Requiring `graphDet ≠ 0`: **both** Mason identities — `transfer_eq_masonGain` over forward
  paths, and `Multigraph.transfer_terminate_eq_edgeMason` together with
  `TerminatedMultigraph.transfer_eq_edgeMason` at edge level.

The reason for the asymmetry is now stated too: a Mason quotient divides by the graph determinant
and the other three do not. The file also keeps the separate point that being unconditional is
not the same as describing a network — the three unconditional identities equate totalized
expressions, and the two Mason identities are gated only to keep a denominator away from zero.
Neither kind asserts a response.

**2. The uniqueness claim about response readings was wrong once a second structure existed.**
`TerminatedGraph.transfer_eq_of_isNodeSolution` was documented as "the only identity in this file"
asserting a response reading. That was true when it was written and was falsified by slice 8b
itself, which added `TerminatedMultigraph.transfer_eq_of_isNodeSolution`. The docstring now claims
only to be the sole such identity in the `TerminatedGraph` API and names its counterpart, and the
references section speaks of the two lemmas rather than one.

### Slice 8c gates

- `lake-lock build` — clean; per-file `lean` checks on all seventeen — zero output; module-scoped
  Batteries linters on all seventeen — passed; `module_doc_lint` and `style_lint` — clean.
- Diff verified doc-only: no line beginning a `lemma`, `def`, `structure`, `omit`, attribute or
  tactic was added or removed.

### Slice 1 gates

- `lake-lock build` of both modules — clean.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true <file>` — zero output on each.
- Batteries declaration linters (the `runPhyslibLinters` linter set including the
  `defsWithUnderscore` exemptions) run module-scoped against both modules — passed. The shipped
  executable resolves its targets from the built `Physlib` olean's imports and so cannot see
  unregistered modules; the full-registry run is a merge-time gate on the conductor's side.
- `module_doc_lint` and `style_lint` rules re-implemented locally and run on both files — clean.
- No `sorry`, `axiom`, `native_decide`, or `set_option maxHeartbeats`.
- No `Physlib.Optics` import.
- Imports checked minimal by removing each in turn; `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
  and `Mathlib.LinearAlgebra.Matrix.Adjugate` were transitively available and were dropped.

### Parity classification for slice 1

**Physlib-original.** The sources — SFG-TR'14 and NSV'16 (Beillahi-Siddique-Tahar), and FMICS'15
Definition 1 (p. 167) — carry a graph as a list of branches `ℕ × ℂ × ℕ` and define Mason's gain by
executable enumeration. None of them states a node-equation semantics, relates the gain to a
matrix inverse, or proves a solvability criterion. Ledger rows IP-21 and IP-22 cover the
enumeration and transfer-function side, which is slices 2 and 3; slice 1 has no source
counterpart and should be classed original rather than parity.
