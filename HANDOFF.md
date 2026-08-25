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
| 6 | Optional: edge-based enumeration closing regression G-02 by proof | pending — attempt after slice 7 |

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
