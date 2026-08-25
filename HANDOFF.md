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
| 3 | Mason's theorem, and `Δ = det (1 - G)` | pending |
| 4 | Regressions: single loop, two non-touching loops, the touching three-node case, `Δ = 0` | pending |
| 5 | `ofCoefficientMatrix` hook, plus the edge-indexed multigraph structure with `toMatrix` | pending |
| 6 | Optional: edge-based enumeration closing regression G-02 by proof | pending — attempt only after 2-5 land |

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
