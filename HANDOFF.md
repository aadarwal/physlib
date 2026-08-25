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
| 2 | Paths, loops, non-touching loop families, the graph determinant and cofactors | pending |
| 3 | Mason's theorem, and `Δ = det (1 - G)` | pending |
| 4 | Regressions: single loop, two non-touching loops, the touching three-node case, `Δ = 0` | pending |
| 5 | `ofCoefficientMatrix` hook for the conductor | pending |

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

**Decision requested:** (i) add the edge-indexed structure with `toMatrix` in slice 5, alongside
`ofCoefficientMatrix`, closing the representation bullets and leaving G-02 open and named; or
(ii) leave the whole multigraph question to a later lane; or (iii) something else. I will take
option (i) by default if I hear nothing, since it is cheap and strictly increases coverage, and I
will report the residual G-02 gap either way.

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
