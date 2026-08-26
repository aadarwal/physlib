/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Tactic.Polyrith
public import Physlib.Optics.Systems.Cascade.PandaBridge

/-!
# Source-formula response of the PANDA forward graph

## i. Overview

This file compares the directed, netlist-derived PANDA projection with the through- and drop-port
expressions printed in NSV'16 Theorems 5 and 6. `SourceParameters` records the paper's symbols
`e^n`, `e_r^n_r`, `e_l^n_l`, and the eight coupler amplitudes. The coefficient dictionary and
`HasPrincipalRootSelection` are explicit cross-model premises: in particular, every comparison
inherits the principal-root branch gate already required by the IP-12 SFG bridge.

The proof solves the eighteen equations through the factorization

```text
(1 - cr*R)*(1 - cl*L) - c1*c2*E*(cr - R)*(cl - L).
```

Expanding this factor gives the denominator printed in both source theorems. No auxiliary division
by either side-ring factor is introduced. Thus the only algebraic response gate is the nonzero
printed denominator.

The source calls its PANDA SFG undirected and gives the branch between nodes 10 and 5 as an example
(text preceding Section 5, pp. 37-38). These results concern the oriented Definition-11 projection
certified in `PandaBridge`; they do not identify that directed matrix with an undirected closure.

## ii. Key results

- `Panda.sourceDenominator_eq_factorized`: audited expansion of the common denominator.
- `Panda.closedState_forwardEquations`: an explicit solution of all eighteen graph equations.
- `Panda.nsv16_throughTransfer`: comparison with printed NSV'16 Theorem 5.
- `Panda.nsv16_dropTransfer`: comparison with printed NSV'16 Theorem 6.
- `Panda.auditedThroughMasonResponse_eq_source`: edge-level Mason form of Theorem 5.
- `Panda.auditedDropMasonResponse_eq_source`: edge-level Mason form of Theorem 6.

## iii. Table of contents

- A. Source dictionary and hypotheses
- B. Printed source expressions
- C. Explicit forward solution
- D. NSV'16 comparisons

## iv. References, corrections, and non-claims

S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering Systems Based on
Signal-Flow-Graph Theory", NSV 2016, LNCS 10152, Definition 11 and Theorems 5-6, pp. 42-44.

The audit recorded in `HOL-CORPUS.md` section 6.2 and parity rows IP-13/IP-14 is carried literally:
the final paragraph on p. 44 says the authors found missing parts in reference [10] and a sign
mismatch in reference [1]. It does not identify an error in their own Theorem 5 or 6; Physlib
therefore reproduces those two printed expressions without a forced correction. IP-13/IP-14's
four complex square-sum hypotheses are exactly `HasSourceCouplerNormalization`; no real-valued or
passivity premise is silently substituted. The only bridge qualification is the explicit
directed/projection and principal-root dictionary above.

The totalized quotients below have response meaning only under `HasNonzeroSourceDenominator`.
No passivity, losslessness, reciprocity, causality, convergence, stability, resonance, bandwidth,
dispersion, pole/zero location, insertion-loss model, or material realization is asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

/-! ## A. Source dictionary and hypotheses -/

/-- The NSV'16 PANDA symbols after collecting each printed round-trip power into one factor. -/
structure SourceParameters where
  /-- Printed main-ring round-trip factor `e^n`. -/
  mainRoundTrip : ℂ
  /-- Printed right-ring round-trip factor `e_r^n_r`. -/
  rightRoundTrip : ℂ
  /-- Printed left-ring round-trip factor `e_l^n_l`. -/
  leftRoundTrip : ℂ
  /-- Input-coupler through amplitude `c1`. -/
  c1 : ℂ
  /-- Input-coupler cross amplitude `s1`, before the printed `-j` phase. -/
  s1 : ℂ
  /-- Output-coupler through amplitude `c2`. -/
  c2 : ℂ
  /-- Output-coupler cross amplitude `s2`, before the printed `-j` phase. -/
  s2 : ℂ
  /-- Right-ring coupler through amplitude `cr`. -/
  cr : ℂ
  /-- Right-ring coupler cross amplitude `sr`, before the printed `-j` phase. -/
  sr : ℂ
  /-- Left-ring coupler through amplitude `cl`. -/
  cl : ℂ
  /-- Left-ring coupler cross amplitude `sl`, before the printed `-j` phase. -/
  sl : ℂ

/-- The source coupler symbols are the real N7 amplitudes, coerced to complex scalars. -/
structure HasSourceCouplerDictionary (p : Parameters) (s : SourceParameters) : Prop where
  /-- Dictionary entry for `c1`. -/
  c1 : s.c1 = (p.inputCoupler.throughAmplitude : ℂ)
  /-- Dictionary entry for `s1`. -/
  s1 : s.s1 = (p.inputCoupler.crossAmplitude : ℂ)
  /-- Dictionary entry for `c2`. -/
  c2 : s.c2 = (p.outputCoupler.throughAmplitude : ℂ)
  /-- Dictionary entry for `s2`. -/
  s2 : s.s2 = (p.outputCoupler.crossAmplitude : ℂ)
  /-- Dictionary entry for `cr`. -/
  cr : s.cr = (p.rightCoupler.throughAmplitude : ℂ)
  /-- Dictionary entry for `sr`. -/
  sr : s.sr = (p.rightCoupler.crossAmplitude : ℂ)
  /-- Dictionary entry for `cl`. -/
  cl : s.cl = (p.leftCoupler.throughAmplitude : ℂ)
  /-- Dictionary entry for `sl`. -/
  sl : s.sl = (p.leftCoupler.crossAmplitude : ℂ)

/-- Explicit principal-root selection and product consistency for the source propagation symbols.

The product fields are stated because Mathlib's `Complex.sqrt` is a principal `cpow`; treating its
products as the paper's formal root symbols is part of the cross-model branch dictionary, not an
unconditional algebraic rewrite.
-/
structure HasPrincipalRootSelection (p : Parameters) (s : SourceParameters) : Prop where
  /-- First main quarter is the principal fourth root. -/
  mainOne : p.mainQuarterOneCoefficient = Complex.sqrt (Complex.sqrt s.mainRoundTrip)
  /-- Second main quarter is the same principal fourth root. -/
  mainTwo : p.mainQuarterTwoCoefficient = Complex.sqrt (Complex.sqrt s.mainRoundTrip)
  /-- Third main quarter is the same principal fourth root. -/
  mainThree : p.mainQuarterThreeCoefficient = Complex.sqrt (Complex.sqrt s.mainRoundTrip)
  /-- Fourth main quarter is the same principal fourth root. -/
  mainFour : p.mainQuarterFourCoefficient = Complex.sqrt (Complex.sqrt s.mainRoundTrip)
  /-- The first two selected quarters multiply to the printed principal square root. -/
  mainFirstHalf :
    p.mainQuarterOneCoefficient * p.mainQuarterTwoCoefficient =
      Complex.sqrt s.mainRoundTrip
  /-- The last two selected quarters multiply to the printed principal square root. -/
  mainSecondHalf :
    p.mainQuarterThreeCoefficient * p.mainQuarterFourCoefficient =
      Complex.sqrt s.mainRoundTrip
  /-- The four selected quarters multiply to the printed main round trip. -/
  mainProduct : p.mainRoundTripCoefficient = s.mainRoundTrip
  /-- First right half is the principal square root. -/
  rightOne : p.rightHalfOneCoefficient = Complex.sqrt s.rightRoundTrip
  /-- Second right half is the same principal square root. -/
  rightTwo : p.rightHalfTwoCoefficient = Complex.sqrt s.rightRoundTrip
  /-- The selected right halves multiply to the printed right round trip. -/
  rightProduct : p.rightRoundTripCoefficient = s.rightRoundTrip
  /-- First left half is the principal square root. -/
  leftOne : p.leftHalfOneCoefficient = Complex.sqrt s.leftRoundTrip
  /-- Second left half is the same principal square root. -/
  leftTwo : p.leftHalfTwoCoefficient = Complex.sqrt s.leftRoundTrip
  /-- The selected left halves multiply to the printed left round trip. -/
  leftProduct : p.leftRoundTripCoefficient = s.leftRoundTrip

/-- The four hypotheses printed verbatim in NSV'16 Theorems 5 and 6. -/
structure HasSourceCouplerNormalization (s : SourceParameters) : Prop where
  /-- Printed input-coupler hypothesis `c1^2 + s1^2 = 1`. -/
  input : s.c1 ^ 2 + s.s1 ^ 2 = 1
  /-- Printed output-coupler hypothesis `c2^2 + s2^2 = 1`. -/
  output : s.c2 ^ 2 + s.s2 ^ 2 = 1
  /-- Printed right-coupler hypothesis `cr^2 + sr^2 = 1`. -/
  right : s.cr ^ 2 + s.sr ^ 2 = 1
  /-- Printed left-coupler hypothesis `cl^2 + sl^2 = 1`. -/
  left : s.cl ^ 2 + s.sl ^ 2 = 1

/-! ## B. Printed source expressions -/

/-- The common denominator printed in NSV'16 Theorems 5 and 6. -/
def sourceDenominator (s : SourceParameters) : ℂ :=
  1 - s.cl * s.leftRoundTrip - s.cr * s.rightRoundTrip -
      s.cr * s.cl * s.c1 * s.c2 * s.mainRoundTrip +
    s.cl * s.cr * s.rightRoundTrip * s.leftRoundTrip +
    s.cl * s.c1 * s.c2 * s.rightRoundTrip * s.mainRoundTrip +
    s.cr * s.c1 * s.c2 * s.leftRoundTrip * s.mainRoundTrip -
    s.c1 * s.c2 * s.rightRoundTrip * s.leftRoundTrip * s.mainRoundTrip

/-- The exact nonzero gate for the two printed PANDA quotients. -/
def HasNonzeroSourceDenominator (s : SourceParameters) : Prop :=
  sourceDenominator s ≠ 0

/-- The through-port numerator printed in NSV'16 Theorem 5. -/
def sourceThroughNumerator (s : SourceParameters) : ℂ :=
  s.c1 * (1 + s.cl * s.cr * s.rightRoundTrip * s.leftRoundTrip -
      s.cl * s.leftRoundTrip - s.cr * s.rightRoundTrip) +
    s.c2 * s.mainRoundTrip *
      (s.cl * s.rightRoundTrip + s.cr * s.leftRoundTrip -
        s.cr * s.cl - s.rightRoundTrip * s.leftRoundTrip)

/-- The drop-port numerator printed in NSV'16 Theorem 6. -/
def sourceDropNumerator (s : SourceParameters) : ℂ :=
  s.s1 * s.s2 * s.rightRoundTrip * Complex.sqrt s.mainRoundTrip -
    s.s1 * s.s2 * s.cl * s.leftRoundTrip * s.rightRoundTrip *
      Complex.sqrt s.mainRoundTrip -
    s.cr * s.s1 * s.s2 * Complex.sqrt s.mainRoundTrip +
    s.cr * s.cl * s.s1 * s.s2 * s.leftRoundTrip *
      Complex.sqrt s.mainRoundTrip

/-- The totalized through-port expression printed in NSV'16 Theorem 5. -/
def sourceThroughTransfer (s : SourceParameters) : ℂ :=
  sourceThroughNumerator s / sourceDenominator s

/-- The totalized drop-port expression printed in NSV'16 Theorem 6. -/
def sourceDropTransfer (s : SourceParameters) : ℂ :=
  sourceDropNumerator s / sourceDenominator s

/-- The edge-indexed Mason quotient of the oriented through-port projection. -/
noncomputable def auditedThroughMasonResponse (p : Parameters) : ℂ :=
  Physlib.SignalFlowGraph.edgeMasonNumerator (signalMultigraph p) 0 2 /
    Physlib.SignalFlowGraph.edgeGraphDet (signalMultigraph p)

/-- The edge-indexed Mason quotient of the oriented drop-port projection. -/
noncomputable def auditedDropMasonResponse (p : Parameters) : ℂ :=
  Physlib.SignalFlowGraph.edgeMasonNumerator (signalMultigraph p) 0 7 /
    Physlib.SignalFlowGraph.edgeGraphDet (signalMultigraph p)

/-- The expanded source denominator is its sparse three-ring factorization. -/
lemma sourceDenominator_eq_factorized (s : SourceParameters) :
    sourceDenominator s =
      (1 - s.cr * s.rightRoundTrip) * (1 - s.cl * s.leftRoundTrip) -
        s.c1 * s.c2 * s.mainRoundTrip *
          (s.cr - s.rightRoundTrip) * (s.cl - s.leftRoundTrip) := by
  rw [sourceDenominator]
  ring

/-- The printed through numerator has the corresponding sparse factorization. -/
lemma sourceThroughNumerator_eq_factorized (s : SourceParameters) :
    sourceThroughNumerator s =
      s.c1 * (1 - s.cr * s.rightRoundTrip) *
          (1 - s.cl * s.leftRoundTrip) -
        s.c2 * s.mainRoundTrip *
          (s.cr - s.rightRoundTrip) * (s.cl - s.leftRoundTrip) := by
  rw [sourceThroughNumerator]
  ring

/-- The printed drop numerator has the sparse path factorization. -/
lemma sourceDropNumerator_eq_factorized (s : SourceParameters) :
    sourceDropNumerator s =
      s.s1 * s.s2 * Complex.sqrt s.mainRoundTrip *
        (s.rightRoundTrip - s.cr) * (1 - s.cl * s.leftRoundTrip) := by
  rw [sourceDropNumerator]
  ring

/-! ## C. Explicit forward solution -/

/-- The negative-quadrature coefficient associated with a printed cross amplitude. -/
def sourceCrossCoefficient (crossAmplitude : ℂ) : ℂ :=
  -Complex.I * crossAmplitude

/-- The explicit eighteen-coordinate solution used for both printed transfers. -/
def closedState (p : Parameters) (s : SourceParameters) (input : ℂ) : Node → ℂ :=
  let x1 := sourceCrossCoefficient s.s1
  let x2 := sourceCrossCoefficient s.s2
  let xr := sourceCrossCoefficient s.sr
  let xl := sourceCrossCoefficient s.sl
  let dr := 1 - s.cr * s.rightRoundTrip
  let dl := 1 - s.cl * s.leftRoundTrip
  let ar := s.cr - s.rightRoundTrip
  let al := s.cl - s.leftRoundTrip
  let d := sourceDenominator s
  ![input,
    s.c2 * s.mainRoundTrip * x1 * ar * al * input / d,
    sourceThroughNumerator s * input / d,
    x1 * dr * dl * input / d,
    Complex.sqrt s.mainRoundTrip * x1 * ar * dl * input / d,
    0,
    s.c2 * Complex.sqrt s.mainRoundTrip * x1 * ar * dl * input / d,
    x1 * x2 * Complex.sqrt s.mainRoundTrip * ar * dl * input / d,
    p.mainQuarterOneCoefficient * x1 * dr * dl * input / d,
    p.mainQuarterOneCoefficient * x1 * ar * dl * input / d,
    s.rightRoundTrip * xr * p.mainQuarterOneCoefficient * x1 * dl * input / d,
    xr * p.mainQuarterOneCoefficient * x1 * dl * input / d,
    p.rightHalfOneCoefficient * xr * p.mainQuarterOneCoefficient * x1 * dl * input / d,
    p.mainQuarterThreeCoefficient * s.c2 * Complex.sqrt s.mainRoundTrip *
      x1 * ar * dl * input / d,
    p.mainQuarterThreeCoefficient * s.c2 * Complex.sqrt s.mainRoundTrip *
      x1 * ar * al * input / d,
    s.leftRoundTrip * xl * p.mainQuarterThreeCoefficient * s.c2 *
      Complex.sqrt s.mainRoundTrip * x1 * ar * input / d,
    xl * p.mainQuarterThreeCoefficient * s.c2 * Complex.sqrt s.mainRoundTrip *
      x1 * ar * input / d,
    p.leftHalfOneCoefficient * xl * p.mainQuarterThreeCoefficient * s.c2 *
      Complex.sqrt s.mainRoundTrip * x1 * ar * input / d]

/-- The source normalization converts each squared `-j*s` edge into `c^2 - 1`. -/
lemma sourceCrossCoefficient_sq (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
    sourceCrossCoefficient s ^ 2 = c ^ 2 - 1 := by
  rw [sourceCrossCoefficient, pow_two]
  calc
    (-Complex.I * s) * (-Complex.I * s) = -(s ^ 2) := by
      rw [pow_two]
      ring_nf
      simp
    _ = c ^ 2 - 1 := by linear_combination -h

/-- The explicit state satisfies all eighteen retained equations under the exact source gates. -/
lemma closedState_forwardEquations (p : Parameters) (s : SourceParameters) (input : ℂ)
    (hDictionary : HasSourceCouplerDictionary p s)
    (hRoot : HasPrincipalRootSelection p s)
    (hNormalization : HasSourceCouplerNormalization s)
    (hDenominator : HasNonzeroSourceDenominator s) :
    ForwardEquations p input (closedState p s input) := by
  have hx1 := sourceCrossCoefficient_sq s.c1 s.s1 hNormalization.input
  have hx2 := sourceCrossCoefficient_sq s.c2 s.s2 hNormalization.output
  have hxr := sourceCrossCoefficient_sq s.cr s.sr hNormalization.right
  have hxl := sourceCrossCoefficient_sq s.cl s.sl hNormalization.left
  rcases hDictionary with ⟨hc1, hs1, hc2, hs2, hcr, hsr, hcl, hsl⟩
  constructor
  all_goals
    simp only [closedState]
  all_goals
    simp only [DirectionalCoupler.crossCoefficient, sourceCrossCoefficient] at *
  all_goals
    simp only [← hc1, ← hs1, ← hc2, ← hs2, ← hcr, ← hsr, ← hcl, ← hsl]
  all_goals
    try rw [← hRoot.mainFirstHalf]
  all_goals
    try rw [← hRoot.mainSecondHalf]
  all_goals
    try rw [← hRoot.mainProduct]
  all_goals
    try rw [← hRoot.rightProduct]
  all_goals
    try rw [← hRoot.leftProduct]
  all_goals
    simp only [Parameters.mainRoundTripCoefficient, Parameters.rightRoundTripCoefficient,
      Parameters.leftRoundTripCoefficient] at *
  all_goals
    field_simp [hDenominator]
  all_goals
    simp only [sourceDenominator_eq_factorized, sourceThroughNumerator_eq_factorized]
  all_goals
    ring_nf at hx1 hx2 hxr hxl ⊢
  all_goals
    simp only [Complex.I_mul_I] at hx1 hx2 hxr hxl ⊢
  all_goals
    polyrith only [hx1, hx2, hxr, hxl]

/-! ## D. NSV'16 comparisons -/

/-- Unit source injection is the singleton vector at printed node one. -/
lemma signalInput_one_eq_single : signalInput 1 = Pi.single (0 : Node) 1 := by
  funext node
  fin_cases node <;> simp [signalInput, Pi.single]

/-- NSV'16 Theorem 5: the solved node-three response is the printed through-port quotient.

Besides the source's four normalization hypotheses, the statement exposes the cross-model
dictionary, principal-root selection, nonzero printed denominator, and invertible oriented graph
as response-semantics gates.
-/
theorem nsv16_throughTransfer (p : Parameters) (s : SourceParameters)
    (hDictionary : HasSourceCouplerDictionary p s)
    (hRoot : HasPrincipalRootSelection p s)
    (hNormalization : HasSourceCouplerNormalization s)
    (hDenominator : HasNonzeroSourceDenominator s)
    (hGraph : Physlib.SignalFlowGraph.graphDet (coefficientMatrix p) ≠ 0) :
    (throughTerminatedMultigraph p).transfer = sourceThroughTransfer s := by
  have hState : Physlib.SignalFlowGraph.IsNodeSolution (coefficientMatrix p)
      (Pi.single (0 : Node) 1) (closedState p s 1) := by
    have hForward := (isNodeSolution_iff_forwardEquations p 1 (closedState p s 1)).mpr
      (closedState_forwardEquations p s 1 hDictionary hRoot hNormalization hDenominator)
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single] using hForward
  have hUnit : IsUnit
      (Physlib.SignalFlowGraph.systemMatrix (coefficientMatrix p)).det := by
    rw [← Physlib.SignalFlowGraph.graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  calc
    (throughTerminatedMultigraph p).transfer = closedState p s 1 2 := by
      exact Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_of_isNodeSolution
        (throughTerminatedMultigraph p) hUnit hState
    _ = sourceThroughTransfer s := by simp [closedState, sourceThroughTransfer]

/-- NSV'16 Theorem 6: the solved node-eight response is the printed drop-port quotient.

The additional hypotheses have exactly the same dictionary and response-semantics roles as in
`nsv16_throughTransfer`.
-/
theorem nsv16_dropTransfer (p : Parameters) (s : SourceParameters)
    (hDictionary : HasSourceCouplerDictionary p s)
    (hRoot : HasPrincipalRootSelection p s)
    (hNormalization : HasSourceCouplerNormalization s)
    (hDenominator : HasNonzeroSourceDenominator s)
    (hGraph : Physlib.SignalFlowGraph.graphDet (coefficientMatrix p) ≠ 0) :
    (dropTerminatedMultigraph p).transfer = sourceDropTransfer s := by
  have hState : Physlib.SignalFlowGraph.IsNodeSolution (coefficientMatrix p)
      (Pi.single (0 : Node) 1) (closedState p s 1) := by
    have hForward := (isNodeSolution_iff_forwardEquations p 1 (closedState p s 1)).mpr
      (closedState_forwardEquations p s 1 hDictionary hRoot hNormalization hDenominator)
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single] using hForward
  have hUnit : IsUnit
      (Physlib.SignalFlowGraph.systemMatrix (coefficientMatrix p)).det := by
    rw [← Physlib.SignalFlowGraph.graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  calc
    (dropTerminatedMultigraph p).transfer = closedState p s 1 7 := by
      exact Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_of_isNodeSolution
        (dropTerminatedMultigraph p) hUnit hState
    _ = sourceDropTransfer s := by
      rw [sourceDropTransfer, sourceDropNumerator_eq_factorized]
      simp [closedState, sourceCrossCoefficient, Complex.I_sq]
      ring

/-- The edge-level Mason quotient of the directed projection is the printed through expression on
the exact response domain. -/
lemma auditedThroughMasonResponse_eq_source (p : Parameters) (s : SourceParameters)
    (hDictionary : HasSourceCouplerDictionary p s)
    (hRoot : HasPrincipalRootSelection p s)
    (hNormalization : HasSourceCouplerNormalization s)
    (hDenominator : HasNonzeroSourceDenominator s)
    (hGraph : Physlib.SignalFlowGraph.graphDet (coefficientMatrix p) ≠ 0) :
    auditedThroughMasonResponse p = sourceThroughTransfer s := by
  calc
    auditedThroughMasonResponse p = (throughTerminatedMultigraph p).transfer := by
      exact (Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_edgeMason
        (throughTerminatedMultigraph p) hGraph).symm
    _ = sourceThroughTransfer s :=
      nsv16_throughTransfer p s hDictionary hRoot hNormalization hDenominator hGraph

/-- The edge-level Mason quotient of the directed projection is the printed drop expression on the
exact response domain. -/
lemma auditedDropMasonResponse_eq_source (p : Parameters) (s : SourceParameters)
    (hDictionary : HasSourceCouplerDictionary p s)
    (hRoot : HasPrincipalRootSelection p s)
    (hNormalization : HasSourceCouplerNormalization s)
    (hDenominator : HasNonzeroSourceDenominator s)
    (hGraph : Physlib.SignalFlowGraph.graphDet (coefficientMatrix p) ≠ 0) :
    auditedDropMasonResponse p = sourceDropTransfer s := by
  calc
    auditedDropMasonResponse p = (dropTerminatedMultigraph p).transfer := by
      exact (Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_edgeMason
        (dropTerminatedMultigraph p) hGraph).symm
    _ = sourceDropTransfer s :=
      nsv16_dropTransfer p s hDictionary hRoot hNormalization hDenominator hGraph

end Panda

end

end Optics
