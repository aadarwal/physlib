/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Physlib.Optics.Network.WiringInvariance

/-!
# Well-posed elimination for flat scattering netlists

## i. Overview

The singular-safe semantics of `FlatNetlist` first defines the complete solution relation and the
external behavior without choosing an inverse. This file adds the proof-gated finite-dimensional
eliminator. A netlist is well posed exactly when every external incident amplitude has one complete
incident/outgoing solution state. For the square feedback operator

```text
F = 1 - C * S,
```

this relational condition is equivalent to injectivity, surjectivity, bijectivity, matrix
invertibility, and a nonzero determinant. Under that condition the complete solution and external
response are the graphs of the expected block formulas.

## ii. Key results

- `FlatNetlist.IsWellPosed`: every external input has one complete solution state.
- `FlatNetlist.HasBijectiveFeedbackOperator`: the proof gate on `1 - C * S`.
- `FlatNetlist.isWellPosed_iff_feedbackOperator_bijective`: the exact algebraic gate.
- `FlatNetlist.feedbackInverse`: the proof-gated inverse of `1 - C * S`.
- `FlatNetlist.solutionBlockFormula`: the complete incident/outgoing solution matrix.
- `FlatNetlist.responseBlockFormula`: the external response
  `E_outᴴ * S * (1 - C * S)⁻¹ * E_in`.
- `FlatNetlist.solutionTransform_eq_blockFormula` and
  `FlatNetlist.responseTransform_eq_blockFormula`: agreement with the relational semantics.
- `FlatNetlist.isWellPosed_withConnections_iff`: wiring presentation does not affect
  well-posedness.
- `FlatNetlist.responseTransform_withConnections`: the response changes only by the canonical
  external relabelling.

## iii. Table of contents

- A. Exact well-posedness criteria
- B. Proof-gated feedback inverse
- C. Complete and external block formulas
- D. Behavior-derived transforms and agreement
- E. Wiring-presentation invariance

## iv. References

Well-posedness here concerns the complete internal state, not merely a unique externally observed
output. The inverse is constructed only from a proof of bijectivity; Mathlib's total matrix inverse
is not used as an ungated network solver. No contraction, passivity, losslessness, reciprocity,
causality, frequency dependence, or physical scattering specialization is asserted.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x y

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, kept local to finite elimination. -/
local instance eliminationChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on connected channels, kept local to finite elimination. -/
local instance eliminationConnectedChannelDecidableEq : DecidableEq netlist.ConnectedChannel :=
  Classical.decEq _

/-- The external complement of the finite aggregate and connected channel families is finite. -/
local instance eliminationExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-!

## A. Exact well-posedness criteria

-/

/-- A flat netlist has well-posed feedback when every external incident amplitude determines one
complete incident/outgoing solution state. -/
abbrev IsWellPosed : Prop := netlist.solutionBehavior.IsFunctional

/-- The algebraic gate asserting that the square feedback operator is bijective. -/
def HasBijectiveFeedbackOperator : Prop :=
  Function.Bijective netlist.feedbackOperator.toLinearMap

/-- Totality of the complete solution relation is exactly solvability of the feedback equation for
every exposed input forcing. -/
lemma isTotal_solutionBehavior_iff_feedbackOperator_solvable :
    netlist.solutionBehavior.IsTotal ↔
      ∀ external : ModeAmplitude netlist.ExternalIncident,
        ∃ incident : ModeAmplitude netlist.IncidentIndex,
          netlist.feedbackOperator.toLinearMap incident =
            netlist.inputExposure.toLinearMap external := by
  constructor
  · intro hTotal external
    rcases hTotal external with ⟨state, hState⟩
    refine ⟨state.restrictInl, ?_⟩
    apply (netlist.exists_outgoing_mem_solutionBehavior_iff_feedbackEquation
      external state.restrictInl).mp
    refine ⟨state.restrictInr, ?_⟩
    simpa only [ModeAmplitude.directSum_restrict] using hState
  · intro hSolvable external
    rcases hSolvable external with ⟨incident, hFeedback⟩
    exact ⟨incident.directSum (netlist.scatteringTransform.toLinearMap incident),
      (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
        external incident _).mpr ⟨rfl, hFeedback⟩⟩

/-- Single-valuedness of the complete solution relation is exactly injectivity of the square
feedback operator. -/
lemma isSingleValued_solutionBehavior_iff_feedbackOperator_injective :
    netlist.solutionBehavior.IsSingleValued ↔
      Function.Injective netlist.feedbackOperator.toLinearMap := by
  constructor
  · intro hSingle first second hEqual
    have hKernel : netlist.feedbackOperator.toLinearMap (first - second) =
        netlist.inputExposure.toLinearMap 0 := by
      rw [map_sub, hEqual, sub_self, map_zero]
    let outgoing := netlist.scatteringTransform.toLinearMap (first - second)
    have hSolution :
        (0, (first - second).directSum outgoing) ∈ netlist.solutionBehavior := by
      apply (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
        0 (first - second) outgoing).mpr
      exact ⟨rfl, hKernel⟩
    have hZero :
        (0, (0 : ModeAmplitude netlist.SolutionIndex)) ∈ netlist.solutionBehavior :=
      netlist.solutionBehavior.zero_mem
    have hState := hSingle hSolution hZero
    have hDifference : first - second = 0 :=
      congrArg ModeAmplitude.restrictInl hState
    exact sub_eq_zero.mp hDifference
  · intro hInjective external firstState secondState hFirst hSecond
    have hFirstDisplayed :
        (external, firstState.restrictInl.directSum firstState.restrictInr) ∈
          netlist.solutionBehavior := by
      simpa only [ModeAmplitude.directSum_restrict] using hFirst
    have hSecondDisplayed :
        (external, secondState.restrictInl.directSum secondState.restrictInr) ∈
          netlist.solutionBehavior := by
      simpa only [ModeAmplitude.directSum_restrict] using hSecond
    have hFirstEquations :=
      (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation external
        firstState.restrictInl firstState.restrictInr).mp hFirstDisplayed
    have hSecondEquations :=
      (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation external
        secondState.restrictInl secondState.restrictInr).mp hSecondDisplayed
    have hIncident : firstState.restrictInl = secondState.restrictInl :=
      hInjective (hFirstEquations.2.trans hSecondEquations.2.symm)
    have hOutgoing : firstState.restrictInr = secondState.restrictInr := by
      rw [hFirstEquations.1, hSecondEquations.1, hIncident]
    rw [← firstState.directSum_restrict, ← secondState.directSum_restrict,
      hIncident, hOutgoing]

/-- Exact finite-dimensional well-posedness: the square feedback operator is injective. -/
lemma isWellPosed_iff_feedbackOperator_injective :
    netlist.IsWellPosed ↔
      Function.Injective netlist.feedbackOperator.toLinearMap := by
  constructor
  · intro hWellPosed
    exact (netlist.isSingleValued_solutionBehavior_iff_feedbackOperator_injective).mp
      hWellPosed.2
  · intro hInjective
    have hSurjective : Function.Surjective netlist.feedbackOperator.toLinearMap :=
      LinearMap.injective_iff_surjective.mp hInjective
    refine ⟨(netlist.isTotal_solutionBehavior_iff_feedbackOperator_solvable).mpr ?_,
      (netlist.isSingleValued_solutionBehavior_iff_feedbackOperator_injective).mpr hInjective⟩
    intro external
    exact hSurjective (netlist.inputExposure.toLinearMap external)

/-- Exact finite-dimensional well-posedness: the square feedback operator is surjective. -/
lemma isWellPosed_iff_feedbackOperator_surjective :
    netlist.IsWellPosed ↔
      Function.Surjective netlist.feedbackOperator.toLinearMap := by
  rw [netlist.isWellPosed_iff_feedbackOperator_injective,
    LinearMap.injective_iff_surjective]

/-- Exact finite-dimensional well-posedness: the square feedback operator is bijective. -/
lemma isWellPosed_iff_feedbackOperator_bijective :
    netlist.IsWellPosed ↔
      Function.Bijective netlist.feedbackOperator.toLinearMap := by
  rw [netlist.isWellPosed_iff_feedbackOperator_injective]
  constructor
  · intro hInjective
    exact ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩
  · exact fun hBijective ↦ hBijective.1

/-- Relational well-posedness is exactly the bijective-feedback-operator gate. -/
lemma isWellPosed_iff_hasBijectiveFeedbackOperator :
    netlist.IsWellPosed ↔ netlist.HasBijectiveFeedbackOperator :=
  netlist.isWellPosed_iff_feedbackOperator_bijective

/-- Exact finite-dimensional well-posedness: the homogeneous feedback equation has only the zero
solution. -/
lemma isWellPosed_iff_feedbackOperator_ker_eq_bot :
    netlist.IsWellPosed ↔
      LinearMap.ker netlist.feedbackOperator.toLinearMap = ⊥ :=
  netlist.isWellPosed_iff_feedbackOperator_injective.trans
    LinearMap.ker_eq_bot.symm

/-- Exact finite-dimensional well-posedness: the feedback matrix is a unit. -/
lemma isWellPosed_iff_feedbackOperator_isUnit :
    netlist.IsWellPosed ↔ IsUnit netlist.feedbackOperator :=
  netlist.isWellPosed_iff_feedbackOperator_bijective.trans
    (ModeTransform.toLinearMap_bijective_iff_isUnit netlist.feedbackOperator)

/-- Exact finite-dimensional well-posedness: the feedback determinant is nonzero. -/
lemma isWellPosed_iff_feedbackOperator_det_ne_zero :
    netlist.IsWellPosed ↔ netlist.feedbackOperator.det ≠ 0 := by
  rw [netlist.isWellPosed_iff_feedbackOperator_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-!

## B. Proof-gated feedback inverse

-/

/-- The inverse feedback matrix, constructed only from complete-solution well-posedness. -/
noncomputable def feedbackInverse (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.IncidentIndex netlist.IncidentIndex :=
  netlist.feedbackOperator.inverseOfBijective
    (netlist.isWellPosed_iff_feedbackOperator_bijective.mp hWellPosed)

/-- Applying the feedback operator after its proof-gated inverse is the identity. -/
lemma feedbackOperator_apply_feedbackInverse
    (hWellPosed : netlist.IsWellPosed)
    (forcing : ModeAmplitude netlist.IncidentIndex) :
    netlist.feedbackOperator.toLinearMap
        ((netlist.feedbackInverse hWellPosed).toLinearMap forcing) = forcing :=
  netlist.feedbackOperator.apply_inverseOfBijective
    (netlist.isWellPosed_iff_feedbackOperator_bijective.mp hWellPosed) forcing

/-- Applying the proof-gated feedback inverse after the feedback operator is the identity. -/
lemma feedbackInverse_apply_feedbackOperator
    (hWellPosed : netlist.IsWellPosed)
    (incident : ModeAmplitude netlist.IncidentIndex) :
    (netlist.feedbackInverse hWellPosed).toLinearMap
        (netlist.feedbackOperator.toLinearMap incident) = incident :=
  netlist.feedbackOperator.inverseOfBijective_apply
    (netlist.isWellPosed_iff_feedbackOperator_bijective.mp hWellPosed) incident

/-- The feedback operator followed by its proof-gated inverse matrix is the identity. -/
lemma feedbackOperator_mul_feedbackInverse
    (hWellPosed : netlist.IsWellPosed) :
    netlist.feedbackOperator * netlist.feedbackInverse hWellPosed = 1 :=
  netlist.feedbackOperator.mul_inverseOfBijective
    (netlist.isWellPosed_iff_feedbackOperator_bijective.mp hWellPosed)

/-- The proof-gated feedback inverse matrix followed by the feedback operator is the identity. -/
lemma feedbackInverse_mul_feedbackOperator
    (hWellPosed : netlist.IsWellPosed) :
    netlist.feedbackInverse hWellPosed * netlist.feedbackOperator = 1 :=
  netlist.feedbackOperator.inverseOfBijective_mul
    (netlist.isWellPosed_iff_feedbackOperator_bijective.mp hWellPosed)

/-!

## C. Complete and external block formulas

-/

/-- The solved incident-amplitude block `(1 - C * S)⁻¹ * E_in`. -/
noncomputable def incidentSolutionBlockFormula
    (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.IncidentIndex :=
  netlist.feedbackInverse hWellPosed * netlist.inputExposure

/-- The solved outgoing-amplitude block `S * (1 - C * S)⁻¹ * E_in`. -/
noncomputable def outgoingSolutionBlockFormula
    (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.OutgoingIndex :=
  netlist.scatteringTransform * netlist.incidentSolutionBlockFormula hWellPosed

/-- The complete solution block obtained by stacking the incident and outgoing solution maps. -/
noncomputable def solutionBlockFormula (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.SolutionIndex :=
  Matrix.fromRows (netlist.incidentSolutionBlockFormula hWellPosed)
    (netlist.outgoingSolutionBlockFormula hWellPosed)

/-- The selected external response
`E_outᴴ * S * (1 - C * S)⁻¹ * E_in`. -/
noncomputable def responseBlockFormula (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  netlist.outputReadout * netlist.outgoingSolutionBlockFormula hWellPosed

/-- The incident solution block acts by applying exposure and then the feedback inverse. -/
lemma incidentSolutionBlockFormula_apply (hWellPosed : netlist.IsWellPosed)
    (external : ModeAmplitude netlist.ExternalIncident) :
    (netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external =
      (netlist.feedbackInverse hWellPosed).toLinearMap
        (netlist.inputExposure.toLinearMap external) := by
  exact ModeTransform.toLinearMap_mul_apply _ _ _

/-- The outgoing solution block applies component scattering to the solved incident amplitude. -/
lemma outgoingSolutionBlockFormula_apply (hWellPosed : netlist.IsWellPosed)
    (external : ModeAmplitude netlist.ExternalIncident) :
    (netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external =
      netlist.scatteringTransform.toLinearMap
        ((netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external) := by
  exact ModeTransform.toLinearMap_mul_apply _ _ _

/-- The complete solution formula returns the solved incident and outgoing amplitudes together. -/
lemma solutionBlockFormula_apply (hWellPosed : netlist.IsWellPosed)
    (external : ModeAmplitude netlist.ExternalIncident) :
    (netlist.solutionBlockFormula hWellPosed).toLinearMap external =
      ((netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external).directSum
        ((netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with index | index <;>
    simp [solutionBlockFormula, ModeAmplitude.directSum, Matrix.toLpLin_apply,
      Matrix.fromRows_mulVec]

/-- The external response formula applies readout to the solved outgoing amplitude. -/
lemma responseBlockFormula_apply (hWellPosed : netlist.IsWellPosed)
    (external : ModeAmplitude netlist.ExternalIncident) :
    (netlist.responseBlockFormula hWellPosed).toLinearMap external =
      netlist.outputReadout.toLinearMap
        ((netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external) := by
  exact ModeTransform.toLinearMap_mul_apply _ _ _

/-- The incident solution block solves the exposed feedback equation. -/
lemma feedbackOperator_mul_incidentSolutionBlockFormula
    (hWellPosed : netlist.IsWellPosed) :
    netlist.feedbackOperator * netlist.incidentSolutionBlockFormula hWellPosed =
      netlist.inputExposure := by
  rw [incidentSolutionBlockFormula, ← Matrix.mul_assoc,
    netlist.feedbackOperator_mul_feedbackInverse hWellPosed, Matrix.one_mul]

/-- The displayed response block has the exact four-factor elimination order. -/
lemma responseBlockFormula_eq
    (hWellPosed : netlist.IsWellPosed) :
    netlist.responseBlockFormula hWellPosed =
      netlist.outputReadout * netlist.scatteringTransform *
        netlist.feedbackInverse hWellPosed * netlist.inputExposure := by
  simp only [responseBlockFormula, outgoingSolutionBlockFormula,
    incidentSolutionBlockFormula, Matrix.mul_assoc]

/-- The complete block formula has exactly the singular-safe complete solution relation as its
graph. -/
lemma toBehavior_solutionBlockFormula (hWellPosed : netlist.IsWellPosed) :
    (netlist.solutionBlockFormula hWellPosed).toBehavior = netlist.solutionBehavior := by
  ext ⟨external, state⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  have hDisplayed :
      (external, state) ∈ netlist.solutionBehavior ↔
        (external, state.restrictInl.directSum state.restrictInr) ∈
          netlist.solutionBehavior := by
    rw [ModeAmplitude.directSum_restrict]
  rw [hDisplayed,
    netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation,
    netlist.solutionBlockFormula_apply hWellPosed]
  let incident := (netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external
  let outgoing := (netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external
  constructor
  · intro hState
    have hIncident := congrArg ModeAmplitude.restrictInl hState
    have hOutgoing := congrArg ModeAmplitude.restrictInr hState
    change state.restrictInl = incident at hIncident
    change state.restrictInr = outgoing at hOutgoing
    refine ⟨?_, ?_⟩
    · rw [hOutgoing]
      change (netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external = _
      rw [netlist.outgoingSolutionBlockFormula_apply, hIncident]
    · rw [hIncident]
      change netlist.feedbackOperator.toLinearMap
          ((netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external) = _
      rw [netlist.incidentSolutionBlockFormula_apply,
        netlist.feedbackOperator_apply_feedbackInverse hWellPosed]
  · rintro ⟨hOutgoing, hFeedback⟩
    have hIncident : state.restrictInl = incident := by
      change state.restrictInl =
        (netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap external
      rw [netlist.incidentSolutionBlockFormula_apply,
        ← netlist.feedbackInverse_apply_feedbackOperator hWellPosed state.restrictInl,
        hFeedback]
    have hOutgoing' : state.restrictInr = outgoing := by
      change state.restrictInr =
        (netlist.outgoingSolutionBlockFormula hWellPosed).toLinearMap external
      rw [netlist.outgoingSolutionBlockFormula_apply]
      simpa only [hIncident] using hOutgoing
    rw [← state.directSum_restrict, hIncident, hOutgoing']

/-- The external response block formula has exactly the projected external behavior as its graph. -/
lemma toBehavior_responseBlockFormula (hWellPosed : netlist.IsWellPosed) :
    (netlist.responseBlockFormula hWellPosed).toBehavior = netlist.behavior := by
  ext ⟨input, output⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    netlist.mem_behavior_iff_feedbackEquation,
    netlist.responseBlockFormula_apply hWellPosed]
  let incident := (netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap input
  constructor
  · intro hOutput
    refine ⟨incident, ?_, ?_⟩
    · change netlist.feedbackOperator.toLinearMap
        ((netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap input) = _
      rw [netlist.incidentSolutionBlockFormula_apply,
        netlist.feedbackOperator_apply_feedbackInverse hWellPosed]
    · rw [hOutput, outgoingSolutionBlockFormula_apply]
  · rintro ⟨candidate, hFeedback, hOutput⟩
    have hCandidate : candidate = incident := by
      change candidate =
        (netlist.incidentSolutionBlockFormula hWellPosed).toLinearMap input
      rw [netlist.incidentSolutionBlockFormula_apply,
        ← netlist.feedbackInverse_apply_feedbackOperator hWellPosed candidate,
        hFeedback]
    rw [hOutput, outgoingSolutionBlockFormula_apply, hCandidate]

/-!

## D. Behavior-derived transforms and agreement

-/

/-- The canonical complete solution transform extracted from the well-posed solution relation. -/
noncomputable def solutionTransform (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.SolutionIndex :=
  netlist.solutionBehavior.toModeTransform hWellPosed

/-- Well-posed complete solutions make the projected external behavior functional. -/
lemma behavior_isFunctional (hWellPosed : netlist.IsWellPosed) :
    netlist.behavior.IsFunctional := by
  unfold behavior
  exact (hWellPosed.series
    (LinearBehavior.isFunctional_ofLinearMap ModeAmplitude.restrictInrLinearMap)).series
      netlist.outputReadout.toBehavior_isFunctional

/-- The canonical external response transform extracted from the well-posed external behavior. -/
noncomputable def responseTransform (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  netlist.behavior.toModeTransform (netlist.behavior_isFunctional hWellPosed)

/-- The extracted complete solution transform reconstructs the complete solution relation. -/
@[simp]
lemma toBehavior_solutionTransform (hWellPosed : netlist.IsWellPosed) :
    (netlist.solutionTransform hWellPosed).toBehavior = netlist.solutionBehavior :=
  LinearBehavior.toBehavior_toModeTransform _ _

/-- The extracted external response transform reconstructs the projected external behavior. -/
@[simp]
lemma toBehavior_responseTransform (hWellPosed : netlist.IsWellPosed) :
    (netlist.responseTransform hWellPosed).toBehavior = netlist.behavior :=
  LinearBehavior.toBehavior_toModeTransform _ _

/-- The behavior-derived complete solution transform equals the explicit proof-gated block
formula. -/
lemma solutionTransform_eq_blockFormula (hWellPosed : netlist.IsWellPosed) :
    netlist.solutionTransform hWellPosed = netlist.solutionBlockFormula hWellPosed :=
  LinearBehavior.toModeTransform_unique _ _ _
    (netlist.toBehavior_solutionBlockFormula hWellPosed)

/-- The behavior-derived external response equals the exact four-factor elimination formula. -/
lemma responseTransform_eq_blockFormula (hWellPosed : netlist.IsWellPosed) :
    netlist.responseTransform hWellPosed = netlist.responseBlockFormula hWellPosed :=
  LinearBehavior.toModeTransform_unique _ _ _
    (netlist.toBehavior_responseBlockFormula hWellPosed)

/-- Complete-solution membership is evaluation of the extracted solution transform. -/
lemma mem_solutionBehavior_iff_eq_solutionTransform
    (hWellPosed : netlist.IsWellPosed)
    (input : ModeAmplitude netlist.ExternalIncident)
    (state : ModeAmplitude netlist.SolutionIndex) :
    (input, state) ∈ netlist.solutionBehavior ↔
      state = (netlist.solutionTransform hWellPosed).toLinearMap input :=
  LinearBehavior.mem_iff_eq_toModeTransform _ _ _ _

/-- External-behavior membership is evaluation of the extracted response transform. -/
lemma mem_behavior_iff_eq_responseTransform
    (hWellPosed : netlist.IsWellPosed)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ netlist.behavior ↔
      output = (netlist.responseTransform hWellPosed).toLinearMap input :=
  LinearBehavior.mem_iff_eq_toModeTransform _ _ _ _

/-!

## E. Wiring-presentation invariance

-/

section WiringInvariance

variable {ι' : Type y}
  (connections' : PortConnectionFamily netlist.PortFamily ι')
  (wiring : PortConnectionFamily.WiringEquiv netlist.connections connections')
  [Fintype connections'.Channel]

/-- External channels in a wiring-equivalent replacement presentation remain finite. -/
local instance replacementExternalChannelFintype :
    Fintype connections'.ExternalChannel := by
  classical
  infer_instance

include wiring in
/-- A wiring presentation change preserves well-posedness exactly.

The proof uses literal invariance of `1 - C * S`; it does not transport or assume an inverse.
-/
lemma isWellPosed_withConnections_iff :
    (netlist.withConnections connections').IsWellPosed ↔ netlist.IsWellPosed := by
  rw [(netlist.withConnections connections').isWellPosed_iff_feedbackOperator_bijective,
    netlist.isWellPosed_iff_feedbackOperator_bijective,
    feedbackOperator_withConnections connections' wiring]

include wiring in
/-- Behavior-derived external response transforms change only by the canonical external
relabelling.

The two well-posedness proofs are intentionally independent: proof irrelevance and uniqueness of
the graph-derived transform make the statement insensitive to how either gate was established.
-/
lemma responseTransform_withConnections
    (hReplacement : (netlist.withConnections connections').IsWellPosed)
    (hOriginal : netlist.IsWellPosed) :
    (netlist.withConnections connections').responseTransform hReplacement =
      (netlist.responseTransform hOriginal).reindex
        (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring)
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring) := by
  apply ModeTransform.toBehavior_injective
  rw [(netlist.withConnections connections').toBehavior_responseTransform,
    ModeTransform.toBehavior_reindex, netlist.toBehavior_responseTransform,
    behavior_withConnections connections' wiring]

end WiringInvariance

end FlatNetlist

end

end Optics
