/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistEliminationRegression
public import Physlib.Optics.Network.ParameterizedResponse

/-!
# Regression tests for parameterized compilation and response domains

## i. Overview

The shared-link topology of the flat-netlist regressions is reused with one parameter-dependent
component. The first component is a fixed nonreciprocal two-port with internal reflection
`Complex.I` at its link port; the second is a two-port whose link-port reflection is the parameter
`value`. The wiring joins the two link ports, leaving one external channel on each component.

Everything about the resulting network is pinned exactly. The internal operator `1 - C * S` has a
displayed sparse matrix whose exact inverse exists precisely when `1 - I * value ≠ 0`, and on that
algebraic solve domain the total-inverse formula is the exact rational family

```text
(1 - I * value)⁻¹ * [[2 * value, 2], [1, I]]
```

in exposed order `(A.ext, B.ext)`, obtained from the network semantics rather than postulated.

`value = -I` is a **singular parameter**: an explicit kernel witness proves that the internal
operator is not injective there, so the network is not well posed and no response of any kind is
defined. That is a candidate pole of the response family and nothing more. No pole theorem is
proved here — no statement about a limit, an order, a residue, or a Laurent expansion — and the
word *pole* is therefore avoided below.

The parameter-validity data is deliberately not the algebraic solve condition. The second
component's stored reflection law is declared valid only where `‖value‖ ≤ 1`. Both inclusions
of the physical response domain are then proved strict:

* `-Complex.I` is declared valid but is not algebraically solvable; and
* `2` is algebraically solvable but is not declared valid.

## ii. Scope

The coefficients are exact algebraic sentinels, not passive, lossless, reciprocal, causal, or
physically normalized optical components. The stored validity predicate is data supplied with the
component, not a proved physical bound. The parameter is an abstract complex variable: no physical
angular frequency, Laplace variable, delay variable, or `Z`-transform variable is named, and no
free-spectral-range or resonance-linewidth statement is made.

## iii. Key results

- `parameterizedResponseRegression_feedbackOperator_eq`: the exact compiled internal operator.
- `parameterizedResponseRegression_solveDomain_eq`: the algebraic solve domain is exactly
  `1 - I * value ≠ 0`, with the singular parameter excluded by an explicit kernel witness.
- `parameterizedResponseRegression_unguardedResponse_eq`: the exact rational family taken by the
  algebraic total-inverse formula on the solve domain.
- `parameterizedResponseRegression_mem_compileBehavior_iff_solve`: parameter evaluation commutes
  with compilation and `N5` elimination on the well-posed domain, stated against the exact matrix
  (`N-10`).
- `parameterizedResponseRegression_mem_compileBehavior_iff`: its physical corollary on the
  response domain.
- `parameterizedResponseRegression_responseDomain_ssubset_solveDomain` and
  `parameterizedResponseRegression_responseDomain_ssubset_validityDomain`: both inclusions of the
  physical response domain are strict.
- `parameterizedResponseRegression_response_i` and `parameterizedResponseRegression_response_zero`:
  exact hand-expanded responses at two admissible parameter values.

## iv. Table of contents

- A. A parameterized shared-link network
- B. The exact internal operator and its inverse
- C. The algebraic solve domain and its singular parameter
- D. The exact rational family and evaluation commutation
- E. Strictness of both response-domain inclusions

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A parameterized shared-link network

-/

/-- The parameterized fixture component matrices.

In local `[external, link]` order the first component is `[[0, 2], [1, I]]` and the second is
`[[0, 1], [1, value]]`. Only the second component's link-port reflection depends on the parameter.
-/
def parameterizedResponseRegressionScattering (value : ℂ) (component : Bool) :
    ScatteringMatrix flatNetlistRegressionPortFamily.Channel where
  toModeTransform := fun output input =>
    match component, output.1, input.1 with
    | false, false, false => 0
    | false, false, true => 2
    | false, true, false => 1
    | false, true, true => Complex.I
    | true, false, false => 0
    | true, false, true => 1
    | true, true, false => 1
    | true, true, true => value

/-- The parameterized fixture components before wiring.

The second component's stored reflection law is declared valid only for a modulus at most one.
This is supplied data recording where the model is claimed to hold; it is not proved here, and it
is deliberately unrelated to algebraic solvability.
-/
abbrev parameterizedResponseRegressionComponents : ParameterizedComponentFamily ℂ where
  Component := Bool
  portFamily := fun _ => flatNetlistRegressionPortFamily
  scattering := parameterizedResponseRegressionScattering
  IsValidAt := fun component value =>
    match component with
    | false => True
    | true => ‖value‖ ≤ 1

/-- The parameterized fixture reuses the exact one-link connection topology. -/
abbrev parameterizedResponseRegression : ParameterizedNetlist ℂ where
  components := parameterizedResponseRegressionComponents
  Connection := Unit
  connections := flatNetlistRegressionConnections

/-- Aggregate channels in the parameterized fixture are finite. -/
local instance parameterizedResponseRegressionChannelFintype :
    Fintype parameterizedResponseRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Connected channels in the parameterized fixture are finite. -/
local instance parameterizedResponseRegressionConnectedChannelFintype :
    Fintype parameterizedResponseRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Aggregate channels in the parameterized fixture have decidable equality. -/
local instance parameterizedResponseRegressionChannelDecidableEq :
    DecidableEq parameterizedResponseRegression.Channel := Classical.decEq _

/-- Connected channels in the parameterized fixture have decidable equality. -/
local instance parameterizedResponseRegressionConnectedChannelDecidableEq :
    DecidableEq parameterizedResponseRegression.ConnectedChannel := Classical.decEq _

/-- The complementary external channels of the parameterized fixture are finite. -/
local instance parameterizedResponseRegressionExternalChannelFintype :
    Fintype parameterizedResponseRegression.ExternalChannel :=
  ParameterizedNetlist.parameterizedExternalChannelFintype parameterizedResponseRegression

/-- The compiled aggregate channels of the parameterized fixture are finite. -/
local instance parameterizedResponseRegressionCompileChannelFintype (value : ℂ) :
    Fintype (parameterizedResponseRegression.compile value).Channel :=
  inferInstanceAs (Fintype parameterizedResponseRegression.Channel)

/-- The compiled connected channels of the parameterized fixture are finite. -/
local instance parameterizedResponseRegressionCompileConnectedChannelFintype (value : ℂ) :
    Fintype (parameterizedResponseRegression.compile value).ConnectedChannel :=
  inferInstanceAs (Fintype parameterizedResponseRegression.ConnectedChannel)

/-- Classical equality on compiled aggregate channels of the parameterized fixture. -/
local instance parameterizedResponseRegressionCompileChannelDecidableEq (value : ℂ) :
    DecidableEq (parameterizedResponseRegression.compile value).Channel := Classical.decEq _

/-- Classical equality on compiled connected channels of the parameterized fixture. -/
local instance parameterizedResponseRegressionCompileConnectedChannelDecidableEq (value : ℂ) :
    DecidableEq (parameterizedResponseRegression.compile value).ConnectedChannel :=
  Classical.decEq _

/-- The first component's external ambient channel. -/
abbrev parameterizedResponseRegressionAExternal :
    parameterizedResponseRegression.Channel := ⟨⟨false, false⟩, ()⟩

/-- The first component's internal-link ambient channel. -/
abbrev parameterizedResponseRegressionALink :
    parameterizedResponseRegression.Channel := ⟨⟨false, true⟩, ()⟩

/-- The second component's external ambient channel. -/
abbrev parameterizedResponseRegressionBExternal :
    parameterizedResponseRegression.Channel := ⟨⟨true, false⟩, ()⟩

/-- The second component's internal-link ambient channel. -/
abbrev parameterizedResponseRegressionBLink :
    parameterizedResponseRegression.Channel := ⟨⟨true, true⟩, ()⟩

/-- The first external ambient channel is outside the internal connection range. -/
lemma parameterizedResponseRegression_aExternal_not_mem_range :
    parameterizedResponseRegressionAExternal ∉
      Set.range parameterizedResponseRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent

/-- The second external ambient channel is outside the internal connection range. -/
lemma parameterizedResponseRegression_bExternal_not_mem_range :
    parameterizedResponseRegressionBExternal ∉
      Set.range parameterizedResponseRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort

/-- The packaged first external channel. -/
abbrev parameterizedResponseRegressionExternalA :
    parameterizedResponseRegression.ExternalChannel :=
  ⟨parameterizedResponseRegressionAExternal,
    parameterizedResponseRegression_aExternal_not_mem_range⟩

/-- The packaged second external channel. -/
abbrev parameterizedResponseRegressionExternalB :
    parameterizedResponseRegression.ExternalChannel :=
  ⟨parameterizedResponseRegressionBExternal,
    parameterizedResponseRegression_bExternal_not_mem_range⟩

/-- Every exposed channel of the parameterized fixture is one of its two external endpoints. -/
lemma parameterizedResponseRegression_external_eq_a_or_b
    (external : parameterizedResponseRegression.ExternalChannel) :
    external = parameterizedResponseRegressionExternalA ∨
      external = parameterizedResponseRegressionExternalB := by
  rcases external with ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  cases component <;> cases port <;> cases mode
  · exact Or.inl rfl
  · exact absurd ⟨⟨(), Sum.inl ()⟩, rfl⟩ hExternal
  · exact Or.inr rfl
  · exact absurd ⟨⟨(), Sum.inr ()⟩, rfl⟩ hExternal

/-- Reassociation of the fixture's aggregate channels as component-indexed local channels.

This is the fixture-local presentation of `ScatteringComponentFamily.channelEquiv`, stated in the
parameterized netlist's own coordinates so that finite sums over aggregate endpoints can be
enumerated componentwise.
-/
def parameterizedResponseRegressionChannelEquiv :
    (Σ _ : Bool, flatNetlistRegressionPortFamily.Channel) ≃
      parameterizedResponseRegression.Channel where
  toFun := fun ⟨component, port, mode⟩ => ⟨⟨component, port⟩, mode⟩
  invFun := fun ⟨⟨component, port⟩, mode⟩ => ⟨component, port, mode⟩
  left_inv := by rintro ⟨component, port, mode⟩; rfl
  right_inv := by rintro ⟨⟨component, port⟩, mode⟩; rfl

/-!

## B. The exact internal operator and its inverse

-/

/-- The explicit assembled component transform in aggregate endpoint coordinates. -/
def parameterizedResponseRegressionScatteringTransform (value : ℂ) :
    ModeTransform parameterizedResponseRegression.IncidentIndex
      parameterizedResponseRegression.OutgoingIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, true => 2
  | false, true, false, false => 1
  | false, true, false, true => Complex.I
  | true, false, true, true => 1
  | true, true, true, false => 1
  | true, true, true, true => value
  | _, _, _, _ => 0

/-- The exact internal operator `1 - C * S` in aggregate order
`(A.ext, A.link, B.ext, B.link)`. -/
def parameterizedResponseRegressionFeedback (value : ℂ) :
    ModeTransform parameterizedResponseRegression.IncidentIndex
      parameterizedResponseRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, true, false, true => 1
  | false, true, true, false => -1
  | false, true, true, true => -value
  | true, false, true, false => 1
  | true, true, false, false => -1
  | true, true, false, true => -Complex.I
  | true, true, true, true => 1
  | _, _, _, _ => 0

/-- The explicit partial-routing transform, exchanging only the two link endpoints. -/
def parameterizedResponseRegressionRoutingTransform :
    ModeTransform parameterizedResponseRegression.OutgoingIndex
      parameterizedResponseRegression.IncidentIndex := fun incident outgoing =>
  match incident.channel.1.1, incident.channel.1.2,
      outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, true, true, true => 1
  | true, true, false, true => 1
  | _, _, _, _ => 0

/-- The explicit injection of the two exposed incident coordinates into the aggregate boundary. -/
def parameterizedResponseRegressionInputExposure :
    ModeTransform parameterizedResponseRegression.ExternalIncident
      parameterizedResponseRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1
  | true, false, true => 1
  | _, _, _ => 0

/-- The explicit readout of the two exposed outgoing coordinates from the aggregate boundary. -/
def parameterizedResponseRegressionOutputReadout :
    ModeTransform parameterizedResponseRegression.OutgoingIndex
      parameterizedResponseRegression.ExternalOutgoing := fun external outgoing =>
  match external.channel.1.1.1, outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, false, false => 1
  | true, true, false => 1
  | _, _, _ => 0

/-- The unnormalized inverse of the internal operator: its adjugate, with polynomial entries.

Keeping the reciprocal denominator out of the matrix makes every verification below a polynomial
identity, so no division and no `Complex.I` square ever enters the algebra.
-/
def parameterizedResponseRegressionAdjugate (value : ℂ) :
    ModeTransform parameterizedResponseRegression.IncidentIndex
      parameterizedResponseRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1 - Complex.I * value
  | false, true, false, false => value
  | false, true, false, true => 1
  | false, true, true, false => 1
  | false, true, true, true => value
  | true, false, true, false => 1 - Complex.I * value
  | true, true, false, false => 1
  | true, true, false, true => Complex.I
  | true, true, true, false => Complex.I
  | true, true, true, true => 1
  | _, _, _, _ => 0

/-- The displayed inverse internal operator, meaningful exactly where `1 - I * value ≠ 0`. -/
def parameterizedResponseRegressionInverse (value : ℂ) :
    ModeTransform parameterizedResponseRegression.IncidentIndex
      parameterizedResponseRegression.IncidentIndex :=
  (1 - Complex.I * value)⁻¹ • parameterizedResponseRegressionAdjugate value

/-- Component assembly recovers the explicit block-diagonal transform at every parameter value. -/
lemma parameterizedResponseRegression_scatteringTransform_eq (value : ℂ) :
    parameterizedResponseRegression.scatteringTransform value =
      parameterizedResponseRegressionScatteringTransform value := by
  classical
  show (parameterizedResponseRegression.compile value).scatteringTransform = _
  ext output input
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  change ((parameterizedResponseRegression.compile value).components.portFamily
    outputComponent).Mode outputPort at outputMode
  change ((parameterizedResponseRegression.compile value).components.portFamily
    inputComponent).Mode inputPort at inputMode
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals first
    | exact ((parameterizedResponseRegression.compile value).scatteringTransform_entry_same
        _ ⟨_, _⟩ ⟨_, _⟩).trans rfl
    | exact ((parameterizedResponseRegression.compile value).scatteringTransform_entry_of_ne
        (show (false : Bool) ≠ true by decide) ⟨_, _⟩ ⟨_, _⟩).trans rfl
    | exact ((parameterizedResponseRegression.compile value).scatteringTransform_entry_of_ne
        (show (true : Bool) ≠ false by decide) ⟨_, _⟩ ⟨_, _⟩).trans rfl

/-- Internal routing in the parameterized fixture is the link-exchange transform already pinned by
the fixed-frequency elimination regression, restated in this fixture's coordinates. -/
lemma parameterizedResponseRegression_routingTransform_eq :
    parameterizedResponseRegression.routingTransform =
      parameterizedResponseRegressionRoutingTransform :=
  flatNetlistEliminationRegression_routingTransform_eq

/-- Incident exposure in the parameterized fixture is the coordinate injection already pinned by
the fixed-frequency elimination regression, restated in this fixture's coordinates. -/
lemma parameterizedResponseRegression_inputExposure_eq :
    parameterizedResponseRegression.inputExposure =
      parameterizedResponseRegressionInputExposure :=
  flatNetlistEliminationRegression_inputExposure_eq

/-- Outgoing readout in the parameterized fixture is the coordinate restriction already pinned by
the fixed-frequency elimination regression, restated in this fixture's coordinates. -/
lemma parameterizedResponseRegression_outputReadout_eq :
    parameterizedResponseRegression.outputReadout =
      parameterizedResponseRegressionOutputReadout :=
  flatNetlistEliminationRegression_outputReadout_eq

/-- The compiled internal operator has the displayed sparse matrix at every parameter value. -/
lemma parameterizedResponseRegression_feedbackOperator_eq (value : ℂ) :
    parameterizedResponseRegression.feedbackOperator value =
      parameterizedResponseRegressionFeedback value := by
  classical
  rw [ParameterizedNetlist.feedbackOperator_eq,
    parameterizedResponseRegression_routingTransform_eq,
    parameterizedResponseRegression_scatteringTransform_eq]
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.sub_apply, Matrix.mul_apply,
    ← (parameterizedResponseRegressionChannelEquiv.trans
      Outgoing.channelEquiv.symm).sum_comp]
  rcases output with ⟨outputChannel⟩
  rcases input with ⟨inputChannel⟩
  simp only [Incident.mk.injEq] at hOutputInput
  rcases outputChannel with ⟨⟨outputComponent, outputPort⟩, outputMode⟩
  rcases inputChannel with ⟨⟨inputComponent, inputPort⟩, inputMode⟩
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Matrix.one_apply, hOutputInput, Fintype.sum_sigma,
      parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionRoutingTransform,
      parameterizedResponseRegressionScatteringTransform,
      parameterizedResponseRegressionFeedback]
  all_goals try cases hOutputInput

/-- The internal operator times its polynomial adjugate is the determinant multiple of the
identity. This is a polynomial identity: no division and no hypothesis on the parameter. -/
lemma parameterizedResponseRegression_feedback_mul_adjugate (value : ℂ) :
    parameterizedResponseRegressionFeedback value *
        parameterizedResponseRegressionAdjugate value =
      (1 - Complex.I * value) • (1 : ModeTransform
        parameterizedResponseRegression.IncidentIndex
        parameterizedResponseRegression.IncidentIndex) := by
  classical
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    ← (parameterizedResponseRegressionChannelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  simp only [Incident.mk.injEq] at hOutputInput
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Fintype.sum_sigma, hOutputInput,
      parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionFeedback,
      parameterizedResponseRegressionAdjugate]
  all_goals try cases hOutputInput
  all_goals try ring

/-- The polynomial adjugate times the internal operator is the same determinant multiple of the
identity. -/
lemma parameterizedResponseRegression_adjugate_mul_feedback (value : ℂ) :
    parameterizedResponseRegressionAdjugate value *
        parameterizedResponseRegressionFeedback value =
      (1 - Complex.I * value) • (1 : ModeTransform
        parameterizedResponseRegression.IncidentIndex
        parameterizedResponseRegression.IncidentIndex) := by
  classical
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    ← (parameterizedResponseRegressionChannelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  simp only [Incident.mk.injEq] at hOutputInput
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Fintype.sum_sigma, hOutputInput,
      parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionFeedback,
      parameterizedResponseRegressionAdjugate]
  all_goals try cases hOutputInput
  all_goals try ring

/-- The displayed internal operator followed by its displayed inverse is the identity away from
the singular parameter. -/
lemma parameterizedResponseRegression_feedback_mul_inverse (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    parameterizedResponseRegressionFeedback value *
        parameterizedResponseRegressionInverse value = 1 := by
  rw [parameterizedResponseRegressionInverse, Matrix.mul_smul,
    parameterizedResponseRegression_feedback_mul_adjugate, smul_smul,
    inv_mul_cancel₀ hValue, one_smul]

/-- The displayed inverse followed by the displayed internal operator is the identity away from
the singular parameter. -/
lemma parameterizedResponseRegression_inverse_mul_feedback (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    parameterizedResponseRegressionInverse value *
        parameterizedResponseRegressionFeedback value = 1 := by
  rw [parameterizedResponseRegressionInverse, Matrix.smul_mul,
    parameterizedResponseRegression_adjugate_mul_feedback, smul_smul,
    inv_mul_cancel₀ hValue, one_smul]

/-!

## C. The algebraic solve domain and its singular parameter

-/

/-- Away from the singular parameter the parameterized network is well posed, with no contraction
assumption. -/
lemma parameterizedResponseRegression_mem_solveDomain (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    value ∈ parameterizedResponseRegression.solveDomain := by
  apply (parameterizedResponseRegression.compile
    value).isWellPosed_iff_feedbackOperator_injective.mpr
  intro first second hEqual
  have hFeedback : (parameterizedResponseRegression.compile value).feedbackOperator =
      parameterizedResponseRegressionFeedback value :=
    parameterizedResponseRegression_feedbackOperator_eq value
  rw [hFeedback] at hEqual
  have hLeft : ∀ amplitude, (parameterizedResponseRegressionInverse value).toLinearMap
      ((parameterizedResponseRegressionFeedback value).toLinearMap amplitude) = amplitude := by
    intro amplitude
    rw [← ModeTransform.toLinearMap_mul_apply,
      parameterizedResponseRegression_inverse_mul_feedback value hValue]
    simp
  exact ((hLeft first).symm.trans
    (congrArg (parameterizedResponseRegressionInverse value).toLinearMap hEqual)).trans
    (hLeft second)

/-- The kernel witness at the singular parameter: unit amplitude on the second link endpoint and
`value` on the first. -/
def parameterizedResponseRegressionKernel (value : ℂ) :
    ModeAmplitude parameterizedResponseRegression.IncidentIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | false, true => value
    | true, true => 1
    | _, _ => 0

/-- The kernel witness is nonzero. -/
lemma parameterizedResponseRegressionKernel_ne_zero (value : ℂ) :
    parameterizedResponseRegressionKernel value ≠ 0 := by
  intro hKernel
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Incident.mk parameterizedResponseRegressionBLink)) hKernel
  simp [parameterizedResponseRegressionKernel] at hCoordinate

/-- At the singular parameter the internal operator annihilates the kernel witness. -/
lemma parameterizedResponseRegression_feedbackOperator_kernel (value : ℂ)
    (hValue : 1 - Complex.I * value = 0) :
    (parameterizedResponseRegressionFeedback value).toLinearMap
        (parameterizedResponseRegressionKernel value) = 0 := by
  classical
  have hOne : Complex.I * value = 1 := by linear_combination -hValue
  refine ((ModeTransform.eq_toLinearMap_iff_mulVec
    (parameterizedResponseRegressionFeedback value)
    (parameterizedResponseRegressionKernel value) 0).mpr ?_).symm
  funext endpoint
  rw [Matrix.mulVec, dotProduct,
    ← (parameterizedResponseRegressionChannelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  all_goals
    simp [Fintype.sum_sigma, hOne, parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionFeedback,
      parameterizedResponseRegressionKernel]

/-- At the singular parameter the parameterized network is not well posed: the total inverse must
not be used there. -/
lemma parameterizedResponseRegression_not_mem_solveDomain (value : ℂ)
    (hValue : 1 - Complex.I * value = 0) :
    value ∉ parameterizedResponseRegression.solveDomain := by
  intro hSolve
  have hInjective :=
    (parameterizedResponseRegression.compile
      value).isWellPosed_iff_feedbackOperator_injective.mp hSolve
  have hZero : (parameterizedResponseRegression.compile value).feedbackOperator.toLinearMap
      (parameterizedResponseRegressionKernel value) =
      (parameterizedResponseRegression.compile value).feedbackOperator.toLinearMap 0 := by
    simp only [map_zero]
    rw [show (parameterizedResponseRegression.compile value).feedbackOperator =
      parameterizedResponseRegressionFeedback value from
        parameterizedResponseRegression_feedbackOperator_eq value]
    exact parameterizedResponseRegression_feedbackOperator_kernel value hValue
  exact parameterizedResponseRegressionKernel_ne_zero value (hInjective hZero)

/-- The algebraic solve domain is exactly the complement of the singular parameter. -/
lemma parameterizedResponseRegression_solveDomain_eq :
    parameterizedResponseRegression.solveDomain = {value : ℂ | 1 - Complex.I * value ≠ 0} := by
  ext value
  constructor
  · intro hSolve hPole
    exact parameterizedResponseRegression_not_mem_solveDomain value hPole hSolve
  · exact parameterizedResponseRegression_mem_solveDomain value

/-!

## D. The exact rational family and evaluation commutation

-/

/-- The unnormalized solved incident block `adj(F) E_in` for the two exposed inputs. -/
def parameterizedResponseRegressionIncidentSolution (value : ℂ) :
    ModeTransform parameterizedResponseRegression.ExternalIncident
      parameterizedResponseRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1 - Complex.I * value
  | false, true, false => value
  | false, true, true => 1
  | true, false, true => 1 - Complex.I * value
  | true, true, false => 1
  | true, true, true => Complex.I
  | _, _, _ => 0

/-- The unnormalized solved outgoing block `S adj(F) E_in` for the two exposed inputs. -/
def parameterizedResponseRegressionOutgoingSolution (value : ℂ) :
    ModeTransform parameterizedResponseRegression.ExternalIncident
      parameterizedResponseRegression.OutgoingIndex := fun outgoing external =>
  match outgoing.channel.1.1, outgoing.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 2 * value
  | false, false, true => 2
  | false, true, false => 1
  | false, true, true => Complex.I
  | true, false, false => 1
  | true, false, true => Complex.I
  | true, true, false => value
  | true, true, true => 1

/-- The unnormalized external response in exposed order `(A.ext, B.ext)`. -/
def parameterizedResponseRegressionUnnormalizedResponse (value : ℂ) :
    ModeTransform parameterizedResponseRegression.ExternalIncident
      parameterizedResponseRegression.ExternalOutgoing := fun output input =>
  match output.channel.1.1.1, input.channel.1.1.1 with
  | false, false => 2 * value
  | false, true => 2
  | true, false => 1
  | true, true => Complex.I

/-- The exact rational family taken by the network's algebraic total-inverse formula.

It is a response only where the physical response domain says so; on the rest of the solve domain
it is the algebraic block formula and nothing more.
-/
def parameterizedResponseRegressionResponse (value : ℂ) :
    ModeTransform parameterizedResponseRegression.ExternalIncident
      parameterizedResponseRegression.ExternalOutgoing :=
  (1 - Complex.I * value)⁻¹ • parameterizedResponseRegressionUnnormalizedResponse value

/-- The proof-gated inverse is exactly the displayed inverse matrix. -/
lemma parameterizedResponseRegression_totalFeedbackInverse_eq (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    parameterizedResponseRegression.totalFeedbackInverse value =
      parameterizedResponseRegressionInverse value := by
  apply Matrix.inv_eq_left_inv
  rw [parameterizedResponseRegression_feedbackOperator_eq]
  exact parameterizedResponseRegression_inverse_mul_feedback value hValue

/-- The polynomial adjugate and exposure give the unnormalized incident solution block. -/
lemma parameterizedResponseRegression_adjugate_mul_inputExposure (value : ℂ) :
    parameterizedResponseRegressionAdjugate value *
        parameterizedResponseRegressionInputExposure =
      parameterizedResponseRegressionIncidentSolution value := by
  classical
  ext incident external
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  rcases external with ⟨external⟩
  rcases parameterizedResponseRegression_external_eq_a_or_b external with rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (parameterizedResponseRegressionChannelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionAdjugate,
      parameterizedResponseRegressionInputExposure,
      parameterizedResponseRegressionIncidentSolution]

/-- Component scattering sends the unnormalized incident solution to the unnormalized outgoing
solution. -/
lemma parameterizedResponseRegression_scattering_mul_incidentSolution (value : ℂ) :
    parameterizedResponseRegressionScatteringTransform value *
        parameterizedResponseRegressionIncidentSolution value =
      parameterizedResponseRegressionOutgoingSolution value := by
  classical
  ext outgoing external
  rcases outgoing with ⟨⟨⟨component, port⟩, mode⟩⟩
  rcases external with ⟨external⟩
  rcases parameterizedResponseRegression_external_eq_a_or_b external with rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (parameterizedResponseRegressionChannelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionScatteringTransform,
      parameterizedResponseRegressionIncidentSolution,
      parameterizedResponseRegressionOutgoingSolution]
  all_goals ring

/-- External readout selects the unnormalized two-by-two response from the outgoing solution. -/
lemma parameterizedResponseRegression_outputReadout_mul_outgoingSolution (value : ℂ) :
    parameterizedResponseRegressionOutputReadout *
        parameterizedResponseRegressionOutgoingSolution value =
      parameterizedResponseRegressionUnnormalizedResponse value := by
  classical
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  rcases parameterizedResponseRegression_external_eq_a_or_b output with rfl | rfl <;>
    rcases parameterizedResponseRegression_external_eq_a_or_b input with rfl | rfl
  all_goals
    rw [Matrix.mul_apply, ← (parameterizedResponseRegressionChannelEquiv.trans
      Outgoing.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, parameterizedResponseRegressionChannelEquiv,
      parameterizedResponseRegressionOutputReadout,
      parameterizedResponseRegressionOutgoingSolution,
      parameterizedResponseRegressionUnnormalizedResponse]

/-- The algebraic total-inverse formula takes this exact rational value at every algebraically
solvable parameter. No claim of physical validity is made here; stored component validity is a
separate and strictly stronger condition. -/
theorem parameterizedResponseRegression_unguardedResponse_eq (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    parameterizedResponseRegression.unguardedResponse value =
      parameterizedResponseRegressionResponse value := by
  rw [ParameterizedNetlist.unguardedResponse,
    parameterizedResponseRegression_outputReadout_eq,
    parameterizedResponseRegression_scatteringTransform_eq,
    parameterizedResponseRegression_inputExposure_eq,
    parameterizedResponseRegression_totalFeedbackInverse_eq value hValue,
    parameterizedResponseRegressionInverse, parameterizedResponseRegressionResponse]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    parameterizedResponseRegression_adjugate_mul_inputExposure,
    parameterizedResponseRegression_scattering_mul_incidentSolution,
    parameterizedResponseRegression_outputReadout_mul_outgoingSolution]

/-- On the physical response domain the proof-gated response is the same exact rational matrix. -/
theorem parameterizedResponseRegression_response_eq {value : ℂ}
    (hValue : value ∈ parameterizedResponseRegression.responseDomain) :
    parameterizedResponseRegression.response hValue =
      parameterizedResponseRegressionResponse value := by
  rw [← parameterizedResponseRegression.unguardedResponse_eq_response hValue]
  exact parameterizedResponseRegression_unguardedResponse_eq value
    ((Set.ext_iff.mp parameterizedResponseRegression_solveDomain_eq value).mp hValue.1)

/-- Parameter evaluation commutes with compilation and `N5` elimination on the well-posed domain:
at every algebraically solvable parameter, the compiled singular-safe relational semantics is
exactly the graph of the exact rational matrix. This is regression row `N-10`.

The gate is `solveDomain`, which is what the milestone asks for. Gating it on `responseDomain`
instead would lose real cases: `2` is algebraically solvable and outside the declared validity
domain, and the equality still holds there.
-/
theorem parameterizedResponseRegression_mem_compileBehavior_iff_solve (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0)
    (input : ModeAmplitude parameterizedResponseRegression.ExternalIncident)
    (output : ModeAmplitude parameterizedResponseRegression.ExternalOutgoing) :
    (input, output) ∈ (parameterizedResponseRegression.compile value).behavior ↔
      output = (parameterizedResponseRegressionResponse value).toLinearMap input := by
  rw [← parameterizedResponseRegression_unguardedResponse_eq value hValue]
  exact parameterizedResponseRegression.mem_compileBehavior_iff_unguardedResponse
    (parameterizedResponseRegression_mem_solveDomain value hValue) input output

/-- The physical corollary of `N-10` on the response domain. -/
theorem parameterizedResponseRegression_mem_compileBehavior_iff {value : ℂ}
    (hValue : value ∈ parameterizedResponseRegression.responseDomain)
    (input : ModeAmplitude parameterizedResponseRegression.ExternalIncident)
    (output : ModeAmplitude parameterizedResponseRegression.ExternalOutgoing) :
    (input, output) ∈ (parameterizedResponseRegression.compile value).behavior ↔
      output = (parameterizedResponseRegressionResponse value).toLinearMap input :=
  parameterizedResponseRegression_mem_compileBehavior_iff_solve value
    ((Set.ext_iff.mp parameterizedResponseRegression_solveDomain_eq value).mp hValue.1)
    input output

/-- The exact rational family is asymmetric at every algebraically solvable parameter, so a
transposed external transfer matrix is detected. This is a statement about the algebraic family,
which is a physical response only on the response domain. -/
lemma parameterizedResponseRegression_rationalFamily_asymmetric (value : ℂ)
    (hValue : 1 - Complex.I * value ≠ 0) :
    parameterizedResponseRegressionResponse value
        (Outgoing.mk parameterizedResponseRegressionExternalB)
        (Incident.mk parameterizedResponseRegressionExternalA) ≠
      parameterizedResponseRegressionResponse value
        (Outgoing.mk parameterizedResponseRegressionExternalA)
        (Incident.mk parameterizedResponseRegressionExternalB) := by
  simp only [parameterizedResponseRegressionResponse, Matrix.smul_apply, smul_eq_mul,
    parameterizedResponseRegressionUnnormalizedResponse]
  intro hEqual
  have hCancel := mul_left_cancel₀ (inv_ne_zero hValue) hEqual
  norm_num at hCancel

/-!

## E. Strictness of both response-domain inclusions

-/

/-- The singular parameter lies in the declared validity domain, since its modulus is one. -/
lemma parameterizedResponseRegression_singularParameter_mem_validityDomain :
    (-Complex.I) ∈ parameterizedResponseRegressionComponents.validityDomain := by
  intro component
  cases component
  · trivial
  · simp

/-- The singular parameter is not algebraically solvable. -/
lemma parameterizedResponseRegression_singularParameter_not_mem_solveDomain :
    (-Complex.I) ∉ parameterizedResponseRegression.solveDomain := by
  apply parameterizedResponseRegression_not_mem_solveDomain
  simp [Complex.I_mul_I]

/-- A modulus-two reflection is algebraically solvable. -/
lemma parameterizedResponseRegression_two_mem_solveDomain :
    (2 : ℂ) ∈ parameterizedResponseRegression.solveDomain := by
  apply parameterizedResponseRegression_mem_solveDomain
  intro hZero
  have hReal := congrArg Complex.re hZero
  norm_num at hReal

/-- A modulus-two reflection is outside the declared component validity domain. -/
lemma parameterizedResponseRegression_two_not_mem_validityDomain :
    (2 : ℂ) ∉ parameterizedResponseRegressionComponents.validityDomain := by
  intro hValid
  have hBound := hValid true
  simp only at hBound
  norm_num at hBound

/-- The physical response domain is strictly smaller than the algebraic solve domain: algebraic
solvability alone does not license a physical response. -/
theorem parameterizedResponseRegression_responseDomain_ssubset_solveDomain :
    parameterizedResponseRegression.responseDomain ⊂
      parameterizedResponseRegression.solveDomain := by
  refine ⟨parameterizedResponseRegression.responseDomain_subset_solveDomain, ?_⟩
  intro hSubset
  exact parameterizedResponseRegression_two_not_mem_validityDomain
    (parameterizedResponseRegression.responseDomain_subset_validityDomain
      (hSubset parameterizedResponseRegression_two_mem_solveDomain))

/-- The physical response domain is strictly smaller than the declared validity domain: a claimed
component model does not make a network solvable. -/
theorem parameterizedResponseRegression_responseDomain_ssubset_validityDomain :
    parameterizedResponseRegression.responseDomain ⊂
      parameterizedResponseRegressionComponents.validityDomain := by
  refine ⟨parameterizedResponseRegression.responseDomain_subset_validityDomain, ?_⟩
  intro hSubset
  exact parameterizedResponseRegression_singularParameter_not_mem_solveDomain
    (parameterizedResponseRegression.responseDomain_subset_solveDomain
      (hSubset parameterizedResponseRegression_singularParameter_mem_validityDomain))

/-- The unit-imaginary reflection lies in the physical response domain. -/
lemma parameterizedResponseRegression_i_mem_responseDomain :
    Complex.I ∈ parameterizedResponseRegression.responseDomain := by
  constructor
  · apply parameterizedResponseRegression_mem_solveDomain
    rw [Complex.I_mul_I]
    norm_num
  · intro component
    cases component
    · trivial
    · simp

/-- The zero reflection lies in the physical response domain. -/
lemma parameterizedResponseRegression_zero_mem_responseDomain :
    (0 : ℂ) ∈ parameterizedResponseRegression.responseDomain := by
  constructor
  · apply parameterizedResponseRegression_mem_solveDomain
    norm_num
  · intro component
    cases component
    · trivial
    · simp

/-- At a unit-imaginary reflection the denominator is exactly two and the response is
`[[I, 1], [1/2, I/2]]` in exposed order. -/
theorem parameterizedResponseRegression_response_i :
    parameterizedResponseRegression.response
        parameterizedResponseRegression_i_mem_responseDomain
        (Outgoing.mk parameterizedResponseRegressionExternalA)
        (Incident.mk parameterizedResponseRegressionExternalA) = Complex.I := by
  rw [parameterizedResponseRegression_response_eq]
  simp only [parameterizedResponseRegressionResponse, Matrix.smul_apply, smul_eq_mul,
    parameterizedResponseRegressionUnnormalizedResponse]
  rw [Complex.I_mul_I]
  norm_num
  ring

/-- At zero reflection the network degenerates to the exact reflectionless response entry `2`. -/
theorem parameterizedResponseRegression_response_zero :
    parameterizedResponseRegression.response
        parameterizedResponseRegression_zero_mem_responseDomain
        (Outgoing.mk parameterizedResponseRegressionExternalA)
        (Incident.mk parameterizedResponseRegressionExternalB) = 2 := by
  rw [parameterizedResponseRegression_response_eq]
  simp [parameterizedResponseRegressionResponse,
    parameterizedResponseRegressionUnnormalizedResponse]

end

end Optics
