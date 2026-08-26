/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistRephase
public import Physlib.Optics.Network.HierarchicalReuseRegression

/-!
# Phase-sensitive regression for hierarchical connection routing

## i. Overview

The four-component, three-stage chain from `HierarchicalReuseRegression` is given distinct
non-real endpoint phases. The component operator, incident state, outgoing state, and both
parenthesized connection assemblies are expanded directly. Nonzero values `2I`, `-6I`, and `30I`
cross the three internal wires, and both external presentations report `-210I`.

The positive anchor does not invoke any matched-gauge covariance, hierarchical associativity, or
flattening lemma. A hostile gauge changes only the incident phase at the second component's west
endpoint from `I` to `1`, while its connected outgoing source remains phased by `I`. The same raw
fixture then demands both `2` and `2I` at that incident coordinate, proving a genuine inequality
and rejection by the connection equations.

## ii. Key results

- `routingRephaseRegression_mem_both_parenthesizations`: independently expanded raw solutions for
  both three-stage parenthesizations agree and expose `-210I`.
- `routingRephaseRegression_componentOperator_eq_rephase`,
  `routingRephaseRegression_incident_eq_rephase`, and
  `routingRephaseRegression_outgoing_eq_rephase`: the hand-expanded positive data are exactly the
  declared primitive rephasings.
- `routingRephaseRegression_cross_amplitudes_nonzero`: all three phase-sensitive wire amplitudes
  are nonzero.
- `routingRephaseRegression_hostile_incidentAssembly_ne`: the one-end hostile phase change is
  rejected by the raw right-associated connection equations.
- `routingRephaseRegression_hostile_idealRouting_mate_entry`: the hostile rephased mate entry is
  exactly `-I`, not one.

## iii. Table of contents

- A. Distinct non-real channel-end phases
- B. Independently expanded component operator and state
- C. Right-associated raw equations
- D. Left-associated raw equations
- E. Agreement of both parenthesizations
- F. Hostile one-end rephasing

## iv. References

This is fail-capable evidence for ledger row N-07, whose failure mode is index- or
convention-dependent behavior, with the three-stage N-08 hierarchy as a downstream canary. The
fixture is algebraic and fixed-frequency. It makes no passivity, losslessness, reciprocity,
reference-plane, time-reversal, propagation, stability, causality, physical-realization, or
electromagnetic-power claim.
-/

@[expose] public section

namespace Optics

noncomputable section

/-- Raw assembly uses the same ambient equality test as relational closure. -/
local instance routingRephaseRegressionClosureChannelDecidableEq :
    DecidableEq ReuseRegressionChannel :=
  PortConnectionFamily.closureChannelDecidableEq

/-- Right-associated raw assembly uses closure equality on connected channels. -/
local instance routingRephaseRegressionRightClosureConnectedDecidableEq :
    DecidableEq reuseRegressionRightFamily.Channel :=
  reuseRegressionRightFamily.closureConnectedChannelDecidableEq

/-- Left-associated raw assembly uses closure equality on connected channels. -/
local instance routingRephaseRegressionLeftClosureConnectedDecidableEq :
    DecidableEq reuseRegressionLeftFamily.Channel :=
  reuseRegressionLeftFamily.closureConnectedChannelDecidableEq

/-!
## A. Distinct non-real channel-end phases
-/

/-- The positive quadrature phase as an element of the complex unit circle. -/
def routingRephaseRegressionI : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

/-- The negative quadrature phase as an element of the complex unit circle. -/
def routingRephaseRegressionNegI : Circle :=
  ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩

/-- The matched ambient gauge. Every internal outgoing source and its incident mate use the same
phase, while opposite directions on each physical connection use the other quadrature phase. -/
def routingRephaseRegressionGauge : ChannelEndGauge ReuseRegressionChannel where
  incident endpoint :=
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .first, true => routingRephaseRegressionNegI
    | .second, false => routingRephaseRegressionI
    | .second, true => routingRephaseRegressionI
    | .third, false => routingRephaseRegressionNegI
    | .third, true => routingRephaseRegressionNegI
    | .fourth, false => routingRephaseRegressionI
    | .fourth, true => 1
  outgoing endpoint :=
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .first, true => routingRephaseRegressionI
    | .second, false => routingRephaseRegressionNegI
    | .second, true => routingRephaseRegressionNegI
    | .third, false => routingRephaseRegressionI
    | .third, true => routingRephaseRegressionI
    | .fourth, false => routingRephaseRegressionNegI
    | .fourth, true => routingRephaseRegressionNegI

/-- The right-associated connection family satisfies the mate-matching condition by direct
inspection of all six routed channel ends. -/
lemma routingRephaseRegression_right_matched :
    reuseRegressionRightFamily.IsMatchedGauge routingRephaseRegressionGauge := by
  rintro ⟨connection, channel⟩
  rcases connection with first | later
  · cases first
    rcases channel with mode | mode <;> cases mode <;> rfl
  · rcases later with second | third
    · cases second
      rcases channel with mode | mode <;> cases mode <;> rfl
    · cases third
      rcases channel with mode | mode <;> cases mode <;> rfl

/-- The left-associated connection family satisfies the same mate-matching condition by direct
inspection, independently of any associativity result. -/
lemma routingRephaseRegression_left_matched :
    reuseRegressionLeftFamily.IsMatchedGauge routingRephaseRegressionGauge := by
  rintro ⟨connection, channel⟩
  rcases connection with earlier | third
  · rcases earlier with first | second
    · cases first
      rcases channel with mode | mode <;> cases mode <;> rfl
    · cases second
      rcases channel with mode | mode <;> cases mode <;> rfl
  · cases third
    rcases channel with mode | mode <;> cases mode <;> rfl

/-!
## B. Independently expanded component operator and state
-/

/-- The directly expanded component operator after the declared channel-end coordinate change.

Its four nonzero west-to-east gains are `2I`, `-3`, `-5`, and `-7`. -/
def routingRephaseRegressionComponentOperator :
    ModeTransform (Incident ReuseRegressionChannel) (Outgoing ReuseRegressionChannel) :=
  fun output input =>
    match output.channel.1.1, output.channel.1.2,
        input.channel.1.1, input.channel.1.2 with
    | .first, true, .first, false => 2 * Complex.I
    | .second, true, .second, false => -3
    | .third, true, .third, false => -5
    | .fourth, true, .fourth, false => -7
    | _, _, _, _ => 0

/-- The graph relation of the directly expanded phase-sensitive component operator. -/
def routingRephaseRegressionComponentBehavior :
    LinearBehavior (Incident ReuseRegressionChannel) (Outgoing ReuseRegressionChannel) :=
  routingRephaseRegressionComponentOperator.toBehavior

/-- The hand-expanded component operator is exactly the primitive entrywise rephasing of the
unphased fixture operator. This finite expansion uses no routing or netlist covariance result. -/
lemma routingRephaseRegression_componentOperator_eq_rephase :
    routingRephaseRegressionComponentOperator =
      reuseRegressionComponentOperator.rephase
        routingRephaseRegressionGauge.incident
        routingRephaseRegressionGauge.outgoing := by
  funext output input
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode <;>
    norm_num [routingRephaseRegressionComponentOperator,
      reuseRegressionComponentOperator, reuseRegressionScattering,
      ModeTransform.rephase, routingRephaseRegressionGauge,
      routingRephaseRegressionI, routingRephaseRegressionNegI,
      Complex.inv_I, Complex.ext_iff] <;>
    ring

/-- The hand-expanded rephased incident state. Its nonzero west-port values are `1`, `2I`,
`-6I`, and `30I`. -/
def routingRephaseRegressionIncident :
    ModeAmplitude (Incident ReuseRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .second, false => 2 * Complex.I
    | .third, false => -6 * Complex.I
    | .fourth, false => 30 * Complex.I
    | _, _ => 0

/-- The hand-expanded rephased outgoing state. Its nonzero east-port values are `2I`, `-6I`,
`30I`, and `-210I`. -/
def routingRephaseRegressionOutgoing :
    ModeAmplitude (Outgoing ReuseRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, true => 2 * Complex.I
    | .second, true => -6 * Complex.I
    | .third, true => 30 * Complex.I
    | .fourth, true => -210 * Complex.I
    | _, _ => 0

/-- The positive incident state is exactly the coordinatewise primitive rephasing of the unphased
state. The proof inspects every component, port, and mode directly. -/
lemma routingRephaseRegression_incident_eq_rephase :
    routingRephaseRegressionIncident =
      ModeAmplitude.rephase routingRephaseRegressionGauge.incident
        reuseRegressionIncident := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode <;>
    norm_num [routingRephaseRegressionIncident, reuseRegressionIncident,
      routingRephaseRegressionGauge, routingRephaseRegressionI,
      routingRephaseRegressionNegI, Complex.ext_iff]

/-- The positive outgoing state is exactly the coordinatewise primitive rephasing of the unphased
state, independently of every connection-family covariance result. -/
lemma routingRephaseRegression_outgoing_eq_rephase :
    routingRephaseRegressionOutgoing =
      ModeAmplitude.rephase routingRephaseRegressionGauge.outgoing
        reuseRegressionOutgoing := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode <;>
    norm_num [routingRephaseRegressionOutgoing, reuseRegressionOutgoing,
      routingRephaseRegressionGauge, routingRephaseRegressionI,
      routingRephaseRegressionNegI, Complex.ext_iff]

/-- Restrict the hand-expanded incident state to an arbitrary connection family's external
input labels. -/
def routingRephaseRegressionExternalInput {index : Type*}
    (family : PortConnectionFamily reuseRegressionPortModeFamily index) :
    ModeAmplitude (Incident family.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    routingRephaseRegressionIncident (Incident.mk endpoint.channel.1)

/-- Restrict the hand-expanded outgoing state to an arbitrary connection family's external
output labels. -/
def routingRephaseRegressionExternalOutput {index : Type*}
    (family : PortConnectionFamily reuseRegressionPortModeFamily index) :
    ModeAmplitude (Outgoing family.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    routingRephaseRegressionOutgoing (Outgoing.mk endpoint.channel.1)

/-- The independently expanded incident and outgoing states satisfy the phase-sensitive component
operator before any connection equation is used. -/
lemma routingRephaseRegression_mem_componentBehavior :
    (routingRephaseRegressionIncident, routingRephaseRegressionOutgoing) ∈
      routingRephaseRegressionComponentBehavior := by
  classical
  rw [routingRephaseRegressionComponentBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [← Incident.channelEquiv.symm.sum_comp]
  cases component <;> cases port <;> cases mode <;>
    simp [routingRephaseRegressionComponentOperator,
      routingRephaseRegressionIncident, routingRephaseRegressionOutgoing,
      Fintype.sum_sigma, Fintype.sum_prod_type, reuseRegression_sum_component] <;>
    ring

/-- The three forward cross-component amplitudes are nonzero and carry the exact distinct values
`2I`, `-6I`, and `30I`. -/
lemma routingRephaseRegression_cross_amplitudes_nonzero :
    routingRephaseRegressionOutgoing
          (Outgoing.mk ⟨(.first, true), ()⟩) ≠ 0 ∧
      routingRephaseRegressionOutgoing
          (Outgoing.mk ⟨(.second, true), ()⟩) ≠ 0 ∧
      routingRephaseRegressionOutgoing
          (Outgoing.mk ⟨(.third, true), ()⟩) ≠ 0 := by
  norm_num [routingRephaseRegressionOutgoing, Complex.ext_iff]

/-!
## C. Right-associated raw equations
-/

/-- The right-associated raw incident assembly satisfies all six mate equations and both external
injection equations, expanded without a rephase-covariance lemma. -/
lemma routingRephaseRegression_right_incidentAssembly :
    routingRephaseRegressionIncident =
      reuseRegressionRightFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionRightFamily) := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · let external : reuseRegressionRightFamily.ExternalChannel :=
      ⟨⟨(.first, false), ()⟩, reuseRegression_right_firstWest_external⟩
    change routingRephaseRegressionIncident (Incident.mk external.1) =
      reuseRegressionRightFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionRightFamily)
          (Incident.mk external.1)
    rw [reuseRegressionRightFamily.incidentAssembly_apply_external]
    rfl
  · rw [show (⟨(.first, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inl (), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inl (), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inl ()), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inl ()), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inr ()), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.fourth, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inr ()), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · let external : reuseRegressionRightFamily.ExternalChannel :=
      ⟨⟨(.fourth, true), ()⟩, reuseRegression_right_fourthEast_external⟩
    change routingRephaseRegressionIncident (Incident.mk external.1) =
      reuseRegressionRightFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionRightFamily)
          (Incident.mk external.1)
    rw [reuseRegressionRightFamily.incidentAssembly_apply_external]
    rfl

/-- Right-associated readout directly restricts the hand-expanded outgoing state. -/
lemma routingRephaseRegression_right_outputReadout :
    routingRephaseRegressionExternalOutput reuseRegressionRightFamily =
      reuseRegressionRightFamily.externalOutgoingReadout.toLinearMap
        routingRephaseRegressionOutgoing := by
  classical
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rw [ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The independently expanded phase-sensitive state satisfies the right-associated raw closure
equations. -/
lemma routingRephaseRegression_mem_right :
    (routingRephaseRegressionExternalInput reuseRegressionRightFamily,
        routingRephaseRegressionExternalOutput reuseRegressionRightFamily) ∈
      reuseRegressionRightFamily.closeBehavior
        routingRephaseRegressionComponentBehavior := by
  classical
  rw [PortConnectionFamily.mem_closeBehavior_iff]
  exact ⟨routingRephaseRegressionIncident, routingRephaseRegressionOutgoing,
    routingRephaseRegression_mem_componentBehavior,
    routingRephaseRegression_right_incidentAssembly,
    routingRephaseRegression_right_outputReadout⟩

/-!
## D. Left-associated raw equations
-/

/-- The left-associated raw incident assembly independently satisfies all six mate equations and
both external injection equations. -/
lemma routingRephaseRegression_left_incidentAssembly :
    routingRephaseRegressionIncident =
      reuseRegressionLeftFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionLeftFamily) := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · let external : reuseRegressionLeftFamily.ExternalChannel :=
      ⟨⟨(.first, false), ()⟩, reuseRegression_left_firstWest_external⟩
    change routingRephaseRegressionIncident (Incident.mk external.1) =
      reuseRegressionLeftFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionLeftFamily)
          (Incident.mk external.1)
    rw [reuseRegressionLeftFamily.incidentAssembly_apply_external]
    rfl
  · rw [show (⟨(.first, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inl (Sum.inl ()), Sum.inl ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inl (Sum.inl ()), Sum.inr ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inl (Sum.inr ()), Sum.inl ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inl (Sum.inr ()), Sum.inr ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inr (), Sum.inl ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.fourth, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionLeftFamily.channelEmbedding
          ⟨Sum.inr (), Sum.inr ()⟩ from rfl,
      reuseRegressionLeftFamily.incidentAssembly_apply_connected_channel]
    rfl
  · let external : reuseRegressionLeftFamily.ExternalChannel :=
      ⟨⟨(.fourth, true), ()⟩, reuseRegression_left_fourthEast_external⟩
    change routingRephaseRegressionIncident (Incident.mk external.1) =
      reuseRegressionLeftFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionLeftFamily)
          (Incident.mk external.1)
    rw [reuseRegressionLeftFamily.incidentAssembly_apply_external]
    rfl

/-- Left-associated readout directly restricts the same hand-expanded outgoing state. -/
lemma routingRephaseRegression_left_outputReadout :
    routingRephaseRegressionExternalOutput reuseRegressionLeftFamily =
      reuseRegressionLeftFamily.externalOutgoingReadout.toLinearMap
        routingRephaseRegressionOutgoing := by
  classical
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rw [ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The independently expanded phase-sensitive state satisfies the left-associated raw closure
equations. -/
lemma routingRephaseRegression_mem_left :
    (routingRephaseRegressionExternalInput reuseRegressionLeftFamily,
        routingRephaseRegressionExternalOutput reuseRegressionLeftFamily) ∈
      reuseRegressionLeftFamily.closeBehavior
        routingRephaseRegressionComponentBehavior := by
  classical
  rw [PortConnectionFamily.mem_closeBehavior_iff]
  exact ⟨routingRephaseRegressionIncident, routingRephaseRegressionOutgoing,
    routingRephaseRegression_mem_componentBehavior,
    routingRephaseRegression_left_incidentAssembly,
    routingRephaseRegression_left_outputReadout⟩

/-!
## E. Agreement of both parenthesizations
-/

/-- Both independently expanded parenthesizations admit the same phase-sensitive ambient raw
state and expose the same exact output value `-210I`. -/
lemma routingRephaseRegression_mem_both_parenthesizations :
    (routingRephaseRegressionExternalInput reuseRegressionRightFamily,
          routingRephaseRegressionExternalOutput reuseRegressionRightFamily) ∈
        reuseRegressionRightFamily.closeBehavior
          routingRephaseRegressionComponentBehavior ∧
      (routingRephaseRegressionExternalInput reuseRegressionLeftFamily,
          routingRephaseRegressionExternalOutput reuseRegressionLeftFamily) ∈
        reuseRegressionLeftFamily.closeBehavior
          routingRephaseRegressionComponentBehavior ∧
      routingRephaseRegressionExternalOutput reuseRegressionRightFamily
          (Outgoing.mk
            ⟨⟨(.fourth, true), ()⟩, reuseRegression_right_fourthEast_external⟩) =
        routingRephaseRegressionExternalOutput reuseRegressionLeftFamily
          (Outgoing.mk
            ⟨⟨(.fourth, true), ()⟩, reuseRegression_left_fourthEast_external⟩) ∧
      routingRephaseRegressionExternalOutput reuseRegressionLeftFamily
          (Outgoing.mk
            ⟨⟨(.fourth, true), ()⟩, reuseRegression_left_fourthEast_external⟩) =
        -210 * Complex.I := by
  refine ⟨routingRephaseRegression_mem_right,
    routingRephaseRegression_mem_left, ?_, ?_⟩ <;>
    norm_num [routingRephaseRegressionExternalOutput,
      routingRephaseRegressionOutgoing]

/-!
## F. Hostile one-end rephasing
-/

/-- The hostile gauge changes only the second-west incident endpoint from phase `I` to phase `1`.
All outgoing phases, including the connected first-east source phase `I`, remain unchanged. -/
def routingRephaseRegressionHostileGauge : ChannelEndGauge ReuseRegressionChannel where
  incident endpoint :=
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .first, true => routingRephaseRegressionNegI
    | .second, false => 1
    | .second, true => routingRephaseRegressionI
    | .third, false => routingRephaseRegressionNegI
    | .third, true => routingRephaseRegressionNegI
    | .fourth, false => routingRephaseRegressionI
    | .fourth, true => 1
  outgoing := routingRephaseRegressionGauge.outgoing

/-- The hostile gauge fails mate matching at the first-east to second-west routed direction. -/
lemma routingRephaseRegression_hostile_not_matched :
    ¬reuseRegressionRightFamily.IsMatchedGauge routingRephaseRegressionHostileGauge := by
  intro hMatched
  have hFirst := hMatched ⟨Sum.inl (), Sum.inl ()⟩
  change (1 : Circle) = routingRephaseRegressionI at hFirst
  have hCoe := congrArg (fun phase : Circle => (phase : ℂ)) hFirst
  have hImag := congrArg Complex.im hCoe
  norm_num [routingRephaseRegressionI] at hImag

/-- The hostile incident state differs from the matched state only at second-west, where it has
the exact value `2` rather than `2I`. -/
def routingRephaseRegressionHostileIncident :
    ModeAmplitude (Incident ReuseRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .second, false => 2
    | .third, false => -6 * Complex.I
    | .fourth, false => 30 * Complex.I
    | _, _ => 0

/-- The hostile second-west incident coordinate is exactly `2`. -/
lemma routingRephaseRegression_hostile_incident_secondWest :
    routingRephaseRegressionHostileIncident
      (Incident.mk ⟨(.second, false), ()⟩) = 2 := rfl

/-- Raw routing still forces the second-west coordinate to equal the first-east outgoing value
`2I`, because changing a coordinate gauge does not change the stored unit-gain connection. -/
lemma routingRephaseRegression_hostile_routed_secondWest :
    reuseRegressionRightFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionRightFamily)
        (Incident.mk ⟨(.second, false), ()⟩) =
      2 * Complex.I := by
  classical
  rw [show (⟨(.second, false), ()⟩ : ReuseRegressionChannel) =
      reuseRegressionRightFamily.channelEmbedding
        ⟨Sum.inl (), Sum.inr ()⟩ from rfl,
    reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
  rfl

/-- The one-end hostile rephasing is rejected by the raw connection equations: at the same
second-west coordinate the proposed incident state is `2`, while routing forces `2I`. -/
lemma routingRephaseRegression_hostile_incidentAssembly_ne :
    routingRephaseRegressionHostileIncident ≠
      reuseRegressionRightFamily.incidentAssembly routingRephaseRegressionOutgoing
        (routingRephaseRegressionExternalInput reuseRegressionRightFamily) := by
  intro hAssembly
  have hCoordinate := congrArg
    (fun incident : ModeAmplitude (Incident ReuseRegressionChannel) =>
      incident (Incident.mk ⟨(.second, false), ()⟩)) hAssembly
  rw [routingRephaseRegression_hostile_incident_secondWest,
    routingRephaseRegression_hostile_routed_secondWest] at hCoordinate
  norm_num [Complex.ext_iff] at hCoordinate

end

end Optics
