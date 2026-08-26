/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.BeamSplitterPhysical
public import Physlib.Optics.Components.MirrorPhysical

/-!
# Regression for the component-owned physical-port suite

## i. Overview

This Phase 9a regression assembles one beam splitter and one mirror into a heterogeneous
`ScatteringComponentFamily`. Its component type and all declarations carry a `9a` suffix so a
later Phase 9b family can add polarization and interface members without changing these anchors.

The nonzero raw fixture uses beam-splitter parameters `t = 3/5`, `k = 4/5`, beam inputs `1` and
`2`, and mirror coefficient `I` with mirror input `3`. The exact outputs are
`(3 - 8I)/5`, `(6 - 4I)/5`, and `3I`. Local actions are expanded from primitive matrices; the
indexed block action and aggregate channel reindex are then expanded without any component
packaging, realization, or `ScatteringComponentFamily` assembled-action lemma under test.

The hostile family swaps only the two beam-splitter output endpoints. On the same input its beam
outputs become `(6 - 4I)/5` and `(3 - 8I)/5`, while the mirror remains `3I`. The first coordinate
therefore proves a genuine output inequality. This sentinel can fail under endpoint-order,
component-ownership, row/column, or component-index errors; Phase 9b can add fiber and side
sentinels without altering it.

## ii. Key results

- `physicalPortSuite9a_beam_raw_action`: primitive `3/5`, `4/5` beam action.
- `physicalPortSuite9a_mirror_raw_action`: primitive phase-`I` mirror action.
- `physicalPortSuite9a_indexed_action`: direct dependent block-diagonal action.
- `physicalPortSuite9a_aggregate_action`: exact mixed-family aggregate output.
- `physicalPortSuite9a_hostile_aggregate_action`: exact swapped-endpoint output.
- `physicalPortSuite9a_hostile_action_ne`: the hostile output differs on the same input.

## iii. Table of contents

- A. Exact parameters and primitive component actions
- B. Extension-safe mixed component family
- C. Raw indexed and aggregate action
- D. Hostile endpoint-swap family
- E. Endpoint graph anchor and non-claims

## iv. References

All coefficients are algebraic sentinels. No reciprocity, time reversal, propagation, causality,
dispersion, material, electromagnetic-power, coating, or physical-realization claim is made.
-/

@[expose] public section

namespace Optics

noncomputable section

/-!
## A. Exact parameters and primitive component actions
-/

/-- The exact `3/5`, `4/5` beam-splitter parameters. -/
def physicalPortSuite9aBeamParameters : BeamSplitter.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5

/-- The regression beam-splitter parameters satisfy the explicit validity predicate. -/
lemma physicalPortSuite9aBeamParameters_isValid :
    physicalPortSuite9aBeamParameters.IsValid := by
  refine ⟨by norm_num [physicalPortSuite9aBeamParameters],
    by norm_num [physicalPortSuite9aBeamParameters], ?_⟩
  norm_num [physicalPortSuite9aBeamParameters, BeamSplitter.Parameters.IsUnitary,
    BeamSplitter.Parameters.powerFactor]

/-- The exact phase-`I` mirror parameters. -/
def physicalPortSuite9aMirrorParameters : Mirror.Parameters where
  reflectionCoefficient := Complex.I

/-- The phase-`I` mirror coefficient has unit squared modulus. -/
lemma physicalPortSuite9aMirrorParameters_isUnitPhase :
    physicalPortSuite9aMirrorParameters.IsUnitPhase := by
  norm_num [physicalPortSuite9aMirrorParameters, Mirror.Parameters.IsUnitPhase,
    Complex.normSq_apply]

/-- The primitive raw beam input has coordinates one and two. -/
def physicalPortSuite9aBeamRawInput : ModeAmplitude (Unit ⊕ Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl () => 1
    | Sum.inr () => 2

/-- The primitive raw beam output has the two exact quadrature-mixed values. -/
def physicalPortSuite9aBeamRawOutput : ModeAmplitude (Unit ⊕ Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl () => (3 - 8 * Complex.I) / 5
    | Sum.inr () => (6 - 4 * Complex.I) / 5

/-- Primitive matrix multiplication gives both exact beam-splitter outputs. -/
lemma physicalPortSuite9a_beam_raw_action :
    (BeamSplitter.scattering physicalPortSuite9aBeamParameters Unit).toModeTransform.toLinearMap
        physicalPortSuite9aBeamRawInput =
      physicalPortSuite9aBeamRawOutput := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟩ | ⟨⟩ <;>
    simp [BeamSplitter.scattering, BeamSplitter.mixing,
      BeamSplitter.crossCoefficient, physicalPortSuite9aBeamParameters,
      physicalPortSuite9aBeamRawInput, physicalPortSuite9aBeamRawOutput,
      ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]
  <;> ring_nf

/-- The primitive raw mirror input is three. -/
def physicalPortSuite9aMirrorRawInput : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 3

/-- The primitive raw phase-`I` mirror output is `3I`. -/
def physicalPortSuite9aMirrorRawOutput : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 3 * Complex.I

/-- Primitive matrix multiplication gives the exact phase-`I` mirror output. -/
lemma physicalPortSuite9a_mirror_raw_action :
    (Mirror.scattering physicalPortSuite9aMirrorParameters Unit).toModeTransform.toLinearMap
        physicalPortSuite9aMirrorRawInput =
      physicalPortSuite9aMirrorRawOutput := by
  apply WithLp.ofLp_injective 2
  funext output
  cases output
  simp [Mirror.scattering, Mirror.reflection, physicalPortSuite9aMirrorParameters,
    physicalPortSuite9aMirrorRawInput, physicalPortSuite9aMirrorRawOutput,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply]
  ring

/-- The beam input transported to the two owned physical ports. -/
def physicalPortSuite9aBeamLocalInput :
    ModeAmplitude (BeamSplitter.portFamily Unit).Channel :=
  ModeAmplitude.reindex (BeamSplitter.channelEquiv Unit)
    physicalPortSuite9aBeamRawInput

/-- The exact beam output transported to the two owned physical ports. -/
def physicalPortSuite9aBeamLocalOutput :
    ModeAmplitude (BeamSplitter.portFamily Unit).Channel :=
  ModeAmplitude.reindex (BeamSplitter.channelEquiv Unit)
    physicalPortSuite9aBeamRawOutput

/-- Unfolding physical scattering recovers the primitive beam action in owned port labels. -/
lemma physicalPortSuite9a_beam_local_action :
    ModeTransform.toLinearMap
        (BeamSplitter.physicalScattering physicalPortSuite9aBeamParameters Unit).toModeTransform
        physicalPortSuite9aBeamLocalInput =
      physicalPortSuite9aBeamLocalOutput := by
  rw [BeamSplitter.physicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq, physicalPortSuite9aBeamLocalInput,
    ModeAmplitude.reindex_symm_reindex, physicalPortSuite9a_beam_raw_action]
  rfl

/-- The mirror input transported to its owned surface port. -/
def physicalPortSuite9aMirrorLocalInput :
    ModeAmplitude (Mirror.portFamily Unit).Channel :=
  ModeAmplitude.reindex (Mirror.channelEquiv Unit)
    physicalPortSuite9aMirrorRawInput

/-- The mirror output transported to its owned surface port. -/
def physicalPortSuite9aMirrorLocalOutput :
    ModeAmplitude (Mirror.portFamily Unit).Channel :=
  ModeAmplitude.reindex (Mirror.channelEquiv Unit)
    physicalPortSuite9aMirrorRawOutput

/-- Unfolding physical scattering recovers the primitive mirror action in owned port labels. -/
lemma physicalPortSuite9a_mirror_local_action :
    ModeTransform.toLinearMap
        (Mirror.physicalScattering physicalPortSuite9aMirrorParameters Unit).toModeTransform
        physicalPortSuite9aMirrorLocalInput =
      physicalPortSuite9aMirrorLocalOutput := by
  rw [Mirror.physicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq, physicalPortSuite9aMirrorLocalInput,
    ModeAmplitude.reindex_symm_reindex, physicalPortSuite9a_mirror_raw_action]
  rfl

/-!
## B. Extension-safe mixed component family
-/

/-- The Phase 9a component labels; later phases use a larger type without modifying these labels. -/
inductive PhysicalPortSuite9aComponent
  | beamSplitter
  | mirror
  deriving DecidableEq

/-- The two Phase 9a component labels form a finite family. -/
instance : Fintype PhysicalPortSuite9aComponent where
  elems := {PhysicalPortSuite9aComponent.beamSplitter,
    PhysicalPortSuite9aComponent.mirror}
  complete component := by
    cases component <;> simp

/-- The component-owned port family selected by each Phase 9a component label. -/
def physicalPortSuite9aPortFamily : PhysicalPortSuite9aComponent → PortModeFamily
  | .beamSplitter => BeamSplitter.portFamily Unit
  | .mirror => Mirror.portFamily Unit

/-- The component-owned scattering law selected by each Phase 9a component label. -/
def physicalPortSuite9aScattering :
    (component : PhysicalPortSuite9aComponent) →
      ScatteringMatrix (physicalPortSuite9aPortFamily component).Channel
  | .beamSplitter =>
      BeamSplitter.physicalScattering physicalPortSuite9aBeamParameters Unit
  | .mirror => Mirror.physicalScattering physicalPortSuite9aMirrorParameters Unit

/-- The mixed Phase 9a scattering-component family. -/
abbrev physicalPortSuite9aFamily : ScatteringComponentFamily where
  Component := PhysicalPortSuite9aComponent
  portFamily := physicalPortSuite9aPortFamily
  scattering := physicalPortSuite9aScattering

/-- Every Phase 9a local channel family is finite. -/
local instance physicalPortSuite9aLocalChannelFintype
    (component : PhysicalPortSuite9aComponent) :
    Fintype (physicalPortSuite9aFamily.portFamily component).Channel := by
  cases component
  · change Fintype (BeamSplitter.portFamily Unit).Channel
    infer_instance
  · change Fintype (Mirror.portFamily Unit).Channel
    infer_instance

/-- Every Phase 9a local channel family has decidable equality. -/
local instance physicalPortSuite9aLocalChannelDecidableEq
    (component : PhysicalPortSuite9aComponent) :
    DecidableEq (physicalPortSuite9aFamily.portFamily component).Channel := by
  cases component
  · change DecidableEq (BeamSplitter.portFamily Unit).Channel
    infer_instance
  · change DecidableEq (Mirror.portFamily Unit).Channel
    infer_instance

/-- The indexed Phase 9a channels have decidable equality. -/
local instance physicalPortSuite9aIndexedChannelDecidableEq :
    DecidableEq physicalPortSuite9aFamily.IndexedChannel :=
  Classical.decEq _

/-- The aggregate Phase 9a channels are finite by component/channel reassociation. -/
local instance physicalPortSuite9aAggregateChannelFintype :
    Fintype physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv physicalPortSuite9aFamily.IndexedChannel
    physicalPortSuite9aFamily.channelEquiv

/-- The aggregate Phase 9a channels have decidable equality in indexed coordinates. -/
local instance physicalPortSuite9aAggregateChannelDecidableEq :
    DecidableEq physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aFamily.channelEquiv.symm.decidableEq

/-- The first local beam-splitter physical channel. -/
abbrev physicalPortSuite9aBeamFirstLocal :
    (physicalPortSuite9aFamily.portFamily .beamSplitter).Channel :=
  ⟨BeamSplitter.Port.first, ()⟩

/-- The second local beam-splitter physical channel. -/
abbrev physicalPortSuite9aBeamSecondLocal :
    (physicalPortSuite9aFamily.portFamily .beamSplitter).Channel :=
  ⟨BeamSplitter.Port.second, ()⟩

/-- The local mirror surface channel. -/
abbrev physicalPortSuite9aMirrorLocal :
    (physicalPortSuite9aFamily.portFamily .mirror).Channel :=
  ⟨Mirror.Port.surface, ()⟩

/-- The first beam channel in indexed component coordinates. -/
abbrev physicalPortSuite9aBeamFirstIndexed : physicalPortSuite9aFamily.IndexedChannel :=
  ⟨.beamSplitter, physicalPortSuite9aBeamFirstLocal⟩

/-- The second beam channel in indexed component coordinates. -/
abbrev physicalPortSuite9aBeamSecondIndexed : physicalPortSuite9aFamily.IndexedChannel :=
  ⟨.beamSplitter, physicalPortSuite9aBeamSecondLocal⟩

/-- The mirror channel in indexed component coordinates. -/
abbrev physicalPortSuite9aMirrorIndexed : physicalPortSuite9aFamily.IndexedChannel :=
  ⟨.mirror, physicalPortSuite9aMirrorLocal⟩

/-- A finite sum over the indexed suite is the sum of its three displayed coordinates. -/
lemma physicalPortSuite9a_sum_indexed
    (value : physicalPortSuite9aFamily.IndexedChannel → ℂ) :
    (∑ channel, value channel) =
      value physicalPortSuite9aBeamFirstIndexed +
        value physicalPortSuite9aBeamSecondIndexed +
          value physicalPortSuite9aMirrorIndexed := by
  classical
  have hUniv :
      (Finset.univ : Finset physicalPortSuite9aFamily.IndexedChannel) =
        {physicalPortSuite9aBeamFirstIndexed,
          physicalPortSuite9aBeamSecondIndexed,
          physicalPortSuite9aMirrorIndexed} := by
    ext channel
    rcases channel with ⟨component, ⟨port, mode⟩⟩
    cases component
    · cases port <;> cases mode <;> simp
    · cases port
      cases mode
      simp
  have hBeamPorts :
      physicalPortSuite9aBeamFirstLocal ≠ physicalPortSuite9aBeamSecondLocal := by
    intro hEqual
    have hPort := congrArg (fun channel => channel.1) hEqual
    cases hPort
  have hFirst :
      physicalPortSuite9aBeamFirstIndexed ∉
        ({physicalPortSuite9aBeamSecondIndexed,
          physicalPortSuite9aMirrorIndexed} :
          Finset physicalPortSuite9aFamily.IndexedChannel) := by
    simp [physicalPortSuite9aBeamFirstIndexed,
      physicalPortSuite9aBeamSecondIndexed, physicalPortSuite9aMirrorIndexed,
      physicalPortSuite9aBeamFirstLocal, physicalPortSuite9aBeamSecondLocal,
      physicalPortSuite9aMirrorLocal, hBeamPorts]
  have hSecond :
      physicalPortSuite9aBeamSecondIndexed ∉
        ({physicalPortSuite9aMirrorIndexed} :
          Finset physicalPortSuite9aFamily.IndexedChannel) := by
    simp [physicalPortSuite9aBeamSecondIndexed, physicalPortSuite9aMirrorIndexed]
  rw [hUniv]
  rw [Finset.sum_insert hFirst, Finset.sum_insert hSecond,
    Finset.sum_singleton]
  ring

/-!
## C. Raw indexed and aggregate action
-/

/-- The nonzero mixed input in indexed component/local-channel coordinates. -/
def physicalPortSuite9aIndexedInput :
    ModeAmplitude physicalPortSuite9aFamily.IndexedChannel :=
  WithLp.toLp 2 fun
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ => 1
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ => 2
    | ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩ => 3

/-- The exact mixed output in indexed component/local-channel coordinates. -/
def physicalPortSuite9aIndexedOutput :
    ModeAmplitude physicalPortSuite9aFamily.IndexedChannel :=
  WithLp.toLp 2 fun
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ =>
        (3 - 8 * Complex.I) / 5
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ =>
        (6 - 4 * Complex.I) / 5
    | ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩ => 3 * Complex.I

/-- The primitive three-channel matrix displayed in indexed component coordinates. -/
def physicalPortSuite9aExplicitIndexedTransform :
    ModeTransform physicalPortSuite9aFamily.IndexedChannel
      physicalPortSuite9aFamily.IndexedChannel := fun output input =>
  match output, input with
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ => 3 / 5
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ =>
      -Complex.I * (4 / 5)
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ =>
      -Complex.I * (4 / 5)
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ => 3 / 5
  | ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩,
      ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩ => Complex.I
  | _, _ => 0

/-- Unfolding the owned component laws gives the displayed primitive indexed matrix. -/
lemma physicalPortSuite9a_indexedScatteringMatrix_eq_explicit :
    physicalPortSuite9aFamily.indexedScatteringMatrix.toModeTransform =
      physicalPortSuite9aExplicitIndexedTransform := by
  ext output input
  rcases output with ⟨outputComponent, ⟨outputPort, outputMode⟩⟩
  rcases input with ⟨inputComponent, ⟨inputPort, inputMode⟩⟩
  cases outputComponent <;> cases inputComponent
  all_goals
    cases outputPort <;> cases outputMode <;>
      cases inputPort <;> cases inputMode
  all_goals
    simp [ScatteringComponentFamily.indexedScatteringMatrix,
      physicalPortSuite9aExplicitIndexedTransform, physicalPortSuite9aFamily,
      physicalPortSuite9aScattering, physicalPortSuite9aPortFamily,
      BeamSplitter.physicalScattering, Mirror.physicalScattering,
      ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
      BeamSplitter.scattering, BeamSplitter.mixing, BeamSplitter.crossCoefficient,
      BeamSplitter.channelEquiv, Mirror.scattering, Mirror.reflection,
      physicalPortSuite9aBeamParameters,
      physicalPortSuite9aMirrorParameters, Matrix.blockDiagonal'_apply]

/-- Restricting the indexed input to the beam component gives the raw owned-port fixture. -/
lemma physicalPortSuite9aIndexedInput_restrict_beam :
    physicalPortSuite9aIndexedInput.restrictEmbedding
        (Function.Embedding.sigmaMk PhysicalPortSuite9aComponent.beamSplitter) =
      physicalPortSuite9aBeamLocalInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, mode⟩
  cases port <;> cases mode <;> rfl

/-- Restricting the indexed input to the mirror gives the raw owned-port fixture. -/
lemma physicalPortSuite9aIndexedInput_restrict_mirror :
    physicalPortSuite9aIndexedInput.restrictEmbedding
        (Function.Embedding.sigmaMk PhysicalPortSuite9aComponent.mirror) =
      physicalPortSuite9aMirrorLocalInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, mode⟩
  cases port
  cases mode
  rfl

/-- Primitive local actions assemble directly into the exact indexed block-diagonal output. -/
lemma physicalPortSuite9a_indexed_action :
    physicalPortSuite9aFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aIndexedInput =
      physicalPortSuite9aIndexedOutput := by
  rw [physicalPortSuite9a_indexedScatteringMatrix_eq_explicit]
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨component, ⟨port, mode⟩⟩
  cases component
  · cases port <;> cases mode
    all_goals
      simp [physicalPortSuite9aExplicitIndexedTransform,
        physicalPortSuite9aIndexedInput, physicalPortSuite9aIndexedOutput,
        ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, physicalPortSuite9a_sum_indexed]
    all_goals ring_nf
  · cases port
    cases mode
    simp [physicalPortSuite9aExplicitIndexedTransform,
      physicalPortSuite9aIndexedInput, physicalPortSuite9aIndexedOutput,
      ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, physicalPortSuite9a_sum_indexed]
    ring

/-- The mixed input in aggregate component-owned physical-port coordinates. -/
def physicalPortSuite9aAggregateInput :
    ModeAmplitude physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9aFamily.channelEquiv
    physicalPortSuite9aIndexedInput

/-- The exact mixed output in aggregate component-owned physical-port coordinates. -/
def physicalPortSuite9aAggregateOutput :
    ModeAmplitude physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9aFamily.channelEquiv
    physicalPortSuite9aIndexedOutput

/-- Aggregate input evaluation is indexed input evaluation at the inverse reassociation. -/
lemma physicalPortSuite9aAggregateInput_apply
    (channel : physicalPortSuite9aFamily.IndexedChannel) :
    physicalPortSuite9aAggregateInput
        (physicalPortSuite9aFamily.channelEquiv channel) =
      physicalPortSuite9aIndexedInput channel := by
  rw [physicalPortSuite9aAggregateInput, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]

/-- Aggregate output evaluation is indexed output evaluation at the inverse reassociation. -/
lemma physicalPortSuite9aAggregateOutput_apply
    (channel : physicalPortSuite9aFamily.IndexedChannel) :
    physicalPortSuite9aAggregateOutput
        (physicalPortSuite9aFamily.channelEquiv channel) =
      physicalPortSuite9aIndexedOutput channel := by
  rw [physicalPortSuite9aAggregateOutput, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]

/-- The first aggregate beam-splitter channel. -/
abbrev physicalPortSuite9aBeamFirst :
    physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aFamily.channelEquiv physicalPortSuite9aBeamFirstIndexed

/-- The second aggregate beam-splitter channel. -/
abbrev physicalPortSuite9aBeamSecond :
    physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aFamily.channelEquiv physicalPortSuite9aBeamSecondIndexed

/-- The aggregate mirror surface channel. -/
abbrev physicalPortSuite9aMirror :
    physicalPortSuite9aFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aFamily.channelEquiv physicalPortSuite9aMirrorIndexed

/-- The aggregate input has values one, two, and three on its three owned channels. -/
lemma physicalPortSuite9a_aggregate_input_coordinates :
    physicalPortSuite9aAggregateInput physicalPortSuite9aBeamFirst = 1 ∧
      physicalPortSuite9aAggregateInput physicalPortSuite9aBeamSecond = 2 ∧
      physicalPortSuite9aAggregateInput physicalPortSuite9aMirror = 3 := by
  constructor
  · rw [physicalPortSuite9aAggregateInput_apply]
    rfl
  constructor
  · rw [physicalPortSuite9aAggregateInput_apply]
    rfl
  · rw [physicalPortSuite9aAggregateInput_apply]
    rfl

/-- The aggregate output records both beam values and the phase-`I` mirror value. -/
lemma physicalPortSuite9a_aggregate_output_coordinates :
    physicalPortSuite9aAggregateOutput physicalPortSuite9aBeamFirst =
        (3 - 8 * Complex.I) / 5 ∧
      physicalPortSuite9aAggregateOutput physicalPortSuite9aBeamSecond =
        (6 - 4 * Complex.I) / 5 ∧
      physicalPortSuite9aAggregateOutput physicalPortSuite9aMirror = 3 * Complex.I := by
  constructor
  · rw [physicalPortSuite9aAggregateOutput_apply]
    rfl
  constructor
  · rw [physicalPortSuite9aAggregateOutput_apply]
    rfl
  · rw [physicalPortSuite9aAggregateOutput_apply]
    rfl

/-- The mixed family's aggregate action is the exact independently expanded output. -/
lemma physicalPortSuite9a_aggregate_action :
    physicalPortSuite9aFamily.assembledScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aAggregateInput =
      physicalPortSuite9aAggregateOutput := by
  rw [ScatteringComponentFamily.assembledScatteringMatrix,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.toLinearMap_reindex_eq,
    physicalPortSuite9aAggregateInput, ModeAmplitude.reindex_symm_reindex,
    physicalPortSuite9a_indexed_action]
  rfl

/-!
## D. Hostile endpoint-swap family
-/

/-- Swap the two beam-splitter physical output channels while preserving their mode values. -/
def physicalPortSuite9aBeamChannelSwap :
    (BeamSplitter.portFamily Unit).Channel ≃ (BeamSplitter.portFamily Unit).Channel where
  toFun
    | ⟨BeamSplitter.Port.first, value⟩ => ⟨BeamSplitter.Port.second, value⟩
    | ⟨BeamSplitter.Port.second, value⟩ => ⟨BeamSplitter.Port.first, value⟩
  invFun
    | ⟨BeamSplitter.Port.first, value⟩ => ⟨BeamSplitter.Port.second, value⟩
    | ⟨BeamSplitter.Port.second, value⟩ => ⟨BeamSplitter.Port.first, value⟩
  left_inv := by
    rintro ⟨port, value⟩
    cases port <;> rfl
  right_inv := by
    rintro ⟨port, value⟩
    cases port <;> rfl

/-- The hostile beam law swaps only output rows, not the incident endpoint labels. -/
def physicalPortSuite9aHostileBeamScattering :
    ScatteringMatrix (BeamSplitter.portFamily Unit).Channel where
  toModeTransform :=
    ModeTransform.reindex (Equiv.refl _) physicalPortSuite9aBeamChannelSwap
      (BeamSplitter.physicalScattering physicalPortSuite9aBeamParameters Unit).toModeTransform

/-- The hostile beam output is the positive output with its two owned endpoints exchanged. -/
def physicalPortSuite9aHostileBeamLocalOutput :
    ModeAmplitude (BeamSplitter.portFamily Unit).Channel :=
  ModeAmplitude.reindex physicalPortSuite9aBeamChannelSwap
    physicalPortSuite9aBeamLocalOutput

/-- Direct row reindexing forces the swapped exact beam output on the same local input. -/
lemma physicalPortSuite9a_hostile_beam_local_action :
    physicalPortSuite9aHostileBeamScattering.toModeTransform.toLinearMap
        physicalPortSuite9aBeamLocalInput =
      physicalPortSuite9aHostileBeamLocalOutput := by
  rw [physicalPortSuite9aHostileBeamScattering, ModeTransform.toLinearMap_reindex_eq]
  have hInput :
      ModeAmplitude.reindex (Equiv.refl _).symm physicalPortSuite9aBeamLocalInput =
        physicalPortSuite9aBeamLocalInput := by
    apply WithLp.ofLp_injective 2
    funext channel
    rfl
  rw [hInput, physicalPortSuite9a_beam_local_action]
  rfl

/-- The hostile family changes only the beam-splitter output endpoint assignment. -/
def physicalPortSuite9aHostileScattering :
    (component : PhysicalPortSuite9aComponent) →
      ScatteringMatrix (physicalPortSuite9aPortFamily component).Channel
  | .beamSplitter => physicalPortSuite9aHostileBeamScattering
  | .mirror => Mirror.physicalScattering physicalPortSuite9aMirrorParameters Unit

/-- The hostile mixed family has the same owned ports and a swapped beam output law. -/
abbrev physicalPortSuite9aHostileFamily : ScatteringComponentFamily where
  Component := PhysicalPortSuite9aComponent
  portFamily := physicalPortSuite9aPortFamily
  scattering := physicalPortSuite9aHostileScattering

/-- Hostile aggregate channels are finite through their explicit indexed reassociation. -/
local instance physicalPortSuite9aHostileAggregateChannelFintype :
    Fintype physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv physicalPortSuite9aHostileFamily.IndexedChannel
    physicalPortSuite9aHostileFamily.channelEquiv

/-- Hostile aggregate channels have decidable equality in indexed coordinates. -/
local instance physicalPortSuite9aHostileAggregateChannelDecidableEq :
    DecidableEq physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-- The hostile indexed output swaps the two beam values and leaves `3I` at the mirror. -/
def physicalPortSuite9aHostileIndexedOutput :
    ModeAmplitude physicalPortSuite9aHostileFamily.IndexedChannel :=
  WithLp.toLp 2 fun
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ =>
        (6 - 4 * Complex.I) / 5
    | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ =>
        (3 - 8 * Complex.I) / 5
    | ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩ => 3 * Complex.I

/-- The hostile family has the same three indexed channel coordinates. -/
lemma physicalPortSuite9a_hostile_sum_indexed
    (value : physicalPortSuite9aHostileFamily.IndexedChannel → ℂ) :
    (∑ channel, value channel) =
      value physicalPortSuite9aBeamFirstIndexed +
        value physicalPortSuite9aBeamSecondIndexed +
          value physicalPortSuite9aMirrorIndexed :=
  physicalPortSuite9a_sum_indexed value

/-- The primitive indexed matrix after swapping only the two beam output rows. -/
def physicalPortSuite9aHostileExplicitIndexedTransform :
    ModeTransform physicalPortSuite9aHostileFamily.IndexedChannel
      physicalPortSuite9aHostileFamily.IndexedChannel := fun output input =>
  match output, input with
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ =>
      -Complex.I * (4 / 5)
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ => 3 / 5
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.first, ()⟩⟩ => 3 / 5
  | ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩,
      ⟨.beamSplitter, ⟨BeamSplitter.Port.second, ()⟩⟩ =>
      -Complex.I * (4 / 5)
  | ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩,
      ⟨.mirror, ⟨Mirror.Port.surface, ()⟩⟩ => Complex.I
  | _, _ => 0

/-- Unfolding the hostile row reindex gives the displayed primitive indexed matrix. -/
lemma physicalPortSuite9a_hostile_indexedScatteringMatrix_eq_explicit :
    physicalPortSuite9aHostileFamily.indexedScatteringMatrix.toModeTransform =
      physicalPortSuite9aHostileExplicitIndexedTransform := by
  ext output input
  rcases output with ⟨outputComponent, ⟨outputPort, outputMode⟩⟩
  rcases input with ⟨inputComponent, ⟨inputPort, inputMode⟩⟩
  cases outputComponent <;> cases inputComponent
  all_goals
    cases outputPort <;> cases outputMode <;>
      cases inputPort <;> cases inputMode
  all_goals
    simp [ScatteringComponentFamily.indexedScatteringMatrix,
      physicalPortSuite9aHostileExplicitIndexedTransform,
      physicalPortSuite9aHostileFamily, physicalPortSuite9aHostileScattering,
      physicalPortSuite9aPortFamily, physicalPortSuite9aHostileBeamScattering,
      physicalPortSuite9aBeamChannelSwap, BeamSplitter.physicalScattering,
      Mirror.physicalScattering, ScatteringMatrix.toModeTransform_reindex,
      ModeTransform.reindex_apply, BeamSplitter.scattering, BeamSplitter.mixing,
      BeamSplitter.crossCoefficient, BeamSplitter.channelEquiv, Mirror.scattering,
      Mirror.reflection, physicalPortSuite9aBeamParameters,
      physicalPortSuite9aMirrorParameters, Matrix.blockDiagonal'_apply]

/-- The hostile indexed family acts by the swapped beam law and unchanged mirror law. -/
lemma physicalPortSuite9a_hostile_indexed_action :
    physicalPortSuite9aHostileFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aIndexedInput =
      physicalPortSuite9aHostileIndexedOutput := by
  rw [physicalPortSuite9a_hostile_indexedScatteringMatrix_eq_explicit]
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨component, ⟨port, mode⟩⟩
  cases component
  · cases port <;> cases mode
    all_goals
      simp [physicalPortSuite9aHostileExplicitIndexedTransform,
        physicalPortSuite9aIndexedInput, physicalPortSuite9aHostileIndexedOutput,
        ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, physicalPortSuite9a_hostile_sum_indexed]
    all_goals ring_nf
  · cases port
    cases mode
    simp [physicalPortSuite9aHostileExplicitIndexedTransform,
      physicalPortSuite9aIndexedInput, physicalPortSuite9aHostileIndexedOutput,
      ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, physicalPortSuite9a_hostile_sum_indexed]
    ring_nf

/-- The hostile exact output in aggregate component-owned physical-port coordinates. -/
def physicalPortSuite9aHostileAggregateOutput :
    ModeAmplitude physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9aHostileFamily.channelEquiv
    physicalPortSuite9aHostileIndexedOutput

/-- The common raw indexed input re-associated to the hostile aggregate channels. -/
def physicalPortSuite9aHostileAggregateInput :
    ModeAmplitude physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9aHostileFamily.channelEquiv
    physicalPortSuite9aIndexedInput

/-- The hostile aggregate channel carrying the first beam-splitter output. -/
abbrev physicalPortSuite9aHostileBeamFirst :
    physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aHostileFamily.channelEquiv physicalPortSuite9aBeamFirstIndexed

/-- The hostile aggregate channel carrying the second beam-splitter output. -/
abbrev physicalPortSuite9aHostileBeamSecond :
    physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aHostileFamily.channelEquiv physicalPortSuite9aBeamSecondIndexed

/-- The hostile aggregate channel carrying the mirror output. -/
abbrev physicalPortSuite9aHostileMirror :
    physicalPortSuite9aHostileFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9aHostileFamily.channelEquiv physicalPortSuite9aMirrorIndexed

/-- Hostile aggregate evaluation is hostile indexed evaluation after reassociation. -/
lemma physicalPortSuite9aHostileAggregateOutput_apply
    (channel : physicalPortSuite9aHostileFamily.IndexedChannel) :
    physicalPortSuite9aHostileAggregateOutput
        (physicalPortSuite9aHostileFamily.channelEquiv channel) =
      physicalPortSuite9aHostileIndexedOutput channel := by
  rw [physicalPortSuite9aHostileAggregateOutput, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]

/-- The hostile aggregate action forces the exact endpoint-swapped output. -/
lemma physicalPortSuite9a_hostile_aggregate_action :
    physicalPortSuite9aHostileFamily.assembledScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aHostileAggregateInput =
      physicalPortSuite9aHostileAggregateOutput := by
  rw [ScatteringComponentFamily.assembledScatteringMatrix,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.toLinearMap_reindex_eq]
  change ModeAmplitude.reindex physicalPortSuite9aHostileFamily.channelEquiv
      (physicalPortSuite9aHostileFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aIndexedInput) = _
  rw [physicalPortSuite9a_hostile_indexed_action]
  rfl

/-- The hostile aggregate output states all three changed or preserved values. -/
lemma physicalPortSuite9a_hostile_output_coordinates :
    physicalPortSuite9aHostileAggregateOutput physicalPortSuite9aHostileBeamFirst =
        (6 - 4 * Complex.I) / 5 ∧
      physicalPortSuite9aHostileAggregateOutput physicalPortSuite9aHostileBeamSecond =
        (3 - 8 * Complex.I) / 5 ∧
      physicalPortSuite9aHostileAggregateOutput physicalPortSuite9aHostileMirror =
        3 * Complex.I := by
  constructor
  · rw [physicalPortSuite9aHostileAggregateOutput_apply]
    rfl
  constructor
  · rw [physicalPortSuite9aHostileAggregateOutput_apply]
    rfl
  · rw [physicalPortSuite9aHostileAggregateOutput_apply]
    rfl

/-- Swapping one beam output endpoint changes the first concrete aggregate coordinate. -/
lemma physicalPortSuite9a_first_output_ne_hostile :
    physicalPortSuite9aAggregateOutput physicalPortSuite9aBeamFirst ≠
      physicalPortSuite9aHostileAggregateOutput physicalPortSuite9aHostileBeamFirst := by
  rw [physicalPortSuite9a_aggregate_output_coordinates.1,
    physicalPortSuite9a_hostile_output_coordinates.1]
  intro hEqual
  have hReal := congrArg Complex.re hEqual
  norm_num at hReal

/-- The hostile family forces a different first output on the common raw indexed input. -/
lemma physicalPortSuite9a_hostile_action_ne :
    physicalPortSuite9aHostileFamily.assembledScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9aHostileAggregateInput physicalPortSuite9aHostileBeamFirst ≠
      physicalPortSuite9aAggregateOutput physicalPortSuite9aBeamFirst := by
  rw [physicalPortSuite9a_hostile_aggregate_action]
  exact physicalPortSuite9a_first_output_ne_hostile.symm

/-!
## E. Endpoint graph anchor and non-claims
-/

/-- The mixed raw input wrapped as aggregate incident endpoints. -/
def physicalPortSuite9aIncident :
    ModeAmplitude
      (Incident physicalPortSuite9aFamily.aggregatePortModeFamily.Channel) :=
  ModeAmplitude.reindex Incident.channelEquiv.symm
    physicalPortSuite9aAggregateInput

/-- The mixed raw output wrapped as aggregate outgoing endpoints. -/
def physicalPortSuite9aOutgoing :
    ModeAmplitude
      (Outgoing physicalPortSuite9aFamily.aggregatePortModeFamily.Channel) :=
  ModeAmplitude.reindex Outgoing.channelEquiv.symm
    physicalPortSuite9aAggregateOutput

/-- The independently expanded mixed state belongs to the aggregate oriented scattering graph. -/
lemma physicalPortSuite9a_assembled_mem :
    (physicalPortSuite9aIncident, physicalPortSuite9aOutgoing) ∈
      physicalPortSuite9aFamily.assembledScatteringMatrix.toOrientedModeTransform.toBehavior := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    physicalPortSuite9aIncident, ModeAmplitude.reindex_reindex_symm,
    physicalPortSuite9a_aggregate_action]
  rfl

end

end Optics
