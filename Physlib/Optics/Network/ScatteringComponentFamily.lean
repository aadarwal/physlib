/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Embedding
public import Physlib.Optics.Network.LinearBehavior
public import Physlib.Optics.Network.Port

/-!
# Typed families of scattering components

## i. Overview

This file packages an indexed family of fixed-frequency optical scattering components. Each
component owns a typed physical-port family and a scattering matrix on the dependent sum of its
local channels. The aggregate physical ports retain both the component tag and the local port, so
later connection families cannot accidentally wire channels while forgetting component ownership.

The indexed sum of local channel spaces is canonically equivalent to the channel space of the
aggregate port family. Local scattering matrices are assembled with `Matrix.blockDiagonal'` and
then relabeled along that equivalence. Exact same-component, cross-component, and amplitude-action
laws show that the result is componentwise block-diagonal scattering before wiring.

The same family also has an order-free relational description: an aggregate incident/outgoing
pair is admitted exactly when its restriction to every component belongs to that component's
oriented scattering graph. This componentwise relation is proved equal to the graph of the
assembled transform.

## ii. Scope

This file assembles only component boundary laws. It does not select internal connections, expose
external channels, solve feedback equations, or assert passivity, losslessness, reciprocity,
causality, bandwidth, or electromagnetic power normalization. Finiteness is absent from the stored
family data. It enters only when finite-dimensional matrix actions or local graph behaviors are
formed; the boundary-restriction map itself is dimension-independent.

## iii. Key results

- `ScatteringComponentFamily.aggregatePortModeFamily`: the physical ports of every component,
  retaining component ownership.
- `ScatteringComponentFamily.channelEquiv`: reassociation between component-indexed local channels
  and the aggregate port-family channels.
- `ScatteringComponentFamily.assembledScatteringMatrix`: dependent block-diagonal component
  scattering in aggregate channel coordinates.
- `ScatteringComponentFamily.assembledScatteringMatrix_entry_same`: an aggregate diagonal block is
  exactly its component scattering matrix.
- `ScatteringComponentFamily.assembledScatteringMatrix_entry_of_ne`: different components never
  scatter directly into one another.
- `ScatteringComponentFamily.assembledScatteringMatrix_apply_component`: each component output is
  determined only by the incident amplitude restricted to that component.
- `ScatteringComponentFamily.componentwiseBehavior`: simultaneous satisfaction of every local
  oriented component graph.
- `ScatteringComponentFamily.componentwiseBehavior_eq_assembledScatteringMatrix_toBehavior`: the
  componentwise relation is exactly the assembled block-diagonal graph.

## iv. Table of contents

- A. Component families and aggregate channels
- B. Dependent block-diagonal scattering
- C. Componentwise amplitude action
- D. Dependent component behavior

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

/-!

## A. Component families and aggregate channels

-/

-- The three universe levels are intentional: component labels, local ports, and local mode fibers
-- are independent types.
set_option linter.checkUnivs false in
/-- An indexed family of fixed-frequency optical scattering components.

Each component supplies its own physical ports, dependent mode fibers, and scattering law. The
family stores no global matrix or wiring data; both are derived in later definitions.
-/
structure ScatteringComponentFamily where
  /-- The type indexing the component instances. -/
  Component : Type u
  /-- The typed physical-port family owned by each component. -/
  portFamily : Component → PortModeFamily.{v, w}
  /-- The fixed-frequency scattering law of each component on its local channels. -/
  scattering : (component : Component) → ScatteringMatrix (portFamily component).Channel

namespace ScatteringComponentFamily

variable (family : ScatteringComponentFamily.{u, v, w})

/-- The dependent sum of every component's local channel family. -/
abbrev IndexedChannel := Σ component, (family.portFamily component).Channel

/-- The aggregate physical-port family, retaining the component tag on every local port. -/
def aggregatePortModeFamily : PortModeFamily.{max u v, w} where
  Port := Σ component, (family.portFamily component).Port
  Mode := fun ⟨component, port⟩ => (family.portFamily component).Mode port

/-- The embedding of one component's physical ports into the aggregate physical-port family. -/
def componentPortEmbedding (component : family.Component) :
    (family.portFamily component).Port ↪ family.aggregatePortModeFamily.Port where
  toFun port := ⟨component, port⟩
  inj' := by
    intro first second h
    cases h
    rfl

/-- Reassociate a component-indexed local channel as an aggregate physical-port channel. -/
def channelEquiv : family.IndexedChannel ≃ family.aggregatePortModeFamily.Channel where
  toFun := fun ⟨component, ⟨port, mode⟩⟩ => ⟨⟨component, port⟩, mode⟩
  invFun := fun ⟨⟨component, port⟩, mode⟩ => ⟨component, ⟨port, mode⟩⟩
  left_inv := by
    rintro ⟨component, ⟨port, mode⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨component, port⟩, mode⟩
    rfl

/-- Channel reassociation retains the component tag, local port, and local mode. -/
@[simp]
lemma channelEquiv_apply (component : family.Component)
    (channel : (family.portFamily component).Channel) :
    family.channelEquiv ⟨component, channel⟩ = ⟨⟨component, channel.1⟩, channel.2⟩ := by
  rcases channel with ⟨port, mode⟩
  rfl

/-- Inverse channel reassociation recovers the component-indexed local channel. -/
@[simp]
lemma channelEquiv_symm_apply (component : family.Component)
    (channel : (family.portFamily component).Channel) :
    family.channelEquiv.symm ⟨⟨component, channel.1⟩, channel.2⟩ =
      ⟨component, channel⟩ := by
  rcases channel with ⟨port, mode⟩
  rfl

/-- The embedding of one component's local channels into the aggregate channel family. -/
def componentChannelEmbedding (component : family.Component) :
    (family.portFamily component).Channel ↪ family.aggregatePortModeFamily.Channel where
  toFun channel := family.channelEquiv ⟨component, channel⟩
  inj' := by
    intro first second h
    have hIndexed := family.channelEquiv.injective h
    cases hIndexed
    rfl

/-- A component-channel embedding retains its local physical port. -/
@[simp]
lemma componentChannelEmbedding_apply (component : family.Component)
    (channel : (family.portFamily component).Channel) :
    family.componentChannelEmbedding component channel =
      ⟨family.componentPortEmbedding component channel.1, channel.2⟩ := by
  rcases channel with ⟨port, mode⟩
  rfl

/-!

## B. Dependent block-diagonal scattering

-/

/-- The block-diagonal component scattering matrix before aggregate-port reassociation. -/
def indexedScatteringMatrix [DecidableEq family.Component] :
    ScatteringMatrix family.IndexedChannel where
  toModeTransform :=
    Matrix.blockDiagonal' fun component => (family.scattering component).toModeTransform

/-- The block-diagonal component scattering matrix in aggregate physical-port coordinates. -/
def assembledScatteringMatrix [DecidableEq family.Component] :
    ScatteringMatrix family.aggregatePortModeFamily.Channel :=
  family.indexedScatteringMatrix.reindex family.channelEquiv

/-- Aggregate scattering differs from indexed block-diagonal scattering only by channel
reassociation. -/
@[simp]
lemma assembledScatteringMatrix_entry [DecidableEq family.Component]
    (output input : family.IndexedChannel) :
    family.assembledScatteringMatrix.toModeTransform
        (family.channelEquiv output) (family.channelEquiv input) =
      family.indexedScatteringMatrix.toModeTransform output input := by
  simp only [assembledScatteringMatrix, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.reindex_apply, Equiv.symm_apply_apply]

/-- A diagonal block of the indexed block-diagonal matrix is exactly the selected component law. -/
@[simp]
lemma indexedScatteringMatrix_entry_same [DecidableEq family.Component]
    (component : family.Component) (output input : (family.portFamily component).Channel) :
    family.indexedScatteringMatrix.toModeTransform ⟨component, output⟩ ⟨component, input⟩ =
      (family.scattering component).toModeTransform output input := by
  exact Matrix.blockDiagonal'_apply_eq
    (fun selected => (family.scattering selected).toModeTransform) component output input

/-- Indexed scattering has zero entries between two different component blocks. -/
lemma indexedScatteringMatrix_entry_of_ne [DecidableEq family.Component]
    {first second : family.Component} (hComponent : first ≠ second)
    (output : (family.portFamily first).Channel)
    (input : (family.portFamily second).Channel) :
    family.indexedScatteringMatrix.toModeTransform ⟨first, output⟩ ⟨second, input⟩ = 0 := by
  exact Matrix.blockDiagonal'_apply_ne
    (fun selected => (family.scattering selected).toModeTransform) output input hComponent

/-- An aggregate diagonal block is exactly the selected component scattering matrix. -/
@[simp]
lemma assembledScatteringMatrix_entry_same [DecidableEq family.Component]
    (component : family.Component) (output input : (family.portFamily component).Channel) :
    family.assembledScatteringMatrix.toModeTransform
        ⟨family.componentPortEmbedding component output.1, output.2⟩
        ⟨family.componentPortEmbedding component input.1, input.2⟩ =
      (family.scattering component).toModeTransform output input := by
  rw [← family.componentChannelEmbedding_apply component output,
    ← family.componentChannelEmbedding_apply component input]
  simp only [assembledScatteringMatrix, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.reindex_apply, componentChannelEmbedding]
  exact family.indexedScatteringMatrix_entry_same component output input

/-- Aggregate scattering has zero entries between two different components. -/
lemma assembledScatteringMatrix_entry_of_ne [DecidableEq family.Component]
    {first second : family.Component} (hComponent : first ≠ second)
    (output : (family.portFamily first).Channel)
    (input : (family.portFamily second).Channel) :
    family.assembledScatteringMatrix.toModeTransform
        (family.componentChannelEmbedding first output)
        (family.componentChannelEmbedding second input) = 0 := by
  simp only [assembledScatteringMatrix, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.reindex_apply, componentChannelEmbedding]
  exact family.indexedScatteringMatrix_entry_of_ne hComponent output input

/-!

## C. Componentwise amplitude action

-/

section Finite

variable [Fintype family.Component] [DecidableEq family.Component]
  [∀ component, Fintype (family.portFamily component).Channel]
  [∀ component, DecidableEq (family.portFamily component).Channel]
  [Fintype family.aggregatePortModeFamily.Channel]
  [DecidableEq family.aggregatePortModeFamily.Channel]

/-- The aggregate scattering action on one component is exactly its local scattering action on the
incident amplitude restricted to that component. -/
lemma assembledScatteringMatrix_apply_component
    (amplitude : ModeAmplitude family.aggregatePortModeFamily.Channel)
    (component : family.Component) (output : (family.portFamily component).Channel) :
    family.assembledScatteringMatrix.toModeTransform.toLinearMap amplitude
        (family.componentChannelEmbedding component output) =
      (family.scattering component).toModeTransform.toLinearMap
        (amplitude.restrictEmbedding (family.componentChannelEmbedding component)) output := by
  have hRestrict :
      (ModeAmplitude.reindex family.channelEquiv.symm amplitude).restrictEmbedding
          (Function.Embedding.sigmaMk component) =
        amplitude.restrictEmbedding (family.componentChannelEmbedding component) := by
    apply WithLp.ofLp_injective 2
    funext input
    rfl
  change
    (family.indexedScatteringMatrix.toModeTransform.reindex family.channelEquiv
      family.channelEquiv).toLinearMap amplitude
        (family.channelEquiv ⟨component, output⟩) = _
  rw [ModeTransform.toLinearMap_reindex_eq, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]
  change ModeTransform.toLinearMap
      (Matrix.blockDiagonal'
        (fun selected => (family.scattering selected).toModeTransform))
      (ModeAmplitude.reindex family.channelEquiv.symm amplitude) ⟨component, output⟩ = _
  rw [ModeTransform.blockDiagonal'_apply, hRestrict]

end Finite

/-!

## D. Dependent component behavior

-/

/-- The linear restriction of an aggregate incident/outgoing state to one component boundary. -/
def componentBoundaryRestriction (component : family.Component) :
    (ModeAmplitude (Incident family.aggregatePortModeFamily.Channel) ×
        ModeAmplitude (Outgoing family.aggregatePortModeFamily.Channel)) →ₗ[ℂ]
      (ModeAmplitude (Incident (family.portFamily component).Channel) ×
        ModeAmplitude (Outgoing (family.portFamily component).Channel)) :=
  (ModeAmplitude.restrictEmbeddingLinearMap
    (Incident.relabelEmbedding (family.componentChannelEmbedding component))).prodMap
      (ModeAmplitude.restrictEmbeddingLinearMap
        (Outgoing.relabelEmbedding (family.componentChannelEmbedding component)))

/-- Boundary restriction returns the incident and outgoing amplitudes selected by the component's
channel embedding. -/
@[simp]
lemma componentBoundaryRestriction_apply (component : family.Component)
    (state : ModeAmplitude (Incident family.aggregatePortModeFamily.Channel) ×
      ModeAmplitude (Outgoing family.aggregatePortModeFamily.Channel)) :
    family.componentBoundaryRestriction component state =
      (state.1.restrictEmbedding
          (Incident.relabelEmbedding (family.componentChannelEmbedding component)),
        state.2.restrictEmbedding
          (Outgoing.relabelEmbedding (family.componentChannelEmbedding component))) := by
  simp only [componentBoundaryRestriction, LinearMap.prodMap_apply,
    ModeAmplitude.restrictEmbeddingLinearMap_apply]

section LocalFinite

variable [∀ component, Fintype (family.portFamily component).Channel]

/-- The order-free aggregate behavior requiring every component's restricted boundary state to
satisfy its local scattering graph. -/
def componentwiseBehavior :
    LinearBehavior (Incident family.aggregatePortModeFamily.Channel)
      (Outgoing family.aggregatePortModeFamily.Channel) :=
  ⨅ component,
    (family.scattering component).toOrientedModeTransform.toBehavior.comap
      (family.componentBoundaryRestriction component)

/-- Componentwise behavior membership is exactly local graph membership at every component. -/
@[simp]
lemma mem_componentwiseBehavior_iff
    (incident : ModeAmplitude (Incident family.aggregatePortModeFamily.Channel))
    (outgoing : ModeAmplitude (Outgoing family.aggregatePortModeFamily.Channel)) :
    (incident, outgoing) ∈ family.componentwiseBehavior ↔
      ∀ component,
        (incident.restrictEmbedding
            (Incident.relabelEmbedding (family.componentChannelEmbedding component)),
          outgoing.restrictEmbedding
            (Outgoing.relabelEmbedding (family.componentChannelEmbedding component))) ∈
          (family.scattering component).toOrientedModeTransform.toBehavior := by
  simp only [componentwiseBehavior, Submodule.mem_iInf, Submodule.mem_comap,
    componentBoundaryRestriction_apply]

variable [∀ component, DecidableEq (family.portFamily component).Channel]

/-- Componentwise behavior membership is exactly the family of local scattering equations. -/
lemma mem_componentwiseBehavior_iff_equations
    (incident : ModeAmplitude (Incident family.aggregatePortModeFamily.Channel))
    (outgoing : ModeAmplitude (Outgoing family.aggregatePortModeFamily.Channel)) :
    (incident, outgoing) ∈ family.componentwiseBehavior ↔
      ∀ component,
        outgoing.restrictEmbedding
            (Outgoing.relabelEmbedding (family.componentChannelEmbedding component)) =
          (family.scattering component).toOrientedModeTransform.toLinearMap
            (incident.restrictEmbedding
              (Incident.relabelEmbedding (family.componentChannelEmbedding component))) := by
  rw [family.mem_componentwiseBehavior_iff]
  simp only [ModeTransform.mem_toBehavior_iff_toLinearMap]

end LocalFinite

section FiniteBehavior

variable [Fintype family.Component] [DecidableEq family.Component]
  [∀ component, Fintype (family.portFamily component).Channel]
  [∀ component, DecidableEq (family.portFamily component).Channel]
  [Fintype family.aggregatePortModeFamily.Channel]
  [DecidableEq family.aggregatePortModeFamily.Channel]

/-- Restricting the assembled oriented action to one component gives exactly that component's
oriented scattering action on the restricted incident amplitude. -/
lemma assembledScatteringMatrix_toOrientedModeTransform_apply_component
    (incident : ModeAmplitude (Incident family.aggregatePortModeFamily.Channel))
    (component : family.Component) :
    ModeAmplitude.restrictEmbedding
        (Outgoing.relabelEmbedding (family.componentChannelEmbedding component))
        (family.assembledScatteringMatrix.toOrientedModeTransform.toLinearMap incident) =
      (family.scattering component).toOrientedModeTransform.toLinearMap
        (incident.restrictEmbedding
          (Incident.relabelEmbedding (family.componentChannelEmbedding component))) := by
  have hIncident :
      (ModeAmplitude.reindex Incident.channelEquiv incident).restrictEmbedding
          (family.componentChannelEmbedding component) =
        ModeAmplitude.reindex Incident.channelEquiv
          (incident.restrictEmbedding
            (Incident.relabelEmbedding (family.componentChannelEmbedding component))) := by
    apply WithLp.ofLp_injective 2
    funext input
    rfl
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨output⟩
  rw [ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  simp only [ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply,
    Equiv.symm_symm, Outgoing.channelEquiv_apply, Outgoing.relabelEmbedding_apply]
  rw [family.assembledScatteringMatrix_apply_component, hIncident]

/-- The order-free componentwise relation is exactly the assembled block-diagonal graph. -/
lemma componentwiseBehavior_eq_assembledScatteringMatrix_toBehavior :
    family.componentwiseBehavior =
      family.assembledScatteringMatrix.toOrientedModeTransform.toBehavior := by
  ext state
  rcases state with ⟨incident, outgoing⟩
  rw [family.mem_componentwiseBehavior_iff_equations,
    ModeTransform.mem_toBehavior_iff_toLinearMap]
  constructor
  · intro hComponents
    apply WithLp.ofLp_injective 2
    funext endpoint
    rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
    let output : (family.portFamily component).Channel := ⟨port, mode⟩
    have hLocal := congrArg (fun amplitude => amplitude (Outgoing.mk output))
      (hComponents component)
    have hAssembled := congrArg (fun amplitude => amplitude (Outgoing.mk output))
      (family.assembledScatteringMatrix_toOrientedModeTransform_apply_component
        incident component)
    change outgoing
        (Outgoing.mk (family.componentChannelEmbedding component output)) = _ at hLocal
    change family.assembledScatteringMatrix.toOrientedModeTransform.toLinearMap incident
        (Outgoing.mk (family.componentChannelEmbedding component output)) = _ at hAssembled
    exact hLocal.trans hAssembled.symm
  · intro hOutgoing component
    rw [hOutgoing]
    exact family.assembledScatteringMatrix_toOrientedModeTransform_apply_component
      incident component

end FiniteBehavior

end ScatteringComponentFamily

end

end Optics
