/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.Lattice

/-!
# Dynamic regression checks for rectangular microring-lattice flattening

## i. Overview

This file pins S-08 with a `2 × 2` lattice whose nonzero response crosses one horizontal and one
vertical connection. The same input/output pair is certified directly in the canonical flat
equations and in an independently staged row-first closure. A swapped vertical successor then
forces a different incident coordinate, so the raw equations reject the miswired hierarchy.

## ii. Key results

- `latticeRegression_mem_flatBehavior`: direct canonical flat-netlist witness.
- `latticeRegression_mem_rowDecomposition`: independent staged row-first witness.
- `latticeRegression_flat_and_rowDecomposition`: common nonzero input/output anchor.
- `latticeRegressionMiswired_incidentAssembly_rejected`: swapped-successor negative control.

## iii. Table of contents

- A. Dynamic two-by-two fixture
- B. Canonical flat equations
- C. Independent staged closure
- D. Nonzero traversal anchors
- E. Swapped-successor negative control

## iv. References

These algebraic fixtures assert no physical realization, coupled-lattice closed form, passivity,
losslessness, reciprocity, stability, resonance, bandwidth, dispersion, measurement, causality,
material, or electromagnetic-power claim. They test the Physlib-original S-08 extension, not a
DATE'14 parity statement.

DATE'14 Figure 3 and the source-incomplete IP-19 disposition are summarized at
`HOL-CORPUS.md:210-216`; the paper prints no `M × N` lattice theorem.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

/-!
## A. Dynamic two-by-two fixture
-/

/-- A sparse site scattering law whose selected path has three distinct nonzero gains. -/
def latticeRegressionSiteScattering (row column : Fin 2) : ScatteringMatrix LatticeSitePort where
  toModeTransform output input :=
    match row.val, column.val, output, input with
    | 0, 0, .east, .west => 2
    | 0, 1, .south, .west => 3
    | 1, 0, .north, .south => 11
    | 1, 1, .east, .north => 5
    | _, _, _, _ => 0

/-- Directional-coupler parameters used by the dynamic lattice fixture. -/
def latticeRegressionCoupler (through cross : ℝ) : DirectionalCoupler.Parameters where
  throughAmplitude := through
  crossAmplitude := cross

/--
The dynamic `2 × 2` parameters, with distinct nonzero through and cross amplitudes at every
coupler.
-/
def latticeRegressionParameters : RectangularLatticeParameters 2 2 where
  ringScattering := latticeRegressionSiteScattering
  horizontalCoupler row _ :=
    if row = 0 then latticeRegressionCoupler 2 3 else latticeRegressionCoupler 11 13
  verticalCoupler _ column :=
    if column = 0 then latticeRegressionCoupler 17 19 else latticeRegressionCoupler 5 7

/-- Local incident values at a horizontal coupler in the concrete solution. -/
def latticeRegressionHorizontalIncidentValue (row : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if row.val = 0 then 2 else 0
  | ⟨.right, ()⟩ => 0

/-- Local incident values at a vertical coupler in the concrete solution. -/
def latticeRegressionVerticalIncidentValue (column : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if column.val = 1 then -18 * Complex.I else 0
  | ⟨.right, ()⟩ => 0

/-- Componentwise incident values for the concrete canonical solution. -/
def latticeRegressionIncidentValue :
    (component : RectangularLatticeComponent 2 2) →
      (rectangularLatticeComponentPortFamily component).Channel → ℂ
  | Sum.inl (row, column), ⟨port, ()⟩ =>
      match row.val, column.val, port with
      | 0, 0, .west => 1
      | 0, 0, .east => 4
      | 0, 1, .west => -6 * Complex.I
      | 0, 1, .south => -90 * Complex.I
      | 1, 1, .north => -126
      | _, _, _ => 0
  | Sum.inr (Sum.inl (row, _edge)), channel => latticeRegressionHorizontalIncidentValue row channel
  | Sum.inr (Sum.inr (_edge, column)), channel =>
      latticeRegressionVerticalIncidentValue column channel

/-- Local outgoing values at a horizontal coupler in the concrete solution. -/
def latticeRegressionHorizontalOutgoingValue (row : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if row.val = 0 then 4 else 0
  | ⟨.right, ()⟩ => if row.val = 0 then -6 * Complex.I else 0

/-- Local outgoing values at a vertical coupler in the concrete solution. -/
def latticeRegressionVerticalOutgoingValue (column : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if column.val = 1 then -90 * Complex.I else 0
  | ⟨.right, ()⟩ => if column.val = 1 then -126 else 0

/-- Componentwise outgoing values for the concrete canonical solution. -/
def latticeRegressionOutgoingValue :
    (component : RectangularLatticeComponent 2 2) →
      (rectangularLatticeComponentPortFamily component).Channel → ℂ
  | Sum.inl (row, column), ⟨port, ()⟩ =>
      match row.val, column.val, port with
      | 0, 0, .east => 2
      | 0, 1, .south => -18 * Complex.I
      | 1, 1, .east => -630
      | _, _, _ => 0
  | Sum.inr (Sum.inl (row, _edge)), channel => latticeRegressionHorizontalOutgoingValue row channel
  | Sum.inr (Sum.inr (_edge, column)), channel =>
      latticeRegressionVerticalOutgoingValue column channel

/-- Aggregate component channel of the dynamic `2 × 2` fixture. -/
abbrev LatticeRegressionChannel :=
  (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Channel

/-- The finite enumeration of single-mode lattice-site channels used in direct sums. -/
noncomputable instance latticeRegressionLatticeSiteChannelFintype :
    Fintype latticeSitePortFamily.Channel :=
  Fintype.ofEquiv LatticeSitePort latticeSiteChannelEquiv

/-- Aggregate incident amplitude of the concrete solution. -/
def latticeRegressionIncident : ModeAmplitude (Incident LatticeRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => latticeRegressionIncidentValue component ⟨port, mode⟩

/-- Aggregate outgoing amplitude of the concrete solution. -/
def latticeRegressionOutgoing : ModeAmplitude (Outgoing LatticeRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => latticeRegressionOutgoingValue component ⟨port, mode⟩

/-- The unique forward-neighbour index in a two-site direction. -/
def latticeRegressionForwardIndex : LatticeForwardIndex 2 :=
  ⟨0, by omega⟩

/-- The single-mode channel belonging to a selected two-port label. -/
def latticeRegressionTwoPortChannel :
    TwoPortSeriesNetlist.Port → (TwoPortSeriesNetlist.portFamily Unit Unit).Channel
  | .left => ⟨.left, ()⟩
  | .right => ⟨.right, ()⟩

/-- A direct enumeration of the two single-mode channels of a series coupler. -/
lemma latticeRegression_twoPort_sum
    (channelFintype : Fintype (TwoPortSeriesNetlist.portFamily Unit Unit).Channel)
    (f : (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ) :
    (@Finset.univ _ channelFintype).sum f =
      f (latticeRegressionTwoPortChannel .left) + f (latticeRegressionTwoPortChannel .right) := by
  letI := channelFintype
  rw [← Fintype.sum_equiv (TwoPortSeriesNetlist.channelEquiv Unit Unit)
    (fun input => f (TwoPortSeriesNetlist.channelEquiv Unit Unit input)) f
    (by intro input; rfl)]
  simp [latticeRegressionTwoPortChannel, TwoPortSeriesNetlist.channelEquiv]

/-- The aggregate channel of a selected site port. -/
def latticeRegressionRingChannel (row column : Fin 2) (port : LatticeSitePort) :
    LatticeRegressionChannel :=
  (rectangularLatticeComponents latticeRegressionParameters).componentChannelEmbedding
    (rectangularRingComponent row column) (latticeSiteChannelEquiv port)

/-- The aggregate channel of a selected horizontal-coupler port. -/
def latticeRegressionHorizontalCouplerChannel
    (row : Fin 2) (port : TwoPortSeriesNetlist.Port) :
    LatticeRegressionChannel :=
  (rectangularLatticeComponents latticeRegressionParameters).componentChannelEmbedding
    (rectangularHorizontalCouplerComponent row latticeRegressionForwardIndex)
    (latticeRegressionTwoPortChannel port)

/-- The aggregate channel of a selected vertical-coupler port. -/
def latticeRegressionVerticalCouplerChannel
    (column : Fin 2) (port : TwoPortSeriesNetlist.Port) :
    LatticeRegressionChannel :=
  (rectangularLatticeComponents latticeRegressionParameters).componentChannelEmbedding
    (rectangularVerticalCouplerComponent latticeRegressionForwardIndex column)
    (latticeRegressionTwoPortChannel port)

@[simp]
/-- Aggregate incident evaluation reduces to its componentwise table. -/
lemma latticeRegressionIncident_component
    (component : RectangularLatticeComponent 2 2)
    (channel : (rectangularLatticeComponentPortFamily component).Channel) :
    latticeRegressionIncident
        (Incident.mk
          ((rectangularLatticeComponents
            latticeRegressionParameters).componentChannelEmbedding component channel)) =
      latticeRegressionIncidentValue component channel := by
  rfl

@[simp]
/-- Aggregate outgoing evaluation reduces to its componentwise table. -/
lemma latticeRegressionOutgoing_component
    (component : RectangularLatticeComponent 2 2)
    (channel : (rectangularLatticeComponentPortFamily component).Channel) :
    latticeRegressionOutgoing
        (Outgoing.mk
          ((rectangularLatticeComponents
            latticeRegressionParameters).componentChannelEmbedding component channel)) =
      latticeRegressionOutgoingValue component channel := by
  rfl

/-- Canonical flat connection family of the dynamic lattice fixture. -/
abbrev latticeRegressionConnections :=
  (rectangularLatticeNetlist latticeRegressionParameters).connections

/-- Decidable equality for direct coordinate checks on connected channels. -/
noncomputable instance latticeRegressionConnectedChannelDecidableEq :
    DecidableEq latticeRegressionConnections.Channel := Classical.decEq _

/-- External input induced by the concrete incident amplitude. -/
def latticeRegressionInput :
    ModeAmplitude (Incident latticeRegressionConnections.ExternalChannel) :=
  latticeRegressionIncident.restrictEmbedding latticeRegressionConnections.externalIncidentEmbedding

/-- External output induced by the concrete outgoing amplitude. -/
def latticeRegressionOutput :
    ModeAmplitude (Outgoing latticeRegressionConnections.ExternalChannel) :=
  latticeRegressionOutgoing.restrictEmbedding latticeRegressionConnections.externalOutgoingEmbedding

/-- The west port of site `(0, 0)`, used as the fixture input. -/
def latticeRegressionInputPort :
    (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Port :=
  ⟨rectangularRingComponent 0 0, LatticeSitePort.west⟩

/-- The east port of site `(1, 1)`, used as the fixture output. -/
def latticeRegressionOutputPort :
    (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Port :=
  ⟨rectangularRingComponent 1 1, LatticeSitePort.east⟩

/-- Recover a lattice-site index from a ring-component equality. -/
def latticeRegressionSiteIndex :
    (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Port →
      Option (Fin 2 × Fin 2)
  | ⟨Sum.inl site, _⟩ => some site
  | ⟨Sum.inr _, _⟩ => none

/-- Recover a lattice-site port label from an equality of site channels. -/
def latticeRegressionSitePortLabel :
    (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Port →
      Option LatticeSitePort
  | ⟨Sum.inl _, port⟩ => some port
  | ⟨Sum.inr _, _⟩ => none

/-!
## B. Canonical flat equations
-/

/-- The chosen input port is not an endpoint of a horizontal connection. -/
lemma latticeRegressionInputPort_not_horizontal :
    latticeRegressionInputPort ∉
      Set.range
        (rectangularHorizontalConnections latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularHorizontalConnection latticeRegressionParameters
    ((row, column), half)).endpointPort endpoint = latticeRegressionInputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularHorizontalConnection, PortConnection.endpointPort] at hPort
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionInputPort,
      rectangularRingComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionInputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionInputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hSite := congrArg latticeRegressionSiteIndex hPort
    have hColumn : column.succ = (0 : Fin 2) := by
      exact congrArg Prod.snd (Option.some.inj hSite)
    have hValue := congrArg Fin.val hColumn
    change column.1.val + 1 = 0 at hValue
    omega

/-- The chosen output port is not an endpoint of a horizontal connection. -/
lemma latticeRegressionOutputPort_not_horizontal :
    latticeRegressionOutputPort ∉
      Set.range
        (rectangularHorizontalConnections latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularHorizontalConnection latticeRegressionParameters
    ((row, column), half)).endpointPort endpoint = latticeRegressionOutputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularHorizontalConnection, PortConnection.endpointPort] at hPort
  · have hSite := congrArg latticeRegressionSiteIndex hPort
    have hColumn : (column.1 : Fin 2) = 1 := by
      exact congrArg Prod.snd (Option.some.inj hSite)
    have hValue := congrArg Fin.val hColumn
    omega
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionOutputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionOutputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionOutputPort,
      rectangularRingComponent] at hLabel

/-- The chosen input port is not an endpoint of a vertical connection. -/
lemma latticeRegressionInputPort_not_vertical :
    latticeRegressionInputPort ∉
      Set.range (rectangularVerticalConnections latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularVerticalConnection latticeRegressionParameters
    ((row, column), half)).endpointPort endpoint = latticeRegressionInputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularVerticalConnection, PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionInputPort, rectangularRingComponent,
      rectangularVerticalCouplerComponent] at hLabel

/-- The chosen output port is not an endpoint of a vertical connection. -/
lemma latticeRegressionOutputPort_not_vertical :
    latticeRegressionOutputPort ∉
      Set.range (rectangularVerticalConnections latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularVerticalConnection latticeRegressionParameters
    ((row, column), half)).endpointPort endpoint = latticeRegressionOutputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularVerticalConnection, PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionOutputPort, rectangularRingComponent,
      rectangularVerticalCouplerComponent] at hLabel

/-- A port absent from both connection stages is external in the appended flat family. -/
lemma latticeRegressionPort_not_flat
    (port : (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily.Port)
    (hHorizontal : port ∉
      Set.range (rectangularHorizontalConnections latticeRegressionParameters).endpointEmbedding)
    (hVertical : port ∉
      Set.range (rectangularVerticalConnections latticeRegressionParameters).endpointEmbedding) :
    port ∉ Set.range latticeRegressionConnections.endpointEmbedding := by
  change port ∉ Set.range
    (((rectangularLatticeRowHierarchy latticeRegressionParameters).inner.append
      (rectangularLatticeRowHierarchy latticeRegressionParameters).outer).endpointEmbedding)
  rw [(rectangularLatticeRowHierarchy
    latticeRegressionParameters).inner.mem_range_append_endpointEmbedding_iff]
  rintro (hInner | ⟨boundary, hBoundary, hPort⟩)
  · exact hHorizontal hInner
  · apply hVertical
    rcases hBoundary with ⟨⟨index, endpoint⟩, hEndpoint⟩
    refine ⟨⟨index, endpoint⟩, ?_⟩
    change
      (rectangularVerticalConnection latticeRegressionParameters index).endpointPort endpoint =
        port
    have hUnderlying := congrArg Subtype.val hEndpoint
    have hSelected := hUnderlying.trans hPort
    have hLift :
        (((rectangularLatticeRowHierarchy
          latticeRegressionParameters).outer.connection index).endpointPort endpoint).1 =
          ((rectangularVerticalConnections
            latticeRegressionParameters).connection index).endpointPort endpoint := by
      cases endpoint <;> rfl
    exact hLift ▸ hSelected

/-- The west channel of site `(0, 0)` is external in the canonical flat family. -/
lemma latticeRegressionInputChannel_not_connected :
    latticeRegressionRingChannel 0 0 .west ∉
      Set.range latticeRegressionConnections.channelEmbedding := by
  intro hConnected
  apply latticeRegressionPort_not_flat latticeRegressionInputPort
    latticeRegressionInputPort_not_horizontal latticeRegressionInputPort_not_vertical
  exact (latticeRegressionConnections.channel_mem_range_channelEmbedding_iff
    (latticeRegressionRingChannel 0 0 .west)).mp hConnected

/-- The east channel of site `(1, 1)` is external in the canonical flat family. -/
lemma latticeRegressionOutputChannel_not_connected :
    latticeRegressionRingChannel 1 1 .east ∉
      Set.range latticeRegressionConnections.channelEmbedding := by
  intro hConnected
  apply latticeRegressionPort_not_flat latticeRegressionOutputPort
    latticeRegressionOutputPort_not_horizontal latticeRegressionOutputPort_not_vertical
  exact (latticeRegressionConnections.channel_mem_range_channelEmbedding_iff
    (latticeRegressionRingChannel 1 1 .east)).mp hConnected

/-- The canonical external channel carrying the fixture input. -/
def latticeRegressionExternalInput : latticeRegressionConnections.ExternalChannel :=
  ⟨latticeRegressionRingChannel 0 0 .west, latticeRegressionInputChannel_not_connected⟩

/-- The canonical external channel carrying the fixture output. -/
def latticeRegressionExternalOutput : latticeRegressionConnections.ExternalChannel :=
  ⟨latticeRegressionRingChannel 1 1 .east, latticeRegressionOutputChannel_not_connected⟩

/-- The concrete amplitudes satisfy every site and coupler scattering equation directly. -/
lemma latticeRegression_mem_componentBehavior :
    (latticeRegressionIncident, latticeRegressionOutgoing) ∈
      (rectangularLatticeNetlist latticeRegressionParameters).componentBehavior := by
  classical
  apply ((rectangularLatticeNetlist
    latticeRegressionParameters).mem_componentBehavior_iff_forall_component
      latticeRegressionIncident latticeRegressionOutgoing).2
  intro component
  change
    (latticeRegressionIncident.restrictEmbedding
        (Incident.relabelEmbedding
          ((rectangularLatticeComponents
            latticeRegressionParameters).componentChannelEmbedding component)),
      latticeRegressionOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          ((rectangularLatticeComponents
            latticeRegressionParameters).componentChannelEmbedding component))) ∈
      ((rectangularLatticeComponents latticeRegressionParameters).scattering
        component).toOrientedModeTransform.toBehavior
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  apply WithLp.ofLp_injective 2
  funext localChannel
  rcases localChannel with ⟨port, mode⟩
  rw [ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  change latticeRegressionOutgoingValue component ⟨port, mode⟩ =
    ∑ input,
      ((rectangularLatticeComponents
        latticeRegressionParameters).scattering component).toModeTransform ⟨port, mode⟩
          input * latticeRegressionIncidentValue component input
  rcases component with ⟨row, column⟩ | (horizontal | vertical)
  · rw [Fintype.sum_equiv latticeSiteChannelEquiv _ _ (by intro input; rfl)]
    fin_cases row <;> fin_cases column <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, latticeRegressionParameters,
        rectangularLatticeComponentScattering, latticeSitePhysicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        ModeAmplitude.restrictEmbedding_apply, latticeRegressionSiteScattering,
        latticeRegressionIncident, latticeRegressionOutgoing, latticeRegressionIncidentValue,
        latticeRegressionOutgoingValue] <;> norm_num
  · rcases horizontal with ⟨row, edge⟩
    rcases edge with ⟨column, hColumn⟩
    have hColumnZero : column = 0 := by
      apply Fin.ext
      omega
    subst column
    rw [latticeRegression_twoPort_sum]
    fin_cases row <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, latticeRegressionParameters,
        rectangularLatticeComponentScattering, TwoPortSeriesNetlist.physicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        latticeCouplingScattering, DirectionalCoupler.mixing, Matrix.fromBlocks,
        ModeAmplitude.restrictEmbedding_apply, latticeRegressionCoupler,
        latticeRegressionIncident, latticeRegressionOutgoing,
        latticeRegressionIncidentValue, latticeRegressionOutgoingValue] <;>
      norm_num <;> ring_nf
  · rcases vertical with ⟨edge, column⟩
    rcases edge with ⟨row, hRow⟩
    have hRowZero : row = 0 := by
      apply Fin.ext
      omega
    subst row
    rw [latticeRegression_twoPort_sum]
    fin_cases column <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, latticeRegressionParameters,
        rectangularLatticeComponentScattering, TwoPortSeriesNetlist.physicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        latticeCouplingScattering, DirectionalCoupler.mixing, Matrix.fromBlocks,
        ModeAmplitude.restrictEmbedding_apply, latticeRegressionCoupler,
        latticeRegressionIncident, latticeRegressionOutgoing,
        latticeRegressionIncidentValue, latticeRegressionOutgoingValue] <;>
      norm_num <;> ring_nf

/-- Every canonical connected coordinate satisfies the mate equation directly. -/
lemma latticeRegression_connectedEquation (connected : latticeRegressionConnections.Channel) :
    latticeRegressionIncident
        (Incident.mk (latticeRegressionConnections.channelEmbedding connected)) =
      latticeRegressionOutgoing
        (Outgoing.mk (latticeRegressionConnections.channelEmbedding
          (latticeRegressionConnections.mateEquiv connected))) := by
  rcases connected with ⟨connection, localChannel⟩
  change latticeRegressionIncident
      (Incident.mk (latticeRegressionConnections.channelEmbedding
        (latticeRegressionConnections.connectionChannelEmbedding connection localChannel))) =
    latticeRegressionOutgoing
      (Outgoing.mk (latticeRegressionConnections.channelEmbedding
        (latticeRegressionConnections.mateEquiv
          (latticeRegressionConnections.connectionChannelEmbedding connection localChannel))))
  rw [latticeRegressionConnections.channelEmbedding_connectionChannelEmbedding,
    latticeRegressionConnections.channelEmbedding_mateEquiv_connectionChannelEmbedding]
  rcases connection with horizontal | vertical
  · rcases horizontal with ⟨⟨row, edge⟩, half⟩
    rcases edge with ⟨column, hColumn⟩
    have hColumnZero : column = 0 := by
      apply Fin.ext
      omega
    subst column
    change latticeRegressionIncidentValue _ _ = latticeRegressionOutgoingValue _ _
    fin_cases row <;> cases half <;>
      rcases localChannel with mode | mode <;> cases mode <;>
      simp [latticeRegressionConnections, rectangularLatticeNetlist,
        rectangularHorizontalConnections,
        PortConnectionFamily.append, ScatteringComponentFamily.componentChannelEmbedding,
        ScatteringComponentFamily.channelEquiv, latticeRegressionIncident,
        latticeRegressionOutgoing, latticeRegressionIncidentValue,
        latticeRegressionOutgoingValue, latticeRegressionHorizontalIncidentValue,
        latticeRegressionHorizontalOutgoingValue]
  · rcases vertical with ⟨⟨edge, column⟩, half⟩
    rcases edge with ⟨row, hRow⟩
    have hRowZero : row = 0 := by
      apply Fin.ext
      omega
    subst row
    change latticeRegressionIncidentValue _ _ = latticeRegressionOutgoingValue _ _
    fin_cases column <;> cases half <;>
      rcases localChannel with mode | mode <;> cases mode <;>
      simp [latticeRegressionConnections, rectangularLatticeNetlist,
        rectangularVerticalBoundaryConnections, LatticeConnectionFamilies.onBoundary,
        LatticeConnectionFamilies.connectionOnBoundary, rectangularVerticalConnections,
        rectangularVerticalConnection, PortConnectionFamily.append,
        PortConnection.liftBoundary, PortConnection.liftBoundary_modeEquiv,
        ScatteringComponentFamily.componentChannelEmbedding,
        ScatteringComponentFamily.channelEquiv, latticeRegressionIncident,
        latticeRegressionOutgoing, latticeRegressionIncidentValue,
        latticeRegressionOutgoingValue, latticeRegressionVerticalIncidentValue,
        latticeRegressionVerticalOutgoingValue]

/-- The concrete incident amplitude is the canonical assembly of its outgoing field and input. -/
lemma latticeRegression_incidentAssembly :
    latticeRegressionIncident =
      latticeRegressionConnections.incidentAssembly latticeRegressionOutgoing
        latticeRegressionInput := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  by_cases hConnected : channel ∈ Set.range latticeRegressionConnections.channelEmbedding
  · rcases hConnected with ⟨connected, rfl⟩
    rw [latticeRegressionConnections.incidentAssembly_apply_connected_channel]
    exact latticeRegression_connectedEquation connected
  · let external : latticeRegressionConnections.ExternalChannel := ⟨channel, hConnected⟩
    rw [show channel = external.1 by rfl,
      latticeRegressionConnections.incidentAssembly_apply_external]
    rfl

/-- The concrete external output is the canonical readout of the outgoing amplitude. -/
lemma latticeRegression_outputReadout :
    latticeRegressionOutput =
      (rectangularLatticeNetlist latticeRegressionParameters).outputReadout.toLinearMap
        latticeRegressionOutgoing := by
  change latticeRegressionOutgoing.restrictEmbedding
      latticeRegressionConnections.externalOutgoingEmbedding =
    latticeRegressionConnections.externalOutgoingReadout.toLinearMap
      latticeRegressionOutgoing
  rw [PortConnectionFamily.externalOutgoingReadout_apply]

/--
The nonzero input/output pair belongs to the canonical flat behavior, expanded from its component,
mate, and readout equations without a production decomposition equality.
-/
lemma latticeRegression_mem_flatBehavior :
    (latticeRegressionInput, latticeRegressionOutput) ∈
      (rectangularLatticeNetlist latticeRegressionParameters).behavior := by
  exact ((rectangularLatticeNetlist
    latticeRegressionParameters).mem_behavior_iff_componentBehavior
      latticeRegressionInput latticeRegressionOutput).2
      ⟨latticeRegressionIncident, latticeRegressionOutgoing,
        latticeRegression_mem_componentBehavior,
        latticeRegression_incidentAssembly, latticeRegression_outputReadout⟩

/-!
## C. Independent staged closure
-/

/-- The row-first hierarchy used for the independent staged closure witness. -/
abbrev latticeRegressionRowHierarchy :=
  rectangularLatticeRowHierarchy latticeRegressionParameters

/-- The boundary drive induced at the horizontal inner stage. -/
def latticeRegressionInnerDrive :
    ModeAmplitude (Incident latticeRegressionRowHierarchy.inner.ExternalChannel) :=
  latticeRegressionRowHierarchy.inner.appendInnerDrive
    latticeRegressionRowHierarchy.outer latticeRegressionOutgoing latticeRegressionInput

/-- The boundary output read from the horizontal inner stage. -/
def latticeRegressionInnerOutput :
    ModeAmplitude (Outgoing latticeRegressionRowHierarchy.inner.ExternalChannel) :=
  latticeRegressionRowHierarchy.inner.externalOutgoingReadout.toLinearMap latticeRegressionOutgoing

/-- The concrete aggregate amplitudes witness the horizontal inner closure directly. -/
lemma latticeRegression_mem_innerClosure :
    (latticeRegressionInnerDrive, latticeRegressionInnerOutput) ∈
      latticeRegressionRowHierarchy.inner.closeBehavior
        (rectangularRowHierarchyComponentBehavior latticeRegressionParameters) := by
  rw [latticeRegressionRowHierarchy.inner.mem_closeBehavior_iff]
  refine ⟨latticeRegressionIncident, latticeRegressionOutgoing, ?_, ?_, rfl⟩
  · change (latticeRegressionIncident, latticeRegressionOutgoing) ∈
      (rectangularLatticeNetlist latticeRegressionParameters).componentBehavior
    exact latticeRegression_mem_componentBehavior
  exact latticeRegression_incidentAssembly.trans
    (latticeRegressionRowHierarchy.inner.append_incidentAssembly_eq
      latticeRegressionRowHierarchy.outer latticeRegressionOutgoing latticeRegressionInput)

/-- The inner-stage drive expressed in its boundary component coordinates. -/
def latticeRegressionBoundaryIncident :
    ModeAmplitude (Incident latticeRegressionRowHierarchy.inner.externalPortModeFamily.Channel) :=
  ModeAmplitude.reindex
    (Incident.relabelEquiv latticeRegressionRowHierarchy.inner.boundaryChannelEquiv.symm)
    latticeRegressionInnerDrive

/-- The inner-stage output expressed in its boundary component coordinates. -/
def latticeRegressionBoundaryOutgoing :
    ModeAmplitude (Outgoing latticeRegressionRowHierarchy.inner.externalPortModeFamily.Channel) :=
  ModeAmplitude.reindex
    (Outgoing.relabelEquiv latticeRegressionRowHierarchy.inner.boundaryChannelEquiv.symm)
    latticeRegressionInnerOutput

/-- The boundary amplitudes belong to the behavior exported by the horizontal stage. -/
lemma latticeRegression_mem_innerBoundary :
    (latticeRegressionBoundaryIncident, latticeRegressionBoundaryOutgoing) ∈
      latticeRegressionRowHierarchy.inner.innerBoundaryBehavior
        (rectangularRowHierarchyComponentBehavior latticeRegressionParameters) := by
  rw [PortConnectionFamily.innerBoundaryBehavior, LinearBehavior.mem_reindex_iff]
  simpa [latticeRegressionBoundaryIncident, latticeRegressionBoundaryOutgoing] using
    latticeRegression_mem_innerClosure

/-- The lattice input reindexed into the vertical outer stage. -/
def latticeRegressionOuterInput :
    ModeAmplitude (Incident latticeRegressionRowHierarchy.outer.ExternalChannel) :=
  ModeAmplitude.reindex
    (Incident.relabelEquiv
      (latticeRegressionRowHierarchy.inner.appendExternalChannelEquiv
        latticeRegressionRowHierarchy.outer))
    latticeRegressionInput

/-- The lattice output reindexed from the vertical outer stage. -/
def latticeRegressionOuterOutput :
    ModeAmplitude (Outgoing latticeRegressionRowHierarchy.outer.ExternalChannel) :=
  ModeAmplitude.reindex
    (Outgoing.relabelEquiv
      (latticeRegressionRowHierarchy.inner.appendExternalChannelEquiv
        latticeRegressionRowHierarchy.outer))
    latticeRegressionOutput

/-- The boundary witness satisfies the vertical outer closure directly. -/
lemma latticeRegression_mem_outerClosure :
    (latticeRegressionOuterInput, latticeRegressionOuterOutput) ∈
      latticeRegressionRowHierarchy.outer.closeBehavior
        (latticeRegressionRowHierarchy.inner.innerBoundaryBehavior
          (rectangularRowHierarchyComponentBehavior latticeRegressionParameters)) := by
  rw [latticeRegressionRowHierarchy.outer.mem_closeBehavior_iff]
  refine ⟨latticeRegressionBoundaryIncident, latticeRegressionBoundaryOutgoing,
    latticeRegression_mem_innerBoundary, ?_, ?_⟩
  · unfold latticeRegressionBoundaryIncident latticeRegressionBoundaryOutgoing
      latticeRegressionInnerDrive latticeRegressionInnerOutput latticeRegressionOuterInput
    exact latticeRegressionRowHierarchy.inner.appendInnerDrive_eq
      latticeRegressionRowHierarchy.outer latticeRegressionOutgoing latticeRegressionInput
  · unfold latticeRegressionBoundaryOutgoing latticeRegressionInnerOutput
      latticeRegressionOuterOutput
    rw [latticeRegression_outputReadout]
    exact latticeRegressionRowHierarchy.inner.append_externalOutgoingReadout_eq
      latticeRegressionRowHierarchy.outer latticeRegressionOutgoing

/--
The same input/output pair belongs to the staged row-first decomposition, independently of either
production equality between flat and decomposed behaviors.
-/
lemma latticeRegression_mem_rowDecomposition :
    (latticeRegressionInput, latticeRegressionOutput) ∈
      rectangularRowDecompositionBehavior latticeRegressionParameters := by
  unfold rectangularRowDecompositionBehavior
  rw [LinearBehavior.mem_reindex_iff, Equiv.symm_symm, Equiv.symm_symm]
  simpa [latticeRegressionOuterInput, latticeRegressionOuterOutput] using
    latticeRegression_mem_outerClosure

/-!
## D. Nonzero traversal anchors
-/

/-- The concrete solution crosses the selected horizontal wire with nonzero amplitude. -/
lemma latticeRegression_horizontalWire_nonzero :
    latticeRegressionIncident (Incident.mk (latticeRegressionRingChannel 0 1 .west)) =
        latticeRegressionOutgoing
          (Outgoing.mk (latticeRegressionHorizontalCouplerChannel 0 .right)) ∧
      latticeRegressionOutgoing
          (Outgoing.mk (latticeRegressionHorizontalCouplerChannel 0 .right)) ≠
        0 := by
  constructor
  · rfl
  · change (-6 * Complex.I : ℂ) ≠ 0
    norm_num

/-- The concrete solution crosses the selected vertical wire with nonzero amplitude. -/
lemma latticeRegression_verticalWire_nonzero :
    latticeRegressionIncident (Incident.mk (latticeRegressionRingChannel 1 1 .north)) =
        latticeRegressionOutgoing
          (Outgoing.mk (latticeRegressionVerticalCouplerChannel 1 .right)) ∧
      latticeRegressionOutgoing
          (Outgoing.mk (latticeRegressionVerticalCouplerChannel 1 .right)) ≠
        0 := by
  constructor
  · rfl
  · change (-126 : ℂ) ≠ 0
    norm_num

/-- The traversed couplers have distinct nonzero cross and through amplitudes. -/
lemma latticeRegression_crossParameters :
    (latticeRegressionParameters.horizontalCoupler
      0 latticeRegressionForwardIndex).crossAmplitude = 3 ∧
      (latticeRegressionParameters.verticalCoupler
        latticeRegressionForwardIndex 1).crossAmplitude = 7 ∧
      (latticeRegressionParameters.horizontalCoupler
        0 latticeRegressionForwardIndex).throughAmplitude = 2 ∧
      (latticeRegressionParameters.verticalCoupler
        latticeRegressionForwardIndex 1).throughAmplitude = 5 := by
  norm_num [latticeRegressionParameters, latticeRegressionForwardIndex, latticeRegressionCoupler]

/-- The aggregate end of the selected two-dimensional path has amplitude `-630`. -/
lemma latticeRegression_outputPathValue :
    latticeRegressionOutgoing (Outgoing.mk (latticeRegressionRingChannel 1 1 .east)) = -630 := by
  rfl

/-- The selected external input coordinate is one. -/
lemma latticeRegression_inputValue :
    latticeRegressionInput (Incident.mk latticeRegressionExternalInput) = 1 := by
  rfl

/-- The selected external output coordinate is `-630`. -/
lemma latticeRegression_outputValue :
    latticeRegressionOutput (Outgoing.mk latticeRegressionExternalOutput) = -630 := by
  rfl

/--
The common nonzero input/output anchor lies in both the directly expanded flat behavior and the
independently staged row-first behavior.
-/
lemma latticeRegression_flat_and_rowDecomposition :
    (latticeRegressionInput, latticeRegressionOutput) ∈
        (rectangularLatticeNetlist latticeRegressionParameters).behavior ∧
      (latticeRegressionInput, latticeRegressionOutput) ∈
        rectangularRowDecompositionBehavior latticeRegressionParameters :=
  ⟨latticeRegression_mem_flatBehavior, latticeRegression_mem_rowDecomposition⟩

/-!
## E. Swapped-successor negative control
-/

/--
A hostile vertical connection that swaps the destination column of every right-hand endpoint.
-/
def latticeRegressionMiswiredVerticalConnection
    (index : RectangularVerticalConnection 2 2) :
    PortConnection
      (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily :=
  match index with
  | ((row, column), false) =>
      { left := ⟨rectangularRingComponent row.1 column, LatticeSitePort.south⟩
        right :=
          ⟨rectangularVerticalCouplerComponent row column,
            TwoPortSeriesNetlist.Port.left⟩
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }
  | ((row, column), true) =>
      { left :=
          ⟨rectangularVerticalCouplerComponent row column,
            TwoPortSeriesNetlist.Port.right⟩
        right :=
          ⟨rectangularRingComponent row.succ ((Equiv.swap (0 : Fin 2) 1) column),
            LatticeSitePort.north⟩
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }

/-- The family of swapped-successor vertical connections. -/
def latticeRegressionMiswiredVerticalConnections :
    PortConnectionFamily
      (rectangularLatticeComponents latticeRegressionParameters).aggregatePortModeFamily
      (RectangularVerticalConnection 2 2) where
  connection := latticeRegressionMiswiredVerticalConnection
  endpointPort_injective := by
    rintro ⟨⟨⟨firstRow, firstColumn⟩, firstHalf⟩, firstEnd⟩
      ⟨⟨⟨secondRow, secondColumn⟩, secondHalf⟩, secondEnd⟩ hPort
    cases firstHalf <;> cases secondHalf <;> cases firstEnd <;> cases secondEnd <;>
      simp only [latticeRegressionMiswiredVerticalConnection, PortConnection.endpointPort] at hPort
    all_goals
      injection hPort
      simp_all [rectangularRingComponent, rectangularVerticalCouplerComponent]

/-- The hostile vertical endpoints remain disjoint from the horizontal connection endpoints. -/
lemma latticeRegressionMiswired_endpointDisjoint :
    LatticeConnectionFamilies.EndpointDisjoint
      (rectangularHorizontalConnections latticeRegressionParameters)
      latticeRegressionMiswiredVerticalConnections := by
  rintro ⟨⟨rowHorizontal, columnHorizontal⟩, halfHorizontal⟩ endHorizontal
    ⟨⟨rowVertical, columnVertical⟩, halfVertical⟩ endVertical hPort
  cases halfHorizontal <;> cases halfVertical <;>
    cases endHorizontal <;> cases endVertical <;>
    simp only [rectangularHorizontalConnections, rectangularHorizontalConnection,
      latticeRegressionMiswiredVerticalConnections, latticeRegressionMiswiredVerticalConnection,
      PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel] at hLabel
  all_goals
    have hComponent := congrArg Sigma.fst hPort
    cases hComponent

/-- The hostile vertical family lifted to the horizontal stage's remaining boundary. -/
def latticeRegressionMiswiredVerticalBoundaryConnections :=
  LatticeConnectionFamilies.onBoundary
    (rectangularHorizontalConnections latticeRegressionParameters)
    latticeRegressionMiswiredVerticalConnections
    latticeRegressionMiswired_endpointDisjoint

/-- The flat family obtained by appending the hostile vertical stage. -/
abbrev latticeRegressionMiswiredConnections :=
  (rectangularHorizontalConnections latticeRegressionParameters).append
    latticeRegressionMiswiredVerticalBoundaryConnections

/-- Finite local channels for each hostile boundary connection. -/
noncomputable instance latticeRegressionMiswiredBoundaryLocalChannelFintype
    (index : RectangularVerticalConnection 2 2) :
    Fintype
      (latticeRegressionMiswiredVerticalBoundaryConnections.connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Finite local channels for every connection in the hostile appended family. -/
noncomputable instance latticeRegressionMiswiredLocalChannelFintype
    (index : RectangularHorizontalConnection 2 2 ⊕ RectangularVerticalConnection 2 2) :
    Fintype (latticeRegressionMiswiredConnections.connection index).LocalChannel := by
  rcases index with index | index
  · exact rectangularHorizontalLocalChannelFintype latticeRegressionParameters index
  · change Fintype
      (latticeRegressionMiswiredVerticalBoundaryConnections.connection index).LocalChannel
    infer_instance

/-- Finite connected channels in the hostile appended family. -/
noncomputable instance latticeRegressionMiswiredConnectedChannelFintype :
    Fintype latticeRegressionMiswiredConnections.Channel :=
  Fintype.ofFinite _

/-- Decidable equality for hostile connected channels. -/
noncomputable instance latticeRegressionMiswiredConnectedChannelDecidableEq :
    DecidableEq latticeRegressionMiswiredConnections.Channel :=
  Classical.decEq _

/-- The hostile mate sends site `(1, 1)` north to vertical column zero rather than column one. -/
lemma latticeRegressionMiswired_incidentAssembly_ring11North
    (input : ModeAmplitude (Incident latticeRegressionMiswiredConnections.ExternalChannel)) :
    latticeRegressionMiswiredConnections.incidentAssembly latticeRegressionOutgoing input
        (Incident.mk (latticeRegressionRingChannel 1 1 .north)) =
      latticeRegressionOutgoing
        (Outgoing.mk (latticeRegressionVerticalCouplerChannel 0 .right)) := by
  change latticeRegressionMiswiredConnections.incidentAssembly latticeRegressionOutgoing input
      (Incident.mk (latticeRegressionMiswiredConnections.channelEmbedding
        ⟨Sum.inr ((latticeRegressionForwardIndex, (0 : Fin 2)), true), Sum.inr ()⟩)) = _
  rw [latticeRegressionMiswiredConnections.incidentAssembly_apply_connected_channel]
  rfl

/-- The canonical nonzero solution is rejected by the swapped-successor incident assembly. -/
lemma latticeRegressionMiswired_incidentAssembly_rejected
    (input : ModeAmplitude (Incident latticeRegressionMiswiredConnections.ExternalChannel)) :
    latticeRegressionIncident ≠
      latticeRegressionMiswiredConnections.incidentAssembly latticeRegressionOutgoing input := by
  intro hAssembly
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Incident.mk (latticeRegressionRingChannel 1 1 .north))) hAssembly
  rw [latticeRegressionMiswired_incidentAssembly_ring11North] at hCoordinate
  change (-126 : ℂ) = 0 at hCoordinate
  norm_num at hCoordinate

end

end MicroringCascade

end


end Optics
