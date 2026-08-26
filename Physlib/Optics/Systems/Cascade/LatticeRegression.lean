/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.Lattice

/-!
# Regression checks for rectangular microring-lattice flattening

## i. Overview

This file pins S-08 at a `2 × 2` lattice whose four site coefficients are distinct. The positive
checks expand a raw flat-netlist behavior witness, the row-first and column-first component laws,
and selected physical wires directly; they do not invoke either production decomposition lemma.
A deliberately transposed site lookup changes the selected component entry from `2` to `3`.

## ii. Key results

- `latticeRegression_rowFlatten_site01West_entry`: direct row-first entry `2`.
- `latticeRegression_columnFlatten_site01West_entry`: direct column-first entry `2`.
- `latticeRegression_rawBehavior`: direct nonzero behavior witness with east response `2`.
- `latticeRegression_flatten_scattering_eq`: both correct component assemblies agree.
- `latticeRegression_selectedVerticalWire`: direct physical-wire anchor.
- `latticeRegression_misindexedFlatten_scattering_ne`: transposed lookup fails agreement.

## iii. Table of contents

- A. Distinct two-by-two fixture
- B. Direct positive flattening anchors
- C. Transposed-index negative control

## iv. References

These algebraic fixtures assert no physical realization, closed-form coupled response, passivity,
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
## A. Distinct two-by-two fixture
-/
/-- A distinct scalar attached to every site of the `2 × 2` regression lattice. -/
def latticeRegressionSiteWeight (row column : Fin 2) : ℂ :=
  (2 * row.val + column.val + 1 : ℕ)

/-- A diagonal four-port site law carrying only its distinct regression coefficient. -/
def latticeRegressionSiteScattering (row column : Fin 2) :
    ScatteringMatrix LatticeSitePort where
  toModeTransform output input :=
    if output = input then latticeRegressionSiteWeight row column else 0

/-- A numbered algebraic coupler used only to make every neighbour parameter explicit. -/
def latticeRegressionCoupler (number : ℕ) : DirectionalCoupler.Parameters where
  throughAmplitude := number
  crossAmplitude := 0

/-- The distinct `2 × 2` parameters used by both positive flattening orders. -/
def latticeRegressionParameters : RectangularLatticeParameters 2 2 where
  ringScattering := latticeRegressionSiteScattering
  horizontalCoupler row column :=
    latticeRegressionCoupler (5 + 2 * row.val + column.1.val)
  verticalCoupler row column :=
    latticeRegressionCoupler (9 + 2 * row.1.val + column.val)

/-- The unique forward-neighbour index in a two-site direction. -/
def latticeRegressionForwardIndex : LatticeForwardIndex 2 :=
  ⟨0, by omega⟩

/-- The selected site `(row 0, column 1)` used by the direct matrix anchors. -/
def latticeRegressionSite01 : RectangularLatticeComponent 2 2 :=
  rectangularRingComponent 0 1

/-- The west local channel of the selected regression site. -/
def latticeRegressionWestChannel :
    ((rectangularLatticeComponents latticeRegressionParameters).portFamily
      latticeRegressionSite01).Channel :=
  latticeSiteChannelEquiv LatticeSitePort.west

/-- The selected west channel in the common aggregate component coordinates. -/
def latticeRegressionAggregateWest :
    (rectangularLatticeComponents
      latticeRegressionParameters).aggregatePortModeFamily.Channel :=
  (rectangularLatticeComponents latticeRegressionParameters).componentChannelEmbedding
    latticeRegressionSite01 latticeRegressionWestChannel

/-- The selected site's east port, which is external in the `2 × 2` fixture. -/
def latticeRegressionSite01EastPort :
    (rectangularLatticeComponents
      latticeRegressionParameters).aggregatePortModeFamily.Port :=
  ⟨latticeRegressionSite01, LatticeSitePort.east⟩

/-- Recover the site index of a ring port and reject a coupler port. -/
def latticeRegressionSiteIndex :
    (rectangularLatticeComponents
      latticeRegressionParameters).aggregatePortModeFamily.Port →
      Option (Fin 2 × Fin 2)
  | ⟨Sum.inl site, _⟩ => some site
  | ⟨Sum.inr _, _⟩ => none

/-- Recover the local four-port label of a ring port and reject a coupler port. -/
def latticeRegressionSitePortLabel :
    (rectangularLatticeComponents
      latticeRegressionParameters).aggregatePortModeFamily.Port →
      Option LatticeSitePort
  | ⟨Sum.inl _, port⟩ => some port
  | ⟨Sum.inr _, _⟩ => none

/-- No horizontal connection in the fixture uses the selected site's east port. -/
lemma latticeRegressionSite01EastPort_not_horizontal :
    latticeRegressionSite01EastPort ∉
      Set.range (rectangularHorizontalConnections
        latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change ((rectangularHorizontalConnections latticeRegressionParameters).connection
    ((row, column), half)).endpointPort endpoint = latticeRegressionSite01EastPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularHorizontalConnections, rectangularHorizontalConnection,
      PortConnection.endpointPort] at hPort
  · have hSite := congrArg latticeRegressionSiteIndex hPort
    have hColumn : (column.1 : Fin 2) = 1 := by
      exact congrArg Prod.snd (Option.some.inj hSite)
    have hValue := congrArg Fin.val hColumn
    omega
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionSite01EastPort,
      latticeRegressionSite01, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionSite01EastPort,
      latticeRegressionSite01, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionSite01EastPort,
      latticeRegressionSite01, rectangularRingComponent] at hLabel

/-- No vertical connection in the fixture uses the selected site's east port. -/
lemma latticeRegressionSite01EastPort_not_vertical :
    latticeRegressionSite01EastPort ∉
      Set.range (rectangularVerticalConnections
        latticeRegressionParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change ((rectangularVerticalConnections latticeRegressionParameters).connection
    ((row, column), half)).endpointPort endpoint = latticeRegressionSite01EastPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularVerticalConnections, rectangularVerticalConnection,
      PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg latticeRegressionSitePortLabel hPort
    simp [latticeRegressionSitePortLabel, latticeRegressionSite01EastPort,
      latticeRegressionSite01, rectangularRingComponent,
      rectangularVerticalCouplerComponent] at hLabel

/-- The selected east port is absent from the complete row-first connection family. -/
lemma latticeRegressionSite01EastPort_not_flat :
    latticeRegressionSite01EastPort ∉
      Set.range (rectangularLatticeNetlist
        latticeRegressionParameters).connections.endpointEmbedding := by
  change latticeRegressionSite01EastPort ∉ Set.range
    (((rectangularLatticeRowHierarchy latticeRegressionParameters).inner.append
      (rectangularLatticeRowHierarchy
        latticeRegressionParameters).outer).endpointEmbedding)
  rw [(rectangularLatticeRowHierarchy
    latticeRegressionParameters).inner.mem_range_append_endpointEmbedding_iff]
  rintro (hHorizontal | ⟨boundary, hBoundary, hPort⟩)
  · exact latticeRegressionSite01EastPort_not_horizontal hHorizontal
  · apply latticeRegressionSite01EastPort_not_vertical
    rcases hBoundary with ⟨⟨index, endpoint⟩, hEndpoint⟩
    refine ⟨⟨index, endpoint⟩, ?_⟩
    change (rectangularVerticalConnection latticeRegressionParameters index).endpointPort
      endpoint = latticeRegressionSite01EastPort
    have hUnderlying := congrArg Subtype.val hEndpoint
    have hSelected := hUnderlying.trans hPort
    have hLift :
        (((rectangularLatticeRowHierarchy
          latticeRegressionParameters).outer.connection index).endpointPort endpoint).1 =
          ((rectangularVerticalConnections
            latticeRegressionParameters).connection index).endpointPort endpoint := by
      cases endpoint <;> rfl
    have hVertical := hLift ▸ hSelected
    exact hVertical

/-- The east local channel of the selected site. -/
def latticeRegressionEastChannel :
    ((rectangularLatticeComponents latticeRegressionParameters).portFamily
      latticeRegressionSite01).Channel :=
  latticeSiteChannelEquiv LatticeSitePort.east

/-- The selected site's local east column is diagonal with value two. -/
lemma latticeRegression_site01East_localEntry (output : LatticeSitePort) :
    (latticeSitePhysicalScattering
      (latticeRegressionSiteScattering 0 1)).toModeTransform
        (latticeSiteChannelEquiv output)
        (latticeSiteChannelEquiv LatticeSitePort.east) =
      if output = LatticeSitePort.east then 2 else 0 := by
  rw [latticeSitePhysicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.reindex_apply]
  simp [latticeRegressionSiteScattering, latticeRegressionSiteWeight]

/-- The selected external east channel in the common aggregate component coordinates. -/
def latticeRegressionAggregateEast :
    (rectangularLatticeNetlist latticeRegressionParameters).Channel :=
  (rectangularLatticeComponents latticeRegressionParameters).componentChannelEmbedding
    latticeRegressionSite01 latticeRegressionEastChannel

/-- The selected aggregate east channel is not connected in the flat lattice. -/
lemma latticeRegressionAggregateEast_not_connected :
    latticeRegressionAggregateEast ∉
      Set.range (rectangularLatticeNetlist
        latticeRegressionParameters).connections.channelEmbedding := by
  intro hConnected
  apply latticeRegressionSite01EastPort_not_flat
  exact ((rectangularLatticeNetlist
    latticeRegressionParameters).connections.channel_mem_range_channelEmbedding_iff
      latticeRegressionAggregateEast).mp hConnected

/-- The selected east channel packaged in the flat lattice's external coordinates. -/
def latticeRegressionExternalEast :
    (rectangularLatticeNetlist latticeRegressionParameters).ExternalChannel :=
  ⟨latticeRegressionAggregateEast, latticeRegressionAggregateEast_not_connected⟩

/-- The concrete aggregate channel labels have classical decidable equality. -/
noncomputable instance latticeRegressionAggregateChannelDecidableEq :
    DecidableEq (rectangularLatticeNetlist latticeRegressionParameters).Channel :=
  Classical.decEq _

/-- The concrete connected channel labels have classical decidable equality. -/
noncomputable instance latticeRegressionConnectedChannelDecidableEq :
    DecidableEq (rectangularLatticeNetlist
      latticeRegressionParameters).ConnectedChannel :=
  Classical.decEq _

/-- The concrete external channel labels have classical decidable equality. -/
noncomputable instance latticeRegressionExternalChannelDecidableEq :
    DecidableEq (rectangularLatticeNetlist latticeRegressionParameters).ExternalChannel :=
  Classical.decEq _

/-- Unit drive on the selected external east channel. -/
def latticeRegressionInput :
    ModeAmplitude (rectangularLatticeNetlist
      latticeRegressionParameters).ExternalIncident :=
  PiLp.single 2 (Incident.mk latticeRegressionExternalEast) 1

/-- The corresponding ambient incident state, zero away from the selected channel. -/
def latticeRegressionIncident :
    ModeAmplitude (rectangularLatticeNetlist
      latticeRegressionParameters).IncidentIndex :=
  PiLp.single 2 (Incident.mk latticeRegressionAggregateEast) 1

/-- The hand-expanded ambient outgoing state with selected coefficient two. -/
def latticeRegressionOutgoing :
    ModeAmplitude (rectangularLatticeNetlist
      latticeRegressionParameters).OutgoingIndex :=
  PiLp.single 2 (Outgoing.mk latticeRegressionAggregateEast) 2

/-- The hand-expanded external response with selected coefficient two. -/
def latticeRegressionOutput :
    ModeAmplitude (rectangularLatticeNetlist
      latticeRegressionParameters).ExternalOutgoing :=
  PiLp.single 2 (Outgoing.mk latticeRegressionExternalEast) 2
/-!
## B. Direct positive flattening anchors
-/
/-- A component-local entry expands directly through the concrete assembled family. -/
lemma latticeRegression_scatteringEntry_component
    (component : (rectangularLatticeNetlist
      latticeRegressionParameters).components.Component)
    (output input : ((rectangularLatticeNetlist
      latticeRegressionParameters).components.portFamily component).Channel) :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding component output))
        (Incident.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding component input)) =
      ((rectangularLatticeNetlist
        latticeRegressionParameters).components.scattering component).toModeTransform
          output input :=
  (rectangularLatticeNetlist
    latticeRegressionParameters).scatteringTransform_entry_same component output input

/-- Distinct concrete component blocks have zero direct assembled entry. -/
lemma latticeRegression_scatteringEntry_of_ne
    {first second : (rectangularLatticeNetlist
      latticeRegressionParameters).components.Component} (hComponent : first ≠ second)
    (output : ((rectangularLatticeNetlist
      latticeRegressionParameters).components.portFamily first).Channel)
    (input : ((rectangularLatticeNetlist
      latticeRegressionParameters).components.portFamily second).Channel) :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding first output))
        (Incident.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding second input)) = 0 :=
  (rectangularLatticeNetlist
    latticeRegressionParameters).scatteringTransform_entry_of_ne hComponent output input

/-- A selected-site outgoing endpoint equals the driven endpoint exactly at the east port. -/
lemma latticeRegression_site01Outgoing_eq_iff (output : LatticeSitePort) :
    Outgoing.mk
        ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            latticeRegressionSite01 (latticeSiteChannelEquiv output)) =
      Outgoing.mk latticeRegressionAggregateEast ↔
    output = LatticeSitePort.east := by
  constructor
  · intro hEndpoint
    have hChannel := congrArg Outgoing.channel hEndpoint
    have hLocal := ((rectangularLatticeNetlist
      latticeRegressionParameters).components.componentChannelEmbedding
        latticeRegressionSite01).injective hChannel
    exact congrArg Sigma.fst hLocal
  · intro hPort
    subst output
    rfl

/-- The selected component contributes exactly the diagonal east-column coefficient. -/
lemma latticeRegression_scatteringColumn_site01 (output : LatticeSitePort) :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            latticeRegressionSite01 (latticeSiteChannelEquiv output)))
        (Incident.mk latticeRegressionAggregateEast) =
      latticeRegressionOutgoing
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            latticeRegressionSite01 (latticeSiteChannelEquiv output))) := by
  have hEntry := latticeRegression_scatteringEntry_component
    latticeRegressionSite01 (latticeSiteChannelEquiv output)
      latticeRegressionEastChannel
  calc
    _ = ((rectangularLatticeNetlist
        latticeRegressionParameters).components.scattering
          latticeRegressionSite01).toModeTransform
            (latticeSiteChannelEquiv output) latticeRegressionEastChannel := hEntry
    _ = _ := by
      change (latticeSitePhysicalScattering
        (latticeRegressionSiteScattering 0 1)).toModeTransform
          (latticeSiteChannelEquiv output)
            (latticeSiteChannelEquiv LatticeSitePort.east) = _
      rw [latticeRegression_site01East_localEntry]
      simp only [latticeRegressionOutgoing, PiLp.single_apply]
      by_cases hPort : output = LatticeSitePort.east
      · rw [if_pos hPort,
          if_pos ((latticeRegression_site01Outgoing_eq_iff output).mpr hPort)]
      · have hEndpoint : Outgoing.mk
              ((rectangularLatticeNetlist
                latticeRegressionParameters).components.componentChannelEmbedding
                  latticeRegressionSite01 (latticeSiteChannelEquiv output)) ≠
            Outgoing.mk latticeRegressionAggregateEast := by
          intro hEqual
          exact hPort ((latticeRegression_site01Outgoing_eq_iff output).mp hEqual)
        rw [if_neg hPort, if_neg hEndpoint]

/-- An outgoing endpoint on a different component cannot be the selected east endpoint. -/
lemma latticeRegression_otherOutgoing_ne
    {component : (rectangularLatticeNetlist
      latticeRegressionParameters).components.Component}
    (hComponent : component ≠ latticeRegressionSite01)
    (channel : ((rectangularLatticeNetlist
      latticeRegressionParameters).components.portFamily component).Channel) :
    Outgoing.mk ((rectangularLatticeNetlist
        latticeRegressionParameters).components.componentChannelEmbedding component channel) ≠
      Outgoing.mk latticeRegressionAggregateEast := by
  intro hEndpoint
  apply hComponent
  have hRaw := congrArg Outgoing.channel hEndpoint
  change (rectangularLatticeComponents latticeRegressionParameters).channelEquiv
      ⟨component, channel⟩ =
    (rectangularLatticeComponents latticeRegressionParameters).channelEquiv
      ⟨latticeRegressionSite01, latticeRegressionEastChannel⟩ at hRaw
  have hIndexed := (rectangularLatticeComponents
    latticeRegressionParameters).channelEquiv.injective hRaw
  exact congrArg Sigma.fst hIndexed

/-- Every other component contributes zero to the selected east incident column. -/
lemma latticeRegression_scatteringColumn_other
    {component : (rectangularLatticeNetlist
      latticeRegressionParameters).components.Component}
    (hComponent : component ≠ latticeRegressionSite01)
    (channel : ((rectangularLatticeNetlist
      latticeRegressionParameters).components.portFamily component).Channel) :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding component channel))
        (Incident.mk latticeRegressionAggregateEast) =
      latticeRegressionOutgoing
        (Outgoing.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            component channel)) := by
  have hEntry := latticeRegression_scatteringEntry_of_ne hComponent
    channel latticeRegressionEastChannel
  calc
    _ = 0 := hEntry
    _ = _ := by
      simp only [latticeRegressionOutgoing, PiLp.single_apply]
      rw [if_neg (latticeRegression_otherOutgoing_ne hComponent channel)]

/-- The selected scattering column is two at site `(0, 1)` and zero everywhere else. -/
lemma latticeRegression_scatteringColumn
    (output : (rectangularLatticeNetlist
      latticeRegressionParameters).OutgoingIndex) :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform output
        (Incident.mk latticeRegressionAggregateEast) =
      latticeRegressionOutgoing output := by
  rcases output with ⟨⟨⟨component, port⟩, mode⟩⟩
  by_cases hComponent : component = latticeRegressionSite01
  · subst component
    change LatticeSitePort at port
    change Unit at mode
    rcases mode with ⟨⟩
    rw [show (⟨⟨latticeRegressionSite01, port⟩, ()⟩ :
      (rectangularLatticeNetlist latticeRegressionParameters).Channel) =
        (rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            latticeRegressionSite01 (latticeSiteChannelEquiv port) by rfl]
    exact latticeRegression_scatteringColumn_site01 port
  · rw [show (⟨⟨component, port⟩, mode⟩ :
      (rectangularLatticeNetlist latticeRegressionParameters).Channel) =
        (rectangularLatticeNetlist
          latticeRegressionParameters).components.componentChannelEmbedding
            component ⟨port, mode⟩ by rfl]
    exact latticeRegression_scatteringColumn_other hComponent ⟨port, mode⟩

/-- The hand-expanded outgoing state satisfies the complete component scattering equation. -/
lemma latticeRegression_scatteringAction :
    latticeRegressionOutgoing =
      (rectangularLatticeNetlist
        latticeRegressionParameters).scatteringTransform.toLinearMap
          latticeRegressionIncident := by
  rw [ModeTransform.eq_toLinearMap_iff_mulVec]
  simp only [latticeRegressionOutgoing, latticeRegressionIncident, PiLp.ofLp_single,
    Matrix.mulVec_single_one]
  funext output
  exact (latticeRegression_scatteringColumn output).symm

/-- Incident assembly is zero on every connected coordinate of the selected-column fixture. -/
lemma latticeRegression_incidentAssembly_connected
    (connected : (rectangularLatticeNetlist
      latticeRegressionParameters).ConnectedChannel) :
    latticeRegressionIncident
        (Incident.mk ((rectangularLatticeNetlist
          latticeRegressionParameters).connections.channelEmbedding connected)) =
      (rectangularLatticeNetlist
        latticeRegressionParameters).connections.incidentAssembly
          latticeRegressionOutgoing latticeRegressionInput
            (Incident.mk ((rectangularLatticeNetlist
              latticeRegressionParameters).connections.channelEmbedding connected)) := by
  rw [(rectangularLatticeNetlist
    latticeRegressionParameters).connections.incidentAssembly_apply_connected_channel]
  have hIncidentNe : Incident.mk ((rectangularLatticeNetlist
      latticeRegressionParameters).connections.channelEmbedding connected) ≠
      Incident.mk latticeRegressionAggregateEast := by
    intro hEndpoint
    exact (rectangularLatticeNetlist
      latticeRegressionParameters).connections.channelEmbedding_ne_externalChannelEmbedding
        connected latticeRegressionExternalEast (congrArg Incident.channel hEndpoint)
  have hOutgoingNe : Outgoing.mk ((rectangularLatticeNetlist
      latticeRegressionParameters).connections.channelEmbedding
        ((rectangularLatticeNetlist
          latticeRegressionParameters).connections.mateEquiv connected)) ≠
      Outgoing.mk latticeRegressionAggregateEast := by
    intro hEndpoint
    exact (rectangularLatticeNetlist
      latticeRegressionParameters).connections.channelEmbedding_ne_externalChannelEmbedding
        _ latticeRegressionExternalEast (congrArg Outgoing.channel hEndpoint)
  simp only [latticeRegressionIncident, latticeRegressionOutgoing, PiLp.single_apply]
  rw [if_neg hIncidentNe, if_neg hOutgoingNe]

/-- Incident assembly copies the selected drive exactly on every external coordinate. -/
lemma latticeRegression_incidentAssembly_external
    (external : (rectangularLatticeNetlist
      latticeRegressionParameters).ExternalChannel) :
    latticeRegressionIncident (Incident.mk external.1) =
      (rectangularLatticeNetlist
        latticeRegressionParameters).connections.incidentAssembly
          latticeRegressionOutgoing latticeRegressionInput (Incident.mk external.1) := by
  rw [(rectangularLatticeNetlist
    latticeRegressionParameters).connections.incidentAssembly_apply_external]
  by_cases hExternal : external = latticeRegressionExternalEast
  · subst external
    simp [latticeRegressionIncident, latticeRegressionInput,
      latticeRegressionExternalEast]
  · have hAmbient : external.1 ≠ latticeRegressionAggregateEast := by
      intro hChannel
      apply hExternal
      exact Subtype.ext hChannel
    have hAmbientEndpoint : Incident.mk external.1 ≠
        Incident.mk latticeRegressionAggregateEast := by
      exact fun hEndpoint => hAmbient (congrArg Incident.channel hEndpoint)
    have hExternalEndpoint : Incident.mk external ≠
        Incident.mk latticeRegressionExternalEast := by
      exact fun hEndpoint => hExternal (congrArg Incident.channel hEndpoint)
    simp only [latticeRegressionIncident, latticeRegressionInput, PiLp.single_apply]
    rw [if_neg hAmbientEndpoint, if_neg hExternalEndpoint]

/-- External injection and zero internal routing reconstruct the selected incident state. -/
lemma latticeRegression_incidentAssembly :
    latticeRegressionIncident =
      (rectangularLatticeNetlist
        latticeRegressionParameters).connections.incidentAssembly
          latticeRegressionOutgoing latticeRegressionInput := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  by_cases hConnected : channel ∈ Set.range
      (rectangularLatticeNetlist
        latticeRegressionParameters).connections.channelEmbedding
  · rcases hConnected with ⟨connected, rfl⟩
    exact latticeRegression_incidentAssembly_connected connected
  · let external : (rectangularLatticeNetlist
        latticeRegressionParameters).ExternalChannel := ⟨channel, hConnected⟩
    simpa only [show channel = external.1 by rfl] using
      latticeRegression_incidentAssembly_external external

/-- External readout restricts the hand-expanded outgoing state to coefficient two. -/
lemma latticeRegression_outputReadout :
    latticeRegressionOutput =
      (rectangularLatticeNetlist
        latticeRegressionParameters).outputReadout.toLinearMap latticeRegressionOutgoing := by
  change latticeRegressionOutput =
    (rectangularLatticeNetlist
      latticeRegressionParameters).connections.externalOutgoingReadout.toLinearMap
        latticeRegressionOutgoing
  rw [PortConnectionFamily.externalOutgoingReadout,
    ModeTransform.toLinearMap_restriction]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨external⟩
  rw [ModeAmplitude.restrictEmbedding_apply,
    PortConnectionFamily.externalOutgoingEmbedding_apply]
  by_cases hExternal : external = latticeRegressionExternalEast
  · have hAmbient : external.1 = latticeRegressionAggregateEast := by
      exact congrArg Subtype.val hExternal
    have hExternalEndpoint : Outgoing.mk external =
        Outgoing.mk latticeRegressionExternalEast := congrArg Outgoing.mk hExternal
    have hAmbientEndpoint : Outgoing.mk external.1 =
        Outgoing.mk latticeRegressionAggregateEast := congrArg Outgoing.mk hAmbient
    simp only [latticeRegressionOutput, latticeRegressionOutgoing, PiLp.single_apply]
    rw [if_pos hExternalEndpoint, if_pos hAmbientEndpoint]
  · have hAmbient : external.1 ≠ latticeRegressionAggregateEast := by
      intro hChannel
      apply hExternal
      apply Subtype.ext
      exact hChannel
    have hExternalEndpoint : Outgoing.mk external ≠
        Outgoing.mk latticeRegressionExternalEast := by
      intro hEndpoint
      exact hExternal (congrArg Outgoing.channel hEndpoint)
    have hAmbientEndpoint : Outgoing.mk external.1 ≠
        Outgoing.mk latticeRegressionAggregateEast := by
      intro hEndpoint
      exact hAmbient (congrArg Outgoing.channel hEndpoint)
    simp only [latticeRegressionOutput, latticeRegressionOutgoing, PiLp.single_apply]
    rw [if_neg hExternalEndpoint, if_neg hAmbientEndpoint]

/-- The raw flat netlist admits the independently expanded nonzero input/output pair. -/
lemma latticeRegression_rawBehavior :
    (latticeRegressionInput, latticeRegressionOutput) ∈
      (rectangularLatticeNetlist latticeRegressionParameters).behavior := by
  exact ((rectangularLatticeNetlist
    latticeRegressionParameters).mem_behavior_iff_componentBehavior
      latticeRegressionInput latticeRegressionOutput).2
        ⟨latticeRegressionIncident, latticeRegressionOutgoing,
          ((rectangularLatticeNetlist
            latticeRegressionParameters).mem_componentBehavior_iff _ _).2
              latticeRegression_scatteringAction,
          latticeRegression_incidentAssembly, latticeRegression_outputReadout⟩

/-- The directly expanded response exposes coefficient two at the selected east channel. -/
lemma latticeRegression_outputEast :
    latticeRegressionOutput (Outgoing.mk latticeRegressionExternalEast) = 2 := by
  simp [latticeRegressionOutput]

/-- Direct primitive expansion gives coefficient `2` at site `(0, 1)` in row-first flattening. -/
lemma latticeRegression_rowFlatten_site01West_entry :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform
        (Outgoing.mk latticeRegressionAggregateWest)
        (Incident.mk latticeRegressionAggregateWest) = 2 := by
  calc
    _ = ((rectangularLatticeNetlist latticeRegressionParameters).components.scattering
        latticeRegressionSite01).toModeTransform latticeRegressionWestChannel
        latticeRegressionWestChannel :=
      (rectangularLatticeNetlist
        latticeRegressionParameters).scatteringTransform_entry_same _ _ _
    _ = 2 := by
      change (latticeSitePhysicalScattering
        (latticeRegressionSiteScattering 0 1)).toModeTransform
          (latticeSiteChannelEquiv LatticeSitePort.west)
          (latticeSiteChannelEquiv LatticeSitePort.west) = 2
      rw [latticeSitePhysicalScattering, ScatteringMatrix.toModeTransform_reindex,
        ModeTransform.reindex_apply]
      simp [latticeRegressionSiteScattering, latticeRegressionSiteWeight]

/-- Direct primitive expansion gives the same coefficient `2` in column-first flattening. -/
lemma latticeRegression_columnFlatten_site01West_entry :
    (rectangularLatticeColumnHierarchy latticeRegressionParameters).flatten.scatteringTransform
        (Outgoing.mk latticeRegressionAggregateWest)
        (Incident.mk latticeRegressionAggregateWest) = 2 := by
  calc
    _ = ((rectangularLatticeColumnHierarchy
        latticeRegressionParameters).flatten.components.scattering
        latticeRegressionSite01).toModeTransform latticeRegressionWestChannel
        latticeRegressionWestChannel :=
      (rectangularLatticeColumnHierarchy
        latticeRegressionParameters).flatten.scatteringTransform_entry_same _ _ _
    _ = 2 := by
      change (latticeSitePhysicalScattering
        (latticeRegressionSiteScattering 0 1)).toModeTransform
          (latticeSiteChannelEquiv LatticeSitePort.west)
          (latticeSiteChannelEquiv LatticeSitePort.west) = 2
      rw [latticeSitePhysicalScattering, ScatteringMatrix.toModeTransform_reindex,
        ModeTransform.reindex_apply]
      simp [latticeRegressionSiteScattering, latticeRegressionSiteWeight]

/-- The two correct flattening orders have the same assembled component law, by expansion. -/
lemma latticeRegression_flatten_scattering_eq :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform =
      (rectangularLatticeColumnHierarchy
        latticeRegressionParameters).flatten.scatteringTransform := by
  rfl

/-- The row-first flat netlist contains the selected vertical lower-to-coupler wire literally. -/
lemma latticeRegression_selectedVerticalWire :
    ((rectangularLatticeNetlist latticeRegressionParameters).connections.connection
      (Sum.inr ((latticeRegressionForwardIndex, (0 : Fin 2)), false))).left =
        ⟨rectangularRingComponent 0 0, LatticeSitePort.south⟩ := by
  rfl

/-- Column-first flattening contains the same selected vertical wire under its direct label. -/
lemma latticeRegression_selectedColumnFirstVerticalWire :
    ((rectangularLatticeColumnHierarchy latticeRegressionParameters).flatten.connections.connection
      (Sum.inl ((latticeRegressionForwardIndex, (0 : Fin 2)), false))).left =
        ⟨rectangularRingComponent 0 0, LatticeSitePort.south⟩ := by
  rfl
/-!
## C. Transposed-index negative control
-/
/-- A deliberately wrong decomposition lookup that exchanges each site's row and column indices. -/
def latticeRegressionTransposedSites : RectangularLatticeParameters 2 2 where
  ringScattering row column := latticeRegressionSiteScattering column row
  horizontalCoupler := latticeRegressionParameters.horizontalCoupler
  verticalCoupler := latticeRegressionParameters.verticalCoupler

/-- The deliberately mis-indexed column-first decomposition fixture. -/
@[reducible]
def latticeRegressionMisindexedColumnHierarchy : HierarchicalNetlist :=
  rectangularLatticeColumnHierarchy latticeRegressionTransposedSites

/-- The transposed lookup changes the selected flattened component coefficient from `2` to `3`. -/
lemma latticeRegression_misindexed_site01West_entry :
    latticeRegressionMisindexedColumnHierarchy.flatten.scatteringTransform
        (Outgoing.mk latticeRegressionAggregateWest)
        (Incident.mk latticeRegressionAggregateWest) = 3 := by
  calc
    _ = (latticeRegressionMisindexedColumnHierarchy.flatten.components.scattering
        latticeRegressionSite01).toModeTransform latticeRegressionWestChannel
        latticeRegressionWestChannel :=
      latticeRegressionMisindexedColumnHierarchy.flatten.scatteringTransform_entry_same _ _ _
    _ = 3 := by
      change (latticeSitePhysicalScattering
        (latticeRegressionSiteScattering 1 0)).toModeTransform
          (latticeSiteChannelEquiv LatticeSitePort.west)
          (latticeSiteChannelEquiv LatticeSitePort.west) = 3
      rw [latticeSitePhysicalScattering, ScatteringMatrix.toModeTransform_reindex,
        ModeTransform.reindex_apply]
      simp [latticeRegressionSiteScattering, latticeRegressionSiteWeight]

/-- The transposed-index decomposition cannot agree with the correct flattened component law. -/
lemma latticeRegression_misindexedFlatten_scattering_ne :
    (rectangularLatticeNetlist latticeRegressionParameters).scatteringTransform ≠
      latticeRegressionMisindexedColumnHierarchy.flatten.scatteringTransform := by
  intro hAgreement
  have hEntry := congrFun
    (congrFun hAgreement (Outgoing.mk latticeRegressionAggregateWest))
    (Incident.mk latticeRegressionAggregateWest)
  have hImpossible : (2 : ℂ) = 3 :=
    latticeRegression_rowFlatten_site01West_entry.symm.trans
      (hEntry.trans latticeRegression_misindexed_site01West_entry)
  norm_num at hImpossible

end MicroringCascade

end

end Optics
