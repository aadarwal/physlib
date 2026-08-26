import Physlib.Optics.Systems.Cascade.Lattice

namespace Optics.MicroringCascade

noncomputable section

def dynSiteScattering (row column : Fin 2) : ScatteringMatrix LatticeSitePort where
  toModeTransform output input :=
    match row.val, column.val, output, input with
    | 0, 0, .east, .west => 2
    | 0, 1, .south, .west => 3
    | 1, 0, .north, .south => 11
    | 1, 1, .east, .north => 5
    | _, _, _, _ => 0

def dynCoupler (through cross : ℝ) : DirectionalCoupler.Parameters where
  throughAmplitude := through
  crossAmplitude := cross

def dynParameters : RectangularLatticeParameters 2 2 where
  ringScattering := dynSiteScattering
  horizontalCoupler row _ :=
    if row = 0 then dynCoupler 2 3 else dynCoupler 11 13
  verticalCoupler _ column :=
    if column = 0 then dynCoupler 17 19 else dynCoupler 5 7

def dynHorizontalIncidentValue (row : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if row.val = 0 then 2 else 0
  | ⟨.right, ()⟩ => 0

def dynVerticalIncidentValue (column : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if column.val = 1 then -18 * Complex.I else 0
  | ⟨.right, ()⟩ => 0

def dynIncidentValue :
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
  | Sum.inr (Sum.inl (row, _edge)), channel => dynHorizontalIncidentValue row channel
  | Sum.inr (Sum.inr (_edge, column)), channel => dynVerticalIncidentValue column channel

def dynHorizontalOutgoingValue (row : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if row.val = 0 then 4 else 0
  | ⟨.right, ()⟩ => if row.val = 0 then -6 * Complex.I else 0

def dynVerticalOutgoingValue (column : Fin 2) :
    (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ
  | ⟨.left, ()⟩ => if column.val = 1 then -90 * Complex.I else 0
  | ⟨.right, ()⟩ => if column.val = 1 then -126 else 0

def dynOutgoingValue :
    (component : RectangularLatticeComponent 2 2) →
      (rectangularLatticeComponentPortFamily component).Channel → ℂ
  | Sum.inl (row, column), ⟨port, ()⟩ =>
      match row.val, column.val, port with
      | 0, 0, .east => 2
      | 0, 1, .south => -18 * Complex.I
      | 1, 1, .east => -630
      | _, _, _ => 0
  | Sum.inr (Sum.inl (row, _edge)), channel => dynHorizontalOutgoingValue row channel
  | Sum.inr (Sum.inr (_edge, column)), channel => dynVerticalOutgoingValue column channel

abbrev DynChannel :=
  (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Channel

noncomputable instance dynLatticeSiteChannelFintype :
    Fintype latticeSitePortFamily.Channel :=
  Fintype.ofEquiv LatticeSitePort latticeSiteChannelEquiv

def dynIncident : ModeAmplitude (Incident DynChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => dynIncidentValue component ⟨port, mode⟩

def dynOutgoing : ModeAmplitude (Outgoing DynChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => dynOutgoingValue component ⟨port, mode⟩

def dynForwardIndex : LatticeForwardIndex 2 :=
  ⟨0, by omega⟩

def dynTwoPortChannel :
    TwoPortSeriesNetlist.Port → (TwoPortSeriesNetlist.portFamily Unit Unit).Channel
  | .left => ⟨.left, ()⟩
  | .right => ⟨.right, ()⟩

lemma dyn_twoPort_sum
    (channelFintype : Fintype (TwoPortSeriesNetlist.portFamily Unit Unit).Channel)
    (f : (TwoPortSeriesNetlist.portFamily Unit Unit).Channel → ℂ) :
    (@Finset.univ _ channelFintype).sum f =
      f (dynTwoPortChannel .left) + f (dynTwoPortChannel .right) := by
  letI := channelFintype
  rw [← Fintype.sum_equiv (TwoPortSeriesNetlist.channelEquiv Unit Unit)
    (fun input => f (TwoPortSeriesNetlist.channelEquiv Unit Unit input)) f
    (by intro input; rfl)]
  simp [dynTwoPortChannel, TwoPortSeriesNetlist.channelEquiv]

def dynRingChannel (row column : Fin 2) (port : LatticeSitePort) : DynChannel :=
  (rectangularLatticeComponents dynParameters).componentChannelEmbedding
    (rectangularRingComponent row column) (latticeSiteChannelEquiv port)

def dynHorizontalCouplerChannel (row : Fin 2) (port : TwoPortSeriesNetlist.Port) :
    DynChannel :=
  (rectangularLatticeComponents dynParameters).componentChannelEmbedding
    (rectangularHorizontalCouplerComponent row dynForwardIndex) (dynTwoPortChannel port)

def dynVerticalCouplerChannel (column : Fin 2) (port : TwoPortSeriesNetlist.Port) :
    DynChannel :=
  (rectangularLatticeComponents dynParameters).componentChannelEmbedding
    (rectangularVerticalCouplerComponent dynForwardIndex column) (dynTwoPortChannel port)

@[simp]
lemma dynIncident_component
    (component : RectangularLatticeComponent 2 2)
    (channel : (rectangularLatticeComponentPortFamily component).Channel) :
    dynIncident
        (Incident.mk ((rectangularLatticeComponents dynParameters).componentChannelEmbedding
          component channel)) =
      dynIncidentValue component channel := by
  rfl

@[simp]
lemma dynOutgoing_component
    (component : RectangularLatticeComponent 2 2)
    (channel : (rectangularLatticeComponentPortFamily component).Channel) :
    dynOutgoing
        (Outgoing.mk ((rectangularLatticeComponents dynParameters).componentChannelEmbedding
          component channel)) =
      dynOutgoingValue component channel := by
  rfl

abbrev dynConnections := (rectangularLatticeNetlist dynParameters).connections

noncomputable instance dynConnectedChannelDecidableEq :
    DecidableEq dynConnections.Channel := Classical.decEq _

def dynInput : ModeAmplitude (Incident dynConnections.ExternalChannel) :=
  dynIncident.restrictEmbedding dynConnections.externalIncidentEmbedding

def dynOutput : ModeAmplitude (Outgoing dynConnections.ExternalChannel) :=
  dynOutgoing.restrictEmbedding dynConnections.externalOutgoingEmbedding

def dynInputPort :
    (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Port :=
  ⟨rectangularRingComponent 0 0, LatticeSitePort.west⟩

def dynOutputPort :
    (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Port :=
  ⟨rectangularRingComponent 1 1, LatticeSitePort.east⟩

def dynSiteIndex :
    (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Port →
      Option (Fin 2 × Fin 2)
  | ⟨Sum.inl site, _⟩ => some site
  | ⟨Sum.inr _, _⟩ => none

def dynSitePortLabel :
    (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Port →
      Option LatticeSitePort
  | ⟨Sum.inl _, port⟩ => some port
  | ⟨Sum.inr _, _⟩ => none

lemma dynInputPort_not_horizontal :
    dynInputPort ∉
      Set.range (rectangularHorizontalConnections dynParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularHorizontalConnection dynParameters
    ((row, column), half)).endpointPort endpoint = dynInputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularHorizontalConnection, PortConnection.endpointPort] at hPort
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynInputPort, rectangularRingComponent] at hLabel
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynInputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynInputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hSite := congrArg dynSiteIndex hPort
    have hColumn : column.succ = (0 : Fin 2) := by
      exact congrArg Prod.snd (Option.some.inj hSite)
    have hValue := congrArg Fin.val hColumn
    change column.1.val + 1 = 0 at hValue
    omega

lemma dynOutputPort_not_horizontal :
    dynOutputPort ∉
      Set.range (rectangularHorizontalConnections dynParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularHorizontalConnection dynParameters
    ((row, column), half)).endpointPort endpoint = dynOutputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularHorizontalConnection, PortConnection.endpointPort] at hPort
  · have hSite := congrArg dynSiteIndex hPort
    have hColumn : (column.1 : Fin 2) = 1 := by
      exact congrArg Prod.snd (Option.some.inj hSite)
    have hValue := congrArg Fin.val hColumn
    omega
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynOutputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynOutputPort, rectangularRingComponent,
      rectangularHorizontalCouplerComponent] at hLabel
  · have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynOutputPort, rectangularRingComponent] at hLabel

lemma dynInputPort_not_vertical :
    dynInputPort ∉
      Set.range (rectangularVerticalConnections dynParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularVerticalConnection dynParameters
    ((row, column), half)).endpointPort endpoint = dynInputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularVerticalConnection, PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynInputPort, rectangularRingComponent,
      rectangularVerticalCouplerComponent] at hLabel

lemma dynOutputPort_not_vertical :
    dynOutputPort ∉
      Set.range (rectangularVerticalConnections dynParameters).endpointEmbedding := by
  rintro ⟨⟨⟨⟨row, column⟩, half⟩, endpoint⟩, hPort⟩
  change (rectangularVerticalConnection dynParameters
    ((row, column), half)).endpointPort endpoint = dynOutputPort at hPort
  cases half <;> cases endpoint <;>
    simp only [rectangularVerticalConnection, PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel, dynOutputPort, rectangularRingComponent,
      rectangularVerticalCouplerComponent] at hLabel

lemma dynPort_not_flat
    (port : (rectangularLatticeComponents dynParameters).aggregatePortModeFamily.Port)
    (hHorizontal : port ∉
      Set.range (rectangularHorizontalConnections dynParameters).endpointEmbedding)
    (hVertical : port ∉
      Set.range (rectangularVerticalConnections dynParameters).endpointEmbedding) :
    port ∉ Set.range dynConnections.endpointEmbedding := by
  change port ∉ Set.range
    (((rectangularLatticeRowHierarchy dynParameters).inner.append
      (rectangularLatticeRowHierarchy dynParameters).outer).endpointEmbedding)
  rw [(rectangularLatticeRowHierarchy
    dynParameters).inner.mem_range_append_endpointEmbedding_iff]
  rintro (hInner | ⟨boundary, hBoundary, hPort⟩)
  · exact hHorizontal hInner
  · apply hVertical
    rcases hBoundary with ⟨⟨index, endpoint⟩, hEndpoint⟩
    refine ⟨⟨index, endpoint⟩, ?_⟩
    change (rectangularVerticalConnection dynParameters index).endpointPort endpoint = port
    have hUnderlying := congrArg Subtype.val hEndpoint
    have hSelected := hUnderlying.trans hPort
    have hLift :
        (((rectangularLatticeRowHierarchy
          dynParameters).outer.connection index).endpointPort endpoint).1 =
          ((rectangularVerticalConnections
            dynParameters).connection index).endpointPort endpoint := by
      cases endpoint <;> rfl
    exact hLift ▸ hSelected

lemma dynInputChannel_not_connected :
    dynRingChannel 0 0 .west ∉ Set.range dynConnections.channelEmbedding := by
  intro hConnected
  apply dynPort_not_flat dynInputPort dynInputPort_not_horizontal dynInputPort_not_vertical
  exact (dynConnections.channel_mem_range_channelEmbedding_iff
    (dynRingChannel 0 0 .west)).mp hConnected

lemma dynOutputChannel_not_connected :
    dynRingChannel 1 1 .east ∉ Set.range dynConnections.channelEmbedding := by
  intro hConnected
  apply dynPort_not_flat dynOutputPort dynOutputPort_not_horizontal dynOutputPort_not_vertical
  exact (dynConnections.channel_mem_range_channelEmbedding_iff
    (dynRingChannel 1 1 .east)).mp hConnected

def dynExternalInput : dynConnections.ExternalChannel :=
  ⟨dynRingChannel 0 0 .west, dynInputChannel_not_connected⟩

def dynExternalOutput : dynConnections.ExternalChannel :=
  ⟨dynRingChannel 1 1 .east, dynOutputChannel_not_connected⟩

lemma dyn_mem_componentBehavior :
    (dynIncident, dynOutgoing) ∈
      (rectangularLatticeNetlist dynParameters).componentBehavior := by
  classical
  apply ((rectangularLatticeNetlist
    dynParameters).mem_componentBehavior_iff_forall_component dynIncident dynOutgoing).2
  intro component
  change
    (dynIncident.restrictEmbedding
        (Incident.relabelEmbedding
          ((rectangularLatticeComponents dynParameters).componentChannelEmbedding component)),
      dynOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          ((rectangularLatticeComponents dynParameters).componentChannelEmbedding component))) ∈
      ((rectangularLatticeComponents dynParameters).scattering
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
  change dynOutgoingValue component ⟨port, mode⟩ =
    ∑ input,
      ((rectangularLatticeComponents dynParameters).scattering component).toModeTransform
          ⟨port, mode⟩ input * dynIncidentValue component input
  rcases component with ⟨row, column⟩ | (horizontal | vertical)
  · rw [Fintype.sum_equiv latticeSiteChannelEquiv _ _ (by intro input; rfl)]
    fin_cases row <;> fin_cases column <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, dynParameters,
        rectangularLatticeComponentScattering, latticeSitePhysicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        ModeAmplitude.restrictEmbedding_apply, dynSiteScattering, dynIncident,
        dynOutgoing, dynIncidentValue, dynOutgoingValue] <;> norm_num
  · rcases horizontal with ⟨row, edge⟩
    rcases edge with ⟨column, hColumn⟩
    have hColumnZero : column = 0 := by
      apply Fin.ext
      omega
    subst column
    rw [dyn_twoPort_sum]
    fin_cases row <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, dynParameters,
        rectangularLatticeComponentScattering, TwoPortSeriesNetlist.physicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        latticeCouplingScattering, DirectionalCoupler.mixing, Matrix.fromBlocks,
        ModeAmplitude.restrictEmbedding_apply, dynCoupler, dynIncident, dynOutgoing,
        dynIncidentValue, dynOutgoingValue] <;> norm_num <;> ring_nf
  · rcases vertical with ⟨edge, column⟩
    rcases edge with ⟨row, hRow⟩
    have hRowZero : row = 0 := by
      apply Fin.ext
      omega
    subst row
    rw [dyn_twoPort_sum]
    fin_cases column <;> cases port <;> cases mode <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, dynParameters,
        rectangularLatticeComponentScattering, TwoPortSeriesNetlist.physicalScattering,
        ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
        latticeCouplingScattering, DirectionalCoupler.mixing, Matrix.fromBlocks,
        ModeAmplitude.restrictEmbedding_apply, dynCoupler, dynIncident, dynOutgoing,
        dynIncidentValue, dynOutgoingValue] <;> norm_num <;> ring_nf

lemma dyn_connectedEquation (connected : dynConnections.Channel) :
    dynIncident (Incident.mk (dynConnections.channelEmbedding connected)) =
      dynOutgoing
        (Outgoing.mk (dynConnections.channelEmbedding (dynConnections.mateEquiv connected))) := by
  rcases connected with ⟨connection, localChannel⟩
  change dynIncident
      (Incident.mk (dynConnections.channelEmbedding
        (dynConnections.connectionChannelEmbedding connection localChannel))) =
    dynOutgoing
      (Outgoing.mk (dynConnections.channelEmbedding
        (dynConnections.mateEquiv
          (dynConnections.connectionChannelEmbedding connection localChannel))))
  rw [dynConnections.channelEmbedding_connectionChannelEmbedding,
    dynConnections.channelEmbedding_mateEquiv_connectionChannelEmbedding]
  rcases connection with horizontal | vertical
  · rcases horizontal with ⟨⟨row, edge⟩, half⟩
    rcases edge with ⟨column, hColumn⟩
    have hColumnZero : column = 0 := by
      apply Fin.ext
      omega
    subst column
    change dynIncidentValue _ _ = dynOutgoingValue _ _
    fin_cases row <;> cases half <;>
      rcases localChannel with mode | mode <;> cases mode <;>
      simp [dynConnections, rectangularLatticeNetlist, rectangularHorizontalConnections,
        PortConnectionFamily.append, ScatteringComponentFamily.componentChannelEmbedding,
        ScatteringComponentFamily.channelEquiv, dynIncident, dynOutgoing, dynIncidentValue,
        dynOutgoingValue, dynHorizontalIncidentValue, dynHorizontalOutgoingValue]
  · rcases vertical with ⟨⟨edge, column⟩, half⟩
    rcases edge with ⟨row, hRow⟩
    have hRowZero : row = 0 := by
      apply Fin.ext
      omega
    subst row
    change dynIncidentValue _ _ = dynOutgoingValue _ _
    fin_cases column <;> cases half <;>
      rcases localChannel with mode | mode <;> cases mode <;>
      simp [dynConnections, rectangularLatticeNetlist,
        rectangularVerticalBoundaryConnections, LatticeConnectionFamilies.onBoundary,
        LatticeConnectionFamilies.connectionOnBoundary, rectangularVerticalConnections,
        rectangularVerticalConnection, PortConnectionFamily.append,
        PortConnection.liftBoundary, PortConnection.liftBoundary_modeEquiv,
        ScatteringComponentFamily.componentChannelEmbedding,
        ScatteringComponentFamily.channelEquiv, dynIncident, dynOutgoing, dynIncidentValue,
        dynOutgoingValue, dynVerticalIncidentValue, dynVerticalOutgoingValue]

lemma dyn_incidentAssembly :
    dynIncident = dynConnections.incidentAssembly dynOutgoing dynInput := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  by_cases hConnected : channel ∈ Set.range dynConnections.channelEmbedding
  · rcases hConnected with ⟨connected, rfl⟩
    rw [dynConnections.incidentAssembly_apply_connected_channel]
    exact dyn_connectedEquation connected
  · let external : dynConnections.ExternalChannel := ⟨channel, hConnected⟩
    rw [show channel = external.1 by rfl,
      dynConnections.incidentAssembly_apply_external]
    rfl

lemma dyn_outputReadout :
    dynOutput =
      (rectangularLatticeNetlist dynParameters).outputReadout.toLinearMap dynOutgoing := by
  change dynOutgoing.restrictEmbedding dynConnections.externalOutgoingEmbedding =
    dynConnections.externalOutgoingReadout.toLinearMap dynOutgoing
  rw [PortConnectionFamily.externalOutgoingReadout_apply]

lemma dyn_mem_flatBehavior :
    (dynInput, dynOutput) ∈ (rectangularLatticeNetlist dynParameters).behavior := by
  exact ((rectangularLatticeNetlist
    dynParameters).mem_behavior_iff_componentBehavior dynInput dynOutput).2
      ⟨dynIncident, dynOutgoing, dyn_mem_componentBehavior,
        dyn_incidentAssembly, dyn_outputReadout⟩

abbrev dynRowHierarchy := rectangularLatticeRowHierarchy dynParameters

def dynInnerDrive : ModeAmplitude (Incident dynRowHierarchy.inner.ExternalChannel) :=
  dynRowHierarchy.inner.appendInnerDrive dynRowHierarchy.outer dynOutgoing dynInput

def dynInnerOutput : ModeAmplitude (Outgoing dynRowHierarchy.inner.ExternalChannel) :=
  dynRowHierarchy.inner.externalOutgoingReadout.toLinearMap dynOutgoing

lemma dyn_mem_innerClosure :
    (dynInnerDrive, dynInnerOutput) ∈
      dynRowHierarchy.inner.closeBehavior
        (rectangularRowHierarchyComponentBehavior dynParameters) := by
  rw [dynRowHierarchy.inner.mem_closeBehavior_iff]
  refine ⟨dynIncident, dynOutgoing, ?_, ?_, rfl⟩
  · change (dynIncident, dynOutgoing) ∈
      (rectangularLatticeNetlist dynParameters).componentBehavior
    exact dyn_mem_componentBehavior
  exact dyn_incidentAssembly.trans
    (dynRowHierarchy.inner.append_incidentAssembly_eq
      dynRowHierarchy.outer dynOutgoing dynInput)

def dynBoundaryIncident :
    ModeAmplitude (Incident dynRowHierarchy.inner.externalPortModeFamily.Channel) :=
  ModeAmplitude.reindex
    (Incident.relabelEquiv dynRowHierarchy.inner.boundaryChannelEquiv.symm) dynInnerDrive

def dynBoundaryOutgoing :
    ModeAmplitude (Outgoing dynRowHierarchy.inner.externalPortModeFamily.Channel) :=
  ModeAmplitude.reindex
    (Outgoing.relabelEquiv dynRowHierarchy.inner.boundaryChannelEquiv.symm) dynInnerOutput

lemma dyn_mem_innerBoundary :
    (dynBoundaryIncident, dynBoundaryOutgoing) ∈
      dynRowHierarchy.inner.innerBoundaryBehavior
        (rectangularRowHierarchyComponentBehavior dynParameters) := by
  rw [PortConnectionFamily.innerBoundaryBehavior, LinearBehavior.mem_reindex_iff]
  simpa [dynBoundaryIncident, dynBoundaryOutgoing] using dyn_mem_innerClosure

def dynOuterInput : ModeAmplitude (Incident dynRowHierarchy.outer.ExternalChannel) :=
  ModeAmplitude.reindex
    (Incident.relabelEquiv
      (dynRowHierarchy.inner.appendExternalChannelEquiv dynRowHierarchy.outer)) dynInput

def dynOuterOutput : ModeAmplitude (Outgoing dynRowHierarchy.outer.ExternalChannel) :=
  ModeAmplitude.reindex
    (Outgoing.relabelEquiv
      (dynRowHierarchy.inner.appendExternalChannelEquiv dynRowHierarchy.outer)) dynOutput

lemma dyn_mem_outerClosure :
    (dynOuterInput, dynOuterOutput) ∈
      dynRowHierarchy.outer.closeBehavior
        (dynRowHierarchy.inner.innerBoundaryBehavior
          (rectangularRowHierarchyComponentBehavior dynParameters)) := by
  rw [dynRowHierarchy.outer.mem_closeBehavior_iff]
  refine ⟨dynBoundaryIncident, dynBoundaryOutgoing, dyn_mem_innerBoundary, ?_, ?_⟩
  · unfold dynBoundaryIncident dynBoundaryOutgoing dynInnerDrive dynInnerOutput
      dynOuterInput
    exact dynRowHierarchy.inner.appendInnerDrive_eq
      dynRowHierarchy.outer dynOutgoing dynInput
  · unfold dynBoundaryOutgoing dynInnerOutput dynOuterOutput
    rw [dyn_outputReadout]
    exact dynRowHierarchy.inner.append_externalOutgoingReadout_eq
      dynRowHierarchy.outer dynOutgoing

lemma dyn_mem_rowDecomposition :
    (dynInput, dynOutput) ∈ rectangularRowDecompositionBehavior dynParameters := by
  unfold rectangularRowDecompositionBehavior
  rw [LinearBehavior.mem_reindex_iff, Equiv.symm_symm, Equiv.symm_symm]
  simpa [dynOuterInput, dynOuterOutput] using dyn_mem_outerClosure

lemma dyn_horizontalWire_nonzero :
    dynIncident (Incident.mk (dynRingChannel 0 1 .west)) =
        dynOutgoing (Outgoing.mk (dynHorizontalCouplerChannel 0 .right)) ∧
      dynOutgoing (Outgoing.mk (dynHorizontalCouplerChannel 0 .right)) ≠ 0 := by
  constructor
  · rfl
  · change (-6 * Complex.I : ℂ) ≠ 0
    norm_num

lemma dyn_verticalWire_nonzero :
    dynIncident (Incident.mk (dynRingChannel 1 1 .north)) =
        dynOutgoing (Outgoing.mk (dynVerticalCouplerChannel 1 .right)) ∧
      dynOutgoing (Outgoing.mk (dynVerticalCouplerChannel 1 .right)) ≠ 0 := by
  constructor
  · rfl
  · change (-126 : ℂ) ≠ 0
    norm_num

lemma dyn_crossParameters :
    (dynParameters.horizontalCoupler 0 dynForwardIndex).crossAmplitude = 3 ∧
      (dynParameters.verticalCoupler dynForwardIndex 1).crossAmplitude = 7 ∧
      (dynParameters.horizontalCoupler 0 dynForwardIndex).throughAmplitude = 2 ∧
      (dynParameters.verticalCoupler dynForwardIndex 1).throughAmplitude = 5 := by
  norm_num [dynParameters, dynForwardIndex, dynCoupler]

lemma dyn_outputPathValue :
    dynOutgoing (Outgoing.mk (dynRingChannel 1 1 .east)) = -630 := by
  rfl

lemma dyn_inputValue :
    dynInput (Incident.mk dynExternalInput) = 1 := by
  rfl

lemma dyn_outputValue :
    dynOutput (Outgoing.mk dynExternalOutput) = -630 := by
  rfl

lemma dyn_flat_and_rowDecomposition :
    (dynInput, dynOutput) ∈ (rectangularLatticeNetlist dynParameters).behavior ∧
      (dynInput, dynOutput) ∈ rectangularRowDecompositionBehavior dynParameters :=
  ⟨dyn_mem_flatBehavior, dyn_mem_rowDecomposition⟩

def dynMiswiredVerticalConnection
    (index : RectangularVerticalConnection 2 2) :
    PortConnection (rectangularLatticeComponents dynParameters).aggregatePortModeFamily :=
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

def dynMiswiredVerticalConnections :
    PortConnectionFamily
      (rectangularLatticeComponents dynParameters).aggregatePortModeFamily
      (RectangularVerticalConnection 2 2) where
  connection := dynMiswiredVerticalConnection
  endpointPort_injective := by
    rintro ⟨⟨⟨firstRow, firstColumn⟩, firstHalf⟩, firstEnd⟩
      ⟨⟨⟨secondRow, secondColumn⟩, secondHalf⟩, secondEnd⟩ hPort
    cases firstHalf <;> cases secondHalf <;> cases firstEnd <;> cases secondEnd <;>
      simp only [dynMiswiredVerticalConnection, PortConnection.endpointPort] at hPort
    all_goals
      injection hPort
      simp_all [rectangularRingComponent, rectangularVerticalCouplerComponent]

lemma dynMiswired_endpointDisjoint :
    LatticeConnectionFamilies.EndpointDisjoint
      (rectangularHorizontalConnections dynParameters)
      dynMiswiredVerticalConnections := by
  rintro ⟨⟨rowHorizontal, columnHorizontal⟩, halfHorizontal⟩ endHorizontal
    ⟨⟨rowVertical, columnVertical⟩, halfVertical⟩ endVertical hPort
  cases halfHorizontal <;> cases halfVertical <;>
    cases endHorizontal <;> cases endVertical <;>
    simp only [rectangularHorizontalConnections, rectangularHorizontalConnection,
      dynMiswiredVerticalConnections, dynMiswiredVerticalConnection,
      PortConnection.endpointPort] at hPort
  all_goals
    have hLabel := congrArg dynSitePortLabel hPort
    simp [dynSitePortLabel] at hLabel
  all_goals
    have hComponent := congrArg Sigma.fst hPort
    cases hComponent

def dynMiswiredVerticalBoundaryConnections :=
  LatticeConnectionFamilies.onBoundary
    (rectangularHorizontalConnections dynParameters) dynMiswiredVerticalConnections
    dynMiswired_endpointDisjoint

abbrev dynMiswiredConnections :=
  (rectangularHorizontalConnections dynParameters).append
    dynMiswiredVerticalBoundaryConnections

noncomputable instance dynMiswiredBoundaryLocalChannelFintype
    (index : RectangularVerticalConnection 2 2) :
    Fintype (dynMiswiredVerticalBoundaryConnections.connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

noncomputable instance dynMiswiredLocalChannelFintype
    (index : RectangularHorizontalConnection 2 2 ⊕ RectangularVerticalConnection 2 2) :
    Fintype (dynMiswiredConnections.connection index).LocalChannel := by
  rcases index with index | index
  · exact rectangularHorizontalLocalChannelFintype dynParameters index
  · change Fintype (dynMiswiredVerticalBoundaryConnections.connection index).LocalChannel
    infer_instance

noncomputable instance dynMiswiredConnectedChannelFintype :
    Fintype dynMiswiredConnections.Channel :=
  Fintype.ofFinite _

noncomputable instance dynMiswiredConnectedChannelDecidableEq :
    DecidableEq dynMiswiredConnections.Channel :=
  Classical.decEq _

lemma dynMiswired_incidentAssembly_ring11North
    (input : ModeAmplitude (Incident dynMiswiredConnections.ExternalChannel)) :
    dynMiswiredConnections.incidentAssembly dynOutgoing input
        (Incident.mk (dynRingChannel 1 1 .north)) =
      dynOutgoing (Outgoing.mk (dynVerticalCouplerChannel 0 .right)) := by
  change dynMiswiredConnections.incidentAssembly dynOutgoing input
      (Incident.mk (dynMiswiredConnections.channelEmbedding
        ⟨Sum.inr ((dynForwardIndex, (0 : Fin 2)), true), Sum.inr ()⟩)) = _
  rw [dynMiswiredConnections.incidentAssembly_apply_connected_channel]
  rfl

lemma dynMiswired_incidentAssembly_rejected
    (input : ModeAmplitude (Incident dynMiswiredConnections.ExternalChannel)) :
    dynIncident ≠ dynMiswiredConnections.incidentAssembly dynOutgoing input := by
  intro hAssembly
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Incident.mk (dynRingChannel 1 1 .north))) hAssembly
  rw [dynMiswired_incidentAssembly_ring11North] at hCoordinate
  change (-126 : ℂ) = 0 at hCoordinate
  norm_num at hCoordinate

end

end Optics.MicroringCascade
