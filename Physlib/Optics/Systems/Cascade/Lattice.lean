/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Network.LinearBehaviorReindex
public import Physlib.Optics.Network.TwoPortSeriesNetlist
public import Physlib.Optics.Systems.Cascade.Termination

/-!
# DATE row sublattices and Physlib-original rectangular microring lattices

## i. Overview

DATE'14 Figure 3(i) describes an uncoupled row as a linear cascade of microring resonators
periodically coupled to two side waveguides. The source-backed object in this file is only a named
view of the heterogeneous DATE cascade already defined at
`Physlib/Optics/Systems/Cascade/Heterogeneous.lean:209-220`. Its matrix, identical-row, Sylvester,
and terminated consequences are reused from
`Physlib/Optics/Systems/Cascade/Heterogeneous.lean:227-261`,
`Physlib/Optics/Systems/Cascade/Identical.lean:84-117,326-343`, and
`Physlib/Optics/Systems/Cascade/Termination.lean:321-447`. No new physics is added to that row.
This is goal.md:2434's "the source-backed uncoupled row-sublattice result".

The remainder supplies "coupled row/column decompositions and the full `M × N` lattice theorem,
explicitly classified as Physlib-original rather than DATE'14 parity", verbatim from
`goal.md:2435-2436`. A rectangular site owns an explicitly supplied four-boundary scattering law.
Neighbouring sites are joined through separately indexed horizontal or vertical coupling
components. Both connection stages flatten to the same physical wiring, up to the order in which
connection labels are presented.

## ii. Key results

- `DateUncoupledRowSublattice`: the source-backed DATE Figure 3(i) row view.
- `RectangularLatticeParameters`: site laws and neighbour-coupling parameters.
- `rectangularLatticeNetlist`: the complete explicit flat lattice.
- `rectangularLatticeRowHierarchy`: horizontal links closed before vertical links.
- `rectangularLatticeColumnHierarchy`: vertical links closed before horizontal links.
- `rectangularLatticeBehavior_eq_rowDecomposition`: row-first hierarchical semantics.
- `rectangularLatticeBehavior_eq_columnDecomposition`: column-first hierarchical semantics.

## iii. Table of contents

- A. Source-backed DATE row sublattice
- B. Rectangular sites and coupling components
- C. Horizontal and vertical connection families
- D. Coupled columns and the full rectangular netlist
- E. Row/column hierarchical flattening

## iv. References

The supplied site and coupling matrices are fixed-carrier algebraic component laws. No physical
realization, coupled-lattice closed form, quadruple-ring result, passivity, losslessness,
reciprocity, stability, resonance, bandwidth, dispersion, bending-loss, measurement, causality,
or material claim is made. The identical-row `^ count` is matrix exponentiation, not an optical
power observable. Any modal-power interpretation is not electromagnetic power before the finite,
common-frequency, pairwise-integrable, flux-orthogonal, unit-normalized profile bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

DATE'14 Figure 3 is summarized at `HOL-CORPUS.md:210-216`. The paper proves only the uncoupled row
sublattice and says only that the coupled case "follows the similar pattern". It prints no coupled
column or `M × N` theorem. Thus Section A is the only DATE'14-parity content here; Sections B--E
are Physlib-original and do not discharge a DATE'14 theorem.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

/-!

## A. Source-backed DATE row sublattice

-/

/-- DATE'14 Figure 3(i)'s uncoupled row periodically coupled to two side waveguides.

The stored stages are exactly the heterogeneous source cascade from
`Physlib/Optics/Systems/Cascade/Heterogeneous.lean:209-220`.
-/
structure DateUncoupledRowSublattice where
  /-- The input-to-output list of DATE rings and following bus lengths. -/
  stages : List DateCascadeStage

namespace DateUncoupledRowSublattice

/-- The row's singular-safe behavior is the existing heterogeneous cascade behavior. -/
def behavior (row : DateUncoupledRowSublattice) :
    BackwardFirstTwoPortBehavior Unit Unit :=
  dateCascadeBehavior row.stages

/-- The row's source matrix product is the existing heterogeneous cascade composition. -/
def composition (row : DateUncoupledRowSublattice) :
    BackwardFirstChainTransform Unit Unit :=
  dateCascadeComposition row.stages

/-- A repeated DATE stage, viewed as the source's identical uncoupled row. -/
def identical (stage : DateCascadeStage) (count : ℕ) : DateUncoupledRowSublattice where
  stages := List.replicate count stage

/-- DATE'14 Thm. 3 transfers unchanged to the Figure 3(i) row view.

This is `dateCascadeBehavior_eq_composition_toBehavior` at
`Physlib/Optics/Systems/Cascade/Heterogeneous.lean:227-241` with no additional hypothesis.
-/
lemma behavior_eq_composition_toBehavior (row : DateUncoupledRowSublattice)
    (hStages : ∀ stage ∈ row.stages, stage.HasBijectiveRingTransmission) :
    row.behavior = row.composition.toBehavior :=
  dateCascadeBehavior_eq_composition_toBehavior row.stages hStages

/-- DATE'14 Thm. 4 transfers unchanged to an identical Figure 3(i) row.

Here `^ count` is matrix exponentiation, not normalized modal power. The reused matrix-power result
is at `Physlib/Optics/Systems/Cascade/Identical.lean:99-103`.
-/
lemma identical_composition_eq_pow (stage : DateCascadeStage) (count : ℕ) :
    (identical stage count).composition = stage.compositionMatrix ^ count :=
  dateIdenticalCascadeComposition_eq_pow stage count

/-- The source-backed identical row inherits the exact DATE Sylvester domain.

This is the specialization at `Physlib/Optics/Systems/Cascade/Identical.lean:336-343`; it makes no
claim outside `DateSylvesterHypotheses`.
-/
lemma identical_composition_eq_sylvesterClosedForm
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateSylvesterHypotheses stage.compositionMatrix) :
    (identical stage count).composition =
      dateSylvesterClosedForm stage.compositionMatrix count :=
  dateIdenticalCascadeComposition_eq_sylvesterClosedForm stage count h

/-- The exact corrected termination domain for a source-backed uncoupled row. -/
abbrev TerminationHypotheses (row : DateUncoupledRowSublattice) : Prop :=
  DateCascadeTerminationHypotheses row.stages

/-- The relationally extracted complex reflection amplitude of a terminated DATE row. -/
noncomputable def reflectivity (row : DateUncoupledRowSublattice)
    (h : row.TerminationHypotheses) : ℂ :=
  dateTerminatedCascadeReflectivity row.stages h

/-- The relationally extracted complex transmission amplitude of a terminated DATE row. -/
noncomputable def transmissivity (row : DateUncoupledRowSublattice)
    (h : row.TerminationHypotheses) : ℂ :=
  dateTerminatedCascadeTransmissivity row.stages h

/-- DATE'14 Thm. 5's reflection formula transfers to the row under the corrected pivot gate.

The source result and its `M11 != 0` correction are at
`Physlib/Optics/Systems/Cascade/Termination.lean:321-330,417-431`.
-/
lemma reflectivity_eq_neg_entry12_div_entry11
    (row : DateUncoupledRowSublattice) (h : row.TerminationHypotheses) :
    row.reflectivity h =
      -dateChainEntry row.composition 0 1 / dateChainEntry row.composition 0 0 :=
  dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11 row.stages h

/-- DATE'14 Thm. 5's transmission formula transfers under the corrected row pivot gate.

The reused relational result is at
`Physlib/Optics/Systems/Cascade/Termination.lean:433-447`.
-/
lemma transmissivity_eq_one_div_entry11
    (row : DateUncoupledRowSublattice) (h : row.TerminationHypotheses) :
    row.transmissivity h = 1 / dateChainEntry row.composition 0 0 :=
  dateTerminatedCascade_transmissivity_eq_one_div_entry11 row.stages h

end DateUncoupledRowSublattice

/-!

## B. Rectangular sites and coupling components

-/

/-- The west, east, north, and south boundaries of one algebraic lattice site. -/
inductive LatticeSitePort
  | west
  | east
  | north
  | south
  deriving DecidableEq

/-- The four lattice-site ports form a finite type. -/
instance : Fintype LatticeSitePort where
  elems := {.west, .east, .north, .south}
  complete port := by cases port <;> simp

/-- A lattice site has one scalar mode at each of its four boundaries. -/
def latticeSitePortFamily : PortModeFamily where
  Port := LatticeSitePort
  Mode := fun _ => Unit

/-- The pinned site-port order as physical one-mode channels. -/
def latticeSiteChannelEquiv : LatticeSitePort ≃ latticeSitePortFamily.Channel where
  toFun port := ⟨port, ()⟩
  invFun channel := channel.1
  left_inv _ := rfl
  right_inv channel := by rcases channel with ⟨port, ⟨⟩⟩; rfl

/-- A site scattering law transported to its owned physical channels. -/
def latticeSitePhysicalScattering (scattering : ScatteringMatrix LatticeSitePort) :
    ScatteringMatrix latticeSitePortFamily.Channel :=
  scattering.reindex latticeSiteChannelEquiv

/-- The two-channel N7 mixer used as an algebraic nearest-neighbour coupling component.

The coefficient convention is `DirectionalCoupler.mixing` at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77`. This is an algebraic coupling block,
not the four-physical-port realization in `DirectionalCouplerPhysical.lean:56-73`.
-/
def latticeCouplingScattering (p : DirectionalCoupler.Parameters) :
    ScatteringMatrix (Unit ⊕ Unit) where
  toModeTransform := DirectionalCoupler.mixing p Unit

/-- A forward neighbour index: a site index together with proof that its successor exists. -/
abbrev LatticeForwardIndex (count : ℕ) := {index : Fin count // index.val + 1 < count}

/-- The site immediately after a forward neighbour index. -/
def LatticeForwardIndex.succ {count : ℕ}
    (index : LatticeForwardIndex count) : Fin count :=
  ⟨index.1.val + 1, index.2⟩

/-- Parameters of a fixed-carrier rectangular algebraic microring lattice.

Each site law is supplied explicitly because DATE'14 prints no coupled-site model. Horizontal and
vertical neighbour couplers use the N7 algebraic coefficient convention cited above.
-/
structure RectangularLatticeParameters (rows columns : ℕ) where
  /-- The four-boundary scattering law of each algebraic microring site. -/
  ringScattering : Fin rows → Fin columns → ScatteringMatrix LatticeSitePort
  /-- Coupling parameters on every horizontal nearest-neighbour edge. -/
  horizontalCoupler :
    Fin rows → LatticeForwardIndex columns → DirectionalCoupler.Parameters
  /-- Coupling parameters on every vertical nearest-neighbour edge. -/
  verticalCoupler :
    LatticeForwardIndex rows → Fin columns → DirectionalCoupler.Parameters

/-- Component labels: ring sites, horizontal couplers, then vertical couplers. -/
abbrev RectangularLatticeComponent (rows columns : ℕ) :=
  (Fin rows × Fin columns) ⊕
    ((Fin rows × LatticeForwardIndex columns) ⊕
      (LatticeForwardIndex rows × Fin columns))

/-- The component label of a selected ring site. -/
def rectangularRingComponent {rows columns : ℕ} (row : Fin rows) (column : Fin columns) :
    RectangularLatticeComponent rows columns :=
  Sum.inl (row, column)

/-- The component label of a selected horizontal neighbour coupler. -/
def rectangularHorizontalCouplerComponent {rows columns : ℕ}
    (row : Fin rows) (column : LatticeForwardIndex columns) :
    RectangularLatticeComponent rows columns :=
  Sum.inr (Sum.inl (row, column))

/-- The component label of a selected vertical neighbour coupler. -/
def rectangularVerticalCouplerComponent {rows columns : ℕ}
    (row : LatticeForwardIndex rows) (column : Fin columns) :
    RectangularLatticeComponent rows columns :=
  Sum.inr (Sum.inr (row, column))

/-- The physical-port family owned by each rectangular-lattice component. -/
def rectangularLatticeComponentPortFamily {rows columns : ℕ} :
    RectangularLatticeComponent rows columns → PortModeFamily
  | Sum.inl _ => latticeSitePortFamily
  | Sum.inr _ => TwoPortSeriesNetlist.portFamily Unit Unit

/-- The scattering law selected by each rectangular-lattice component. -/
def rectangularLatticeComponentScattering {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (component : RectangularLatticeComponent rows columns) →
      ScatteringMatrix (rectangularLatticeComponentPortFamily component).Channel
  | Sum.inl (row, column) => latticeSitePhysicalScattering (p.ringScattering row column)
  | Sum.inr (Sum.inl (row, column)) =>
      TwoPortSeriesNetlist.physicalScattering
        (latticeCouplingScattering (p.horizontalCoupler row column))
  | Sum.inr (Sum.inr (row, column)) =>
      TwoPortSeriesNetlist.physicalScattering
        (latticeCouplingScattering (p.verticalCoupler row column))

/-- All ring sites and neighbour couplers before the lattice wiring is installed. -/
def rectangularLatticeComponents {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) : ScatteringComponentFamily where
  Component := RectangularLatticeComponent rows columns
  portFamily := rectangularLatticeComponentPortFamily
  scattering := rectangularLatticeComponentScattering p

/-- Rectangular component labels inherit their finite sum/product enumeration. -/
noncomputable instance rectangularLatticeComponentFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeComponents p).Component := by
  change Fintype (RectangularLatticeComponent rows columns)
  infer_instance

/-- Rectangular component labels inherit decidable equality. -/
noncomputable instance rectangularLatticeComponentDecidableEq {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    DecidableEq (rectangularLatticeComponents p).Component := by
  change DecidableEq (RectangularLatticeComponent rows columns)
  infer_instance

/-- Every rectangular component has a finite local channel family. -/
noncomputable instance rectangularLatticeLocalChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (component : (rectangularLatticeComponents p).Component) :
    Fintype ((rectangularLatticeComponents p).portFamily component).Channel := by
  change Fintype (rectangularLatticeComponentPortFamily component).Channel
  rcases component with component | component
  · change Fintype latticeSitePortFamily.Channel
    exact Fintype.ofEquiv LatticeSitePort latticeSiteChannelEquiv
  · change Fintype (TwoPortSeriesNetlist.portFamily Unit Unit).Channel
    infer_instance

/-- Every rectangular component has decidable equality on local channels. -/
noncomputable instance rectangularLatticeLocalChannelDecidableEq {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (component : (rectangularLatticeComponents p).Component) :
    DecidableEq ((rectangularLatticeComponents p).portFamily component).Channel := by
  change DecidableEq (rectangularLatticeComponentPortFamily component).Channel
  rcases component with component | component
  · exact latticeSiteChannelEquiv.symm.decidableEq
  · rcases component with component | component
    · change DecidableEq (TwoPortSeriesNetlist.portFamily Unit Unit).Channel
      exact TwoPortSeriesNetlist.channelDecidableEq
    · change DecidableEq (TwoPortSeriesNetlist.portFamily Unit Unit).Channel
      exact TwoPortSeriesNetlist.channelDecidableEq

/-- The aggregate rectangular component boundary is finite. -/
noncomputable instance rectangularLatticeAggregateChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeComponents p).aggregatePortModeFamily.Channel := by
  letI : Fintype (rectangularLatticeComponents p).IndexedChannel := by
    infer_instance
  exact Fintype.ofEquiv (rectangularLatticeComponents p).IndexedChannel
    (rectangularLatticeComponents p).channelEquiv

/-- The aggregate rectangular component boundary has decidable equality. -/
noncomputable instance rectangularLatticeAggregateChannelDecidableEq {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    DecidableEq (rectangularLatticeComponents p).aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-!

## C. Horizontal and vertical connection families

-/

/-- A horizontal edge has two wires, one on each side of its coupling component. -/
abbrev RectangularHorizontalConnection (rows columns : ℕ) :=
  (Fin rows × LatticeForwardIndex columns) × Bool

/-- A vertical edge has two wires, one on each side of its coupling component. -/
abbrev RectangularVerticalConnection (rows columns : ℕ) :=
  (LatticeForwardIndex rows × Fin columns) × Bool

/-- Successor preserves equality of forward neighbour indices. -/
lemma LatticeForwardIndex.succ_injective {count : ℕ} :
    Function.Injective (@LatticeForwardIndex.succ count) := by
  intro first second hSucc
  apply Subtype.ext
  apply Fin.ext
  have hValue := congrArg Fin.val hSucc
  change first.1.val + 1 = second.1.val + 1 at hValue
  omega

/-- Equal underlying site indices determine equal forward neighbour indices. -/
@[simp]
lemma LatticeForwardIndex.coe_eq_coe {count : ℕ}
    (first second : LatticeForwardIndex count) :
    (first.1 : Fin count) = second.1 ↔ first = second :=
  Subtype.val_injective.eq_iff

/-- Equal successor sites determine equal forward neighbour indices. -/
@[simp]
lemma LatticeForwardIndex.succ_eq_succ {count : ℕ}
    (first second : LatticeForwardIndex count) :
    first.succ = second.succ ↔ first = second :=
  LatticeForwardIndex.succ_injective.eq_iff

/-- One horizontal lattice wire, with `false` before and `true` after the coupler. -/
def rectangularHorizontalConnection {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (index : RectangularHorizontalConnection rows columns) :
    PortConnection (rectangularLatticeComponents p).aggregatePortModeFamily :=
  match index with
  | ((row, column), false) =>
      { left := ⟨rectangularRingComponent row column.1, LatticeSitePort.east⟩
        right :=
          ⟨rectangularHorizontalCouplerComponent row column,
            TwoPortSeriesNetlist.Port.left⟩
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }
  | ((row, column), true) =>
      { left :=
          ⟨rectangularHorizontalCouplerComponent row column,
            TwoPortSeriesNetlist.Port.right⟩
        right := ⟨rectangularRingComponent row column.succ, LatticeSitePort.west⟩
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }

/-- One vertical lattice wire, with `false` before and `true` after the coupler. -/
def rectangularVerticalConnection {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (index : RectangularVerticalConnection rows columns) :
    PortConnection (rectangularLatticeComponents p).aggregatePortModeFamily :=
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
        right := ⟨rectangularRingComponent row.succ column, LatticeSitePort.north⟩
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }

/-- All horizontal neighbour wires, grouped by their row index. -/
def rectangularHorizontalConnections {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    PortConnectionFamily (rectangularLatticeComponents p).aggregatePortModeFamily
      (RectangularHorizontalConnection rows columns) where
  connection := rectangularHorizontalConnection p
  endpointPort_injective := by
    rintro ⟨⟨⟨firstRow, firstColumn⟩, firstHalf⟩, firstEnd⟩
      ⟨⟨⟨secondRow, secondColumn⟩, secondHalf⟩, secondEnd⟩ hPort
    cases firstHalf <;> cases secondHalf <;> cases firstEnd <;> cases secondEnd <;>
      simp only [rectangularHorizontalConnection, PortConnection.endpointPort] at hPort
    all_goals
      injection hPort
      simp_all [rectangularRingComponent, rectangularHorizontalCouplerComponent]

/-- All vertical neighbour wires, grouped by their column index. -/
def rectangularVerticalConnections {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    PortConnectionFamily (rectangularLatticeComponents p).aggregatePortModeFamily
      (RectangularVerticalConnection rows columns) where
  connection := rectangularVerticalConnection p
  endpointPort_injective := by
    rintro ⟨⟨⟨firstRow, firstColumn⟩, firstHalf⟩, firstEnd⟩
      ⟨⟨⟨secondRow, secondColumn⟩, secondHalf⟩, secondEnd⟩ hPort
    cases firstHalf <;> cases secondHalf <;> cases firstEnd <;> cases secondEnd <;>
      simp only [rectangularVerticalConnection, PortConnection.endpointPort] at hPort
    all_goals
      injection hPort
      simp_all [rectangularRingComponent, rectangularVerticalCouplerComponent]

/-- Each horizontal connection has a finite pair of endpoint channels. -/
noncomputable instance rectangularHorizontalLocalChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (index : RectangularHorizontalConnection rows columns) :
    Fintype ((rectangularHorizontalConnections p).connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Horizontal connected-channel labels form a finite family. -/
noncomputable instance rectangularHorizontalConnectedChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularHorizontalConnections p).Channel := by
  exact Fintype.ofFinite _

/-- Each vertical connection has a finite pair of endpoint channels. -/
noncomputable instance rectangularVerticalLocalChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns)
    (index : RectangularVerticalConnection rows columns) :
    Fintype ((rectangularVerticalConnections p).connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Vertical connected-channel labels form a finite family. -/
noncomputable instance rectangularVerticalConnectedChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularVerticalConnections p).Channel := by
  exact Fintype.ofFinite _

/-- Channels exposed after horizontal wiring form a finite family. -/
noncomputable instance rectangularHorizontalExternalChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularHorizontalConnections p).ExternalChannel := by
  classical
  infer_instance

/-- The horizontal stage's boundary port family has finitely many channels. -/
noncomputable instance rectangularHorizontalBoundaryPortChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularHorizontalConnections p).externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ (rectangularHorizontalConnections p).boundaryChannelEquiv.symm

/-- Channels exposed after vertical wiring form a finite family. -/
noncomputable instance rectangularVerticalExternalChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularVerticalConnections p).ExternalChannel := by
  classical
  infer_instance

/-- The vertical stage's boundary port family has finitely many channels. -/
noncomputable instance rectangularVerticalBoundaryPortChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularVerticalConnections p).externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ (rectangularVerticalConnections p).boundaryChannelEquiv.symm

/-- Two connection families use disjoint ambient physical-port endpoints. -/
def LatticeConnectionFamilies.EndpointDisjoint
    {P : PortModeFamily} {firstIndex secondIndex : Type*}
    (first : PortConnectionFamily P firstIndex)
    (second : PortConnectionFamily P secondIndex) : Prop :=
  ∀ firstConnection firstEnd secondConnection secondEnd,
    (first.connection firstConnection).endpointPort firstEnd ≠
      (second.connection secondConnection).endpointPort secondEnd

/-- Horizontal and vertical lattice wires use distinct site ports and distinct couplers. -/
lemma rectangularConnections_endpointDisjoint {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    LatticeConnectionFamilies.EndpointDisjoint
      (rectangularHorizontalConnections p) (rectangularVerticalConnections p) := by
  rintro ⟨⟨rowHorizontal, columnHorizontal⟩, halfHorizontal⟩ endHorizontal
    ⟨⟨rowVertical, columnVertical⟩, halfVertical⟩ endVertical hPort
  cases halfHorizontal <;> cases halfVertical <;>
    cases endHorizontal <;> cases endVertical <;>
    simp only [rectangularHorizontalConnections, rectangularVerticalConnections,
      rectangularHorizontalConnection, rectangularVerticalConnection,
      PortConnection.endpointPort] at hPort
  all_goals cases hPort

namespace LatticeConnectionFamilies

variable {P : PortModeFamily} {firstIndex secondIndex : Type*}

/-- Endpoint disjointness is symmetric in the two connection families. -/
lemma EndpointDisjoint.symm
    {first : PortConnectionFamily P firstIndex}
    {second : PortConnectionFamily P secondIndex}
    (hDisjoint : EndpointDisjoint first second) : EndpointDisjoint second first := by
  intro secondConnection secondEnd firstConnection firstEnd
  exact (hDisjoint firstConnection firstEnd secondConnection secondEnd).symm

/-- Connection families are equal when their indexed physical connections are equal. -/
lemma family_eq_of_connection_eq
    {first second : PortConnectionFamily P firstIndex}
    (hConnection : first.connection = second.connection) : first = second := by
  cases first with
  | mk firstConnection firstInjective =>
      cases second with
      | mk secondConnection secondInjective =>
          cases hConnection
          rfl

/-- Present one ambient connection using two certified ports of an inner boundary. -/
def connectionOnBoundary (inner : PortConnectionFamily P firstIndex)
    (connection : PortConnection P)
    (hLeft : connection.left ∉ Set.range inner.endpointEmbedding)
    (hRight : connection.right ∉ Set.range inner.endpointEmbedding) :
    PortConnection inner.externalPortModeFamily where
  left := ⟨connection.left, hLeft⟩
  right := ⟨connection.right, hRight⟩
  left_ne_right := by
    intro hPort
    exact connection.left_ne_right (congrArg Subtype.val hPort)
  modeEquiv := connection.modeEquiv

/-- Lifting one boundary-presented connection recovers the ambient connection. -/
lemma liftBoundary_connectionOnBoundary (inner : PortConnectionFamily P firstIndex)
    (connection : PortConnection P)
    (hLeft : connection.left ∉ Set.range inner.endpointEmbedding)
    (hRight : connection.right ∉ Set.range inner.endpointEmbedding) :
    (connectionOnBoundary inner connection hLeft hRight).liftBoundary = connection := by
  cases connection
  rfl

/-- Present a disjoint ambient connection family on the boundary left by an inner family. -/
def onBoundary (inner : PortConnectionFamily P firstIndex)
    (later : PortConnectionFamily P secondIndex)
    (hDisjoint : EndpointDisjoint inner later) :
    PortConnectionFamily inner.externalPortModeFamily secondIndex where
  connection index :=
    connectionOnBoundary inner (later.connection index)
      (by
        rintro ⟨⟨innerIndex, innerEnd⟩, hPort⟩
        exact hDisjoint innerIndex innerEnd index PortConnection.End.left hPort)
      (by
        rintro ⟨⟨innerIndex, innerEnd⟩, hPort⟩
        exact hDisjoint innerIndex innerEnd index PortConnection.End.right hPort)
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstEnd <;> cases secondEnd
    all_goals
      apply later.endpointPort_injective
      exact congrArg Subtype.val hPort

/-- Lifting a disjoint boundary connection recovers its ambient physical connection. -/
lemma liftBoundary_onBoundary_connection
    (inner : PortConnectionFamily P firstIndex)
    (later : PortConnectionFamily P secondIndex)
    (hDisjoint : EndpointDisjoint inner later) (index : secondIndex) :
    ((onBoundary inner later hDisjoint).connection index).liftBoundary =
      later.connection index := by
  exact liftBoundary_connectionOnBoundary inner (later.connection index) _ _

end LatticeConnectionFamilies

/-!

## D. Coupled columns and the full rectangular netlist

-/

/-- Restrict rectangular parameters to one selected column.

The one-column lattice retains the selected site laws and vertical coupling components. Its
horizontal edge type is empty by construction.
-/
def RectangularLatticeParameters.singleColumn {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) (column : Fin columns) :
    RectangularLatticeParameters rows 1 where
  ringScattering row _ := p.ringScattering row column
  horizontalCoupler _ edge := by
    exfalso
    have := edge.2
    omega
  verticalCoupler row _ := p.verticalCoupler row column

/-- The explicit Physlib-original flat netlist of one mutually coupled column.

It contains the selected ring sites and a separate coupling component between each pair of
vertical neighbours. DATE'14 supplies no theorem or formal definition for this object.
-/
def rectangularCoupledColumnNetlist {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) (column : Fin columns) : FlatNetlist where
  components := rectangularLatticeComponents (p.singleColumn column)
  Connection := RectangularVerticalConnection rows 1
  connections := rectangularVerticalConnections (p.singleColumn column)

/-- An explicit coupled column has a finite aggregate channel family. -/
noncomputable instance rectangularCoupledColumnChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) (column : Fin columns) :
    Fintype (rectangularCoupledColumnNetlist p column).Channel :=
  rectangularLatticeAggregateChannelFintype (p.singleColumn column)

/-- An explicit coupled column has finitely many connected channels. -/
noncomputable instance rectangularCoupledColumnConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns)
    (column : Fin columns) :
    Fintype (rectangularCoupledColumnNetlist p column).ConnectedChannel :=
  rectangularVerticalConnectedChannelFintype (p.singleColumn column)

/-- A coupled column's relational composition closes its explicit vertical neighbour wires.

This is a singular-safe relation, not a closed-form transfer matrix.
-/
def rectangularCoupledColumnComposition {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) (column : Fin columns) :
    LinearBehavior
      (Incident (rectangularCoupledColumnNetlist p column).ExternalChannel)
      (Outgoing (rectangularCoupledColumnNetlist p column).ExternalChannel) :=
  (rectangularCoupledColumnNetlist p column).connections.closeBehavior
    (rectangularCoupledColumnNetlist p column).componentBehavior

/-- The explicit coupled-column behavior is its relational connection composition.

DATE'14 gives no coupled-column statement; this Physlib-original result is the generic flat-netlist
closure at `Physlib/Optics/Network/Hierarchical.lean:1054-1063` instantiated by the column.
-/
lemma rectangularCoupledColumn_behavior_eq_composition {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) (column : Fin columns) :
    (rectangularCoupledColumnNetlist p column).behavior =
      rectangularCoupledColumnComposition p column :=
  (rectangularCoupledColumnNetlist p column).behavior_eq_closeBehavior

/-- Vertical links presented on the boundary left after all horizontal links are installed. -/
def rectangularVerticalBoundaryConnections {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :=
  LatticeConnectionFamilies.onBoundary
    (rectangularHorizontalConnections p) (rectangularVerticalConnections p)
    (rectangularConnections_endpointDisjoint p)

/-- Horizontal links presented on the boundary left after all vertical links are installed. -/
def rectangularHorizontalBoundaryConnections {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :=
  LatticeConnectionFamilies.onBoundary
    (rectangularVerticalConnections p) (rectangularHorizontalConnections p)
    (rectangularConnections_endpointDisjoint p).symm

/-- Each row-first outer connection retains its finite endpoint-channel pair. -/
noncomputable instance rectangularVerticalBoundaryLocalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns)
    (index : RectangularVerticalConnection rows columns) :
    Fintype ((rectangularVerticalBoundaryConnections p).connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Row-first outer connected channels retain the finite vertical connection labels. -/
noncomputable instance rectangularVerticalBoundaryChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularVerticalBoundaryConnections p).Channel := by
  exact Fintype.ofFinite _

/-- Each column-first outer connection retains its finite endpoint-channel pair. -/
noncomputable instance rectangularHorizontalBoundaryLocalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns)
    (index : RectangularHorizontalConnection rows columns) :
    Fintype ((rectangularHorizontalBoundaryConnections p).connection index).LocalChannel := by
  rcases index with ⟨edge, half⟩
  cases half <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Column-first outer connected channels retain the finite horizontal connection labels. -/
noncomputable instance rectangularHorizontalBoundaryChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularHorizontalBoundaryConnections p).Channel := by
  exact Fintype.ofFinite _

/-- Row-first hierarchical presentation of all components and lattice wires.

This is Physlib-original: DATE'14 prints no coupled or full-lattice statement.
-/
@[reducible]
def rectangularLatticeRowHierarchy {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) : HierarchicalNetlist where
  components := rectangularLatticeComponents p
  InnerConnection := RectangularHorizontalConnection rows columns
  inner := rectangularHorizontalConnections p
  OuterConnection := RectangularVerticalConnection rows columns
  outer := rectangularVerticalBoundaryConnections p

/-- Column-first hierarchical presentation of all components and lattice wires.

This is Physlib-original: its inner stage is the disjoint union of the explicit coupled-column
connection patterns, and its outer stage installs the horizontal neighbour links.
-/
@[reducible]
def rectangularLatticeColumnHierarchy {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) : HierarchicalNetlist where
  components := rectangularLatticeComponents p
  InnerConnection := RectangularVerticalConnection rows columns
  inner := rectangularVerticalConnections p
  OuterConnection := RectangularHorizontalConnection rows columns
  outer := rectangularHorizontalBoundaryConnections p

/-- The row-first hierarchy's flattened ambient channels are finite. -/
noncomputable instance rectangularRowHierarchyFlattenChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).flatten.Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The row-first inner netlist shares the finite aggregate component boundary. -/
noncomputable instance rectangularRowHierarchyInnerChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).innerNetlist.Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The row-first inner netlist has the finite horizontal connected channels. -/
noncomputable instance rectangularRowHierarchyInnerConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).innerNetlist.ConnectedChannel :=
  rectangularHorizontalConnectedChannelFintype p

/-- The row-first inner netlist has finitely many exposed channels. -/
noncomputable instance rectangularRowHierarchyInnerExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).innerNetlist.ExternalChannel :=
  rectangularHorizontalExternalChannelFintype p

/-- The row-first inner connection family has finitely many exposed channels. -/
noncomputable instance rectangularRowHierarchyInnerFamilyExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).inner.ExternalChannel :=
  rectangularHorizontalExternalChannelFintype p

/-- The row-first inner boundary has finitely many physical channels. -/
noncomputable instance rectangularRowHierarchyInnerBoundaryChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).inner.externalPortModeFamily.Channel :=
  rectangularHorizontalBoundaryPortChannelFintype p

/-- The row-first outer stage has finite vertical connected channels. -/
noncomputable instance rectangularRowHierarchyOuterChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).outer.Channel :=
  rectangularVerticalBoundaryChannelFintype p

/-- The row-first outer connection family has finitely many exposed channels. -/
noncomputable instance rectangularRowHierarchyOuterExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).outer.ExternalChannel := by
  classical
  infer_instance

/-- The column-first hierarchy's flattened ambient channels are finite. -/
noncomputable instance rectangularColumnHierarchyFlattenChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The column-first inner netlist shares the finite aggregate component boundary. -/
noncomputable instance rectangularColumnHierarchyInnerChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).innerNetlist.Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The column-first inner netlist has the finite vertical connected channels. -/
noncomputable instance rectangularColumnHierarchyInnerConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).innerNetlist.ConnectedChannel :=
  rectangularVerticalConnectedChannelFintype p

/-- The column-first inner netlist has finitely many exposed channels. -/
noncomputable instance rectangularColumnHierarchyInnerExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).innerNetlist.ExternalChannel :=
  rectangularVerticalExternalChannelFintype p

/-- The column-first inner connection family has finitely many exposed channels. -/
noncomputable instance rectangularColumnHierarchyInnerFamilyExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).inner.ExternalChannel :=
  rectangularVerticalExternalChannelFintype p

/-- The column-first inner boundary has finitely many physical channels. -/
noncomputable instance rectangularColumnHierarchyInnerBoundaryChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).inner.externalPortModeFamily.Channel :=
  rectangularVerticalBoundaryPortChannelFintype p

/-- The column-first outer stage has finite horizontal connected channels. -/
noncomputable instance rectangularColumnHierarchyOuterChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).outer.Channel :=
  rectangularHorizontalBoundaryChannelFintype p

/-- The column-first outer connection family has finitely many exposed channels. -/
noncomputable instance rectangularColumnHierarchyOuterExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).outer.ExternalChannel := by
  classical
  infer_instance

/-- The row-first flattened component graph, typed on the hierarchy's ambient boundary. -/
def rectangularRowHierarchyComponentBehavior {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    LinearBehavior
      (Incident (rectangularLatticeRowHierarchy p).components.aggregatePortModeFamily.Channel)
      (Outgoing (rectangularLatticeRowHierarchy p).components.aggregatePortModeFamily.Channel) :=
  (rectangularLatticeRowHierarchy p).flatten.componentBehavior

/-- The column-first flattened component graph, typed on the hierarchy's ambient boundary. -/
def rectangularColumnHierarchyComponentBehavior {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    LinearBehavior
      (Incident
        (rectangularLatticeColumnHierarchy p).components.aggregatePortModeFamily.Channel)
      (Outgoing
        (rectangularLatticeColumnHierarchy p).components.aggregatePortModeFamily.Channel) :=
  (rectangularLatticeColumnHierarchy p).flatten.componentBehavior

/-- The complete explicit `M × N` flat lattice, with horizontal labels before vertical labels.

Its connection type and appended connection family are written directly, independently of either
behavior decomposition. It is Physlib-original rather than a DATE'14 parity object.
-/
@[reducible]
def rectangularLatticeNetlist {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) : FlatNetlist where
  components := rectangularLatticeComponents p
  Connection := RectangularHorizontalConnection rows columns ⊕
    RectangularVerticalConnection rows columns
  connections := (rectangularHorizontalConnections p).append
    (rectangularVerticalBoundaryConnections p)

/-- The complete rectangular flat-netlist channel family is finite. -/
noncomputable instance rectangularLatticeNetlistChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeNetlist p).Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The complete rectangular flat-netlist connected channels are finite. -/
noncomputable instance rectangularLatticeNetlistConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeNetlist p).ConnectedChannel := by
  exact Fintype.ofEquiv _
    ((rectangularHorizontalConnections p).appendChannelEquiv
      (rectangularVerticalBoundaryConnections p)).symm

/-- The row-first flattened connection family has finite connected channels. -/
noncomputable instance rectangularRowFlattenConnectionsChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).flatten.connections.Channel :=
  rectangularLatticeNetlistConnectedChannelFintype p

/-- The complete rectangular flat netlist has finitely many external channels. -/
noncomputable instance rectangularLatticeNetlistExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeNetlist p).ExternalChannel := by
  classical
  infer_instance

/-- The canonical flat lattice has finitely many external incident labels. -/
noncomputable instance rectangularLatticeNetlistExternalIncidentFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeNetlist p).ExternalIncident :=
  Incident.fintypeOf (rectangularLatticeNetlistExternalChannelFintype p)

/-- The canonical flat lattice has finitely many external outgoing labels. -/
noncomputable instance rectangularLatticeNetlistExternalOutgoingFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeNetlist p).ExternalOutgoing :=
  Outgoing.fintypeOf (rectangularLatticeNetlistExternalChannelFintype p)

/-- The row-first flattened connection family has finite external channels. -/
noncomputable instance rectangularRowFlattenConnectionsExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeRowHierarchy p).flatten.connections.ExternalChannel :=
  rectangularLatticeNetlistExternalChannelFintype p

/-- The row-first appended family has finite connected channels. -/
noncomputable instance rectangularRowAppendChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype ((rectangularLatticeRowHierarchy p).inner.append
      (rectangularLatticeRowHierarchy p).outer).Channel :=
  rectangularLatticeNetlistConnectedChannelFintype p

/-- The row-first appended family has finite external channels. -/
noncomputable instance rectangularRowAppendExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype ((rectangularLatticeRowHierarchy p).inner.append
      (rectangularLatticeRowHierarchy p).outer).ExternalChannel :=
  rectangularLatticeNetlistExternalChannelFintype p

/-- The row-first appended family has finite external incident labels. -/
noncomputable instance rectangularRowAppendExternalIncidentFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Incident
        ((rectangularLatticeRowHierarchy p).inner.append
          (rectangularLatticeRowHierarchy p).outer).ExternalChannel) :=
  Incident.fintypeOf (rectangularRowAppendExternalChannelFintype p)

/-- The row-first appended family has finite external outgoing labels. -/
noncomputable instance rectangularRowAppendExternalOutgoingFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Outgoing
        ((rectangularLatticeRowHierarchy p).inner.append
          (rectangularLatticeRowHierarchy p).outer).ExternalChannel) :=
  Outgoing.fintypeOf (rectangularRowAppendExternalChannelFintype p)

/-- The column-first flattened ambient channel family is finite. -/
noncomputable instance rectangularColumnFlattenChannelFintype {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.Channel :=
  rectangularLatticeAggregateChannelFintype p

/-- The column-first flattened connected-channel family is finite. -/
noncomputable instance rectangularColumnFlattenConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.ConnectedChannel := by
  exact Fintype.ofEquiv _
    ((rectangularVerticalConnections p).appendChannelEquiv
      (rectangularHorizontalBoundaryConnections p)).symm

/-- The column-first flattened connection family has finite connected channels. -/
noncomputable instance rectangularColumnFlattenConnectionsChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.connections.Channel :=
  rectangularColumnFlattenConnectedChannelFintype p

/-- The column-first flattening has finitely many external channels. -/
noncomputable instance rectangularColumnFlattenExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.ExternalChannel := by
  classical
  infer_instance

/-- The column-first flattening has finitely many external incident labels. -/
noncomputable instance rectangularColumnFlattenExternalIncidentFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.ExternalIncident :=
  Incident.fintypeOf (rectangularColumnFlattenExternalChannelFintype p)

/-- The column-first flattening has finitely many external outgoing labels. -/
noncomputable instance rectangularColumnFlattenExternalOutgoingFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.ExternalOutgoing :=
  Outgoing.fintypeOf (rectangularColumnFlattenExternalChannelFintype p)

/-- The column-first flattened connection family has finite external channels. -/
noncomputable instance rectangularColumnFlattenConnectionsExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype (rectangularLatticeColumnHierarchy p).flatten.connections.ExternalChannel :=
  rectangularColumnFlattenExternalChannelFintype p

/-- The column-first flattened connection family has finite external incident labels. -/
noncomputable instance rectangularColumnFlattenConnectionsExternalIncidentFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Incident
        (rectangularLatticeColumnHierarchy p).flatten.connections.ExternalChannel) :=
  Incident.fintypeOf (rectangularColumnFlattenConnectionsExternalChannelFintype p)

/-- The column-first flattened connection family has finite external outgoing labels. -/
noncomputable instance rectangularColumnFlattenConnectionsExternalOutgoingFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Outgoing
        (rectangularLatticeColumnHierarchy p).flatten.connections.ExternalChannel) :=
  Outgoing.fintypeOf (rectangularColumnFlattenConnectionsExternalChannelFintype p)

/-- The column-first appended family has finite connected channels. -/
noncomputable instance rectangularColumnAppendChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype ((rectangularLatticeColumnHierarchy p).inner.append
      (rectangularLatticeColumnHierarchy p).outer).Channel :=
  rectangularColumnFlattenConnectedChannelFintype p

/-- The column-first appended family has finite external channels. -/
noncomputable instance rectangularColumnAppendExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype ((rectangularLatticeColumnHierarchy p).inner.append
      (rectangularLatticeColumnHierarchy p).outer).ExternalChannel :=
  rectangularColumnFlattenExternalChannelFintype p

/-- The column-first appended family has finite external incident labels. -/
noncomputable instance rectangularColumnAppendExternalIncidentFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Incident
        ((rectangularLatticeColumnHierarchy p).inner.append
          (rectangularLatticeColumnHierarchy p).outer).ExternalChannel) :=
  Incident.fintypeOf (rectangularColumnAppendExternalChannelFintype p)

/-- The column-first appended family has finite external outgoing labels. -/
noncomputable instance rectangularColumnAppendExternalOutgoingFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      (Outgoing
        ((rectangularLatticeColumnHierarchy p).inner.append
          (rectangularLatticeColumnHierarchy p).outer).ExternalChannel) :=
  Outgoing.fintypeOf (rectangularColumnAppendExternalChannelFintype p)

/-- The canonical netlist with column-first wiring has the column flatten's ambient channels. -/
noncomputable instance rectangularColumnWithConnectionsChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      ((rectangularLatticeNetlist p).withConnections
        ((rectangularLatticeColumnHierarchy p).inner.append
          (rectangularLatticeColumnHierarchy p).outer)).Channel :=
  rectangularColumnFlattenChannelFintype p

/-- The canonical netlist with column-first wiring has finite connected channels. -/
noncomputable instance rectangularColumnWithConnectionsConnectedChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      ((rectangularLatticeNetlist p).withConnections
        ((rectangularLatticeColumnHierarchy p).inner.append
          (rectangularLatticeColumnHierarchy p).outer)).ConnectedChannel :=
  rectangularColumnFlattenConnectedChannelFintype p

/-- The canonical netlist with column-first wiring has finite external channels. -/
noncomputable instance rectangularColumnWithConnectionsExternalChannelFintype
    {rows columns : ℕ} (p : RectangularLatticeParameters rows columns) :
    Fintype
      ((rectangularLatticeNetlist p).withConnections
        ((rectangularLatticeColumnHierarchy p).inner.append
          (rectangularLatticeColumnHierarchy p).outer)).ExternalChannel :=
  rectangularColumnFlattenExternalChannelFintype p

/-!

## E. Row/column hierarchical flattening

-/

/-- Column-first flattening is row-first flattening with the two connection-label sums swapped. -/
lemma rectangularColumnFlatten_connections_eq_reindex {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (rectangularLatticeColumnHierarchy p).flatten.connections =
      (rectangularLatticeNetlist p).connections.reindex
        (Equiv.sumComm
          (RectangularHorizontalConnection rows columns)
          (RectangularVerticalConnection rows columns)) := by
  apply LatticeConnectionFamilies.family_eq_of_connection_eq
  funext index
  rcases index with vertical | horizontal
  · exact (LatticeConnectionFamilies.liftBoundary_onBoundary_connection
      (rectangularHorizontalConnections p) (rectangularVerticalConnections p)
      (rectangularConnections_endpointDisjoint p) vertical).symm
  · exact LatticeConnectionFamilies.liftBoundary_onBoundary_connection
      (rectangularVerticalConnections p) (rectangularHorizontalConnections p)
      (rectangularConnections_endpointDisjoint p).symm horizontal

/-- The two flattening orders are equivalent presentations of the same physical wiring. -/
def rectangularRowColumnWiringEquiv {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    PortConnectionFamily.WiringEquiv
      (rectangularLatticeNetlist p).connections
      (rectangularLatticeColumnHierarchy p).flatten.connections := by
  rw [rectangularColumnFlatten_connections_eq_reindex]
  exact PortConnectionFamily.WiringEquiv.ofReindex
    (rectangularLatticeNetlist p).connections
    (Equiv.sumComm
      (RectangularHorizontalConnection rows columns)
      (RectangularVerticalConnection rows columns))

/-- The row-first relational composition closes horizontal wiring before vertical wiring. -/
def rectangularRowDecompositionBehavior {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :=
  ((rectangularLatticeRowHierarchy p).outer.closeBehavior
    ((rectangularLatticeRowHierarchy p).inner.innerBoundaryBehavior
      (rectangularRowHierarchyComponentBehavior p))).reindex
    (Incident.relabelEquiv
      ((rectangularLatticeRowHierarchy p).inner.appendExternalChannelEquiv
        (rectangularLatticeRowHierarchy p).outer)).symm
    (Outgoing.relabelEquiv
      ((rectangularLatticeRowHierarchy p).inner.appendExternalChannelEquiv
        (rectangularLatticeRowHierarchy p).outer)).symm

/-- The canonical flat lattice has the row-first hierarchical relational semantics.

This Physlib-original S-08 result instantiates
`Physlib/Optics/Network/Hierarchical.lean:1015-1023,1053-1058`. It assumes no well-posedness or
matrix inverse.
-/
lemma rectangularLatticeBehavior_eq_rowDecomposition {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (rectangularLatticeNetlist p).behavior =
      rectangularRowDecompositionBehavior p := by
  change (rectangularLatticeRowHierarchy p).flatten.behavior = _
  rw [(rectangularLatticeRowHierarchy p).flatten.behavior_eq_closeBehavior]
  change (((rectangularLatticeRowHierarchy p).inner.append
    (rectangularLatticeRowHierarchy p).outer).closeBehavior
      (rectangularRowHierarchyComponentBehavior p)) = _
  unfold rectangularRowDecompositionBehavior
  ext ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff, Equiv.symm_symm, Equiv.symm_symm]
  exact (rectangularLatticeRowHierarchy p).inner.mem_closeBehavior_append_iff
    (rectangularLatticeRowHierarchy p).outer
    (rectangularRowHierarchyComponentBehavior p) input output

/-- The column-first relational composition closes vertical wiring before horizontal wiring. -/
def rectangularColumnDecompositionBehavior {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :=
  ((rectangularLatticeColumnHierarchy p).outer.closeBehavior
    ((rectangularLatticeColumnHierarchy p).inner.innerBoundaryBehavior
      (rectangularColumnHierarchyComponentBehavior p))).reindex
    (Incident.relabelEquiv
      ((rectangularLatticeColumnHierarchy p).inner.appendExternalChannelEquiv
        (rectangularLatticeColumnHierarchy p).outer)).symm
    (Outgoing.relabelEquiv
      ((rectangularLatticeColumnHierarchy p).inner.appendExternalChannelEquiv
        (rectangularLatticeColumnHierarchy p).outer)).symm

/-- Column-first flattening has the coupled-column hierarchical relational semantics.

This Physlib-original S-08 result is singular-safe and does not assert a coupled-lattice closed
form.
-/
lemma rectangularColumnFlattenBehavior_eq_columnDecomposition {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (rectangularLatticeColumnHierarchy p).flatten.behavior =
      rectangularColumnDecompositionBehavior p := by
  rw [(rectangularLatticeColumnHierarchy p).flatten.behavior_eq_closeBehavior]
  change (((rectangularLatticeColumnHierarchy p).inner.append
    (rectangularLatticeColumnHierarchy p).outer).closeBehavior
      (rectangularColumnHierarchyComponentBehavior p)) = _
  unfold rectangularColumnDecompositionBehavior
  ext ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff, Equiv.symm_symm, Equiv.symm_symm]
  exact (rectangularLatticeColumnHierarchy p).inner.mem_closeBehavior_append_iff
    (rectangularLatticeColumnHierarchy p).outer
    (rectangularColumnHierarchyComponentBehavior p) input output

/-- The canonical flat behavior transported to column-first external-channel coordinates. -/
def rectangularLatticeBehaviorInColumnCoordinates {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    LinearBehavior
      (rectangularLatticeColumnHierarchy p).flatten.ExternalIncident
      (rectangularLatticeColumnHierarchy p).flatten.ExternalOutgoing :=
  @LinearBehavior.reindex _ _ _ _
    (rectangularLatticeNetlistExternalIncidentFintype p)
    (rectangularColumnFlattenConnectionsExternalIncidentFintype p)
    (rectangularLatticeNetlistExternalOutgoingFintype p)
    (rectangularColumnFlattenConnectionsExternalOutgoingFintype p)
    (rectangularRowColumnWiringEquiv p).externalIncidentEquiv
    (rectangularRowColumnWiringEquiv p).externalOutgoingEquiv
    (rectangularLatticeNetlist p).behavior

/-- Column-first flattening is the canonical lattice behavior in canonically relabelled channels.

This is the wiring-order bridge used to compare the two S-08 decompositions.
-/
lemma rectangularColumnFlattenBehavior_eq_latticeBehavior_reindex {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (rectangularLatticeColumnHierarchy p).flatten.behavior =
      rectangularLatticeBehaviorInColumnCoordinates p := by
  change ((rectangularLatticeNetlist p).withConnections
    ((rectangularLatticeColumnHierarchy p).inner.append
      (rectangularLatticeColumnHierarchy p).outer)).behavior = _
  unfold rectangularLatticeBehaviorInColumnCoordinates
  exact FlatNetlist.behavior_withConnections
    (netlist := rectangularLatticeNetlist p)
    ((rectangularLatticeColumnHierarchy p).inner.append
      (rectangularLatticeColumnHierarchy p).outer)
    (rectangularRowColumnWiringEquiv p)

/-- The column-first composition transported back to canonical flat-lattice coordinates. -/
def rectangularColumnDecompositionInLatticeCoordinates {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    LinearBehavior (rectangularLatticeNetlist p).ExternalIncident
      (rectangularLatticeNetlist p).ExternalOutgoing :=
  @LinearBehavior.reindex _ _ _ _
    (rectangularColumnFlattenConnectionsExternalIncidentFintype p)
    (rectangularLatticeNetlistExternalIncidentFintype p)
    (rectangularColumnFlattenConnectionsExternalOutgoingFintype p)
    (rectangularLatticeNetlistExternalOutgoingFintype p)
    (rectangularRowColumnWiringEquiv p).externalIncidentEquiv.symm
    (rectangularRowColumnWiringEquiv p).externalOutgoingEquiv.symm
    (rectangularColumnDecompositionBehavior p)

/-- The canonical `M × N` behavior agrees with its coupled-column decomposition.

This is the column-first half of Physlib-original S-08. It follows from generic hierarchical
flattening and the proved connection-order wiring equivalence, without a well-posedness gate.
-/
lemma rectangularLatticeBehavior_eq_columnDecomposition {rows columns : ℕ}
    (p : RectangularLatticeParameters rows columns) :
    (rectangularLatticeNetlist p).behavior =
      rectangularColumnDecompositionInLatticeCoordinates p := by
  have hForward : rectangularLatticeBehaviorInColumnCoordinates p =
      rectangularColumnDecompositionBehavior p :=
    (rectangularColumnFlattenBehavior_eq_latticeBehavior_reindex p).symm.trans
      (rectangularColumnFlattenBehavior_eq_columnDecomposition p)
  have hBackward := congrArg
    (fun behavior => @LinearBehavior.reindex _ _ _ _
      (rectangularColumnFlattenConnectionsExternalIncidentFintype p)
      (rectangularLatticeNetlistExternalIncidentFintype p)
      (rectangularColumnFlattenConnectionsExternalOutgoingFintype p)
      (rectangularLatticeNetlistExternalOutgoingFintype p)
      (rectangularRowColumnWiringEquiv p).externalIncidentEquiv.symm
      (rectangularRowColumnWiringEquiv p).externalOutgoingEquiv.symm behavior)
    hForward
  have hRoundtrip := @LinearBehavior.reindex_symm_reindex
    (rectangularLatticeNetlist p).ExternalIncident
    (rectangularLatticeNetlist p).ExternalOutgoing
    (rectangularLatticeColumnHierarchy p).flatten.ExternalIncident
    (rectangularLatticeColumnHierarchy p).flatten.ExternalOutgoing
    (rectangularLatticeNetlistExternalIncidentFintype p)
    (rectangularLatticeNetlistExternalOutgoingFintype p)
    (rectangularColumnFlattenConnectionsExternalIncidentFintype p)
    (rectangularColumnFlattenConnectionsExternalOutgoingFintype p)
    (rectangularRowColumnWiringEquiv p).externalIncidentEquiv
    (rectangularRowColumnWiringEquiv p).externalOutgoingEquiv
    (rectangularLatticeNetlist p).behavior
  unfold rectangularLatticeBehaviorInColumnCoordinates at hBackward
  exact hRoundtrip.symm.trans hBackward

end MicroringCascade

end

end Optics
