/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.NetworkPoleCriterion

/-!
# Regression tests for one-delay network pole visibility

## i. Overview

This file builds a one-component, three-port rational netlist with a single internal connection.
Its coefficients use the exact `3/5` through and `-4*I/5` cross amplitudes, together with the
formal propagation entry `q/2`. Direct finite-matrix expansion gives the retained response

`(3/5 - q/2) / (1 - 3*q/10)`.

At `q = 10/3`, the cleared determinant vanishes while the retained numerator is `-16/15`. The
regression expands the polynomial matrices, the reduced quotient, and a nonzero kernel vector of
the raw compiled N5 feedback operator separately. It does not use the network pole-identification
lemmas that it exercises.

## ii. Key results

- `visiblePole_responseNumerator`: the selected retained numerator is `3/5 - q/2`.
- `visiblePole_responseDenominator`: the cleared determinant is `1 - 3*q/10`.
- `visiblePole_actualPole`: `q = 10/3` is a reduced denominator root.
- `visiblePole_not_mem_solveDomain`: the raw N5 feedback matrix is singular there.
- `visiblePole_independent_anchor`: the independently expanded pole and N5 facts agree.

## iii. Table of contents

- A. Three-port rational fixture
- B. Typed finite coordinates
- C. Cleared matrix expansion
- D. Independent visible-pole anchor

## iv. References

This is a formal-delay algebra regression, not a physical resonator model. The coefficient pattern
is chosen to expose a noncancelled root and to make a wrong feedback sign fail at the exact value
`q = 10/3`. No physical-frequency, resonance, causality, stability, passivity, reciprocity,
bandwidth, material, reachability, or observability claim is made.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Matrix Polynomial

/-!

## A. Three-port rational fixture

-/

/-- The external port and the two ports joined by the fixture's feedback connection. -/
inductive VisiblePolePort
  | external
  | left
  | right
  deriving DecidableEq

/-- The three fixture ports form a finite type. -/
instance visiblePolePortFintype : Fintype VisiblePolePort where
  elems := {.external, .left, .right}
  complete := by
    intro port
    cases port <;> simp

/-- Every fixture port carries one scalar mode. -/
def visiblePolePortFamily : PortModeFamily where
  Port := VisiblePolePort
  Mode := fun _ => Unit

/-- The formal single-delay polynomial used by the propagation entry. -/
def visiblePolePropagationPolynomial : DelayPolynomial 1 :=
  MvPolynomial.C (1 / 2) * MvPolynomial.X 0

/-- The sparse three-port scattering polynomial of the fixture. -/
def visiblePoleEntryPolynomial :
    visiblePolePortFamily.Channel → visiblePolePortFamily.Channel → DelayPolynomial 1
  | ⟨.external, ()⟩, ⟨.external, ()⟩ => MvPolynomial.C (3 / 5)
  | ⟨.external, ()⟩, ⟨.left, ()⟩ => MvPolynomial.C (-4 / 5 * Complex.I)
  | ⟨.left, ()⟩, ⟨.external, ()⟩ => MvPolynomial.C (-4 / 5 * Complex.I)
  | ⟨.left, ()⟩, ⟨.left, ()⟩ => MvPolynomial.C (3 / 5)
  | ⟨.right, ()⟩, ⟨.right, ()⟩ => visiblePolePropagationPolynomial
  | _, _ => 0

/-- The singleton rational component carrying the sparse three-port law. -/
def visiblePoleComponents : RationalComponentFamily 1 where
  Component := Unit
  portFamily := fun _ => visiblePolePortFamily
  entryModel := fun _ output input =>
    RationalModel.ofPolynomial (visiblePoleEntryPolynomial output input)
  ModelValidAt := fun _ value => ‖value 0‖ ≤ 4

/-- The component-family aggregate channel at one selected fixture port. -/
def visiblePoleAggregateChannel (port : VisiblePolePort) :
    visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily.Channel :=
  ⟨⟨(), port⟩, ()⟩

/-- The aggregate left feedback port. -/
def visiblePoleLeftPort :
    visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily.Port :=
  ⟨(), .left⟩

/-- The aggregate right feedback port. -/
def visiblePoleRightPort :
    visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily.Port :=
  ⟨(), .right⟩

/-- The single internal connection joins the left and right feedback ports. -/
def visiblePoleConnection : PortConnection
    visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily where
  left := visiblePoleLeftPort
  right := visiblePoleRightPort
  left_ne_right := by
    intro hEqual
    exact VisiblePolePort.noConfusion (congrArg (fun port => port.2) hEqual)
  modeEquiv := Equiv.refl Unit

/-- The proof-carrying singleton connection family. -/
def visiblePoleConnections : PortConnectionFamily
    visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily Unit where
  connection := fun _ => visiblePoleConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact VisiblePolePort.noConfusion (congrArg (fun port => port.2) hPort)
    · exact VisiblePolePort.noConfusion (congrArg (fun port => port.2) hPort)
    · rfl

/-- The one-component rational netlist with one feedback connection. -/
def visiblePoleNetlist : RationalNetlist 1 where
  components := visiblePoleComponents
  Connection := Unit
  connections := visiblePoleConnections

/-- The unique component in the assembled rational fixture. -/
def visiblePoleComponent : visiblePoleNetlist.components.Component := by
  change Unit
  exact ()

/-- One local channel of the fixture's unique component. -/
def visiblePoleLocalChannel (port : VisiblePolePort) :
    (visiblePoleNetlist.components.portFamily visiblePoleComponent).Channel := by
  change visiblePolePortFamily.Channel
  exact ⟨port, ()⟩

/-- The aggregate channel at one selected fixture port. -/
def visiblePoleChannel (port : VisiblePolePort) : visiblePoleNetlist.Channel :=
  ⟨⟨(), port⟩, ()⟩

@[simp]
lemma visiblePoleComponent_channel (port : VisiblePolePort) :
    visiblePoleNetlist.components.indexedChannelEquiv
        ⟨visiblePoleComponent, visiblePoleLocalChannel port⟩ =
      visiblePoleChannel port := by
  rfl

/-- The externally exposed aggregate channel. -/
def visiblePoleExternalChannel : visiblePoleNetlist.ExternalChannel :=
  ⟨visiblePoleChannel .external, by
    rintro ⟨⟨connection, localChannel⟩, hChannel⟩
    cases connection
    rcases localChannel with mode | mode <;> cases mode
    · exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hChannel)
    · exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hChannel)⟩

/-- The external aggregate channel is outside the connected-channel embedding. -/
lemma visiblePoleAggregateExternal_not_mem_range :
    visiblePoleAggregateChannel .external ∉
      Set.range visiblePoleConnections.channelEmbedding := by
  rintro ⟨⟨connection, localChannel⟩, hChannel⟩
  cases connection
  rcases localChannel with mode | mode <;> cases mode
  · exact VisiblePolePort.noConfusion
      (congrArg (fun channel => channel.1.2) hChannel)
  · exact VisiblePolePort.noConfusion
      (congrArg (fun channel => channel.1.2) hChannel)

/-!

## B. Typed finite coordinates

-/

/-- Aggregate channels of the three-port fixture are finite. -/
noncomputable instance visiblePoleChannelFintype : Fintype visiblePoleNetlist.Channel := by
  change Fintype (Σ _ : (Σ _ : Unit, VisiblePolePort), Unit)
  infer_instance

/-- Connected channels of the singleton connection are finite. -/
noncomputable instance visiblePoleConnectedChannelFintype :
    Fintype visiblePoleNetlist.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- The connection-family spelling of connected fixture channels is finite. -/
noncomputable instance visiblePoleConnectionChannelFintype :
    Fintype visiblePoleConnections.Channel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Classical equality on aggregate fixture channels. -/
noncomputable instance visiblePoleChannelDecidableEq :
    DecidableEq visiblePoleNetlist.Channel := Classical.decEq _

/-- Classical equality in the component-family spelling of aggregate channels. -/
noncomputable instance visiblePoleAggregateChannelDecidableEq :
    DecidableEq
      visiblePoleComponents.toParameterizedComponentFamily.aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-- Classical equality on connected fixture channels. -/
noncomputable instance visiblePoleConnectedChannelDecidableEq :
    DecidableEq visiblePoleNetlist.ConnectedChannel := Classical.decEq _

/-- Classical equality in the connection-family spelling of connected channels. -/
noncomputable instance visiblePoleConnectionChannelDecidableEq :
    DecidableEq visiblePoleConnections.Channel := Classical.decEq _

/-- The explicit ordering `external`, `left`, `right` of aggregate fixture channels. -/
def visiblePoleChannelEquiv : visiblePoleNetlist.Channel ≃ Fin 3 where
  toFun
    | ⟨⟨(), .external⟩, ()⟩ => 0
    | ⟨⟨(), .left⟩, ()⟩ => 1
    | ⟨⟨(), .right⟩, ()⟩ => 2
  invFun := Fin.cases (visiblePoleChannel .external)
    (Fin.cases (visiblePoleChannel .left) fun _ => visiblePoleChannel .right)
  left_inv := by
    rintro ⟨⟨component, port⟩, mode⟩
    cases component
    cases port <;> cases mode <;> rfl
  right_inv := by
    intro index
    fin_cases index <;> rfl

/-- The corresponding ordering of incident endpoints. -/
def visiblePoleIncidentEquiv : visiblePoleNetlist.IncidentIndex ≃ Fin 3 :=
  (Incident.relabelEquiv visiblePoleChannelEquiv).trans Incident.channelEquiv

/-- The corresponding ordering of outgoing endpoints. -/
def visiblePoleOutgoingEquiv : visiblePoleNetlist.OutgoingIndex ≃ Fin 3 :=
  (Outgoing.relabelEquiv visiblePoleChannelEquiv).trans Outgoing.channelEquiv

@[simp]
lemma visiblePoleIncidentEquiv_symm_zero :
    visiblePoleIncidentEquiv.symm 0 = Incident.mk (visiblePoleChannel .external) := rfl

@[simp]
lemma visiblePoleIncidentEquiv_symm_one :
    visiblePoleIncidentEquiv.symm 1 = Incident.mk (visiblePoleChannel .left) := rfl

@[simp]
lemma visiblePoleIncidentEquiv_symm_two :
    visiblePoleIncidentEquiv.symm 2 = Incident.mk (visiblePoleChannel .right) := rfl

@[simp]
lemma visiblePoleOutgoingEquiv_symm_zero :
    visiblePoleOutgoingEquiv.symm 0 = Outgoing.mk (visiblePoleChannel .external) := rfl

@[simp]
lemma visiblePoleOutgoingEquiv_symm_one :
    visiblePoleOutgoingEquiv.symm 1 = Outgoing.mk (visiblePoleChannel .left) := rfl

@[simp]
lemma visiblePoleOutgoingEquiv_symm_two :
    visiblePoleOutgoingEquiv.symm 2 = Outgoing.mk (visiblePoleChannel .right) := rfl

/-- The left endpoint of the internal connection. -/
def visiblePoleConnectedLeft : visiblePoleNetlist.ConnectedChannel :=
  ⟨(), Sum.inl ()⟩

/-- The right endpoint of the internal connection. -/
def visiblePoleConnectedRight : visiblePoleNetlist.ConnectedChannel :=
  ⟨(), Sum.inr ()⟩

@[simp]
lemma visiblePoleConnectedLeft_embedding :
    visiblePoleConnections.channelEmbedding visiblePoleConnectedLeft =
      visiblePoleAggregateChannel .left := rfl

@[simp]
lemma visiblePoleConnectedRight_embedding :
    visiblePoleConnections.channelEmbedding visiblePoleConnectedRight =
      visiblePoleAggregateChannel .right := rfl

@[simp]
lemma visiblePoleConnectedLeft_mate :
    visiblePoleConnections.mateEquiv visiblePoleConnectedLeft =
      visiblePoleConnectedRight := rfl

@[simp]
lemma visiblePoleConnectedRight_mate :
    visiblePoleConnections.mateEquiv visiblePoleConnectedRight =
      visiblePoleConnectedLeft := rfl

/-- The externally exposed aggregate channel is unique. -/
instance visiblePoleExternalChannelUnique : Unique visiblePoleNetlist.ExternalChannel where
  default := visiblePoleExternalChannel
  uniq := by
    rintro ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
    cases component
    cases mode
    cases port
    · rfl
    · exact (hExternal ⟨visiblePoleConnectedLeft, rfl⟩).elim
    · exact (hExternal ⟨visiblePoleConnectedRight, rfl⟩).elim

/-- The external incident endpoint is unique. -/
instance visiblePoleExternalIncidentUnique : Unique visiblePoleNetlist.ExternalIncident where
  default := Incident.mk visiblePoleExternalChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Incident.mk (Subsingleton.elim channel visiblePoleExternalChannel)

/-- The external outgoing endpoint is unique. -/
instance visiblePoleExternalOutgoingUnique : Unique visiblePoleNetlist.ExternalOutgoing where
  default := Outgoing.mk visiblePoleExternalChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Outgoing.mk (Subsingleton.elim channel visiblePoleExternalChannel)

/-- External incident endpoints are displayed in a singleton coordinate. -/
def visiblePoleExternalIncidentEquiv : visiblePoleNetlist.ExternalIncident ≃ Unit :=
  Equiv.ofUnique _ _

/-- External outgoing endpoints are displayed in a singleton coordinate. -/
def visiblePoleExternalOutgoingEquiv : visiblePoleNetlist.ExternalOutgoing ≃ Unit :=
  Equiv.ofUnique _ _

/-!

## C. Cleared matrix expansion

-/

/-- The assembled entry model is the stored polynomial entry. -/
lemma visiblePole_scatteringEntryModel (output input : VisiblePolePort) :
    visiblePoleNetlist.scatteringEntryModel
        (visiblePoleChannel output) (visiblePoleChannel input) =
      RationalModel.ofPolynomial
        (visiblePoleEntryPolynomial ⟨output, ()⟩ ⟨input, ()⟩) := by
  rw [← visiblePoleComponent_channel output, ← visiblePoleComponent_channel input,
    visiblePoleNetlist.scatteringEntryModel_same]
  rfl

/-- Every assembled fixture entry has unit retained denominator. -/
lemma visiblePole_scatteringEntryModel_denominator
    (output input : visiblePoleNetlist.Channel) :
    (visiblePoleNetlist.scatteringEntryModel output input).denominator = 1 := by
  obtain ⟨⟨outputComponent, outputChannel⟩, rfl⟩ :=
    visiblePoleNetlist.components.indexedChannelEquiv.surjective output
  obtain ⟨⟨inputComponent, inputChannel⟩, rfl⟩ :=
    visiblePoleNetlist.components.indexedChannelEquiv.surjective input
  cases outputComponent
  cases inputComponent
  rcases outputChannel with ⟨outputPort, outputMode⟩
  rcases inputChannel with ⟨inputPort, inputMode⟩
  cases outputMode
  cases inputMode
  change VisiblePolePort at outputPort inputPort
  change (visiblePoleNetlist.scatteringEntryModel
    (visiblePoleChannel outputPort) (visiblePoleChannel inputPort)).denominator = 1
  rw [visiblePole_scatteringEntryModel]
  rfl

/-- Every stored denominator is one, so the aggregate common denominator is one. -/
lemma visiblePole_commonDenominator : visiblePoleNetlist.commonDenominator = 1 := by
  classical
  rw [RationalNetlist.commonDenominator]
  apply Finset.prod_eq_one
  rintro ⟨output, input⟩ _
  exact visiblePole_scatteringEntryModel_denominator output input

/-- Removing any selected entry still leaves a product of unit denominators. -/
lemma visiblePole_denominatorComplement (output input : visiblePoleNetlist.Channel) :
    visiblePoleNetlist.denominatorComplement output input = 1 := by
  classical
  rw [RationalNetlist.denominatorComplement]
  apply Finset.prod_eq_one
  rintro ⟨otherOutput, otherInput⟩ _
  exact visiblePole_scatteringEntryModel_denominator otherOutput otherInput

/-- Clearing denominators leaves each stored polynomial entry unchanged. -/
lemma visiblePole_clearedScattering_entry (output input : VisiblePolePort) :
    visiblePoleNetlist.clearedScattering
        (Outgoing.mk (visiblePoleChannel output))
        (Incident.mk (visiblePoleChannel input)) =
      visiblePoleEntryPolynomial ⟨output, ()⟩ ⟨input, ()⟩ := by
  rw [RationalNetlist.clearedScattering]
  change
    (visiblePoleNetlist.scatteringEntryModel
      (visiblePoleChannel output) (visiblePoleChannel input)).numerator * _ = _
  rw [visiblePole_scatteringEntryModel, visiblePole_denominatorComplement]
  simp [RationalModel.ofPolynomial]

/-- The displayed cleared scattering matrix in external-left-right order. -/
def visiblePoleClearedScatteringMatrix : Matrix (Fin 3) (Fin 3) (DelayPolynomial 1) :=
  !![MvPolynomial.C (3 / 5), MvPolynomial.C (-4 / 5 * Complex.I), 0;
     MvPolynomial.C (-4 / 5 * Complex.I), MvPolynomial.C (3 / 5), 0;
     0, 0, visiblePolePropagationPolynomial]

/-- The displayed ideal routing matrix: external rows and columns vanish, while the internal
connection swaps left and right. -/
def visiblePolePolynomialRoutingMatrix : Matrix (Fin 3) (Fin 3) (DelayPolynomial 1) :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- The directly multiplied cleared feedback matrix `1 - C*S_clear`. -/
def visiblePoleClearedFeedbackMatrix : Matrix (Fin 3) (Fin 3) (DelayPolynomial 1) :=
  !![1, 0, 0;
     0, 1, -(MvPolynomial.C (1 / 2) * MvPolynomial.X 0);
     MvPolynomial.C (4 / 5 * Complex.I), MvPolynomial.C (-3 / 5), 1]

/-- The displayed injection of the singleton external incident coordinate. -/
def visiblePolePolynomialInputExposureMatrix :
    Matrix (Fin 3) Unit (DelayPolynomial 1) :=
  fun incident _ => if incident = 0 then 1 else 0

/-- The displayed readout of the singleton external outgoing coordinate. -/
def visiblePolePolynomialOutputReadoutMatrix :
    Matrix Unit (Fin 3) (DelayPolynomial 1) :=
  fun _ outgoing => if outgoing = 0 then 1 else 0

/-- The exact selected external response numerator `3/5 - q/2`. -/
def visiblePoleNumeratorPolynomial : Polynomial ℂ :=
  Polynomial.C (3 / 5) - Polynomial.C (1 / 2) * Polynomial.X

/-- The exact cleared determinant `1 - 3*q/10`. -/
def visiblePoleDenominatorPolynomial : Polynomial ℂ :=
  1 - Polynomial.C (3 / 10) * Polynomial.X

/-- Reindexing the cleared scattering law exposes the displayed sparse polynomial matrix. -/
lemma visiblePole_clearedScattering_reindex :
    Matrix.reindex visiblePoleOutgoingEquiv visiblePoleIncidentEquiv
        visiblePoleNetlist.clearedScattering =
      visiblePoleClearedScatteringMatrix := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [Matrix.reindex_apply, visiblePoleClearedScatteringMatrix,
      visiblePole_clearedScattering_entry, visiblePoleEntryPolynomial]

@[simp]
lemma visiblePole_polynomialRouting_external_row (outgoing : VisiblePolePort) :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel .external))
        (Outgoing.mk (visiblePoleChannel outgoing)) = 0 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel .external))
    (Outgoing.mk (visiblePoleAggregateChannel outgoing))) = 0
  rw [visiblePoleConnections.partialRouting_entry_of_incident_not_mem_range
    (visiblePoleAggregateChannel .external) visiblePoleAggregateExternal_not_mem_range]
  simp

@[simp]
lemma visiblePole_polynomialRouting_external_column (incident : VisiblePolePort) :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel incident))
        (Outgoing.mk (visiblePoleChannel .external)) = 0 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel incident))
    (Outgoing.mk (visiblePoleAggregateChannel .external))) = 0
  rw [visiblePoleConnections.partialRouting_entry_of_outgoing_not_mem_range
    (visiblePoleAggregateChannel .external) visiblePoleAggregateExternal_not_mem_range]
  simp

@[simp]
lemma visiblePole_polynomialRouting_left_left :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel .left))
        (Outgoing.mk (visiblePoleChannel .left)) = 0 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel .left))
    (Outgoing.mk (visiblePoleConnections.channelEmbedding visiblePoleConnectedLeft))) = 0
  have hNe : visiblePoleAggregateChannel .left ≠ visiblePoleAggregateChannel .right := by
    intro hEqual
    exact VisiblePolePort.noConfusion (congrArg (fun channel => channel.1.2) hEqual)
  have hRouting := visiblePoleConnections.partialRouting_entry_connected_column
    (visiblePoleAggregateChannel .left) visiblePoleConnectedLeft
  simp only [visiblePoleConnectedLeft_mate,
    visiblePoleConnectedRight_embedding] at hRouting
  have hZero := hRouting.trans (if_neg hNe)
  have hZero' : visiblePoleConnections.partialRouting
      (Incident.mk (visiblePoleAggregateChannel .left))
      (Outgoing.mk (visiblePoleAggregateChannel .left)) = 0 := by
    simpa only [visiblePoleConnectedLeft_embedding] using hZero
  simpa using congrArg (MvPolynomial.C : ℂ → DelayPolynomial 1) hZero'

@[simp]
lemma visiblePole_polynomialRouting_left_right :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel .left))
        (Outgoing.mk (visiblePoleChannel .right)) = 1 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel .left))
    (Outgoing.mk (visiblePoleConnections.channelEmbedding visiblePoleConnectedRight))) = 1
  simpa using congrArg MvPolynomial.C
    (visiblePoleConnections.partialRouting_entry_mate visiblePoleConnectedRight)

@[simp]
lemma visiblePole_polynomialRouting_right_left :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel .right))
        (Outgoing.mk (visiblePoleChannel .left)) = 1 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel .right))
    (Outgoing.mk (visiblePoleConnections.channelEmbedding visiblePoleConnectedLeft))) = 1
  simpa using congrArg MvPolynomial.C
    (visiblePoleConnections.partialRouting_entry_mate visiblePoleConnectedLeft)

@[simp]
lemma visiblePole_polynomialRouting_right_right :
    visiblePoleNetlist.polynomialRouting
        (Incident.mk (visiblePoleChannel .right))
        (Outgoing.mk (visiblePoleChannel .right)) = 0 := by
  change MvPolynomial.C (visiblePoleConnections.partialRouting
    (Incident.mk (visiblePoleAggregateChannel .right))
    (Outgoing.mk (visiblePoleConnections.channelEmbedding visiblePoleConnectedRight))) = 0
  have hNe : visiblePoleAggregateChannel .right ≠ visiblePoleAggregateChannel .left := by
    intro hEqual
    exact VisiblePolePort.noConfusion (congrArg (fun channel => channel.1.2) hEqual)
  have hRouting := visiblePoleConnections.partialRouting_entry_connected_column
    (visiblePoleAggregateChannel .right) visiblePoleConnectedRight
  simp only [visiblePoleConnectedRight_mate,
    visiblePoleConnectedLeft_embedding] at hRouting
  have hZero := hRouting.trans (if_neg hNe)
  have hZero' : visiblePoleConnections.partialRouting
      (Incident.mk (visiblePoleAggregateChannel .right))
      (Outgoing.mk (visiblePoleAggregateChannel .right)) = 0 := by
    simpa only [visiblePoleConnectedRight_embedding] using hZero
  simpa using congrArg (MvPolynomial.C : ℂ → DelayPolynomial 1) hZero'

/-- Reindexing ideal routing exposes the displayed internal left-right swap. -/
lemma visiblePole_polynomialRouting_reindex :
    Matrix.reindex visiblePoleIncidentEquiv visiblePoleOutgoingEquiv
        visiblePoleNetlist.polynomialRouting =
      visiblePolePolynomialRoutingMatrix := by
  ext incident outgoing
  fin_cases incident <;> fin_cases outgoing <;>
    simp [Matrix.reindex_apply, visiblePolePolynomialRoutingMatrix]

/-- Reindexing the cleared feedback law exposes `1 - C*S_clear` in displayed coordinates. -/
lemma visiblePole_clearedFeedback_reindex :
    Matrix.reindex visiblePoleIncidentEquiv visiblePoleIncidentEquiv
        visiblePoleNetlist.clearedFeedback =
      visiblePoleClearedFeedbackMatrix := by
  rw [RationalNetlist.clearedFeedback, visiblePole_commonDenominator]
  simp only [one_smul]
  change (Matrix.reindexLinearEquiv (DelayPolynomial 1) (DelayPolynomial 1)
    visiblePoleIncidentEquiv visiblePoleIncidentEquiv)
      (1 - visiblePoleNetlist.polynomialRouting *
        visiblePoleNetlist.clearedScattering) = _
  rw [map_sub, Matrix.reindexLinearEquiv_one,
    ← Matrix.reindexLinearEquiv_mul (DelayPolynomial 1) (DelayPolynomial 1)
      visiblePoleIncidentEquiv visiblePoleOutgoingEquiv visiblePoleIncidentEquiv]
  change 1 - Matrix.reindex visiblePoleIncidentEquiv visiblePoleOutgoingEquiv
      visiblePoleNetlist.polynomialRouting *
    Matrix.reindex visiblePoleOutgoingEquiv visiblePoleIncidentEquiv
      visiblePoleNetlist.clearedScattering = _
  rw [visiblePole_polynomialRouting_reindex, visiblePole_clearedScattering_reindex]
  ext incident input
  fin_cases incident <;> fin_cases input <;>
    simp [Matrix.sub_apply, visiblePolePolynomialRoutingMatrix,
      visiblePoleClearedScatteringMatrix, visiblePoleClearedFeedbackMatrix,
      visiblePolePropagationPolynomial]
  all_goals split <;> ring

/-- Reindexing the external incident injection selects the displayed external coordinate. -/
lemma visiblePole_polynomialInputExposure_reindex :
    Matrix.reindex visiblePoleIncidentEquiv visiblePoleExternalIncidentEquiv
        visiblePoleNetlist.polynomialInputExposure =
      visiblePolePolynomialInputExposureMatrix := by
  apply Matrix.ext
  intro incident external
  cases external
  fin_cases incident
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalIncidentInjection
      (Incident.mk (visiblePoleChannel .external))
      (Incident.mk visiblePoleExternalChannel)) = 1
    have hEmbedding :
        visiblePoleNetlist.toParameterizedNetlist.connections.externalIncidentEmbedding
            (Incident.mk visiblePoleExternalChannel) =
          Incident.mk (visiblePoleChannel .external) := by
      rw [PortConnectionFamily.externalIncidentEmbedding_apply]
      rfl
    rw [PortConnectionFamily.externalIncidentInjection,
      ModeTransform.zeroExtension_entry, if_pos hEmbedding]
    simp
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalIncidentInjection
      (Incident.mk (visiblePoleChannel .left))
      (Incident.mk visiblePoleExternalChannel)) = 0
    rw [PortConnectionFamily.externalIncidentInjection_entry_of_ne]
    · simp
    · intro hEqual
      exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hEqual)
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalIncidentInjection
      (Incident.mk (visiblePoleChannel .right))
      (Incident.mk visiblePoleExternalChannel)) = 0
    rw [PortConnectionFamily.externalIncidentInjection_entry_of_ne]
    · simp
    · intro hEqual
      exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hEqual)

/-- Reindexing the external outgoing readout selects the displayed external coordinate. -/
lemma visiblePole_polynomialOutputReadout_reindex :
    Matrix.reindex visiblePoleExternalOutgoingEquiv visiblePoleOutgoingEquiv
        visiblePoleNetlist.polynomialOutputReadout =
      visiblePolePolynomialOutputReadoutMatrix := by
  apply Matrix.ext
  intro external outgoing
  cases external
  fin_cases outgoing
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalOutgoingReadout
      (Outgoing.mk visiblePoleExternalChannel)
      (Outgoing.mk (visiblePoleChannel .external))) = 1
    have hEmbedding :
        visiblePoleNetlist.toParameterizedNetlist.connections.externalOutgoingEmbedding
            (Outgoing.mk visiblePoleExternalChannel) =
          Outgoing.mk (visiblePoleChannel .external) := by
      rw [PortConnectionFamily.externalOutgoingEmbedding_apply]
      rfl
    rw [PortConnectionFamily.externalOutgoingReadout,
      ModeTransform.restriction_entry, if_pos hEmbedding]
    simp
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalOutgoingReadout
      (Outgoing.mk visiblePoleExternalChannel)
      (Outgoing.mk (visiblePoleChannel .left))) = 0
    rw [PortConnectionFamily.externalOutgoingReadout_entry_of_ne]
    · simp
    · intro hEqual
      exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hEqual)
  · change MvPolynomial.C
      (visiblePoleNetlist.toParameterizedNetlist.connections.externalOutgoingReadout
      (Outgoing.mk visiblePoleExternalChannel)
      (Outgoing.mk (visiblePoleChannel .right))) = 0
    rw [PortConnectionFamily.externalOutgoingReadout_entry_of_ne]
    · simp
    · intro hEqual
      exact VisiblePolePort.noConfusion
        (congrArg (fun channel => channel.1.2) hEqual)

/-- Reindexing the four retained-numerator factors exposes the selected scalar polynomial. -/
lemma visiblePole_responseNumerator_reindex :
    Matrix.reindex visiblePoleExternalOutgoingEquiv visiblePoleExternalIncidentEquiv
        visiblePoleNetlist.responseNumerator =
      (fun _ _ => MvPolynomial.C (3 / 5) -
        MvPolynomial.C (1 / 2) * MvPolynomial.X 0 :
        Matrix Unit Unit (DelayPolynomial 1)) := by
  rw [RationalNetlist.responseNumerator]
  change (Matrix.reindexLinearEquiv (DelayPolynomial 1) (DelayPolynomial 1)
    visiblePoleExternalOutgoingEquiv visiblePoleExternalIncidentEquiv)
      (((visiblePoleNetlist.polynomialOutputReadout *
        visiblePoleNetlist.clearedScattering) *
        visiblePoleNetlist.clearedFeedback.adjugate) *
        visiblePoleNetlist.polynomialInputExposure) = _
  rw [← Matrix.reindexLinearEquiv_mul (DelayPolynomial 1) (DelayPolynomial 1)
      visiblePoleExternalOutgoingEquiv visiblePoleIncidentEquiv
      visiblePoleExternalIncidentEquiv,
    ← Matrix.reindexLinearEquiv_mul (DelayPolynomial 1) (DelayPolynomial 1)
      visiblePoleExternalOutgoingEquiv visiblePoleIncidentEquiv visiblePoleIncidentEquiv,
    ← Matrix.reindexLinearEquiv_mul (DelayPolynomial 1) (DelayPolynomial 1)
      visiblePoleExternalOutgoingEquiv visiblePoleOutgoingEquiv visiblePoleIncidentEquiv]
  change
    Matrix.reindex visiblePoleExternalOutgoingEquiv visiblePoleOutgoingEquiv
        visiblePoleNetlist.polynomialOutputReadout *
      Matrix.reindex visiblePoleOutgoingEquiv visiblePoleIncidentEquiv
        visiblePoleNetlist.clearedScattering *
      Matrix.reindex visiblePoleIncidentEquiv visiblePoleIncidentEquiv
        visiblePoleNetlist.clearedFeedback.adjugate *
      Matrix.reindex visiblePoleIncidentEquiv visiblePoleExternalIncidentEquiv
        visiblePoleNetlist.polynomialInputExposure = _
  rw [visiblePole_polynomialOutputReadout_reindex,
    visiblePole_clearedScattering_reindex,
    ← Matrix.adjugate_reindex,
    visiblePole_clearedFeedback_reindex,
    visiblePole_polynomialInputExposure_reindex]
  apply Matrix.ext
  intro output input
  cases output
  cases input
  have hI : (MvPolynomial.C Complex.I : DelayPolynomial 1) ^ 2 = -1 := by
    rw [sq, ← MvPolynomial.C_mul, Complex.I_mul_I]
    simp
  have hRatio :
      (MvPolynomial.C (3 / 5) * MvPolynomial.C (-3 / 5) +
        MvPolynomial.C (-4 / 5) * MvPolynomial.C (4 / 5) :
        DelayPolynomial 1) = -1 := by
    rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul,
      ← MvPolynomial.C_add]
    norm_num
  simp [Matrix.mul_apply, visiblePolePolynomialOutputReadoutMatrix,
    visiblePoleClearedScatteringMatrix, visiblePoleClearedFeedbackMatrix,
    visiblePolePolynomialInputExposureMatrix, Matrix.adjugate_fin_three_of,
    Fin.sum_univ_three]
  linear_combination
    (MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.X 0) * hRatio -
      (MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.X 0 *
        MvPolynomial.C (-4 / 5) * MvPolynomial.C (4 / 5)) * hI

/-- Direct four-factor expansion gives the retained one-delay response numerator. -/
lemma visiblePole_responseNumerator_mv :
    visiblePoleNetlist.responseNumerator
        (Outgoing.mk visiblePoleExternalChannel)
        (Incident.mk visiblePoleExternalChannel) =
      MvPolynomial.C (3 / 5) -
        MvPolynomial.C (1 / 2) * MvPolynomial.X 0 := by
  have hEntry := congrArg (fun matrix => matrix () ())
    visiblePole_responseNumerator_reindex
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Subsingleton.elim (visiblePoleExternalOutgoingEquiv.symm ())
      (Outgoing.mk visiblePoleExternalChannel),
    Subsingleton.elim (visiblePoleExternalIncidentEquiv.symm ())
      (Incident.mk visiblePoleExternalChannel)] using hEntry

/-- In the canonical one-delay coordinate, the retained numerator is `3/5 - q/2`. -/
lemma visiblePole_responseNumerator :
    oneDelayPolynomialEquiv
        (visiblePoleNetlist.responseNumerator
          (Outgoing.mk visiblePoleExternalChannel)
          (Incident.mk visiblePoleExternalChannel)) =
      visiblePoleNumeratorPolynomial := by
  rw [visiblePole_responseNumerator_mv]
  simp [oneDelayPolynomialEquiv, visiblePoleNumeratorPolynomial]

/-- Direct determinant expansion gives the cleared one-delay denominator. -/
lemma visiblePole_responseDenominator_mv :
    visiblePoleNetlist.responseDenominator =
      MvPolynomial.C 1 - MvPolynomial.C (3 / 10) * MvPolynomial.X 0 := by
  rw [RationalNetlist.responseDenominator,
    ← Matrix.det_reindex_self visiblePoleIncidentEquiv
      visiblePoleNetlist.clearedFeedback,
    visiblePole_clearedFeedback_reindex, Matrix.det_fin_three]
  simp [visiblePoleClearedFeedbackMatrix]
  have hCoefficient :
      (MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.X 0 *
        MvPolynomial.C (-3 / 5 : ℂ) :
        DelayPolynomial 1) =
        -(MvPolynomial.C (3 / 10 : ℂ) * MvPolynomial.X 0) := by
    calc
      (MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.X 0 *
          MvPolynomial.C (-3 / 5 : ℂ) : DelayPolynomial 1) =
          (MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.C (-3 / 5 : ℂ)) *
            MvPolynomial.X 0 := by ring
      _ = MvPolynomial.C ((2 : ℂ)⁻¹ * (-3 / 5)) * MvPolynomial.X 0 := by
        rw [MvPolynomial.C_mul]
      _ = MvPolynomial.C (-3 / 10 : ℂ) * MvPolynomial.X 0 := by norm_num
      _ = -(MvPolynomial.C (3 / 10 : ℂ) * MvPolynomial.X 0) := by
        norm_num
  rw [hCoefficient]
  ring

/-- In the canonical one-delay coordinate, the cleared denominator is `1 - 3*q/10`. -/
lemma visiblePole_responseDenominator :
    oneDelayPolynomialEquiv visiblePoleNetlist.responseDenominator =
      visiblePoleDenominatorPolynomial := by
  rw [visiblePole_responseDenominator_mv]
  simp [oneDelayPolynomialEquiv, visiblePoleDenominatorPolynomial]

/-!

## D. Independent visible-pole anchor

-/

/-- The retained numerator is a nonzero formal polynomial. -/
lemma visiblePoleNumeratorPolynomial_ne_zero : visiblePoleNumeratorPolynomial ≠ 0 := by
  intro hZero
  have hEval := congrArg (Polynomial.eval 0) hZero
  norm_num [visiblePoleNumeratorPolynomial] at hEval

/-- The retained denominator is a nonzero formal polynomial. -/
lemma visiblePoleDenominatorPolynomial_ne_zero : visiblePoleDenominatorPolynomial ≠ 0 := by
  intro hZero
  have hEval := congrArg (Polynomial.eval 0) hZero
  norm_num [visiblePoleDenominatorPolynomial] at hEval

/-- The visible fixture numerator and denominator are coprime by an explicit Bézout identity. -/
lemma visiblePolePolynomials_isCoprime :
    IsCoprime visiblePoleNumeratorPolynomial visiblePoleDenominatorPolynomial := by
  refine ⟨Polynomial.C (-15 / 16), Polynomial.C (25 / 16), ?_⟩
  ext degree
  rcases degree with _ | _ | degree
  · norm_num [visiblePoleNumeratorPolynomial, visiblePoleDenominatorPolynomial]
  · norm_num [visiblePoleNumeratorPolynomial, visiblePoleDenominatorPolynomial,
      Polynomial.coeff_one]
  · simp [visiblePoleNumeratorPolynomial, visiblePoleDenominatorPolynomial,
      Polynomial.coeff_one]

/-- The selected quotient is already reduced: its cancelled factor is one. -/
def visiblePoleReducedResponse : ReducedRationalResponse where
  numerator := visiblePoleNumeratorPolynomial
  denominator := visiblePoleDenominatorPolynomial
  numerator_ne_zero := visiblePoleNumeratorPolynomial_ne_zero
  denominator_ne_zero := visiblePoleDenominatorPolynomial_ne_zero
  isCoprime := visiblePolePolynomials_isCoprime

/-- The explicit unit-factor reduction of the selected raw network quotient. -/
def visiblePoleReduction : RationalReduction where
  rawNumerator := visiblePoleNumeratorPolynomial
  rawDenominator := visiblePoleDenominatorPolynomial
  cancelledFactor := 1
  reduced := visiblePoleReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by simp [visiblePoleReducedResponse]
  rawDenominator_eq := by simp [visiblePoleReducedResponse]

/-- The selected external response entry is certified by the independently expanded reduction. -/
def visiblePoleCertificate : OneDelayNetworkResponseReduction visiblePoleNetlist
    (Outgoing.mk visiblePoleExternalChannel) (Incident.mk visiblePoleExternalChannel) where
  reduction := visiblePoleReduction
  rawNumerator_eq := by
    simpa [visiblePoleReduction] using visiblePole_responseNumerator.symm
  rawDenominator_eq := by
    simpa [visiblePoleReduction] using visiblePole_responseDenominator.symm

end

end Optics.DelayTransfer
