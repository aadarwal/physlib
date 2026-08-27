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

/-- Classical equality on aggregate fixture channels. -/
noncomputable instance visiblePoleChannelDecidableEq :
    DecidableEq visiblePoleNetlist.Channel := Classical.decEq _

/-- Classical equality on connected fixture channels. -/
noncomputable instance visiblePoleConnectedChannelDecidableEq :
    DecidableEq visiblePoleNetlist.ConnectedChannel := Classical.decEq _

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

/-- The left endpoint of the internal connection. -/
def visiblePoleConnectedLeft : visiblePoleNetlist.ConnectedChannel :=
  ⟨(), Sum.inl ()⟩

/-- The right endpoint of the internal connection. -/
def visiblePoleConnectedRight : visiblePoleNetlist.ConnectedChannel :=
  ⟨(), Sum.inr ()⟩

@[simp]
lemma visiblePoleConnectedLeft_embedding :
    visiblePoleConnections.channelEmbedding visiblePoleConnectedLeft =
      visiblePoleChannel .left := rfl

@[simp]
lemma visiblePoleConnectedRight_embedding :
    visiblePoleConnections.channelEmbedding visiblePoleConnectedRight =
      visiblePoleChannel .right := rfl

@[simp]
lemma visiblePoleConnectedLeft_mate :
    visiblePoleConnections.mateEquiv visiblePoleConnectedLeft =
      visiblePoleConnectedRight := rfl

@[simp]
lemma visiblePoleConnectedRight_mate :
    visiblePoleConnections.mateEquiv visiblePoleConnectedRight =
      visiblePoleConnectedLeft := rfl

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

/-- The exact selected external response numerator `3/5 - q/2`. -/
def visiblePoleNumeratorPolynomial : Polynomial ℂ :=
  Polynomial.C (3 / 5) - Polynomial.C (1 / 2) * Polynomial.X

/-- The exact cleared determinant `1 - 3*q/10`. -/
def visiblePoleDenominatorPolynomial : Polynomial ℂ :=
  1 - Polynomial.C (3 / 10) * Polynomial.X

end

end Optics.DelayTransfer
