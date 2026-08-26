/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ConnectionFamilyTransport

/-!
# Reuse and associativity of hierarchical optical wiring

## i. Overview

This file uses dependent connection-family transport to reuse a subsystem behind an equivalent
boundary relation. It also makes three-stage append associativity literal: the third stage is
transported to the regrouped boundary and the connection labels are relabelled by the canonical
associator for binary sums.

The construction is relational throughout. It compares the complete singular-safe boundary
relations and therefore does not require any stage to determine a unique response.

## ii. Key results

- `PortConnectionFamily.replaceInnerFamily`: an inner family may be replaced by one with the
  same transported boundary relation.
- `PortConnectionFamily.append_assoc_transport`: three append stages agree after boundary
  transport and the sum associator.

## iii. Table of contents

- A. Regrouped external boundaries
- B. Literal three-stage append associativity
- C. Replacement by an equivalent boundary relation

## iv. References

This discharges the remaining reuse-machinery bullet in `goal.md` lines 2098--2102. The source
states literally: "All current N-08 hypotheses are structural `Fintype` assumptions on channel
indices, not physical assumptions." Accordingly, no well-posedness, functionality, passivity,
losslessness, reciprocity, stability, causality, or physical-realization claim is made.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x y

namespace PortConnectionFamily

/-!

## A. Regrouped external boundaries

-/

variable {P : PortModeFamily.{u, v}} {innerIndex : Type w} {middleIndex : Type x}
variable (inner : PortConnectionFamily P innerIndex)
variable (middle : PortConnectionFamily inner.externalPortModeFamily middleIndex)

/-- The boundary of an appended pair, presented as the second family's external dependent port
family. -/
def appendExternalPortModeFamilyEquiv :
    (inner.append middle).externalPortModeFamily.Equiv
      middle.externalPortModeFamily where
  portEquiv := inner.appendUnconnectedPortEquiv middle
  modeEquiv _ := Equiv.refl _

/-- The second family's external dependent port family, presented as the boundary of an appended
pair. This direction transports a third wiring stage to the left-associated boundary. -/
def prependExternalPortModeFamilyEquiv :
    middle.externalPortModeFamily.Equiv
      (inner.append middle).externalPortModeFamily where
  portEquiv := (inner.appendUnconnectedPortEquiv middle).symm
  modeEquiv _ := Equiv.refl _

/-- The induced appended-boundary channel equivalence agrees with the existing external-channel
equivalence after both canonical boundary presentations. -/
lemma appendExternalPortModeFamilyEquiv_boundaryChannelEquiv
    (channel : (inner.append middle).externalPortModeFamily.Channel) :
    middle.boundaryChannelEquiv
        ((inner.appendExternalPortModeFamilyEquiv middle).channelEquiv channel) =
      inner.appendExternalChannelEquiv middle
        ((inner.append middle).boundaryChannelEquiv channel) := by
  apply Subtype.ext
  rfl

/-!

## B. Literal three-stage append associativity

-/

variable {outerIndex : Type y}
variable (outer : PortConnectionFamily middle.externalPortModeFamily outerIndex)

/-- The left-associated three-stage connection family, with the third family transported to the
boundary exposed after appending the first two stages. -/
def appendThreeLeft : PortConnectionFamily P ((innerIndex ⊕ middleIndex) ⊕ outerIndex) :=
  (inner.append middle).append
    (outer.transport (inner.prependExternalPortModeFamilyEquiv middle))

/-- The right-associated three-stage connection family. -/
def appendThreeRight : PortConnectionFamily P (innerIndex ⊕ (middleIndex ⊕ outerIndex)) :=
  inner.append (middle.append outer)

/-- Connection families are equal when every indexed connection is equal. -/
lemma eq_of_connection_eq {index : Type*} {first second : PortConnectionFamily P index}
    (hConnection : ∀ connectionIndex, first.connection connectionIndex =
      second.connection connectionIndex) :
    first = second := by
  cases first with
  | mk firstConnection firstInjective =>
      cases second with
      | mk secondConnection secondInjective =>
          have hFunctions : firstConnection = secondConnection := funext hConnection
          subst secondConnection
          rfl

/-- Three-stage append is literally associative after transporting the third boundary family and
reassociating the sum of connection labels. -/
lemma append_assoc_transport :
    (inner.appendThreeLeft middle outer).reindex
        (Equiv.sumAssoc innerIndex middleIndex outerIndex) =
      inner.appendThreeRight middle outer := by
  apply eq_of_connection_eq
  intro connectionIndex
  rcases connectionIndex with innerConnection | middleOrOuter
  · rfl
  · rcases middleOrOuter with middleConnection | outerConnection
    · rfl
    · rfl

/-!

## C. Replacement by an equivalent boundary relation

-/

variable {replacementIndex : Type*}
variable (replacement : PortConnectionFamily P replacementIndex)
variable (boundary : inner.externalPortModeFamily.Equiv
  replacement.externalPortModeFamily)

/-- The external-channel equivalence induced by an explicitly supplied equivalence of dependent
boundary port families. -/
def boundaryExternalChannelEquiv : inner.ExternalChannel ≃ replacement.ExternalChannel :=
  inner.boundaryChannelEquiv.symm.trans
    (boundary.channelEquiv.trans replacement.boundaryChannelEquiv)

/-- The final external-channel equivalence induced when an outer family is transported across an
equivalent inner boundary. -/
def replacementExternalChannelEquiv
    (outer : PortConnectionFamily inner.externalPortModeFamily middleIndex) :
    (inner.append outer).ExternalChannel ≃
      (replacement.append (outer.transport boundary)).ExternalChannel :=
  (inner.appendExternalChannelEquiv outer).trans
    ((outer.transportExternalChannelEquiv boundary).trans
      (replacement.appendExternalChannelEquiv (outer.transport boundary)).symm)

variable [Fintype P.Channel] [Fintype inner.Channel] [Fintype replacement.Channel]
variable [Fintype inner.ExternalChannel] [Fintype replacement.ExternalChannel]

/-- The first inner boundary inherits the external-channel enumeration. -/
local instance replacementSourceBoundaryChannelFintype :
    Fintype inner.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ inner.boundaryChannelEquiv.symm

/-- The replacement boundary inherits its external-channel enumeration. -/
local instance replacementTargetBoundaryChannelFintype :
    Fintype replacement.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ replacement.boundaryChannelEquiv.symm

/-- Equivalent transported closure relations induce equivalent behaviors on the dependent
boundaries exposed to the next hierarchy stage. -/
lemma innerBoundaryBehavior_eq_of_boundaryRelation
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (hBoundary : replacement.closeBehavior behavior =
      (inner.closeBehavior behavior).reindex
        (Incident.relabelEquiv (inner.boundaryExternalChannelEquiv replacement boundary))
        (Outgoing.relabelEquiv
          (inner.boundaryExternalChannelEquiv replacement boundary))) :
    replacement.innerBoundaryBehavior behavior =
      (inner.innerBoundaryBehavior behavior).reindex
        (Incident.relabelEquiv boundary.channelEquiv)
        (Outgoing.relabelEquiv boundary.channelEquiv) := by
  have hIncidentEquiv :
      (Incident.relabelEquiv
          (inner.boundaryExternalChannelEquiv replacement boundary)).trans
          (Incident.relabelEquiv replacement.boundaryChannelEquiv.symm) =
        (Incident.relabelEquiv inner.boundaryChannelEquiv.symm).trans
          (Incident.relabelEquiv boundary.channelEquiv) := by
    apply Equiv.ext
    rintro ⟨channel⟩
    apply Incident.ext
    rfl
  have hOutgoingEquiv :
      (Outgoing.relabelEquiv
          (inner.boundaryExternalChannelEquiv replacement boundary)).trans
          (Outgoing.relabelEquiv replacement.boundaryChannelEquiv.symm) =
        (Outgoing.relabelEquiv inner.boundaryChannelEquiv.symm).trans
          (Outgoing.relabelEquiv boundary.channelEquiv) := by
    apply Equiv.ext
    rintro ⟨channel⟩
    apply Outgoing.ext
    rfl
  calc
    replacement.innerBoundaryBehavior behavior =
        ((inner.closeBehavior behavior).reindex
          (Incident.relabelEquiv
            (inner.boundaryExternalChannelEquiv replacement boundary))
          (Outgoing.relabelEquiv
            (inner.boundaryExternalChannelEquiv replacement boundary))).reindex
              (Incident.relabelEquiv replacement.boundaryChannelEquiv.symm)
              (Outgoing.relabelEquiv replacement.boundaryChannelEquiv.symm) := by
                rw [innerBoundaryBehavior, hBoundary]
                rfl
    _ = (inner.closeBehavior behavior).reindex
          ((Incident.relabelEquiv
            (inner.boundaryExternalChannelEquiv replacement boundary)).trans
              (Incident.relabelEquiv replacement.boundaryChannelEquiv.symm))
          ((Outgoing.relabelEquiv
            (inner.boundaryExternalChannelEquiv replacement boundary)).trans
              (Outgoing.relabelEquiv replacement.boundaryChannelEquiv.symm)) :=
        LinearBehavior.reindex_trans _ _ _ _ _
    _ = (inner.closeBehavior behavior).reindex
          ((Incident.relabelEquiv inner.boundaryChannelEquiv.symm).trans
            (Incident.relabelEquiv boundary.channelEquiv))
          ((Outgoing.relabelEquiv inner.boundaryChannelEquiv.symm).trans
            (Outgoing.relabelEquiv boundary.channelEquiv)) := by
              rw [hIncidentEquiv, hOutgoingEquiv]
    _ = (inner.innerBoundaryBehavior behavior).reindex
          (Incident.relabelEquiv boundary.channelEquiv)
          (Outgoing.relabelEquiv boundary.channelEquiv) := by
            unfold innerBoundaryBehavior
            exact (LinearBehavior.reindex_trans _ _ _ _ _).symm

variable (outer : PortConnectionFamily inner.externalPortModeFamily middleIndex)
variable [Fintype outer.Channel] [Fintype (outer.transport boundary).Channel]
variable [Fintype outer.ExternalChannel]
variable [Fintype (outer.transport boundary).ExternalChannel]
variable [Fintype (inner.append outer).ExternalChannel]
variable [Fintype (replacement.append (outer.transport boundary)).ExternalChannel]

/-- The left flattened connected channels inherit the two finite stage enumerations. -/
local instance replacementSourceAppendChannelFintype :
    Fintype (inner.append outer).Channel :=
  Fintype.ofEquiv _ (inner.appendChannelEquiv outer).symm

/-- The replacement flattened channels inherit the two finite stage enumerations. -/
local instance replacementTargetAppendChannelFintype :
    Fintype (replacement.append (outer.transport boundary)).Channel :=
  Fintype.ofEquiv _
    (replacement.appendChannelEquiv (outer.transport boundary)).symm

omit [Fintype P.Channel] [Fintype inner.Channel] [Fintype replacement.Channel]
  [Fintype (inner.append outer).ExternalChannel] in
/-- Closing a transported outer family and then presenting the final appended boundary is the
same as first transporting the outer closure and then presenting that boundary. -/
lemma transportedOuterClosure_reindex
    (boundaryBehavior :
      LinearBehavior (Incident inner.externalPortModeFamily.Channel)
        (Outgoing inner.externalPortModeFamily.Channel)) :
    ((outer.transport boundary).closeBehavior
          (boundaryBehavior.reindex
            (Incident.relabelEquiv boundary.channelEquiv)
            (Outgoing.relabelEquiv boundary.channelEquiv))).reindex
        (Incident.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm
        (Outgoing.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm =
      ((outer.closeBehavior boundaryBehavior).reindex
          (Incident.relabelEquiv (outer.transportExternalChannelEquiv boundary))
          (Outgoing.relabelEquiv
            (outer.transportExternalChannelEquiv boundary))).reindex
        (Incident.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm
        (Outgoing.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm := by
  exact congrArg
    (fun relation => relation.reindex
      (Incident.relabelEquiv
        (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm
      (Outgoing.relabelEquiv
        (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm)
    (outer.closeBehavior_transport boundary boundaryBehavior)

omit [Fintype P.Channel] [Fintype inner.Channel] [Fintype replacement.Channel]
  [Fintype inner.ExternalChannel] [Fintype replacement.ExternalChannel]
  [Fintype outer.Channel] [Fintype (outer.transport boundary).Channel] in
/-- The two routes from an outer external relation to the replacement's final boundary induce
the same behavior relabelling. -/
lemma replacementExternal_reindex
    (closed : LinearBehavior (Incident outer.ExternalChannel)
      (Outgoing outer.ExternalChannel)) :
    (closed.reindex
          (Incident.relabelEquiv (outer.transportExternalChannelEquiv boundary))
          (Outgoing.relabelEquiv
            (outer.transportExternalChannelEquiv boundary))).reindex
        (Incident.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm
        (Outgoing.relabelEquiv
          (replacement.appendExternalChannelEquiv (outer.transport boundary))).symm =
      (closed.reindex
          (Incident.relabelEquiv (inner.appendExternalChannelEquiv outer).symm)
          (Outgoing.relabelEquiv (inner.appendExternalChannelEquiv outer).symm)).reindex
        (Incident.relabelEquiv
          (inner.replacementExternalChannelEquiv replacement boundary outer))
        (Outgoing.relabelEquiv
          (inner.replacementExternalChannelEquiv replacement boundary outer)) := by
  have hIncidentEquiv :
      (Incident.relabelEquiv (outer.transportExternalChannelEquiv boundary)).trans
          (Incident.relabelEquiv
            (replacement.appendExternalChannelEquiv
              (outer.transport boundary)).symm) =
        (Incident.relabelEquiv (inner.appendExternalChannelEquiv outer).symm).trans
          (Incident.relabelEquiv
            (inner.replacementExternalChannelEquiv replacement boundary outer)) := by
    apply Equiv.ext
    rintro ⟨channel⟩
    apply Incident.ext
    simp [replacementExternalChannelEquiv, Incident.relabelEquiv]
  have hOutgoingEquiv :
      (Outgoing.relabelEquiv (outer.transportExternalChannelEquiv boundary)).trans
          (Outgoing.relabelEquiv
            (replacement.appendExternalChannelEquiv
              (outer.transport boundary)).symm) =
        (Outgoing.relabelEquiv (inner.appendExternalChannelEquiv outer).symm).trans
          (Outgoing.relabelEquiv
            (inner.replacementExternalChannelEquiv replacement boundary outer)) := by
    apply Equiv.ext
    rintro ⟨channel⟩
    apply Outgoing.ext
    simp [replacementExternalChannelEquiv, Outgoing.relabelEquiv]
  calc
    _ = closed.reindex
          ((Incident.relabelEquiv
            (outer.transportExternalChannelEquiv boundary)).trans
              (Incident.relabelEquiv
                (replacement.appendExternalChannelEquiv
                  (outer.transport boundary)).symm))
          ((Outgoing.relabelEquiv
            (outer.transportExternalChannelEquiv boundary)).trans
              (Outgoing.relabelEquiv
                (replacement.appendExternalChannelEquiv
                  (outer.transport boundary)).symm)) :=
        LinearBehavior.reindex_trans _ _ _ _ _
    _ = closed.reindex
          ((Incident.relabelEquiv (inner.appendExternalChannelEquiv outer).symm).trans
            (Incident.relabelEquiv
              (inner.replacementExternalChannelEquiv replacement boundary outer)))
          ((Outgoing.relabelEquiv (inner.appendExternalChannelEquiv outer).symm).trans
            (Outgoing.relabelEquiv
              (inner.replacementExternalChannelEquiv replacement boundary outer))) := by
                rw [hIncidentEquiv, hOutgoingEquiv]
    _ = _ := (LinearBehavior.reindex_trans _ _ _ _ _).symm

/-- An inner connection family may be replaced behind an outer stage when its closed relation is
the same after the supplied boundary transport. -/
lemma replaceInnerFamily
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (hBoundary : replacement.closeBehavior behavior =
      (inner.closeBehavior behavior).reindex
        (Incident.relabelEquiv (inner.boundaryExternalChannelEquiv replacement boundary))
        (Outgoing.relabelEquiv
          (inner.boundaryExternalChannelEquiv replacement boundary))) :
    (replacement.append (outer.transport boundary)).closeBehavior behavior =
      ((inner.append outer).closeBehavior behavior).reindex
        (Incident.relabelEquiv
          (inner.replacementExternalChannelEquiv replacement boundary outer))
        (Outgoing.relabelEquiv
          (inner.replacementExternalChannelEquiv replacement boundary outer)) := by
  rw [replacement.closeBehavior_append (outer.transport boundary),
    inner.closeBehavior_append outer,
    inner.innerBoundaryBehavior_eq_of_boundaryRelation replacement boundary behavior hBoundary]
  rw [outer.closeBehavior_transport boundary (inner.innerBoundaryBehavior behavior)]
  exact replacementExternal_reindex
    (inner := inner) (replacement := replacement)
    (boundary := boundary) (outer := outer)
    (outer.closeBehavior (inner.innerBoundaryBehavior behavior))

end PortConnectionFamily

end


end Optics
