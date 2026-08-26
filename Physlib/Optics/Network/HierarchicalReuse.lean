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

end PortConnectionFamily

end


end Optics
