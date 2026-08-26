/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Systems.Microring.AllPassTwoPortBoundary

/-!
# Typed two-port scattering semantics of the all-pass microring

## i. Overview

This file states an independent reflectionless two-port law for the all-pass bus. Both directional
transmissions are the totalized scalar `throughTransfer`; the two same-side reflection blocks are
zero. On `Parameters.HasNonzeroDenominator`, the explicit N5 netlist realizes that law after the
exhaustive external boundary is relabeled left then right.

The N5 realization is built through `FlatNetlist.packagedScattering`, whose graph is the original
relational behavior. The resulting typed transform is then proved equal to the independently
specified reflectionless matrix. Equality of the two directional coefficients is derived from the
selected component and wiring equations; it is not called reciprocity.

The packaged realization needs only the solve gate. It makes no chain-pivot, full-matrix inverse,
passivity, losslessness, delay, causality, ROC, frequency, material, or source-parity claim.

## ii. Key results

- `AllPass.twoPortBehavior`: the independent parameter-level bus law.
- `AllPass.twoPortScattering`: its reflectionless scattering realization.
- `AllPass.packagedTwoPortScattering`: the canonically ordered N5 boundary transform.
- `AllPass.packagedTwoPortScattering_eq_twoPortScatteringTransform`: N5 realizes the matrix law.
- `AllPass.externalBehavior_eq_twoPortBehavior`: relational and independent specifications agree.

## iii. Table of contents

- A. Independent two-port specification
- B. Packaged N5 realization

## iv. References

This typed boundary realization is Physlib-original and source-neutral.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-!
## A. Independent two-port specification
-/

/-- The totalized scalar bus transmission as a one-mode transform. -/
def twoPortTransmission (p : Parameters) : ModeTransform Unit Unit :=
  fun _ _ => throughTransfer p

/-- The independent reflectionless two-port behavior of the all-pass bus.

Using the same transform in both directional slots is an explicit choice of the component model,
not a reciprocity inference.
-/
def twoPortBehavior (p : Parameters) : TwoPortScatteringBehavior Unit Unit :=
  ReflectionlessTwoPort.behavior (twoPortTransmission p) (twoPortTransmission p)

/-- The independent reflectionless scattering matrix of the all-pass bus. -/
def twoPortScattering (p : Parameters) : ScatteringMatrix (Unit ⊕ Unit) :=
  ReflectionlessTwoPort.scattering (twoPortTransmission p) (twoPortTransmission p)

/-- The independent scattering matrix realizes the independently stated bus behavior. -/
lemma twoPortScattering_realizes_behavior (p : Parameters) :
    (twoPortScattering p).toTwoPortScatteringBehavior = twoPortBehavior p := by
  exact ReflectionlessTwoPort.scattering_realizes_behavior
    (twoPortTransmission p) (twoPortTransmission p)

/-!
## B. Packaged N5 realization
-/

/-- The singular-safe external netlist behavior in typed left/right scattering coordinates. -/
def externalBehavior (p : Parameters) : TwoPortScatteringBehavior Unit Unit :=
  (netlist p).behavior.reindex
    (twoPortExternalIncidentEquiv p) (twoPortExternalOutgoingEquiv p)

/-- The well-posed N5 response packaged and relabeled as a typed two-port scattering transform. -/
noncomputable def packagedTwoPortScattering (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    TwoPortScatteringTransform Unit Unit :=
  ((((netlist p).packagedScattering
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)).reindex
        (twoPortExternalChannelEquiv p).symm).toTwoPortScatteringTransform)

/-- Packaging and channel relabeling are exactly direct endpoint relabeling of the N5 response. -/
lemma packagedTwoPortScattering_eq_responseTransform_reindex (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator =
      ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).reindex
          (twoPortExternalIncidentEquiv p) (twoPortExternalOutgoingEquiv p) := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;> rfl

/-- The packaged typed scattering matrix has zero left reflection. -/
@[simp]
lemma packagedTwoPortScattering_apply_inl_inl (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = 0 := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_input_input p hDenominator

/-- The packaged typed scattering matrix has the all-pass right-to-left entry. -/
@[simp]
lemma packagedTwoPortScattering_apply_inl_inr (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = throughTransfer p := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_input_through p hDenominator

/-- The packaged typed scattering matrix has the all-pass left-to-right entry. -/
@[simp]
lemma packagedTwoPortScattering_apply_inr_inl (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = throughTransfer p := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_through_input p hDenominator

/-- The packaged typed scattering matrix has zero right reflection. -/
@[simp]
lemma packagedTwoPortScattering_apply_inr_inr (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = 0 := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_through_through p hDenominator

/-- The packaged two-port graph is exactly the relabeled singular-safe netlist behavior. -/
lemma toBehavior_packagedTwoPortScattering (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).toBehavior = externalBehavior p := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex,
    ModeTransform.toBehavior_reindex, externalBehavior]
  ext state
  rcases state with ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff, LinearBehavior.mem_reindex_iff]
  have hGraph := (netlist p).toBehavior_responseTransform
    (isWellPosed_of_hasNonzeroDenominator p hDenominator)
  constructor
  · intro hMember
    exact hGraph ▸ hMember
  · intro hMember
    exact hGraph.symm ▸ hMember

/-- The packaged N5 transform is exactly the independent reflectionless scattering law. -/
lemma packagedTwoPortScattering_eq_twoPortScatteringTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedTwoPortScattering p hDenominator =
      (twoPortScattering p).toTwoPortScatteringTransform := by
  rw [packagedTwoPortScattering_eq_responseTransform_reindex]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩
  · exact responseTransform_entry_input_input p hDenominator
  · exact responseTransform_entry_input_through p hDenominator
  · exact responseTransform_entry_through_input p hDenominator
  · exact responseTransform_entry_through_through p hDenominator

/-- On the solve gate, the relabeled netlist behavior equals the independent two-port behavior. -/
lemma externalBehavior_eq_twoPortBehavior (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    externalBehavior p = twoPortBehavior p := by
  calc
    externalBehavior p = (packagedTwoPortScattering p hDenominator).toBehavior :=
      (toBehavior_packagedTwoPortScattering p hDenominator).symm
    _ = (twoPortScattering p).toTwoPortScatteringTransform.toBehavior := by
      rw [packagedTwoPortScattering_eq_twoPortScatteringTransform]
    _ = twoPortBehavior p := twoPortScattering_realizes_behavior p

end AllPass

end

end Optics
