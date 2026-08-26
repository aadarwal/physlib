/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module
public import Physlib.Optics.Systems.Microring.AddDrop

/-!
# SFG-TR'14 source bridge for the add-drop microring

## i. Overview

This file records the SFG-TR'14 parameter and port dictionary needed to compare Physlib's
explicit microring network with the source statements catalogued at `HOL-CORPUS.md:335-349` in
the parity audit checkout. SFG-TR uses `(xi, S1, S2, C1, C2)`.

SFG-TR's complex square root is principal, while Physlib stores a selected half-arc factor. Its
bridge consequently states their equality as an explicit hypothesis.

## ii. Key results

- `sfgAddDropTransfer_eq_dropTransfer`: SFG-TR Thm. 7 under its square-root branch map.
- `sfgAddDropTransfer_eq_n5Response`: the source formula and proof-gated N5 response entry.

## iii. Table of contents

- E. SFG-TR'14 parameter, port, and square-root dictionary

## iv. References and non-claims

SFG-TR Def. 35 and Thm. 7 are summarized at `HOL-CORPUS.md:345-346`.

The source predicates store their transfer formulas; this file does not recast them as component
derivations. It also does not assert that every source record maps to N7-valid components.
Physical response meaning on the Physlib side remains gated by N5 well-posedness and N7
validity. No reciprocity, omitted-loss completeness, time-domain causality, bandwidth,
dispersion, or measurement-validation claim is made. The SFG transfer quotient is totalized at
zero denominator; its algebraic identity remains meaningful there, but an N5 response claim
requires the displayed nonzero-denominator gate.
-/
@[expose] public section

namespace Optics

noncomputable section

namespace MicroringSourceBridge
/-! ## E. SFG-TR'14 parameter, port, and square-root dictionary -/

/-- The five complex SFG-TR add-drop coefficients from `HOL-CORPUS.md:345-346`. -/
structure SfgParameters where
  /-- Source complete round-trip coefficient `xi`. -/
  roundTripCoefficient : ℂ
  /-- Source first cross amplitude `S1`. -/
  inputCrossAmplitude : ℂ
  /-- Source second cross amplitude `S2`. -/
  dropCrossAmplitude : ℂ
  /-- Source first through amplitude `C1`. -/
  inputThroughAmplitude : ℂ
  /-- Source second through amplitude `C2`. -/
  dropThroughAmplitude : ℂ

/-- Physlib add-drop data mapped to SFG-TR's complex coefficient names.

The SFG input node 1 and output node 8 are Physlib's input and drop channels; Def. 35 and Thm. 7
are at `HOL-CORPUS.md:345-346`.
-/
def SfgParameters.ofAddDrop (p : AddDrop.Parameters) : SfgParameters where
  roundTripCoefficient := p.roundTripCoefficient
  inputCrossAmplitude := p.inputCrossAmplitude
  dropCrossAmplitude := p.dropCrossAmplitude
  inputThroughAmplitude := p.inputThroughAmplitude
  dropThroughAmplitude := p.dropThroughAmplitude

/-- The SFG dictionary preserves the round trip and all four real Physlib coupler amplitudes. -/
lemma SfgParameters.ofAddDrop_data (p : AddDrop.Parameters) :
    (SfgParameters.ofAddDrop p).roundTripCoefficient = p.roundTripCoefficient ∧
      (SfgParameters.ofAddDrop p).inputCrossAmplitude = p.inputCrossAmplitude ∧
      (SfgParameters.ofAddDrop p).dropCrossAmplitude = p.dropCrossAmplitude ∧
      (SfgParameters.ofAddDrop p).inputThroughAmplitude = p.inputThroughAmplitude ∧
      (SfgParameters.ofAddDrop p).dropThroughAmplitude = p.dropThroughAmplitude :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- SFG-TR Thm. 7's transfer `-S1*S2*sqrt(xi)/(1-C1*C2*xi)`
(`HOL-CORPUS.md:346`). -/
def sfgAddDropTransfer (p : SfgParameters) : ℂ :=
  -(p.inputCrossAmplitude * p.dropCrossAmplitude *
      Complex.sqrt p.roundTripCoefficient) /
    (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.roundTripCoefficient)

/-- SFG-TR's two `-j*S` branches use the N7 negative-quadrature gauge at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. -/
def sfgCrossCoefficient (crossAmplitude : ℂ) : ℂ :=
  -Complex.I * crossAmplitude

/-- Under an explicit principal-square-root branch match, SFG-TR Thm. 7 is the S2 drop field. -/
theorem sfgAddDropTransfer_eq_dropTransfer (p : AddDrop.Parameters)
    (hSqrt : Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient) :
    sfgAddDropTransfer (SfgParameters.ofAddDrop p) = AddDrop.dropTransfer p := by
  rw [AddDrop.dropTransfer_eq_standard, sfgAddDropTransfer,
    AddDrop.standardDropTransfer]
  simp only [SfgParameters.ofAddDrop, hSqrt, AddDrop.Parameters.denominator,
    AddDrop.Parameters.loopGain]

/-- With the N5 solve gate, SFG-TR Thm. 7 is the input-to-drop response entry. -/
theorem sfgAddDropTransfer_eq_n5Response (p : AddDrop.Parameters)
    (hSqrt : Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient)
    (hDenominator : p.HasNonzeroDenominator) :
    sfgAddDropTransfer (SfgParameters.ofAddDrop p) =
      (AddDrop.netlist p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p))
        (Incident.mk (AddDrop.inputChannel p)) := by
  have hResponse := AddDrop.responseTransform_entry_drop_input p hDenominator
  rw [sfgAddDropTransfer_eq_dropTransfer p hSqrt]
  exact hResponse.symm

end MicroringSourceBridge

end

end Optics
