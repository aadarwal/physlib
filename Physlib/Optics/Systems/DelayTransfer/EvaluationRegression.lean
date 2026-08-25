/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Evaluation
public import Physlib.Optics.Systems.Microring.AllPassRegression

/-!
# One-delay all-pass evaluation regressions

## i. Overview

The retained rational model `allPassDelayModel t a` is
`(t - a*q) / (1 - t*a*q)`. Its formal variable is the single propagation phase factor; the field
attenuation `a` remains a coefficient. On the denominator's nonzero domain, the generic bridge
agrees with `AllPass.throughTransfer` when the N7 coupler is unitary and its loop coefficient is
`a*q`.

The exact S2 fixtures are expanded independently at `q = 1` and `q = -1`. They give `1 / 7` and
`11 / 13`, respectively, before those values are compared with the named S2 transfer results.

## ii. Key definitions and results

- `allPassDelayModel`: the retained one-delay rational presentation.
- `allPassDelayModel_eq_throughTransfer`: agreement with the S2 all-pass response.
- `allPassDelayModel_resonance_value`: direct evaluation at the zero-phase fixture.
- `allPassDelayModel_antiresonance_value`: direct evaluation at the half-turn fixture.
- `allPassDelayModel_resonance_agrees`: agreement with the S2 zero-phase transfer.
- `allPassDelayModel_antiresonance_agrees`: agreement with the S2 half-turn transfer.

## iii. Table of contents

- A. The retained rational all-pass response
- B. Exact S2 phase-point regressions

## iv. References and non-claims

The all-pass transfer, loop coefficient, and solve gate are defined in
`Physlib/Optics/Systems/Microring/AllPass.lean:114-188`. The two exact phase fixtures and transfer
values are defined and proved in
`Physlib/Optics/Systems/Microring/AllPassRegression.lean:62-99,219-247`.

Here `q` is a formal propagation factor. The declarations make no rational-in-frequency,
dispersion, group-delay, global-phase, stability, or physical-resonance claim.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. The retained rational all-pass response

-/

/-- The one-delay all-pass presentation `(t - a*q) / (1 - t*a*q)`. -/
def allPassDelayModel (t a : ℂ) : RationalModel 1 where
  numerator := MvPolynomial.C t - MvPolynomial.C a * MvPolynomial.X 0
  denominator := 1 - MvPolynomial.C (t * a) * MvPolynomial.X 0
  denominator_ne_zero := by
    intro hZero
    have hEval := congrArg (MvPolynomial.eval fun _ : Fin 1 => (0 : ℂ)) hZero
    simp at hEval

/-- Evaluation expands to `(t - a*q) / (1 - t*a*q)`. -/
lemma allPassDelayModel_eval (t a q : ℂ) :
    (allPassDelayModel t a).eval (fun _ => q) =
      (t - a * q) / (1 - t * a * q) := by
  simp [allPassDelayModel, RationalModel.eval, mul_assoc]

/-- The retained all-pass denominator is regular exactly when `1 - t*a*q` is nonzero. -/
lemma mem_allPassDelayModel_evaluationDomain_iff (t a q : ℂ) :
    (fun _ : Fin 1 => q) ∈ (allPassDelayModel t a).evaluationDomain ↔
      1 - t * a * q ≠ 0 := by
  simp [allPassDelayModel, RationalModel.evaluationDomain, mul_assoc]

/-- On the solve domain, the formal all-pass response agrees with the N7/N5F all-pass transfer. -/
lemma allPassDelayModel_eq_throughTransfer (p : AllPass.Parameters) (q : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    (allPassDelayModel (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ)).eval
        (fun _ => q) = AllPass.throughTransfer p := by
  rw [AllPass.throughTransfer_eq_standard p hUnitary hDenominator]
  simp [allPassDelayModel_eval, AllPass.standardThroughTransfer,
    AllPass.Parameters.denominator, AllPass.Parameters.loopGain, hLoop, mul_assoc]

/-!

## B. Exact S2 phase-point regressions

-/

/-- Direct rational evaluation at the S2 zero-phase point gives `1 / 7`. -/
lemma allPassDelayModel_resonance_value :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => 1) = 1 / 7 := by
  norm_num [allPassDelayModel, RationalModel.eval]

/-- The formal-delay and S2 all-pass transfers agree at the zero-phase point. -/
lemma allPassDelayModel_resonance_agrees :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => 1) =
      AllPass.throughTransfer AllPass.allPassRegressionResonanceParameters := by
  rw [allPassDelayModel_resonance_value,
    AllPass.allPassRegression_resonance_throughTransfer]

/-- Direct rational evaluation at the S2 half-turn point gives `11 / 13`. -/
lemma allPassDelayModel_antiresonance_value :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => -1) = 11 / 13 := by
  norm_num [allPassDelayModel, RationalModel.eval]

/-- The formal-delay and S2 all-pass transfers agree at the half-turn point. -/
lemma allPassDelayModel_antiresonance_agrees :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => -1) =
      AllPass.throughTransfer AllPass.allPassRegressionAntiresonanceParameters := by
  rw [allPassDelayModel_antiresonance_value,
    AllPass.allPassRegression_antiresonance_throughTransfer]

end

end Optics.DelayTransfer
