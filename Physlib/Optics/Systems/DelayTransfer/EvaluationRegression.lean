/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPassDelayTransfer
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
The non-real point `q = -I` gives `75 / 109 + (32 / 109) I`; separate equalities obtain this
formal value from both `laplaceEvaluation` at `s = I*pi/2`, `τ = 1`, and
`zInverseEvaluation` at `z = I`.

Proof-gated anchors then carry both substitutions through the actual reparameterized netlists.
The `.laplace` response at unit delay and `s = I*pi/2`, and the `.reciprocalZ` response at
`z = I`, both equal the compiled non-real response. The anchors use the equality-aware reindexed
corollaries whose proofs invoke `response_laplace` and `response_reciprocalZ`, so a broken
reparameterization layer makes the fixture fail.

The production `AllPassDelayTransfer` module independently lifts the constant N7 coupler entries
and the formal propagation entries `a*q`, then reuses the exact S2 connection family. These
regressions exercise its proof-gated response at real and nonreal points through rational
evaluation, pointwise compilation, S2 wiring, and N5 elimination.

## ii. Key results

- `allPassDelayModel`: the retained one-delay rational presentation.
- `allPassDelayModel_eq_throughTransfer`: agreement with the S2 all-pass response.
- `allPassDelayModel_resonance_value`: direct evaluation at the zero-phase fixture.
- `allPassDelayModel_antiresonance_value`: direct evaluation at the half-turn fixture.
- `allPassDelayModel_resonance_agrees`: agreement with the S2 zero-phase transfer.
- `allPassDelayModel_antiresonance_agrees`: agreement with the S2 half-turn transfer.
- `allPassRationalNetlist_resonance_response_entry`: compiled zero-phase response `1/7`.
- `allPassRationalNetlist_antiresonance_response_entry`: compiled half-turn response `11/13`.
- `allPassRationalNetlist_quadrature_response_entry`: compiled non-real response.
- `laplaceEvaluation_quadrature`, `zInverseEvaluation_quadrature`: both conventions give `-I`.
- `allPassRationalNetlist_laplace_quadrature_response_entry`: mapped Laplace response anchor.
- `allPassRationalNetlist_reciprocalZ_quadrature_response_entry`: mapped reciprocal-Z anchor.

## iii. Table of contents

- A. The retained rational all-pass response
- B. Exact S2 phase-point regressions
- C. Non-real convention anchor

## iv. References

The all-pass transfer, loop coefficient, and solve gate are defined in
`Physlib/Optics/Systems/Microring/AllPass.lean:114-188`. The two exact phase fixtures and transfer
values are defined and proved in
`Physlib/Optics/Systems/Microring/AllPassRegression.lean:62-99,219-247`.
The production rational netlist and raw response derivation are in
`Physlib/Optics/Systems/Microring/AllPassDelayTransfer.lean`.

Here `q` is a formal propagation factor. The declarations make no rational-in-frequency,
dispersion, group-delay, global-phase, stability, or physical-resonance claim. They do not perform
symbolic external-response elimination in the fraction field.

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


/-!

## C. Non-real convention anchor

-/

/-- At the named zero-phase S2 point, the stored loop coefficient is `a*1`. -/
lemma allPassRational_resonance_loopCoefficient :
    AllPass.allPassRegressionResonanceParameters.loopCoefficient =
      (AllPass.allPassRegressionResonanceParameters.fieldAttenuation : ℂ) * 1 := by
  rw [AllPass.allPassRegression_resonance_loopCoefficient]
  norm_num [AllPass.allPassRegressionResonanceParameters]

/-- The named zero-phase S2 point has a nonzero feedback denominator. -/
lemma allPassRational_resonance_hasNonzeroDenominator :
    AllPass.allPassRegressionResonanceParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    AllPass.allPassRegression_resonance_denominator]
  norm_num

/-- The named zero-phase S2 point belongs to the compiled rational response domain. -/
lemma allPassRationalResonanceDomain :
    (fun _ : Fin 1 => (1 : ℂ)) ∈
      (allPassRationalNetlist
        AllPass.allPassRegressionResonanceParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    AllPass.allPassRegressionResonanceParameters 1
    allPassRational_resonance_loopCoefficient
    AllPass.allPassRegression_resonance_isValid
    allPassRational_resonance_hasNonzeroDenominator

/-- The compiled rational fixture recovers the named S2 zero-phase response `1/7`. -/
lemma allPassRationalNetlist_resonance_response_entry :
    (allPassRationalNetlist
      AllPass.allPassRegressionResonanceParameters).toParameterizedNetlist.response
        allPassRationalResonanceDomain
        (Outgoing.mk (allPassRationalThroughChannel
          AllPass.allPassRegressionResonanceParameters 1))
        (Incident.mk (allPassRationalInputChannel
          AllPass.allPassRegressionResonanceParameters 1)) = 1 / 7 := by
  have hResponse := allPassRationalNetlist_response_entry
    AllPass.allPassRegressionResonanceParameters 1
    allPassRational_resonance_loopCoefficient
    AllPass.allPassRegression_resonance_isValid
    allPassRational_resonance_hasNonzeroDenominator
  rw [AllPass.allPassRegression_resonance_throughTransfer] at hResponse
  simpa [allPassRationalResonanceDomain] using hResponse

/-- The named half-turn S2 point satisfies the component-validity predicates. -/
lemma allPassRational_antiresonance_isValid :
    AllPass.allPassRegressionAntiresonanceParameters.IsValid := by
  constructor
  · constructor
    · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
        DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
      MatchedPropagation.Parameters.IsValid]

/-- At the named half-turn S2 point, the stored loop coefficient is `a*(-1)`. -/
lemma allPassRational_antiresonance_loopCoefficient :
    AllPass.allPassRegressionAntiresonanceParameters.loopCoefficient =
      (AllPass.allPassRegressionAntiresonanceParameters.fieldAttenuation : ℂ) * (-1) := by
  rw [AllPass.allPassRegression_antiresonance_loopCoefficient]
  norm_num [AllPass.allPassRegressionAntiresonanceParameters]

/-- The named half-turn S2 point has a nonzero feedback denominator. -/
lemma allPassRational_antiresonance_hasNonzeroDenominator :
    AllPass.allPassRegressionAntiresonanceParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    AllPass.allPassRegression_antiresonance_denominator]
  norm_num

/-- The named half-turn S2 point belongs to the compiled rational response domain. -/
lemma allPassRationalAntiresonanceDomain :
    (fun _ : Fin 1 => (-1 : ℂ)) ∈
      (allPassRationalNetlist
        AllPass.allPassRegressionAntiresonanceParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    AllPass.allPassRegressionAntiresonanceParameters (-1)
    allPassRational_antiresonance_loopCoefficient
    allPassRational_antiresonance_isValid
    allPassRational_antiresonance_hasNonzeroDenominator

/-- The compiled rational fixture recovers the named S2 half-turn response `11/13`. -/
lemma allPassRationalNetlist_antiresonance_response_entry :
    (allPassRationalNetlist
      AllPass.allPassRegressionAntiresonanceParameters).toParameterizedNetlist.response
        allPassRationalAntiresonanceDomain
        (Outgoing.mk (allPassRationalThroughChannel
          AllPass.allPassRegressionAntiresonanceParameters (-1)))
        (Incident.mk (allPassRationalInputChannel
          AllPass.allPassRegressionAntiresonanceParameters (-1))) = 11 / 13 := by
  have hResponse := allPassRationalNetlist_response_entry
    AllPass.allPassRegressionAntiresonanceParameters (-1)
    allPassRational_antiresonance_loopCoefficient
    allPassRational_antiresonance_isValid
    allPassRational_antiresonance_hasNonzeroDenominator
  rw [AllPass.allPassRegression_antiresonance_throughTransfer] at hResponse
  simpa [allPassRationalAntiresonanceDomain] using hResponse

/-- The `3-4-5` all-pass fixture at quarter-turn round-trip phase. -/
def allPassRationalQuadratureParameters : AllPass.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := (((Real.pi / 2 : ℝ)) : Real.Angle)

/-- The quarter-turn fixture satisfies the component-validity predicates. -/
lemma allPassRational_quadrature_isValid : allPassRationalQuadratureParameters.IsValid := by
  constructor
  · constructor
    · norm_num [allPassRationalQuadratureParameters,
        DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [allPassRationalQuadratureParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [allPassRationalQuadratureParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [allPassRationalQuadratureParameters, MatchedPropagation.Parameters.IsValid]

/-- The quarter-turn fixture has one-pass coefficient `(1/2)*(-I)`. -/
lemma allPassRational_quadrature_loopCoefficient :
    allPassRationalQuadratureParameters.loopCoefficient =
      (allPassRationalQuadratureParameters.fieldAttenuation : ℂ) * (-Complex.I) := by
  simp [allPassRationalQuadratureParameters, AllPass.Parameters.loopCoefficient,
    AllPass.Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe, Circle.coe_exp,
    Complex.exp_mul_I]

/-- The quarter-turn fixture denominator is `1 + (3/10) I`. -/
lemma allPassRational_quadrature_denominator :
    allPassRationalQuadratureParameters.denominator = 1 + (3 / 10 : ℂ) * Complex.I := by
  rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain,
    allPassRational_quadrature_loopCoefficient]
  norm_num [allPassRationalQuadratureParameters]
  ring

/-- The quarter-turn fixture has a nonzero feedback denominator. -/
lemma allPassRational_quadrature_hasNonzeroDenominator :
    allPassRationalQuadratureParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    allPassRational_quadrature_denominator]
  intro hZero
  have hImag := congrArg Complex.im hZero
  norm_num at hImag

/-- Direct scalar expansion gives the non-real through response
`75/109 + (32/109) I`. -/
lemma allPassRational_quadrature_throughTransfer :
    AllPass.throughTransfer allPassRationalQuadratureParameters =
      75 / 109 + (32 / 109) * Complex.I := by
  rw [AllPass.throughTransfer, allPassRational_quadrature_loopCoefficient,
    allPassRational_quadrature_denominator]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  simp [allPassRationalQuadratureParameters, AllPass.Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  conv_lhs =>
    rhs
    rw [div_eq_mul_inv, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The quarter-turn point belongs to the compiled rational response domain at `q = -I`. -/
lemma allPassRationalQuadratureDomain :
    (fun _ : Fin 1 => -Complex.I) ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    allPassRationalQuadratureParameters (-Complex.I)
    allPassRational_quadrature_loopCoefficient
    allPassRational_quadrature_isValid
    allPassRational_quadrature_hasNonzeroDenominator

/-- The compiled fixture's non-real response is `75/109 + (32/109) I`. -/
lemma allPassRationalNetlist_quadrature_response_entry :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).toParameterizedNetlist.response
        allPassRationalQuadratureDomain
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      75 / 109 + (32 / 109) * Complex.I := by
  have hResponse := allPassRationalNetlist_response_entry
    allPassRationalQuadratureParameters (-Complex.I)
    allPassRational_quadrature_loopCoefficient
    allPassRational_quadrature_isValid
    allPassRational_quadrature_hasNonzeroDenominator
  rw [allPassRational_quadrature_throughTransfer] at hResponse
  convert hResponse using 1
  all_goals rfl

/-- With unit delay and `s = I*pi/2`, the Laplace convention evaluates to `q = -I`. -/
lemma laplaceEvaluation_quadrature :
    laplaceEvaluation (fun _ : Fin 1 => 1) (Complex.I * (Real.pi / 2 : ℝ)) =
      (fun _ => -Complex.I) := by
  funext i
  rw [laplaceEvaluation_apply]
  have hExponent :
      -(Complex.I * (Real.pi / 2 : ℝ)) * ((1 : ℝ) : ℂ) =
        ((-(Real.pi / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.exp_mul_I]
  simp

/-- At `z = I`, reciprocal-Z evaluation gives `q = z⁻¹ = -I`. -/
lemma zInverseEvaluation_quadrature :
    zInverseEvaluation Complex.I = (fun _ => -Complex.I) := by
  funext i
  rw [zInverseEvaluation_apply, Complex.inv_I]

/-- The unit-delay quadrature Laplace point belongs to the mapped proof-gated response domain. -/
lemma allPassRationalNetlistLaplaceQuadratureDomain :
    Complex.I * (Real.pi / 2 : ℝ) ∈
      ((allPassRationalNetlist allPassRationalQuadratureParameters).laplace
        (fun _ : Fin 1 => 1)).responseDomain := by
  change laplaceEvaluation (fun _ : Fin 1 => 1)
    (Complex.I * (Real.pi / 2 : ℝ)) ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).toParameterizedNetlist.responseDomain
  rw [laplaceEvaluation_quadrature]
  exact allPassRationalQuadratureDomain

/-- The proof-gated Laplace-reparameterized fixture carries the compiled non-real response. -/
lemma allPassRationalNetlist_laplace_quadrature_response_entry :
    (((allPassRationalNetlist allPassRationalQuadratureParameters).laplace
      (fun _ : Fin 1 => 1)).response
        allPassRationalNetlistLaplaceQuadratureDomain).reindex
          (Incident.relabelEquiv ((allPassRationalNetlist
            allPassRationalQuadratureParameters).laplaceExternalChannelEquiv
              (fun _ : Fin 1 => 1)))
          (Outgoing.relabelEquiv ((allPassRationalNetlist
            allPassRationalQuadratureParameters).laplaceExternalChannelEquiv
              (fun _ : Fin 1 => 1)))
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      75 / 109 + (32 / 109) * Complex.I := by
  have hResponse :=
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).response_laplace_reindex_of_evaluation_eq
        (fun _ : Fin 1 => 1) allPassRationalNetlistLaplaceQuadratureDomain
        laplaceEvaluation_quadrature allPassRationalQuadratureDomain
  have hEntry := congrArg
    (fun response => response
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))) hResponse
  exact hEntry.trans allPassRationalNetlist_quadrature_response_entry

/-- The point `z = I` belongs to the reciprocal-Z proof-gated response domain. -/
lemma allPassRationalNetlistReciprocalZQuadratureDomain :
    Complex.I ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).reciprocalZ.responseDomain := by
  change zInverseEvaluation Complex.I ∈
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).toParameterizedNetlist.responseDomain
  rw [zInverseEvaluation_quadrature]
  exact allPassRationalQuadratureDomain

/-- The proof-gated reciprocal-Z fixture carries the compiled non-real response at `z = I`. -/
lemma allPassRationalNetlist_reciprocalZ_quadrature_response_entry :
    ((allPassRationalNetlist
      allPassRationalQuadratureParameters).reciprocalZ.response
        allPassRationalNetlistReciprocalZQuadratureDomain).reindex
          (Incident.relabelEquiv ((allPassRationalNetlist
            allPassRationalQuadratureParameters).reciprocalZExternalChannelEquiv))
          (Outgoing.relabelEquiv ((allPassRationalNetlist
            allPassRationalQuadratureParameters).reciprocalZExternalChannelEquiv))
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      75 / 109 + (32 / 109) * Complex.I := by
  have hResponse :=
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).response_reciprocalZ_reindex_of_evaluation_eq
        allPassRationalNetlistReciprocalZQuadratureDomain
        zInverseEvaluation_quadrature allPassRationalQuadratureDomain
  have hEntry := congrArg
    (fun response => response
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))) hResponse
  exact hEntry.trans allPassRationalNetlist_quadrature_response_entry

end

end Optics.DelayTransfer
