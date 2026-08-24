/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalPolarization
public import Physlib.Optics.Polarization.PositiveNormalDecayFrameRegression

/-!
# Regression tests for negative-radicand transmitted polarization

## i. Overview

This file connects the exact positive-normal-decay polarization frame to a planar dielectric
configuration. The incident wave has real wave vector `(5, 0, 12)` in a medium with
`epsilon = mu = 13`, while the positive-side medium has `epsilon = mu = 3`, all at angular
frequency one. The transmitted normal radicand is therefore

`3 * 3 - 5^2 = -16`,

and the canonical negative-imaginary root is the existing complex regression vector
`(5, 0, -4 I)`. Raw TM coordinates `(0, -3 I)` reconstruct the independently defined TM
electric and magnetic-induction amplitudes. The same configuration exercises the sharp
positive-medium Maxwell and zero stored-normal one-period mean-flux endpoints. Its stored
transmitted slot is an unrelated zero candidate, so these equalities exercise the canonical
constructor rather than reusing the expected carrier.

## ii. Key results

- `supercriticalPolarizationRegression_transmittedNormalRadicand`: the exact radicand `-16`.
- `supercriticalPolarizationRegression_incident_isDispersionMatched`: the incident `5-12-13`
  material-shell identity.
- `supercriticalPolarizationRegression_positiveNormalDecayTransmittedWaveVector`: recovery of
  the exact `(5, 0, -4 I)` wave vector.
- `supercriticalPolarizationRegression_candidate_eq_complexDecayRegressionTM`: recovery of the
  existing TM carrier.
- `supercriticalPolarizationRegression_tangentialElectricAmplitude` and
  `supercriticalPolarizationRegression_tangentialMagneticFieldStrengthAmplitude`: the exact
  fixed-plane amplitudes `(4, 0, 0)` and `(0, 3 I, 0)`.
- `supercriticalPolarizationRegression_isMacroscopicMaxwellSolution`: the configuration-level
  positive-medium Maxwell endpoint.
- `supercriticalPolarizationRegression_normalMeanFlux_eq_zero`: the
  configuration-level zero stored-normal mean-flux endpoint.
- `supercriticalPolarizationRegressionShifted_referencedJones`: a nonzero affine interface point
  contributes the exact stored-point spatial factor to the transmitted Jones data.

## iii. Table of contents

- A. Exact interface configuration
- B. Canonical frame and carrier recovery
- C. Maxwell and flux endpoints
- D. Nonzero affine reference point

## iv. References

This regression combines independently defined Physlib exact fixtures and public connector APIs.
No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension MeasureTheory Space Time
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PlanarDielectricWaveConfiguration
open PositiveNormalDecayPolarizationFrame
open scoped Interval Real

noncomputable section

/-!

## A. Exact interface configuration

-/

/-- The negative-side medium with `epsilon = mu = 13`. -/
def supercriticalPolarizationRegressionNegativeMedium : HomogeneousIsotropicMedium where
  ε := 13
  μ := 13
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The real incident wave vector `(5, 0, 12)` on the `13^2` shell. -/
def supercriticalPolarizationRegressionIncidentWaveVector : ComplexWaveVector 3 :=
  ofReal (WithLp.toLp 2 ![(5 : ℝ), 0, 12])

/-- The real incident plane-wave candidate at angular frequency one. -/
def supercriticalPolarizationRegressionIncident : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := supercriticalPolarizationRegressionIncidentWaveVector
  electricAmplitude := WithLp.toLp 2 ![(0 : ℂ), 1, 0]

/-- A dummy zero reflected candidate; no boundary equation is asserted in this regression. -/
def supercriticalPolarizationRegressionReflected : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := 0
  electricAmplitude := 0

/-- An unrelated zero transmitted slot, ensuring that the canonical constructor regression does
not reuse the configuration's stored transmitted candidate. -/
def supercriticalPolarizationRegressionDummyTransmitted : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := 0
  electricAmplitude := 0

/-- The exact regression interface with stored normal `+z`. -/
def supercriticalPolarizationRegressionInterface : PlanarDielectricInterface where
  plane := complexDecayRegressionPlane
  negativeMedium := supercriticalPolarizationRegressionNegativeMedium
  positiveMedium := complexDecayRegressionMedium

/-- The interface configuration with an unrelated dummy transmitted slot. -/
def supercriticalPolarizationRegressionConfiguration : PlanarDielectricWaveConfiguration where
  interface := supercriticalPolarizationRegressionInterface
  incident := supercriticalPolarizationRegressionIncident
  reflected := supercriticalPolarizationRegressionReflected
  transmitted := supercriticalPolarizationRegressionDummyTransmitted

/-- The incident `5-12-13` wave vector lies on the exact negative-medium material shell. -/
lemma supercriticalPolarizationRegression_incident_isDispersionMatched :
    supercriticalPolarizationRegressionIncident.IsDispersionMatched
      supercriticalPolarizationRegressionNegativeMedium := by
  rw [IsDispersionMatched]
  norm_num [supercriticalPolarizationRegressionIncident,
    supercriticalPolarizationRegressionIncidentWaveVector,
    supercriticalPolarizationRegressionNegativeMedium,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]

/-- The incident phase vector projects to the exact tangent `(5, 0, 0)`. -/
lemma supercriticalPolarizationRegression_incidentTangentialPhaseVector :
    complexDecayRegressionPlane.tangentialProjection
        supercriticalPolarizationRegressionIncident.waveVector.phaseVector =
      WithLp.toLp 2 ![(5 : ℝ), 0, 0] := by
  ext i
  fin_cases i <;>
    simp [supercriticalPolarizationRegressionIncident,
      supercriticalPolarizationRegressionIncidentWaveVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
      ComplexWaveVector.phaseVector, ComplexWaveVector.ofReal,
      ComplexWaveVector.realPart, PiLp.inner_apply, RCLike.inner_apply]

/-- The exact transmitted normal radicand is `-16`. -/
lemma supercriticalPolarizationRegression_transmittedNormalRadicand :
    supercriticalPolarizationRegressionConfiguration.transmittedNormalRadicand = -16 := by
  rw [PlanarDielectricWaveConfiguration.transmittedNormalRadicand,
    show supercriticalPolarizationRegressionConfiguration.interface.plane =
        complexDecayRegressionPlane by rfl,
    show supercriticalPolarizationRegressionConfiguration.incident =
        supercriticalPolarizationRegressionIncident by rfl,
    supercriticalPolarizationRegression_incidentTangentialPhaseVector]
  norm_num [supercriticalPolarizationRegressionConfiguration,
    supercriticalPolarizationRegressionInterface, complexDecayRegressionMedium,
    supercriticalPolarizationRegressionIncident, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp; norm_num

/-- The positive-side regression wave speed is exactly `1 / 3`. -/
lemma supercriticalPolarizationRegression_positiveMedium_waveSpeed :
    supercriticalPolarizationRegressionConfiguration.interface.positiveMedium.waveSpeed =
      1 / 3 := by
  have hSqrt : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [supercriticalPolarizationRegressionConfiguration,
    supercriticalPolarizationRegressionInterface, complexDecayRegressionMedium,
    HomogeneousIsotropicMedium.waveSpeed, hSqrt]

private lemma supercriticalPolarizationRegression_sqrt_sixteen :
    Real.sqrt 16 = 4 := by
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

/-- The regression radicand is strictly negative. -/
lemma supercriticalPolarizationRegression_transmittedNormalRadicand_neg :
    supercriticalPolarizationRegressionConfiguration.transmittedNormalRadicand < 0 := by
  rw [supercriticalPolarizationRegression_transmittedNormalRadicand]
  norm_num

/-!

## B. Canonical frame and carrier recovery

-/

/-- The canonical negative-radicand transmitted vector is the exact `(5, 0, -4 I)` regression
vector. -/
lemma supercriticalPolarizationRegression_positiveNormalDecayTransmittedWaveVector :
    supercriticalPolarizationRegressionConfiguration.positiveNormalDecayTransmittedWaveVector =
      complexDecayRegressionWaveVector := by
  rw [positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation,
    supercriticalPolarizationRegression_transmittedNormalRadicand,
    complexDecayRegressionWaveVector_eq]
  simp only [neg_neg]
  rw [supercriticalPolarizationRegression_sqrt_sixteen]
  ext i
  fin_cases i <;>
    simp [supercriticalPolarizationRegressionConfiguration,
      supercriticalPolarizationRegressionInterface,
      supercriticalPolarizationRegressionIncident,
      supercriticalPolarizationRegressionIncidentWaveVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
      ComplexWaveVector.phaseVector,
      ComplexWaveVector.ofReal, ComplexWaveVector.realPart, ComplexWaveVector.ofPhaseAttenuation,
      PiLp.inner_apply, RCLike.inner_apply]
  all_goals ring

/-- The canonical frame has normalized normal component `-4 I / 3`. -/
lemma supercriticalPolarizationRegression_normalizedWaveVectorNormalComponent :
    PositiveNormalDecayPolarizationFrame.normalizedWaveVectorNormalComponent
        supercriticalPolarizationRegressionConfiguration.interface.plane
        (positiveNormalDecayTransmittedPolarizationFrame
          supercriticalPolarizationRegressionConfiguration
          supercriticalPolarizationRegression_transmittedNormalRadicand_neg) =
      -4 * Complex.I / 3 := by
  rw [positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent,
    supercriticalPolarizationRegression_transmittedNormalRadicand,
    supercriticalPolarizationRegression_positiveMedium_waveSpeed]
  simp only [neg_neg]
  rw [supercriticalPolarizationRegression_sqrt_sixteen]
  norm_num [supercriticalPolarizationRegressionConfiguration,
    supercriticalPolarizationRegressionIncident]
  ring

/-- The configuration-level negative-radicand frame is the independent exact `5-4-3` frame. -/
lemma supercriticalPolarizationRegression_polarizationFrame :
    PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalPolarizationRegressionConfiguration
        supercriticalPolarizationRegression_transmittedNormalRadicand_neg =
      complexDecayRegressionPolarizationFrame := by
  unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
  unfold complexDecayRegressionPolarizationFrame
  congr 1
  · unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedData
    unfold positiveNormalDecayRegression
    congr 1
    · exact supercriticalPolarizationRegression_incidentTangentialPhaseVector
    · rw [supercriticalPolarizationRegression_transmittedNormalRadicand]
      simp only [neg_neg]
      exact supercriticalPolarizationRegression_sqrt_sixteen
  · rw [supercriticalPolarizationRegression_positiveMedium_waveSpeed]
    norm_num [supercriticalPolarizationRegressionConfiguration,
      supercriticalPolarizationRegressionIncident]

/-- The configuration-level raw TM carrier selected by the exact negative radicand. -/
def supercriticalPolarizationRegressionCandidate : ComplexMonochromaticPlaneWave :=
  PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
    supercriticalPolarizationRegressionConfiguration
    supercriticalPolarizationRegression_transmittedNormalRadicand_neg
    complexDecayRegressionTMJones

/-- The configuration-level raw TM carrier is the independently defined exact TM regression
wave. -/
lemma supercriticalPolarizationRegression_candidate_eq_complexDecayRegressionTM :
    supercriticalPolarizationRegressionCandidate =
      complexDecayRegressionTM := by
  unfold supercriticalPolarizationRegressionCandidate
  unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
  unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedCandidate
  congr 1
  · exact supercriticalPolarizationRegression_positiveNormalDecayTransmittedWaveVector
  · rw [supercriticalPolarizationRegression_polarizationFrame]
    exact complexDecayRegressionPolarizationFrame_embedJones_TM

/-- The configuration-level TM carrier recovers the independently defined compatible
magnetic-induction amplitude `(0, 9 I, 0)`. -/
lemma supercriticalPolarizationRegression_magneticAmplitude :
    supercriticalPolarizationRegressionCandidate.magneticAmplitude =
      WithLp.toLp 2 ![(0 : ℂ), 9 * Complex.I, 0] := by
  rw [supercriticalPolarizationRegression_candidate_eq_complexDecayRegressionTM,
    complexDecayRegressionTM_magneticAmplitude]

/-- The exact tangential electric amplitude is `(4, 0, 0)`, fixing the sign of the converted
TM coordinate in the stored interface plane. -/
lemma supercriticalPolarizationRegression_tangentialElectricAmplitude :
    hyperplaneTangentialProjection
        supercriticalPolarizationRegressionConfiguration.interface.plane
        supercriticalPolarizationRegressionCandidate.electricAmplitude =
      WithLp.toLp 2 ![(4 : ℂ), 0, 0] := by
  unfold supercriticalPolarizationRegressionCandidate
  rw [positiveNormalDecayTransmittedJonesCandidate_tangentialElectricAmplitude,
    supercriticalPolarizationRegression_polarizationFrame]
  change complexDecayRegressionPolarizationFrame.planeFrame.embedJones
      (complexDecayRegressionPolarizationFrame.tangentialJones
        complexDecayRegressionPlane complexDecayRegressionTMJones) = _
  rw [← complexDecayRegressionPolarizationFrame.hyperplaneTangentialProjection_embedJones]
  exact complexDecayRegressionPolarizationFrame_tangentialProjection_embedJones_TM

/-- The positive-side regression impedance is one. -/
lemma supercriticalPolarizationRegression_positiveMedium_waveImpedance :
    supercriticalPolarizationRegressionConfiguration.interface.positiveMedium.waveImpedance =
      1 := by
  norm_num [supercriticalPolarizationRegressionConfiguration,
    supercriticalPolarizationRegressionInterface, complexDecayRegressionMedium,
    HomogeneousIsotropicMedium.waveImpedance]

/-- The exact tangential magnetic-field-strength amplitude is `(0, 3 I, 0)`, fixing both the
quarter-turn sign and the positive-side impedance factor. -/
lemma supercriticalPolarizationRegression_tangentialMagneticFieldStrengthAmplitude :
    mediumTangentialMagneticFieldStrengthAmplitude
        supercriticalPolarizationRegressionConfiguration.interface.plane
        supercriticalPolarizationRegressionConfiguration.interface.positiveMedium
        supercriticalPolarizationRegressionCandidate =
      WithLp.toLp 2 ![(0 : ℂ), 3 * Complex.I, 0] := by
  unfold supercriticalPolarizationRegressionCandidate
  rw [positiveNormalDecayTransmittedJonesCandidate_tangentialMagneticFieldStrengthAmplitude,
    supercriticalPolarizationRegression_polarizationFrame,
    supercriticalPolarizationRegression_positiveMedium_waveImpedance]
  change (((1 : ℝ)⁻¹ : ℝ) : ℂ) •
      complexDecayRegressionPolarizationFrame.planeFrame.embedJones
        (JonesVector.ofComponents (-complexDecayRegressionTMJones.components 1)
          (complexDecayRegressionPolarizationFrame.normalizedWaveVectorNormalComponent
            complexDecayRegressionPlane * complexDecayRegressionTMJones.components 0)) = _
  rw [inv_one, show ((1 : ℝ) : ℂ) = 1 by norm_num, one_smul]
  rw [← hyperplaneTangentialProjection_embedJones_propagationCross]
  exact
    complexDecayRegressionPolarizationFrame_tangentialProjection_embedJones_propagationCross_TM

/-!

## C. Maxwell and flux endpoints

-/

/-- The exact configuration-level TM carrier satisfies the source-free macroscopic Maxwell
equations in the positive-side medium. -/
lemma supercriticalPolarizationRegression_isMacroscopicMaxwellSolution :
    HomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution
        supercriticalPolarizationRegressionConfiguration.interface.positiveMedium
        supercriticalPolarizationRegressionCandidate.electricField
        (supercriticalPolarizationRegressionCandidate.electricDisplacement
          supercriticalPolarizationRegressionConfiguration.interface.positiveMedium)
        supercriticalPolarizationRegressionCandidate.magneticInduction
        (supercriticalPolarizationRegressionCandidate.magneticFieldStrength
          supercriticalPolarizationRegressionConfiguration.interface.positiveMedium) 0 0 := by
  unfold supercriticalPolarizationRegressionCandidate
  exact positiveNormalDecayTransmittedJonesCandidate_isMacroscopicMaxwellSolution
    supercriticalPolarizationRegressionConfiguration
    supercriticalPolarizationRegression_transmittedNormalRadicand_neg
    complexDecayRegressionTMJones

/-- The exact configuration-level TM carrier has zero one-period mean Poynting component along
the stored interface normal at every point and period start. -/
lemma supercriticalPolarizationRegression_normalMeanFlux_eq_zero
    (startTime : Time) (x : Space) :
    supercriticalPolarizationRegressionConfiguration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi /
          supercriticalPolarizationRegressionCandidate.angularFrequency,
        poyntingVector supercriticalPolarizationRegressionCandidate.electricField
          (supercriticalPolarizationRegressionCandidate.magneticFieldStrength
            supercriticalPolarizationRegressionConfiguration.interface.positiveMedium)
          (time : Time) x) = 0 :=
  positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero
    supercriticalPolarizationRegressionConfiguration
    supercriticalPolarizationRegression_transmittedNormalRadicand_neg
    complexDecayRegressionTMJones startTime x

/-!

## D. Nonzero affine reference point

-/

/-- The parallel regression plane shifted to first coordinate `pi / 10`. -/
def supercriticalPolarizationRegressionShiftedPlane : OrientedAffineHyperplane 3 where
  point := ⟨![Real.pi / 10, 0, 0]⟩
  normal := positiveNormalDecayRegressionDirection

/-- The negative-radicand interface with a nonzero stored affine point. -/
def supercriticalPolarizationRegressionShiftedInterface : PlanarDielectricInterface where
  plane := supercriticalPolarizationRegressionShiftedPlane
  negativeMedium := supercriticalPolarizationRegressionNegativeMedium
  positiveMedium := complexDecayRegressionMedium

/-- The shifted-point configuration retains the independent dummy transmitted slot. -/
def supercriticalPolarizationRegressionShiftedConfiguration :
    PlanarDielectricWaveConfiguration where
  interface := supercriticalPolarizationRegressionShiftedInterface
  incident := supercriticalPolarizationRegressionIncident
  reflected := supercriticalPolarizationRegressionReflected
  transmitted := supercriticalPolarizationRegressionDummyTransmitted

/-- Shifting the stored plane point does not change the exact negative transmitted radicand. -/
lemma supercriticalPolarizationRegressionShifted_transmittedNormalRadicand :
    supercriticalPolarizationRegressionShiftedConfiguration.transmittedNormalRadicand = -16 := by
  rw [PlanarDielectricWaveConfiguration.transmittedNormalRadicand]
  have hTangential :
      supercriticalPolarizationRegressionShiftedPlane.tangentialProjection
          supercriticalPolarizationRegressionIncident.waveVector.phaseVector =
        WithLp.toLp 2 ![(5 : ℝ), 0, 0] := by
    ext i
    fin_cases i <;>
      simp [supercriticalPolarizationRegressionShiftedPlane,
        supercriticalPolarizationRegressionIncident,
        supercriticalPolarizationRegressionIncidentWaveVector,
        positiveNormalDecayRegressionDirection,
        OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
        ComplexWaveVector.phaseVector, ComplexWaveVector.ofReal,
        ComplexWaveVector.realPart, PiLp.inner_apply, RCLike.inner_apply]
  rw [show supercriticalPolarizationRegressionShiftedConfiguration.interface.plane =
      supercriticalPolarizationRegressionShiftedPlane by rfl,
    show supercriticalPolarizationRegressionShiftedConfiguration.incident =
      supercriticalPolarizationRegressionIncident by rfl,
    hTangential]
  norm_num [supercriticalPolarizationRegressionShiftedConfiguration,
    supercriticalPolarizationRegressionShiftedInterface, complexDecayRegressionMedium,
    supercriticalPolarizationRegressionIncident, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Nat.ofNat_nonneg,
    Real.sq_sqrt]
  norm_num

/-- The shifted-point regression remains on the strict negative-radicand branch. -/
lemma supercriticalPolarizationRegressionShifted_transmittedNormalRadicand_neg :
    supercriticalPolarizationRegressionShiftedConfiguration.transmittedNormalRadicand < 0 := by
  rw [supercriticalPolarizationRegressionShifted_transmittedNormalRadicand]
  norm_num

/-- The shifted-point configuration constructs the same exact `(5, 0, -4 I)` wave vector. -/
lemma supercriticalPolarizationRegressionShifted_positiveNormalDecayTransmittedWaveVector :
    PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedWaveVector
        supercriticalPolarizationRegressionShiftedConfiguration =
      complexDecayRegressionWaveVector := by
  rw [positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation,
    supercriticalPolarizationRegressionShifted_transmittedNormalRadicand,
    complexDecayRegressionWaveVector_eq]
  simp only [neg_neg]
  rw [supercriticalPolarizationRegression_sqrt_sixteen]
  ext i
  fin_cases i <;>
    simp [supercriticalPolarizationRegressionShiftedConfiguration,
      supercriticalPolarizationRegressionShiftedInterface,
      supercriticalPolarizationRegressionShiftedPlane,
      supercriticalPolarizationRegressionIncident,
      supercriticalPolarizationRegressionIncidentWaveVector,
      positiveNormalDecayRegressionDirection,
      OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
      ComplexWaveVector.phaseVector, ComplexWaveVector.ofReal,
      ComplexWaveVector.realPart, ComplexWaveVector.ofPhaseAttenuation,
      PiLp.inner_apply, RCLike.inner_apply]
  all_goals ring

/-- At the shifted affine point, the canonical decay wave has spatial factor `-I`. -/
lemma supercriticalPolarizationRegressionShifted_spatialFactor :
    (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedWaveVector
      supercriticalPolarizationRegressionShiftedConfiguration).spatialFactor
        supercriticalPolarizationRegressionShiftedPlane.point = -Complex.I := by
  rw [supercriticalPolarizationRegressionShifted_positiveNormalDecayTransmittedWaveVector,
    complexDecayRegressionWaveVector_eq]
  norm_num [ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, supercriticalPolarizationRegressionShiftedPlane,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]
  rw [show -(Complex.I * (5 * ((Real.pi : ℂ) / 10))) =
    (-(Real.pi : ℂ) / 2) * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

/-- The plane-referenced transmitted Jones data includes the exact nontrivial stored-point phase
`-I`, rather than silently reusing the raw coordinate-origin amplitude. -/
lemma supercriticalPolarizationRegressionShifted_referencedJones (J : JonesVector) :
    PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones
        supercriticalPolarizationRegressionShiftedConfiguration J =
      JonesVector.scale (-Complex.I) J := by
  rw [PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones]
  change JonesVector.scale
      ((PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedWaveVector
        supercriticalPolarizationRegressionShiftedConfiguration).spatialFactor
          supercriticalPolarizationRegressionShiftedPlane.point) J = _
  rw [supercriticalPolarizationRegressionShifted_spatialFactor]

end

end Optics
