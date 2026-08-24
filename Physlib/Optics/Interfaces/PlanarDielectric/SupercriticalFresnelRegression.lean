/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundaryRegression
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnel
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalPolarizationRegression

/-!
# Exact complex Fresnel regression for total internal reflection

## i. Overview

This file tests the complex Fresnel API on an exact unequal-admittance total-internal-reflection
fixture. The interface is the origin plane with normal `+z`. At angular frequency one, the
negative-side medium has `epsilon = 50/9`, `mu = 25/2`, wave number `25/3`, and admittance `2/3`.
The positive-side medium has `epsilon = mu = 3`, wave number `3`, and admittance one.

The incident and reflected directions are the existing `(3/5, 0, ±4/5)` Jones-boundary
frames. Their wave vectors are `(5, 0, ±20/3)`. The transmitted tangential wave number is five,
so its canonical positive-normal-decay wave vector is the existing `(5, 0, -4 I)` fixture and its
normalized normal factor is `-4 I/3`.

For unit input in both Jones coordinates, the exact full-vector Fresnel coefficients are

```text
r_s = (-21 + 20 I)/29, t_s = (8 + 20 I)/29,
r_p = (-19 + 180 I)/181, t_p = (108 + 120 I)/181.
```

Both reflection coefficients have squared modulus one. Thus the reflected Jones vector has the
same intensity two as the incident Jones vector, while the complex transmitted coefficients are
not interpreted as a propagating power ratio.

## ii. Key results

- `supercriticalFresnelRegression_s_coefficients` and
  `supercriticalFresnelRegression_p_coefficients`: exact complex coefficient values.
- `supercriticalFresnelRegression_reflection_normSq`: both reflection coefficients have squared
  modulus one.
- `supercriticalFresnelRegression_reflectedJones_intensity`: exact preservation of the two-mode
  Jones intensity.
- `supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance` and
  `supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance`:
  independent witnesses for both complete referenced boundary balances.
- `supercriticalFresnelRegression_connected_components` and
  `supercriticalFresnelRegression_connected_reflectedJones_intensity`: the public connected
  solver recovers the simultaneous `s`/`p` data and its reflected-intensity consequence.

## iii. Table of contents

- A. Unequal-admittance interface
- B. Exact complex Fresnel coefficients
- C. Exact Jones amplitudes and intensity
- D. Connected positive-normal-decay configuration

## iv. References

The regression is derived from the imported Physlib complex Fresnel definitions and exact
polarization fixtures. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Matrix
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PlanarDielectricWaveConfiguration

noncomputable section

/-!

## A. Unequal-admittance interface

-/

/-- The negative-side medium with wave number `25/3` and admittance `2/3` at frequency one. -/
def supercriticalFresnelRegressionNegativeMedium : HomogeneousIsotropicMedium where
  ε := 50 / 9
  μ := 25 / 2
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The exact unequal-admittance interface on the existing origin plane. -/
def supercriticalFresnelRegressionInterface : PlanarDielectricInterface where
  plane := complexDecayRegressionPlane
  negativeMedium := supercriticalFresnelRegressionNegativeMedium
  positiveMedium := complexDecayRegressionMedium

/-- The negative-side wave speed is `3/25`. -/
lemma supercriticalFresnelRegression_negativeMedium_waveSpeed :
    supercriticalFresnelRegressionNegativeMedium.waveSpeed = 3 / 25 := by
  have hSqrt : Real.sqrt (625 / 9) = 25 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveSpeed,
    supercriticalFresnelRegressionNegativeMedium, hSqrt]

/-- The negative-side wave admittance is `2/3`. -/
lemma supercriticalFresnelRegression_negativeMedium_waveImpedance_inv :
    supercriticalFresnelRegressionNegativeMedium.waveImpedance⁻¹ = 2 / 3 := by
  have hSqrt : Real.sqrt (9 / 4) = 3 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveImpedance,
    supercriticalFresnelRegressionNegativeMedium, hSqrt]

/-- The positive-side wave admittance is one. -/
lemma supercriticalFresnelRegression_positiveMedium_waveImpedance_inv :
    complexDecayRegressionMedium.waveImpedance⁻¹ = 1 := by
  norm_num [HomogeneousIsotropicMedium.waveImpedance, complexDecayRegressionMedium]

/-!

## B. Exact complex Fresnel coefficients

-/

/-- The exact `s` reflection and transmission coefficients are
`(-21 + 20 I)/29` and `(8 + 20 I)/29`. -/
lemma supercriticalFresnelRegression_s_coefficients :
    supercriticalFresnelRegressionInterface.complexSFresnelReflectionCoefficient
        (4 / 5 : ℂ) (-4 * Complex.I / 3) = (-21 + 20 * Complex.I) / 29 ∧
      supercriticalFresnelRegressionInterface.complexSFresnelTransmissionCoefficient
        (4 / 5 : ℂ) (-4 * Complex.I / 3) = (8 + 20 * Complex.I) / 29 := by
  rw [PlanarDielectricInterface.complexSFresnelReflectionCoefficient,
    PlanarDielectricInterface.complexSFresnelTransmissionCoefficient,
    PlanarDielectricInterface.complexSFresnelDenominator]
  have hNegative :
      supercriticalFresnelRegressionInterface.negativeMedium.waveImpedance⁻¹ = 2 / 3 := by
    exact supercriticalFresnelRegression_negativeMedium_waveImpedance_inv
  have hPositive :
      supercriticalFresnelRegressionInterface.positiveMedium.waveImpedance⁻¹ = 1 := by
    exact supercriticalFresnelRegression_positiveMedium_waveImpedance_inv
  rw [hNegative, hPositive]
  change
    (((2 / 3 : ℝ) : ℂ) * (4 / 5) - ((1 : ℝ) : ℂ) * (-4 * Complex.I / 3)) /
          (((2 / 3 : ℝ) : ℂ) * (4 / 5) + ((1 : ℝ) : ℂ) * (-4 * Complex.I / 3)) =
        (-21 + 20 * Complex.I) / 29 ∧
      (2 * ((2 / 3 : ℝ) : ℂ) * (4 / 5)) /
          (((2 / 3 : ℝ) : ℂ) * (4 / 5) + ((1 : ℝ) : ℂ) * (-4 * Complex.I / 3)) =
        (8 + 20 * Complex.I) / 29
  constructor <;>
    norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

/-- The exact full-vector `p` reflection and transmission coefficients are
`(-19 + 180 I)/181` and `(108 + 120 I)/181`. -/
lemma supercriticalFresnelRegression_p_coefficients :
    supercriticalFresnelRegressionInterface.complexPFresnelReflectionCoefficient
        (4 / 5 : ℂ) (-4 * Complex.I / 3) = (-19 + 180 * Complex.I) / 181 ∧
      supercriticalFresnelRegressionInterface.complexPFresnelTransmissionCoefficient
        (4 / 5 : ℂ) (-4 * Complex.I / 3) = (108 + 120 * Complex.I) / 181 := by
  rw [PlanarDielectricInterface.complexPFresnelReflectionCoefficient,
    PlanarDielectricInterface.complexPFresnelTransmissionCoefficient,
    PlanarDielectricInterface.complexPFresnelDenominator]
  have hNegative :
      supercriticalFresnelRegressionInterface.negativeMedium.waveImpedance⁻¹ = 2 / 3 := by
    exact supercriticalFresnelRegression_negativeMedium_waveImpedance_inv
  have hPositive :
      supercriticalFresnelRegressionInterface.positiveMedium.waveImpedance⁻¹ = 1 := by
    exact supercriticalFresnelRegression_positiveMedium_waveImpedance_inv
  rw [hNegative, hPositive]
  change
    (((1 : ℝ) : ℂ) * (4 / 5) - ((2 / 3 : ℝ) : ℂ) * (-4 * Complex.I / 3)) /
          (((1 : ℝ) : ℂ) * (4 / 5) + ((2 / 3 : ℝ) : ℂ) * (-4 * Complex.I / 3)) =
        (-19 + 180 * Complex.I) / 181 ∧
      (2 * ((2 / 3 : ℝ) : ℂ) * (4 / 5)) /
          (((1 : ℝ) : ℂ) * (4 / 5) + ((2 / 3 : ℝ) : ℂ) * (-4 * Complex.I / 3)) =
        (108 + 120 * Complex.I) / 181
  constructor <;>
    norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

/-- Both exact reflection coefficients have squared modulus one. -/
lemma supercriticalFresnelRegression_reflection_normSq :
    Complex.normSq ((-21 + 20 * Complex.I) / 29) = 1 ∧
      Complex.normSq ((-19 + 180 * Complex.I) / 181) = 1 := by
  constructor <;> norm_num [Complex.normSq, Complex.div_re, Complex.div_im]

/-!

## C. Exact Jones amplitudes and intensity

-/

/-- The unit incident Jones data used for both polarizations. -/
def supercriticalFresnelRegressionIncidentJones : JonesVector :=
  JonesVector.ofComponents 1 1

/-- The exact total-internal-reflection Jones data. -/
def supercriticalFresnelRegressionReflectedJones : JonesVector :=
  JonesVector.ofComponents ((-21 + 20 * Complex.I) / 29)
    ((-19 + 180 * Complex.I) / 181)

/-- The exact transmitted full-vector Jones data in the complex decay frame. -/
def supercriticalFresnelRegressionTransmittedJones : JonesVector :=
  JonesVector.ofComponents ((8 + 20 * Complex.I) / 29)
    ((108 + 120 * Complex.I) / 181)

/-- The exact incident Jones intensity is two. -/
lemma supercriticalFresnelRegression_incidentJones_intensity :
    supercriticalFresnelRegressionIncidentJones.intensity = 2 := by
  simp [supercriticalFresnelRegressionIncidentJones, JonesVector.intensity_eq_sum_normSq,
    Fin.sum_univ_two, JonesVector.ofComponents, Complex.normSq]
  norm_num

/-- The exact reflected Jones intensity is also two. -/
lemma supercriticalFresnelRegression_reflectedJones_intensity :
    supercriticalFresnelRegressionReflectedJones.intensity = 2 := by
  rw [JonesVector.intensity_eq_sum_normSq, Fin.sum_univ_two]
  simp only [supercriticalFresnelRegressionReflectedJones, JonesVector.ofComponents_zero,
    JonesVector.ofComponents_one]
  rw [supercriticalFresnelRegression_reflection_normSq.1,
    supercriticalFresnelRegression_reflection_normSq.2]
  norm_num

/-!

## D. Connected positive-normal-decay configuration

-/

/-- The incident material carrier with wave vector `(5, 0, 20/3)`. -/
def supercriticalFresnelRegressionIncidentWave : ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    (supercriticalFresnelRegressionIncidentJones.toMaterialPlaneWave
      supercriticalFresnelRegressionNegativeMedium jonesBoundaryRegressionIncidentFrame 1
        (by norm_num))

/-- The reflected material carrier with wave vector `(5, 0, -20/3)`. -/
def supercriticalFresnelRegressionReflectedWave : ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    (supercriticalFresnelRegressionReflectedJones.toMaterialPlaneWave
      supercriticalFresnelRegressionNegativeMedium jonesBoundaryRegressionReflectedFrame 1
        (by norm_num))

/-- An auxiliary configuration whose transmitted slot is deliberately unrelated to the
canonical positive-normal-decay carrier. -/
def supercriticalFresnelRegressionBaseConfiguration : PlanarDielectricWaveConfiguration where
  interface := supercriticalFresnelRegressionInterface
  incident := supercriticalFresnelRegressionIncidentWave
  reflected := supercriticalFresnelRegressionReflectedWave
  transmitted := supercriticalPolarizationRegressionDummyTransmitted

/-- The material constructor gives the exact incident wave vector `(5, 0, 20/3)`. -/
lemma supercriticalFresnelRegression_incidentWave_waveVector :
    supercriticalFresnelRegressionIncidentWave.waveVector =
      ComplexWaveVector.ofReal (WithLp.toLp 2 ![(5 : ℝ), 0, 20 / 3]) := by
  rw [supercriticalFresnelRegressionIncidentWave,
    supercriticalFresnelRegressionIncidentJones.ofReal_toMaterialPlaneWave_waveVector,
    supercriticalFresnelRegression_negativeMedium_waveSpeed]
  ext i
  fin_cases i <;>
    norm_num [jonesBoundaryRegressionIncidentFrame, PolarizationFrame.propagationVector,
      jonesBoundaryRegressionIncidentDirection, ComplexWaveVector.ofReal]

/-- The material constructor gives the exact reflected wave vector `(5, 0, -20/3)`. -/
lemma supercriticalFresnelRegression_reflectedWave_waveVector :
    supercriticalFresnelRegressionReflectedWave.waveVector =
      ComplexWaveVector.ofReal (WithLp.toLp 2 ![(5 : ℝ), 0, -20 / 3]) := by
  rw [supercriticalFresnelRegressionReflectedWave,
    supercriticalFresnelRegressionReflectedJones.ofReal_toMaterialPlaneWave_waveVector,
    supercriticalFresnelRegression_negativeMedium_waveSpeed]
  ext i
  fin_cases i <;>
    norm_num [jonesBoundaryRegressionReflectedFrame, PolarizationFrame.propagationVector,
      jonesBoundaryRegressionReflectedDirection, ComplexWaveVector.ofReal]

/-- The exact incident tangential phase vector is `(5, 0, 0)`. -/
lemma supercriticalFresnelRegression_incidentTangentialPhaseVector :
    complexDecayRegressionPlane.tangentialProjection
        supercriticalFresnelRegressionIncidentWave.waveVector.phaseVector =
      WithLp.toLp 2 ![(5 : ℝ), 0, 0] := by
  rw [supercriticalFresnelRegression_incidentWave_waveVector]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
      ComplexWaveVector.phaseVector, ComplexWaveVector.ofReal,
      ComplexWaveVector.realPart, PiLp.inner_apply, RCLike.inner_apply,
      Matrix.cons_val_two, Matrix.head_cons]

/-- The unequal-admittance configuration has exact transmitted normal radicand `-16`. -/
lemma supercriticalFresnelRegression_transmittedNormalRadicand :
    supercriticalFresnelRegressionBaseConfiguration.transmittedNormalRadicand = -16 := by
  rw [PlanarDielectricWaveConfiguration.transmittedNormalRadicand,
    show supercriticalFresnelRegressionBaseConfiguration.interface.plane =
        complexDecayRegressionPlane by rfl,
    show supercriticalFresnelRegressionBaseConfiguration.incident =
        supercriticalFresnelRegressionIncidentWave by rfl,
    supercriticalFresnelRegression_incidentTangentialPhaseVector]
  norm_num [supercriticalFresnelRegressionBaseConfiguration,
    supercriticalFresnelRegressionInterface, complexDecayRegressionMedium,
    supercriticalFresnelRegressionIncidentWave, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Nat.ofNat_nonneg,
    Real.sq_sqrt]
  norm_num

/-- The exact transmitted normal radicand is strictly negative. -/
lemma supercriticalFresnelRegression_transmittedNormalRadicand_neg :
    supercriticalFresnelRegressionBaseConfiguration.transmittedNormalRadicand < 0 := by
  rw [supercriticalFresnelRegression_transmittedNormalRadicand]
  norm_num

/-- The positive-side wave speed is `1/3`. -/
lemma supercriticalFresnelRegression_positiveMedium_waveSpeed :
    supercriticalFresnelRegressionBaseConfiguration.interface.positiveMedium.waveSpeed =
      1 / 3 := by
  exact supercriticalPolarizationRegression_positiveMedium_waveSpeed

/-- The canonical complex transmitted frame is the independent exact `5-4-3` decay frame. -/
lemma supercriticalFresnelRegression_polarizationFrame :
    supercriticalFresnelRegressionBaseConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegression_transmittedNormalRadicand_neg =
      complexDecayRegressionPolarizationFrame := by
  unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
  unfold complexDecayRegressionPolarizationFrame
  congr 1
  · unfold PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedData
    unfold positiveNormalDecayRegression
    congr 1
    · exact supercriticalFresnelRegression_incidentTangentialPhaseVector
    · rw [supercriticalFresnelRegression_transmittedNormalRadicand]
      simp only [neg_neg]
      have hSqrt : Real.sqrt 16 = 4 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      exact hSqrt
  · rw [supercriticalFresnelRegression_positiveMedium_waveSpeed]
    norm_num [supercriticalFresnelRegressionBaseConfiguration,
      supercriticalFresnelRegressionIncidentWave]

/-- The exact canonical normalized transmitted normal factor is `-4 I/3`. -/
lemma supercriticalFresnelRegression_normalizedWaveVectorNormalComponent :
    PositiveNormalDecayPolarizationFrame.normalizedWaveVectorNormalComponent
        complexDecayRegressionPlane
        (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegressionBaseConfiguration
          supercriticalFresnelRegression_transmittedNormalRadicand_neg) =
      -4 * Complex.I / 3 := by
  rw [supercriticalFresnelRegression_polarizationFrame]
  exact complexDecayRegressionPolarizationFrame_normalizedWaveVectorNormalComponent

/-- The exact canonical positive-normal-decay transmitted carrier. -/
def supercriticalFresnelRegressionTransmittedWave : ComplexMonochromaticPlaneWave :=
  PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
    supercriticalFresnelRegressionBaseConfiguration
    supercriticalFresnelRegression_transmittedNormalRadicand_neg
    supercriticalFresnelRegressionTransmittedJones

/-- The connected interface configuration containing all three exact carriers. -/
def supercriticalFresnelRegressionConfiguration : PlanarDielectricWaveConfiguration where
  interface := supercriticalFresnelRegressionInterface
  incident := supercriticalFresnelRegressionIncidentWave
  reflected := supercriticalFresnelRegressionReflectedWave
  transmitted := supercriticalFresnelRegressionTransmittedWave

/-- Replacing the auxiliary transmitted slot does not change the exact radicand. -/
lemma supercriticalFresnelRegression_configuration_transmittedNormalRadicand :
    supercriticalFresnelRegressionConfiguration.transmittedNormalRadicand = -16 :=
  supercriticalFresnelRegression_transmittedNormalRadicand

/-- The connected configuration remains in the strict supercritical regime. -/
lemma supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg :
    supercriticalFresnelRegressionConfiguration.transmittedNormalRadicand < 0 := by
  rw [supercriticalFresnelRegression_configuration_transmittedNormalRadicand]
  norm_num

/-- The connected configuration selects the same independent exact complex decay frame. -/
lemma supercriticalFresnelRegression_configuration_polarizationFrame :
    supercriticalFresnelRegressionConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg =
      complexDecayRegressionPolarizationFrame :=
  supercriticalFresnelRegression_polarizationFrame

/-- The connected configuration has exact normalized transmitted normal factor `-4 I/3`. -/
lemma supercriticalFresnelRegression_configuration_normalizedWaveVectorNormalComponent :
    PositiveNormalDecayPolarizationFrame.normalizedWaveVectorNormalComponent
        supercriticalFresnelRegressionConfiguration.interface.plane
        (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegressionConfiguration
          supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg) =
      -4 * Complex.I / 3 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact complexDecayRegressionPolarizationFrame_normalizedWaveVectorNormalComponent

/-- The stored transmitted carrier is exactly the canonical carrier selected from the connected
configuration itself. -/
lemma supercriticalFresnelRegression_transmitted_eq_candidate :
    supercriticalFresnelRegressionConfiguration.transmitted =
      PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
        supercriticalFresnelRegressionTransmittedJones := by
  rfl

/-- Referencing at the origin leaves the raw transmitted Jones coordinates unchanged. -/
lemma supercriticalFresnelRegression_transmittedReferencedJones :
    PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegressionTransmittedJones =
      supercriticalFresnelRegressionTransmittedJones := by
  ext i
  simp [PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones,
    supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface, complexDecayRegressionPlane,
    JonesVector.scale, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot]

/-- The origin-referenced incident carrier is represented by the supplied unit Jones data. -/
lemma supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave :
    IsReferencedMaterialJonesWave complexDecayRegressionPlane
      supercriticalFresnelRegressionNegativeMedium
      supercriticalFresnelRegressionIncidentWave jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
  have h := JonesVector.isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
    supercriticalFresnelRegressionIncidentJones complexDecayRegressionPlane
      supercriticalFresnelRegressionNegativeMedium jonesBoundaryRegressionIncidentFrame 1
        (by norm_num)
  simpa [supercriticalFresnelRegressionIncidentWave, complexDecayRegressionPlane,
    JonesVector.scale, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot] using h

/-- The origin-referenced reflected carrier is represented by the exact reflected Jones data. -/
lemma supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave :
    IsReferencedMaterialJonesWave complexDecayRegressionPlane
      supercriticalFresnelRegressionNegativeMedium
      supercriticalFresnelRegressionReflectedWave jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
  have h := JonesVector.isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
    supercriticalFresnelRegressionReflectedJones complexDecayRegressionPlane
      supercriticalFresnelRegressionNegativeMedium jonesBoundaryRegressionReflectedFrame 1
        (by norm_num)
  simpa [supercriticalFresnelRegressionReflectedWave, complexDecayRegressionPlane,
    JonesVector.scale, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot] using h

private lemma supercriticalFresnelRegression_planeFrame_axis_zero :
    jonesBoundaryRegressionAxisZero =
      complexDecayRegressionPolarizationFrame.planeFrame.axis 0 := by
  rw [PositiveNormalDecayPolarizationFrame.planeFrame_axis_zero]
  symm
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayPolarizationFrame.realSAxis,
      complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression,
      positiveNormalDecayRegressionTangentialVector,
      PositiveNormalDecayWaveVector.normalVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      jonesBoundaryRegressionAxisZero, NormedSpace.normalize,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, crossProduct]

private lemma supercriticalFresnelRegression_incidentFrame_align :
    jonesBoundaryRegressionIncidentFrame.axis 0 =
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact supercriticalFresnelRegression_planeFrame_axis_zero

private lemma supercriticalFresnelRegression_reflectedFrame_align :
    jonesBoundaryRegressionReflectedFrame.axis 0 =
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact supercriticalFresnelRegression_planeFrame_axis_zero

/-- The exact incident signed normal component is `4/5`. -/
lemma supercriticalFresnelRegression_incidentNormalComponent :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
        jonesBoundaryRegressionIncidentFrame.propagationVector = 4 / 5 := by
  change inner ℝ
    (Space.basis.repr positiveNormalDecayRegressionDirection.unit)
    (Space.basis.repr jonesBoundaryRegressionIncidentDirection.unit) = 4 / 5
  norm_num [positiveNormalDecayRegressionDirection,
    jonesBoundaryRegressionIncidentDirection, Space.basis_repr_apply,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    Matrix.cons_val_two, Matrix.head_cons]

/-- The exact reflected signed normal component is `-4/5`. -/
lemma supercriticalFresnelRegression_reflectedNormalComponent :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
        jonesBoundaryRegressionReflectedFrame.propagationVector = -4 / 5 := by
  change inner ℝ
    (Space.basis.repr positiveNormalDecayRegressionDirection.unit)
    (Space.basis.repr jonesBoundaryRegressionReflectedDirection.unit) = -4 / 5
  norm_num [positiveNormalDecayRegressionDirection,
    jonesBoundaryRegressionReflectedDirection, Space.basis_repr_apply,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    Matrix.cons_val_two, Matrix.head_cons]

private lemma supercriticalFresnelRegression_incidentFrame_normalElectricComponent
    (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent
        supercriticalFresnelRegressionConfiguration.interface.plane
        (jonesBoundaryRegressionIncidentFrame.embedJones J) =
      (3 / 5 : ℂ) * J.components 1 := by
  norm_num [ComplexWaveVector.hyperplaneNormalComponent,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    supercriticalFresnelRegressionConfiguration, supercriticalFresnelRegressionInterface,
    complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
    jonesBoundaryRegressionIncidentFrame, jonesBoundaryRegressionIncidentDirection,
    jonesBoundaryRegressionAxisZero, PolarizationFrame.ofAxisZero,
    PolarizationFrame.embedJones, PolarizationFrame.complexAxis,
    OrientedAffineHyperplane.normalVector, Space.basis_repr_apply, crossProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Complex.ofReal_zero, zero_mul, neg_zero,
    add_zero, zero_add]
  ring

private lemma supercriticalFresnelRegression_reflectedFrame_normalElectricComponent
    (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent
        supercriticalFresnelRegressionConfiguration.interface.plane
        (jonesBoundaryRegressionReflectedFrame.embedJones J) =
      (3 / 5 : ℂ) * J.components 1 := by
  norm_num [ComplexWaveVector.hyperplaneNormalComponent,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    supercriticalFresnelRegressionConfiguration, supercriticalFresnelRegressionInterface,
    complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
    jonesBoundaryRegressionReflectedFrame, jonesBoundaryRegressionReflectedDirection,
    jonesBoundaryRegressionAxisZero, PolarizationFrame.ofAxisZero,
    PolarizationFrame.embedJones, PolarizationFrame.complexAxis,
    OrientedAffineHyperplane.normalVector, Space.basis_repr_apply, crossProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Complex.ofReal_zero, zero_mul, add_zero,
    zero_add]
  ring

private lemma supercriticalFresnelRegression_decayFrame_normalElectricComponent
    (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent complexDecayRegressionPlane
        (complexDecayRegressionPolarizationFrame.embedJones J) =
      (5 / 3 : ℂ) * J.components 1 := by
  rw [PositiveNormalDecayPolarizationFrame.embedJones_eq,
    ComplexWaveVector.hyperplaneNormalComponent,
    ComplexWaveVector.bilinearDot_add_right,
    ComplexWaveVector.bilinearDot_smul_right,
    ComplexWaveVector.bilinearDot_smul_right]
  rw [← ComplexWaveVector.hyperplaneNormalComponent,
    complexDecayRegressionPolarizationFrame.hyperplaneNormalComponent_sAxis,
    ← ComplexWaveVector.hyperplaneNormalComponent,
    complexDecayRegressionPolarizationFrame.hyperplaneNormalComponent_pAxis]
  have hNorm :
      ‖positiveNormalDecayRegressionTangentialVector 5‖ = 5 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [positiveNormalDecayRegressionTangentialVector, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons]
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  simp only [complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression]
  rw [hNorm]
  norm_num
  ring

private lemma supercriticalFresnelRegression_configurationFrame_normalElectricComponent
    (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent
        supercriticalFresnelRegressionConfiguration.interface.plane
        ((PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegressionConfiguration
          supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).embedJones
            J) =
      (5 / 3 : ℂ) * J.components 1 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact supercriticalFresnelRegression_decayFrame_normalElectricComponent J

/-- The referenced normal electric-displacement amplitude of the exact decay carrier is five
times its full-vector `p` Jones coordinate. -/
lemma supercriticalFresnelRegression_transmitted_referencedNormalDisplacementAmplitude :
    (referencedMediumJointElectricTraceAmplitude
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.positiveMedium
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
        supercriticalFresnelRegressionTransmittedJones)).2 =
      (5 : ℂ) * supercriticalFresnelRegressionTransmittedJones.components 1 := by
  rw [referencedMediumJointElectricTraceAmplitude, mediumJointElectricTraceAmplitude]
  simp only [Prod.smul_snd]
  change
    (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
      supercriticalFresnelRegressionConfiguration
      supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
      supercriticalFresnelRegressionTransmittedJones).waveVector.spatialFactor 0 •
        ((3 : ℂ) * ComplexWaveVector.hyperplaneNormalComponent
          supercriticalFresnelRegressionConfiguration.interface.plane
          (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate
            supercriticalFresnelRegressionConfiguration
            supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
            supercriticalFresnelRegressionTransmittedJones).electricAmplitude) =
      (5 : ℂ) * supercriticalFresnelRegressionTransmittedJones.components 1
  rw [positiveNormalDecayTransmittedJonesCandidate_electricAmplitude,
    supercriticalFresnelRegression_configurationFrame_normalElectricComponent]
  simp [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface, complexDecayRegressionPlane,
    complexDecayRegressionMedium, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot]
  ring

private lemma supercriticalFresnelRegression_configuration_positiveMedium_waveImpedance_inv :
    supercriticalFresnelRegressionConfiguration.interface.positiveMedium.waveImpedance⁻¹ =
      1 :=
  supercriticalFresnelRegression_positiveMedium_waveImpedance_inv

private lemma supercriticalFresnelRegression_configuration_negativeMedium_waveImpedance_inv :
    supercriticalFresnelRegressionConfiguration.interface.negativeMedium.waveImpedance⁻¹ =
      2 / 3 :=
  supercriticalFresnelRegression_negativeMedium_waveImpedance_inv

private lemma supercriticalFresnelRegression_configuration_s_coefficients :
    supercriticalFresnelRegressionConfiguration.interface.complexSFresnelReflectionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (-21 + 20 * Complex.I) / 29 ∧
      supercriticalFresnelRegressionConfiguration.interface.complexSFresnelTransmissionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (8 + 20 * Complex.I) / 29 := by
  change supercriticalFresnelRegressionInterface.complexSFresnelReflectionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (-21 + 20 * Complex.I) / 29 ∧
      supercriticalFresnelRegressionInterface.complexSFresnelTransmissionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (8 + 20 * Complex.I) / 29
  convert supercriticalFresnelRegression_s_coefficients using 1 <;> norm_num

private lemma supercriticalFresnelRegression_configuration_p_coefficients :
    supercriticalFresnelRegressionConfiguration.interface.complexPFresnelReflectionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (-19 + 180 * Complex.I) / 181 ∧
      supercriticalFresnelRegressionConfiguration.interface.complexPFresnelTransmissionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (108 + 120 * Complex.I) / 181 := by
  change supercriticalFresnelRegressionInterface.complexPFresnelReflectionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (-19 + 180 * Complex.I) / 181 ∧
      supercriticalFresnelRegressionInterface.complexPFresnelTransmissionCoefficient
        (((4 / 5 : ℝ) : ℂ)) (-4 * Complex.I / 3) =
        (108 + 120 * Complex.I) / 181
  convert supercriticalFresnelRegression_p_coefficients using 1 <;> norm_num

/-- The exact three-wave tuple satisfies the complete referenced tangential-electric and normal
electric-displacement balance. -/
lemma supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance :
    supercriticalFresnelRegressionConfiguration.HasReferencedJointElectricBalance := by
  have hIncident : IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.incident jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave
  have hReflected : IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave
  change referencedMediumJointElectricTraceAmplitude
        supercriticalFresnelRegressionConfiguration.interface.plane
        supercriticalFresnelRegressionConfiguration.interface.positiveMedium
        supercriticalFresnelRegressionConfiguration.transmitted =
      referencedMediumJointElectricTraceAmplitude
          supercriticalFresnelRegressionConfiguration.interface.plane
          supercriticalFresnelRegressionConfiguration.interface.negativeMedium
          supercriticalFresnelRegressionConfiguration.incident +
        referencedMediumJointElectricTraceAmplitude
          supercriticalFresnelRegressionConfiguration.interface.plane
          supercriticalFresnelRegressionConfiguration.interface.negativeMedium
          supercriticalFresnelRegressionConfiguration.reflected
  rw [supercriticalFresnelRegression_transmitted_eq_candidate]
  apply Prod.ext
  · simp only [Prod.fst_add]
    rw [positiveNormalDecayTransmittedJonesCandidate_referencedTangentialElectricAmplitude,
      hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
        (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegressionConfiguration
          supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame
            supercriticalFresnelRegression_incidentFrame_align,
      hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
        (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
          supercriticalFresnelRegressionConfiguration
          supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame
            supercriticalFresnelRegression_reflectedFrame_align,
      supercriticalFresnelRegression_transmittedReferencedJones]
    simp only [PositiveNormalDecayPolarizationFrame.tangentialJones]
    rw [supercriticalFresnelRegression_configuration_normalizedWaveVectorNormalComponent,
      supercriticalFresnelRegression_incidentNormalComponent,
      supercriticalFresnelRegression_reflectedNormalComponent]
    ext k
    fin_cases k <;>
      simp [supercriticalFresnelRegressionIncidentJones,
        supercriticalFresnelRegressionReflectedJones,
        supercriticalFresnelRegressionTransmittedJones,
        PolarizationFrame.embedJones]
    all_goals ring_nf
    all_goals rw [Complex.I_sq]
    all_goals ring
  · simp only [Prod.snd_add]
    rw [supercriticalFresnelRegression_transmitted_referencedNormalDisplacementAmplitude,
      hIncident.referencedMediumJointElectricTraceAmplitude_snd,
      hReflected.referencedMediumJointElectricTraceAmplitude_snd,
      supercriticalFresnelRegression_incidentFrame_normalElectricComponent,
      supercriticalFresnelRegression_reflectedFrame_normalElectricComponent]
    rw [show supercriticalFresnelRegressionConfiguration.interface.negativeMedium.ε =
      50 / 9 by rfl]
    norm_num [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface,
      supercriticalFresnelRegressionNegativeMedium,
      supercriticalFresnelRegressionIncidentJones,
      supercriticalFresnelRegressionReflectedJones,
      supercriticalFresnelRegressionTransmittedJones]
    ring

/-- The exact three-wave tuple satisfies the referenced tangential magnetic-field-strength
balance. -/
lemma supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance :
    PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      supercriticalFresnelRegressionConfiguration := by
  have hIncident : IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.incident jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave
  have hReflected : IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave
  change referencedMediumTangentialMagneticFieldStrengthAmplitude
        supercriticalFresnelRegressionConfiguration.interface.plane
        supercriticalFresnelRegressionConfiguration.interface.positiveMedium
        supercriticalFresnelRegressionConfiguration.transmitted =
      referencedMediumTangentialMagneticFieldStrengthAmplitude
          supercriticalFresnelRegressionConfiguration.interface.plane
          supercriticalFresnelRegressionConfiguration.interface.negativeMedium
          supercriticalFresnelRegressionConfiguration.incident +
        referencedMediumTangentialMagneticFieldStrengthAmplitude
          supercriticalFresnelRegressionConfiguration.interface.plane
          supercriticalFresnelRegressionConfiguration.interface.negativeMedium
          supercriticalFresnelRegressionConfiguration.reflected
  rw [supercriticalFresnelRegression_transmitted_eq_candidate,
    positiveNormalDecayTransmittedJonesCandidate_referencedTangentialMagneticFieldStrengthAmplitude,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame
          supercriticalFresnelRegression_incidentFrame_align,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame
          supercriticalFresnelRegression_reflectedFrame_align,
    supercriticalFresnelRegression_transmittedReferencedJones,
    supercriticalFresnelRegression_configuration_normalizedWaveVectorNormalComponent,
    supercriticalFresnelRegression_incidentNormalComponent,
    supercriticalFresnelRegression_reflectedNormalComponent,
    supercriticalFresnelRegression_configuration_positiveMedium_waveImpedance_inv,
    supercriticalFresnelRegression_configuration_negativeMedium_waveImpedance_inv]
  ext k
  fin_cases k <;>
    simp [supercriticalFresnelRegressionIncidentJones,
      supercriticalFresnelRegressionReflectedJones,
      supercriticalFresnelRegressionTransmittedJones,
      PolarizationFrame.embedJones]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

private lemma supercriticalFresnelRegression_configuration_incidentConnector :
    IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.incident jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
  simpa only [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface] using
      supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave

private lemma supercriticalFresnelRegression_configuration_reflectedConnector :
    IsZeroOrReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
  exact Or.inr (by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave)

private lemma supercriticalFresnelRegression_reflection_guard :
    supercriticalFresnelRegressionConfiguration.reflected.electricAmplitude = 0 ∨
      supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionReflectedFrame.propagationVector =
        -supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionIncidentFrame.propagationVector := by
  right
  rw [supercriticalFresnelRegression_reflectedNormalComponent,
    supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

private lemma supercriticalFresnelRegression_incidentNormalComponent_pos :
    0 < supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      jonesBoundaryRegressionIncidentFrame.propagationVector := by
  rw [supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

/-- The connected electric and magnetic boundary solver recovers all four exact complex Fresnel
component values from one simultaneous two-component Jones wave. -/
lemma supercriticalFresnelRegression_connected_components :
    supercriticalFresnelRegressionReflectedJones.components 0 =
        (-21 + 20 * Complex.I) / 29 ∧
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegressionTransmittedJones).components 0 =
        (8 + 20 * Complex.I) / 29 ∧
      supercriticalFresnelRegressionReflectedJones.components 1 =
        (-19 + 180 * Complex.I) / 181 ∧
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedReferencedJones
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegressionTransmittedJones).components 1 =
        (108 + 120 * Complex.I) / 181 := by
  have hSolved :=
    PlanarDielectricWaveConfiguration.complexFresnel_components_of_referenced_balances
        (configuration := supercriticalFresnelRegressionConfiguration)
        supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance
        supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
        supercriticalFresnelRegression_configuration_incidentConnector
        supercriticalFresnelRegression_configuration_reflectedConnector
        supercriticalFresnelRegression_transmitted_eq_candidate
        supercriticalFresnelRegression_incidentFrame_align
        (fun _ ↦ supercriticalFresnelRegression_reflectedFrame_align)
        supercriticalFresnelRegression_reflection_guard
        supercriticalFresnelRegression_incidentNormalComponent_pos
  rw [supercriticalFresnelRegression_incidentNormalComponent,
    supercriticalFresnelRegression_configuration_normalizedWaveVectorNormalComponent,
    supercriticalFresnelRegression_configuration_s_coefficients.1,
    supercriticalFresnelRegression_configuration_s_coefficients.2,
    supercriticalFresnelRegression_configuration_p_coefficients.1,
    supercriticalFresnelRegression_configuration_p_coefficients.2] at hSolved
  simpa [supercriticalFresnelRegressionIncidentJones,
    supercriticalFresnelRegressionReflectedJones,
    supercriticalFresnelRegressionTransmittedJones] using hSolved

/-- The connected total-internal-reflection theorem preserves the exact two-mode Jones intensity
between the incident and reflected material waves. -/
lemma supercriticalFresnelRegression_connected_reflectedJones_intensity :
    supercriticalFresnelRegressionReflectedJones.intensity =
      supercriticalFresnelRegressionIncidentJones.intensity := by
  exact
    complexFresnel_reflectedJones_intensity_eq_of_referenced_balances
      (configuration := supercriticalFresnelRegressionConfiguration)
      supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance
      supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
      supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
      supercriticalFresnelRegression_configuration_incidentConnector
      supercriticalFresnelRegression_configuration_reflectedConnector
      supercriticalFresnelRegression_transmitted_eq_candidate
      supercriticalFresnelRegression_incidentFrame_align
      (fun _ ↦ supercriticalFresnelRegression_reflectedFrame_align)
      supercriticalFresnelRegression_reflection_guard
      supercriticalFresnelRegression_incidentNormalComponent_pos

end

end Optics
