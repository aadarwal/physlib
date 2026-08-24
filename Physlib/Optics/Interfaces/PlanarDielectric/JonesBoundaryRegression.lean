/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundary

/-!
# Exact Jones boundary-equation regression

## i. Overview

This file checks the plane-referenced material Jones connector and the four scalar Jones boundary
equations on one exact propagating fixture. The stored interface point is `(pi / 6, 0, 0)`, the
normal is `(0, 0, 1)`, and every wave has tangential wave-vector component `3`. Consequently the
stored-point spatial factor is `-I`, not one. Multiplying each origin-referenced Jones amplitude
by `I` makes its plane-referenced Jones data equal the supplied amplitude.

The incident, reflected, and transmitted unit directions are respectively
`(3/5, 0, 4/5)`, `(3/5, 0, -4/5)`, and `(4/5, 0, 3/5)`. Their signed normal components are
`4/5`, `-4/5`, and `3/5`. The two media have inverse impedance values `5/2` and `5/4`. A
simultaneous unit input in both Jones coordinates gives the following unique solution of the
complete referenced joint electric and tangential magnetic equalities:

```text
r_s = 5/11, t_s = 16/11, r_p = -1/5, t_p = 8/5.
```

The coefficients multiply full-vector electric Jones axes. The result is an exact regression for
one supplied reduced boundary problem, not a general Fresnel formula. It does not construct a
primitive time-domain boundary or infer the reduced equalities from a primitive boundary law.

## ii. Key results

- `jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave` and the corresponding
  reflected and transmitted results: the material connector keeps the nonzero stored-point phase.
- `jonesBoundaryRegression_electric_component_zero` through
  `jonesBoundaryRegression_magnetic_component_one`: the four exact scalar equations.
- `jonesBoundaryRegression_exact_hasReferencedJointElectricBalance` and
  `jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance`: the exact
  tuple satisfies both complete reduced vector equalities, including normal electric displacement.
- `jonesBoundaryRegression_coefficients_of_balances`: any tuple satisfying both equalities has the
  stated coefficients.
- `jonesBoundaryRegression_existsUnique_coefficients`: existence and uniqueness of the stated
  coefficient tuple.

## iii. Table of contents

- A. Exact geometry and material data
- B. Nonzero stored-point phase and connected waves
- C. Balance witnesses, four boundary equations, and their exact solution

## iv. References

The regression is derived entirely from the imported Physlib planar-frame, referenced material
wave, and Jones boundary-equation APIs. No external formal development is copied or translated
here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Matrix
  InnerProductSpace
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PlanarDielectricWaveConfiguration

noncomputable section

/-!

## A. Exact geometry and material data

-/

/-- The positive third-coordinate normal of the Jones boundary regression. -/
def jonesBoundaryRegressionNormal : Space.Direction 3 where
  unit := ⟨![0, 0, 1]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]

/-- The nonzero stored point and oriented plane of the Jones boundary regression. -/
def jonesBoundaryRegressionPlane : OrientedAffineHyperplane 3 where
  point := ⟨![Real.pi / 6, 0, 0]⟩
  normal := jonesBoundaryRegressionNormal

/-- The common second-coordinate transverse axis of all regression frames. -/
def jonesBoundaryRegressionAxisZero : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, 1, 0]

/-- The incident unit direction `(3/5, 0, 4/5)`. -/
def jonesBoundaryRegressionIncidentDirection : Space.Direction 3 where
  unit := ⟨![3 / 5, 0, 4 / 5]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]
    norm_num

/-- The reflected unit direction `(3/5, 0, -4/5)`. -/
def jonesBoundaryRegressionReflectedDirection : Space.Direction 3 where
  unit := ⟨![3 / 5, 0, -4 / 5]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]
    norm_num

/-- The transmitted unit direction `(4/5, 0, 3/5)`. -/
def jonesBoundaryRegressionTransmittedDirection : Space.Direction 3 where
  unit := ⟨![4 / 5, 0, 3 / 5]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]
    norm_num

/-- The common first frame axis has unit norm. -/
lemma jonesBoundaryRegressionAxisZero_norm :
    ‖jonesBoundaryRegressionAxisZero‖ = 1 := by
  simp [jonesBoundaryRegressionAxisZero, EuclideanSpace.norm_eq, Fin.sum_univ_three]

/-- The common first frame axis is transverse to the plane normal. -/
lemma jonesBoundaryRegressionAxisZero_normal_transverse :
    inner ℝ (Space.basis.repr jonesBoundaryRegressionNormal.unit)
      jonesBoundaryRegressionAxisZero = 0 := by
  norm_num [jonesBoundaryRegressionNormal, jonesBoundaryRegressionAxisZero, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two, Matrix.head_cons]

/-- The common first frame axis is transverse to the incident direction. -/
lemma jonesBoundaryRegressionAxisZero_incident_transverse :
    inner ℝ (Space.basis.repr jonesBoundaryRegressionIncidentDirection.unit)
      jonesBoundaryRegressionAxisZero = 0 := by
  norm_num [jonesBoundaryRegressionIncidentDirection, jonesBoundaryRegressionAxisZero,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
    Matrix.head_cons]

/-- The common first frame axis is transverse to the reflected direction. -/
lemma jonesBoundaryRegressionAxisZero_reflected_transverse :
    inner ℝ (Space.basis.repr jonesBoundaryRegressionReflectedDirection.unit)
      jonesBoundaryRegressionAxisZero = 0 := by
  norm_num [jonesBoundaryRegressionReflectedDirection, jonesBoundaryRegressionAxisZero,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
    Matrix.head_cons]

/-- The common first frame axis is transverse to the transmitted direction. -/
lemma jonesBoundaryRegressionAxisZero_transmitted_transverse :
    inner ℝ (Space.basis.repr jonesBoundaryRegressionTransmittedDirection.unit)
      jonesBoundaryRegressionAxisZero = 0 := by
  norm_num [jonesBoundaryRegressionTransmittedDirection, jonesBoundaryRegressionAxisZero,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
    Matrix.head_cons]

/-- The common plane-normal polarization frame, with first axis `(0, 1, 0)`. -/
def jonesBoundaryRegressionPlaneFrame :
    PolarizationFrame jonesBoundaryRegressionPlane.normal :=
  PolarizationFrame.ofAxisZero jonesBoundaryRegressionPlane.normal
    jonesBoundaryRegressionAxisZero jonesBoundaryRegressionAxisZero_norm
    jonesBoundaryRegressionAxisZero_normal_transverse

/-- The incident propagation frame sharing the common first axis. -/
def jonesBoundaryRegressionIncidentFrame :
    PolarizationFrame jonesBoundaryRegressionIncidentDirection :=
  PolarizationFrame.ofAxisZero jonesBoundaryRegressionIncidentDirection
    jonesBoundaryRegressionAxisZero jonesBoundaryRegressionAxisZero_norm
    jonesBoundaryRegressionAxisZero_incident_transverse

/-- The reflected propagation frame sharing the common first axis. -/
def jonesBoundaryRegressionReflectedFrame :
    PolarizationFrame jonesBoundaryRegressionReflectedDirection :=
  PolarizationFrame.ofAxisZero jonesBoundaryRegressionReflectedDirection
    jonesBoundaryRegressionAxisZero jonesBoundaryRegressionAxisZero_norm
    jonesBoundaryRegressionAxisZero_reflected_transverse

/-- The transmitted propagation frame sharing the common first axis. -/
def jonesBoundaryRegressionTransmittedFrame :
    PolarizationFrame jonesBoundaryRegressionTransmittedDirection :=
  PolarizationFrame.ofAxisZero jonesBoundaryRegressionTransmittedDirection
    jonesBoundaryRegressionAxisZero jonesBoundaryRegressionAxisZero_norm
    jonesBoundaryRegressionAxisZero_transmitted_transverse

private lemma jonesBoundaryRegressionIncidentFrame_align :
    jonesBoundaryRegressionIncidentFrame.axis 0 =
      jonesBoundaryRegressionPlaneFrame.axis 0 := rfl

private lemma jonesBoundaryRegressionReflectedFrame_align :
    jonesBoundaryRegressionReflectedFrame.axis 0 =
      jonesBoundaryRegressionPlaneFrame.axis 0 := rfl

private lemma jonesBoundaryRegressionTransmittedFrame_align :
    jonesBoundaryRegressionTransmittedFrame.axis 0 =
      jonesBoundaryRegressionPlaneFrame.axis 0 := rfl

/-- The incident signed normal propagation component is `4/5`. -/
lemma jonesBoundaryRegression_incidentNormalComponent :
    jonesBoundaryRegressionPlane.normalComponent
      jonesBoundaryRegressionIncidentFrame.propagationVector = 4 / 5 := by
  change inner ℝ (WithLp.toLp 2 ![0, 0, 1])
    (WithLp.toLp 2 ![3 / 5, 0, 4 / 5]) = 4 / 5
  rw [PiLp.inner_apply]
  norm_num [Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two, Matrix.head_cons]

/-- The reflected signed normal propagation component is `-4/5`. -/
lemma jonesBoundaryRegression_reflectedNormalComponent :
    jonesBoundaryRegressionPlane.normalComponent
      jonesBoundaryRegressionReflectedFrame.propagationVector = -4 / 5 := by
  change inner ℝ (WithLp.toLp 2 ![0, 0, 1])
    (WithLp.toLp 2 ![3 / 5, 0, -4 / 5]) = -4 / 5
  rw [PiLp.inner_apply]
  norm_num [Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two, Matrix.head_cons]

/-- The transmitted signed normal propagation component is `3/5`. -/
lemma jonesBoundaryRegression_transmittedNormalComponent :
    jonesBoundaryRegressionPlane.normalComponent
      jonesBoundaryRegressionTransmittedFrame.propagationVector = 3 / 5 := by
  change inner ℝ (WithLp.toLp 2 ![0, 0, 1])
    (WithLp.toLp 2 ![4 / 5, 0, 3 / 5]) = 3 / 5
  rw [PiLp.inner_apply]
  norm_num [Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two, Matrix.head_cons]

/-- The negative-side medium of the exact regression. -/
def jonesBoundaryRegressionNegativeMedium : HomogeneousIsotropicMedium where
  ε := 25 / 2
  μ := 2
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The positive-side medium of the exact regression. -/
def jonesBoundaryRegressionPositiveMedium : HomogeneousIsotropicMedium where
  ε := 75 / 16
  μ := 3
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The negative-side wave speed is `1/5`. -/
lemma jonesBoundaryRegression_negativeMedium_waveSpeed :
    jonesBoundaryRegressionNegativeMedium.waveSpeed = 1 / 5 := by
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveSpeed, jonesBoundaryRegressionNegativeMedium,
    hsqrt25]

/-- The positive-side wave speed is `4/15`. -/
lemma jonesBoundaryRegression_positiveMedium_waveSpeed :
    jonesBoundaryRegressionPositiveMedium.waveSpeed = 4 / 15 := by
  have hsqrt16 : Real.sqrt 16 = 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt225 : Real.sqrt 225 = 15 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveSpeed, jonesBoundaryRegressionPositiveMedium,
    hsqrt16, hsqrt225]

/-- The negative-side wave admittance is `5/2`. -/
lemma jonesBoundaryRegression_negativeMedium_waveImpedance_inv :
    jonesBoundaryRegressionNegativeMedium.waveImpedance⁻¹ = 5 / 2 := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveImpedance, jonesBoundaryRegressionNegativeMedium,
    hsqrt4, hsqrt25]

/-- The positive-side wave admittance is `5/4`. -/
lemma jonesBoundaryRegression_positiveMedium_waveImpedance_inv :
    jonesBoundaryRegressionPositiveMedium.waveImpedance⁻¹ = 5 / 4 := by
  have hsqrt16 : Real.sqrt 16 = 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveImpedance, jonesBoundaryRegressionPositiveMedium,
    hsqrt16, hsqrt25]

/-!

## B. Nonzero stored-point phase and connected waves

-/

/-- Multiply origin-referenced Jones data by `I` to cancel the regression plane's `-I`
spatial factor. -/
def jonesBoundaryRegressionPrephase (J : JonesVector) : JonesVector :=
  JonesVector.scale Complex.I J

/-- The incident complex carrier built from phase-adjusted Jones data. -/
def jonesBoundaryRegressionIncidentWave (J : JonesVector) :
    ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    ((jonesBoundaryRegressionPrephase J).toMaterialPlaneWave
      jonesBoundaryRegressionNegativeMedium jonesBoundaryRegressionIncidentFrame 1 (by norm_num))

/-- The reflected complex carrier built from phase-adjusted Jones data. -/
def jonesBoundaryRegressionReflectedWave (J : JonesVector) :
    ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    ((jonesBoundaryRegressionPrephase J).toMaterialPlaneWave
      jonesBoundaryRegressionNegativeMedium jonesBoundaryRegressionReflectedFrame 1 (by norm_num))

/-- The transmitted complex carrier built from phase-adjusted Jones data. -/
def jonesBoundaryRegressionTransmittedWave (J : JonesVector) :
    ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    ((jonesBoundaryRegressionPrephase J).toMaterialPlaneWave
      jonesBoundaryRegressionPositiveMedium jonesBoundaryRegressionTransmittedFrame 1 (by norm_num))

/-- The incident wave has the nontrivial stored-point spatial factor `-I`. -/
lemma jonesBoundaryRegression_incidentWave_spatialFactor (J : JonesVector) :
    (jonesBoundaryRegressionIncidentWave J).waveVector.spatialFactor
      jonesBoundaryRegressionPlane.point = -Complex.I := by
  rw [jonesBoundaryRegressionIncidentWave,
    (jonesBoundaryRegressionPrephase J).ofReal_toMaterialPlaneWave_waveVector,
    jonesBoundaryRegression_negativeMedium_waveSpeed]
  norm_num [ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, jonesBoundaryRegressionPlane,
    jonesBoundaryRegressionIncidentFrame, PolarizationFrame.propagationVector,
    jonesBoundaryRegressionIncidentDirection, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons]
  rw [show -(Complex.I * (3 * ((Real.pi : ℂ) / 6))) =
    (-(Real.pi : ℂ) / 2) * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

/-- The reflected wave has the same nontrivial stored-point spatial factor `-I`. -/
lemma jonesBoundaryRegression_reflectedWave_spatialFactor (J : JonesVector) :
    (jonesBoundaryRegressionReflectedWave J).waveVector.spatialFactor
      jonesBoundaryRegressionPlane.point = -Complex.I := by
  rw [jonesBoundaryRegressionReflectedWave,
    (jonesBoundaryRegressionPrephase J).ofReal_toMaterialPlaneWave_waveVector,
    jonesBoundaryRegression_negativeMedium_waveSpeed]
  norm_num [ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, jonesBoundaryRegressionPlane,
    jonesBoundaryRegressionReflectedFrame, PolarizationFrame.propagationVector,
    jonesBoundaryRegressionReflectedDirection, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons]
  rw [show -(Complex.I * (3 * ((Real.pi : ℂ) / 6))) =
    (-(Real.pi : ℂ) / 2) * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

/-- The transmitted wave has the same nontrivial stored-point spatial factor `-I`. -/
lemma jonesBoundaryRegression_transmittedWave_spatialFactor (J : JonesVector) :
    (jonesBoundaryRegressionTransmittedWave J).waveVector.spatialFactor
      jonesBoundaryRegressionPlane.point = -Complex.I := by
  rw [jonesBoundaryRegressionTransmittedWave,
    (jonesBoundaryRegressionPrephase J).ofReal_toMaterialPlaneWave_waveVector,
    jonesBoundaryRegression_positiveMedium_waveSpeed]
  norm_num [ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, jonesBoundaryRegressionPlane,
    jonesBoundaryRegressionTransmittedFrame, PolarizationFrame.propagationVector,
    jonesBoundaryRegressionTransmittedDirection, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons]
  rw [show -(Complex.I * (3 * ((Real.pi : ℂ) / 6))) =
    (-(Real.pi : ℂ) / 2) * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

/-- The phase-adjusted incident carrier is represented at the nonzero stored point by the supplied
Jones amplitude. -/
lemma jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave (J : JonesVector) :
    IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionNegativeMedium (jonesBoundaryRegressionIncidentWave J)
      jonesBoundaryRegressionIncidentFrame J := by
  have h : IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionNegativeMedium (jonesBoundaryRegressionIncidentWave J)
      jonesBoundaryRegressionIncidentFrame
      (JonesVector.scale
        ((jonesBoundaryRegressionIncidentWave J).waveVector.spatialFactor
          jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J)) := by
    simpa only [jonesBoundaryRegressionIncidentWave] using
      (jonesBoundaryRegressionPrephase J).isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
        jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
          jonesBoundaryRegressionIncidentFrame 1 (by norm_num)
  have hJones : JonesVector.scale
      ((jonesBoundaryRegressionIncidentWave J).waveVector.spatialFactor
        jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J) = J := by
    ext i
    simp [jonesBoundaryRegressionPrephase, JonesVector.scale,
      jonesBoundaryRegression_incidentWave_spatialFactor]
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  simpa only [hJones] using h

/-- The phase-adjusted reflected carrier is represented at the nonzero stored point by the supplied
Jones amplitude. -/
lemma jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave (J : JonesVector) :
    IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionNegativeMedium (jonesBoundaryRegressionReflectedWave J)
      jonesBoundaryRegressionReflectedFrame J := by
  have h : IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionNegativeMedium (jonesBoundaryRegressionReflectedWave J)
      jonesBoundaryRegressionReflectedFrame
      (JonesVector.scale
        ((jonesBoundaryRegressionReflectedWave J).waveVector.spatialFactor
          jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J)) := by
    simpa only [jonesBoundaryRegressionReflectedWave] using
      (jonesBoundaryRegressionPrephase J).isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
        jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
          jonesBoundaryRegressionReflectedFrame 1 (by norm_num)
  have hJones : JonesVector.scale
      ((jonesBoundaryRegressionReflectedWave J).waveVector.spatialFactor
        jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J) = J := by
    ext i
    simp [jonesBoundaryRegressionPrephase, JonesVector.scale,
      jonesBoundaryRegression_reflectedWave_spatialFactor]
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  simpa only [hJones] using h

/-- The phase-adjusted transmitted carrier is represented at the nonzero stored point by the
supplied Jones amplitude. -/
lemma jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave (J : JonesVector) :
    IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionPositiveMedium (jonesBoundaryRegressionTransmittedWave J)
      jonesBoundaryRegressionTransmittedFrame J := by
  have h : IsReferencedMaterialJonesWave jonesBoundaryRegressionPlane
      jonesBoundaryRegressionPositiveMedium (jonesBoundaryRegressionTransmittedWave J)
      jonesBoundaryRegressionTransmittedFrame
      (JonesVector.scale
        ((jonesBoundaryRegressionTransmittedWave J).waveVector.spatialFactor
          jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J)) := by
    simpa only [jonesBoundaryRegressionTransmittedWave] using
      (jonesBoundaryRegressionPrephase J).isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
        jonesBoundaryRegressionPlane jonesBoundaryRegressionPositiveMedium
          jonesBoundaryRegressionTransmittedFrame 1 (by norm_num)
  have hJones : JonesVector.scale
      ((jonesBoundaryRegressionTransmittedWave J).waveVector.spatialFactor
        jonesBoundaryRegressionPlane.point) (jonesBoundaryRegressionPrephase J) = J := by
    ext i
    simp [jonesBoundaryRegressionPrephase, JonesVector.scale,
      jonesBoundaryRegression_transmittedWave_spatialFactor]
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  simpa only [hJones] using h

private lemma jonesBoundaryRegression_incidentFrame_normalElectricComponent (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent jonesBoundaryRegressionPlane
      (jonesBoundaryRegressionIncidentFrame.embedJones J) =
        (3 / 5 : ℂ) * J.components 1 := by
  norm_num [ComplexWaveVector.hyperplaneNormalComponent, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal,
    jonesBoundaryRegressionIncidentFrame, jonesBoundaryRegressionIncidentDirection,
    jonesBoundaryRegressionAxisZero, PolarizationFrame.ofAxisZero,
    PolarizationFrame.embedJones, PolarizationFrame.complexAxis,
    OrientedAffineHyperplane.normalVector, Space.basis_repr_apply, crossProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons]
  ring

private lemma jonesBoundaryRegression_reflectedFrame_normalElectricComponent (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent jonesBoundaryRegressionPlane
      (jonesBoundaryRegressionReflectedFrame.embedJones J) =
        (3 / 5 : ℂ) * J.components 1 := by
  norm_num [ComplexWaveVector.hyperplaneNormalComponent, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal,
    jonesBoundaryRegressionReflectedFrame, jonesBoundaryRegressionReflectedDirection,
    jonesBoundaryRegressionAxisZero, PolarizationFrame.ofAxisZero,
    PolarizationFrame.embedJones, PolarizationFrame.complexAxis,
    OrientedAffineHyperplane.normalVector, Space.basis_repr_apply, crossProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons]
  ring

private lemma jonesBoundaryRegression_transmittedFrame_normalElectricComponent (J : JonesVector) :
    ComplexWaveVector.hyperplaneNormalComponent jonesBoundaryRegressionPlane
      (jonesBoundaryRegressionTransmittedFrame.embedJones J) =
        (4 / 5 : ℂ) * J.components 1 := by
  norm_num [ComplexWaveVector.hyperplaneNormalComponent, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal,
    jonesBoundaryRegressionTransmittedFrame, jonesBoundaryRegressionTransmittedDirection,
    jonesBoundaryRegressionAxisZero, PolarizationFrame.ofAxisZero,
    PolarizationFrame.embedJones, PolarizationFrame.complexAxis,
    OrientedAffineHyperplane.normalVector, Space.basis_repr_apply, crossProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons]
  ring

/-- The two-coordinate unit incident Jones amplitude used to test all four equations. -/
def jonesBoundaryRegressionIncidentJones : JonesVector :=
  JonesVector.ofComponents 1 1

/-- Reflected Jones data with independent `s` and full-vector `p` coefficients. -/
def jonesBoundaryRegressionReflectedJones (rS rP : ℂ) : JonesVector :=
  JonesVector.ofComponents rS rP

/-- Transmitted Jones data with independent `s` and full-vector `p` coefficients. -/
def jonesBoundaryRegressionTransmittedJones (tS tP : ℂ) : JonesVector :=
  JonesVector.ofComponents tS tP

/-- The exact interface carrying the regression plane and media. -/
def jonesBoundaryRegressionInterface : PlanarDielectricInterface where
  plane := jonesBoundaryRegressionPlane
  negativeMedium := jonesBoundaryRegressionNegativeMedium
  positiveMedium := jonesBoundaryRegressionPositiveMedium

/-- The phase-referenced three-wave configuration with four variable Jones coefficients. -/
def jonesBoundaryRegressionConfiguration (rS tS rP tP : ℂ) :
    PlanarDielectricWaveConfiguration where
  interface := jonesBoundaryRegressionInterface
  incident := jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones
  reflected := jonesBoundaryRegressionReflectedWave
    (jonesBoundaryRegressionReflectedJones rS rP)
  transmitted := jonesBoundaryRegressionTransmittedWave
    (jonesBoundaryRegressionTransmittedJones tS tP)

/-!

## C. Balance witnesses, four boundary equations, and their exact solution

-/

/-- The equation carried by the first Jones component gives `t_s = 1 + r_s`. -/
lemma jonesBoundaryRegression_electric_component_zero {rS tS rP tP : ℂ}
    (h : (jonesBoundaryRegressionConfiguration rS tS rP tP).HasReferencedJointElectricBalance) :
    tS = 1 + rS := by
  have hEquation :=
    HasReferencedJointElectricBalance.jones_component_zero h
      jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones rS rP)))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones tS tP))
    jonesBoundaryRegressionIncidentFrame_align jonesBoundaryRegressionReflectedFrame_align
    jonesBoundaryRegressionTransmittedFrame_align
  simp [jonesBoundaryRegressionIncidentJones,
    jonesBoundaryRegressionReflectedJones, jonesBoundaryRegressionTransmittedJones] at hEquation
  linear_combination hEquation

/-- The equation carried by the second Jones component gives
`(3/5) t_p = (4/5) (1 - r_p)`. -/
lemma jonesBoundaryRegression_electric_component_one {rS tS rP tP : ℂ}
    (h : (jonesBoundaryRegressionConfiguration rS tS rP tP).HasReferencedJointElectricBalance) :
    (3 / 5 : ℂ) * tP = (4 / 5 : ℂ) * (1 - rP) := by
  have hEquation :=
    HasReferencedJointElectricBalance.jones_component_one h
      jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones rS rP)))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones tS tP))
    jonesBoundaryRegressionIncidentFrame_align jonesBoundaryRegressionReflectedFrame_align
    jonesBoundaryRegressionTransmittedFrame_align
  dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface] at hEquation
  rw [jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent,
    jonesBoundaryRegression_transmittedNormalComponent] at hEquation
  simp [jonesBoundaryRegressionIncidentJones,
    jonesBoundaryRegressionReflectedJones, jonesBoundaryRegressionTransmittedJones] at hEquation
  linear_combination hEquation

/-- The magnetic equation carried by the first Jones component gives
`(3/4) t_s = 2 (1 - r_s)`. -/
lemma jonesBoundaryRegression_magnetic_component_zero {rS tS rP tP : ℂ}
    (h : PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      (jonesBoundaryRegressionConfiguration rS tS rP tP)) :
    (3 / 4 : ℂ) * tS = 2 * (1 - rS) := by
  have hEquation :=
    HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_zero h
      jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones rS rP)))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones tS tP))
    jonesBoundaryRegressionIncidentFrame_align jonesBoundaryRegressionReflectedFrame_align
    jonesBoundaryRegressionTransmittedFrame_align
  dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface] at hEquation
  rw [jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent,
    jonesBoundaryRegression_transmittedNormalComponent,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv] at hEquation
  simp [jonesBoundaryRegressionIncidentJones,
    jonesBoundaryRegressionReflectedJones, jonesBoundaryRegressionTransmittedJones] at hEquation
  linear_combination hEquation

/-- The magnetic equation carried by the second Jones component gives
`(5/4) t_p = (5/2) (1 + r_p)`. -/
lemma jonesBoundaryRegression_magnetic_component_one {rS tS rP tP : ℂ}
    (h : PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      (jonesBoundaryRegressionConfiguration rS tS rP tP)) :
    (5 / 4 : ℂ) * tP = (5 / 2 : ℂ) * (1 + rP) := by
  have hEquation :=
    HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_one h
      jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones rS rP)))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones tS tP))
    jonesBoundaryRegressionIncidentFrame_align jonesBoundaryRegressionReflectedFrame_align
    jonesBoundaryRegressionTransmittedFrame_align
  dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface] at hEquation
  rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv] at hEquation
  simp [jonesBoundaryRegressionIncidentJones,
    jonesBoundaryRegressionReflectedJones, jonesBoundaryRegressionTransmittedJones] at hEquation
  linear_combination hEquation

/-- The expected exact coefficients satisfy the complete referenced tangential-electric and
normal-displacement balance. -/
lemma jonesBoundaryRegression_exact_hasReferencedJointElectricBalance :
    PlanarDielectricWaveConfiguration.HasReferencedJointElectricBalance
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5)) := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    jonesBoundaryRegressionIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))
  have hTransmitted := jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))
  change referencedMediumJointElectricTraceAmplitude jonesBoundaryRegressionPlane
        jonesBoundaryRegressionPositiveMedium
        (jonesBoundaryRegressionTransmittedWave
          (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))) =
      referencedMediumJointElectricTraceAmplitude jonesBoundaryRegressionPlane
          jonesBoundaryRegressionNegativeMedium
          (jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones) +
        referencedMediumJointElectricTraceAmplitude jonesBoundaryRegressionPlane
          jonesBoundaryRegressionNegativeMedium
          (jonesBoundaryRegressionReflectedWave
            (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5)))
  apply Prod.ext
  · simp only [Prod.fst_add]
    rw [hTransmitted.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
        jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionTransmittedFrame_align,
      hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
        jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionIncidentFrame_align,
      hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
        jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionReflectedFrame_align,
      jonesBoundaryRegression_transmittedNormalComponent,
      jonesBoundaryRegression_incidentNormalComponent,
      jonesBoundaryRegression_reflectedNormalComponent]
    ext k
    simp [jonesBoundaryRegressionIncidentJones, jonesBoundaryRegressionReflectedJones,
      jonesBoundaryRegressionTransmittedJones, PolarizationFrame.embedJones]
    ring
  · simp only [Prod.snd_add]
    rw [hTransmitted.referencedMediumJointElectricTraceAmplitude_snd,
      hIncident.referencedMediumJointElectricTraceAmplitude_snd,
      hReflected.referencedMediumJointElectricTraceAmplitude_snd,
      jonesBoundaryRegression_transmittedFrame_normalElectricComponent,
      jonesBoundaryRegression_incidentFrame_normalElectricComponent,
      jonesBoundaryRegression_reflectedFrame_normalElectricComponent]
    norm_num [jonesBoundaryRegressionPositiveMedium, jonesBoundaryRegressionNegativeMedium,
      jonesBoundaryRegressionIncidentJones, jonesBoundaryRegressionReflectedJones,
      jonesBoundaryRegressionTransmittedJones]

/-- The expected exact coefficients satisfy the referenced tangential magnetic-field-strength
balance. -/
lemma jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance :
    PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5)) := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    jonesBoundaryRegressionIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))
  have hTransmitted := jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))
  change referencedMediumTangentialMagneticFieldStrengthAmplitude
        jonesBoundaryRegressionPlane jonesBoundaryRegressionPositiveMedium
        (jonesBoundaryRegressionTransmittedWave
          (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))) =
      referencedMediumTangentialMagneticFieldStrengthAmplitude
          jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
          (jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones) +
        referencedMediumTangentialMagneticFieldStrengthAmplitude
          jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
          (jonesBoundaryRegressionReflectedWave
            (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5)))
  rw [hTransmitted.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionTransmittedFrame_align,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionIncidentFrame_align,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      jonesBoundaryRegressionPlaneFrame jonesBoundaryRegressionReflectedFrame_align,
    jonesBoundaryRegression_transmittedNormalComponent,
    jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
  ext k
  simp [jonesBoundaryRegressionIncidentJones, jonesBoundaryRegressionReflectedJones,
    jonesBoundaryRegressionTransmittedJones, PolarizationFrame.embedJones]
  ring

/-- On the exact `3-4-5` fixture, the two reduced vector equalities uniquely force the expected
full-vector Jones reflection and transmission coefficients. -/
lemma jonesBoundaryRegression_coefficients_of_balances {rS tS rP tP : ℂ}
    (hElectric :
      (jonesBoundaryRegressionConfiguration rS tS rP tP).HasReferencedJointElectricBalance)
    (hMagnetic :
      PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      (jonesBoundaryRegressionConfiguration rS tS rP tP)) :
    rS = 5 / 11 ∧ tS = 16 / 11 ∧ rP = -1 / 5 ∧ tP = 8 / 5 := by
  have hElectricS := jonesBoundaryRegression_electric_component_zero hElectric
  have hElectricP := jonesBoundaryRegression_electric_component_one hElectric
  have hMagneticS := jonesBoundaryRegression_magnetic_component_zero hMagnetic
  have hMagneticP := jonesBoundaryRegression_magnetic_component_one hMagnetic
  have hrS : rS = 5 / 11 := by
    linear_combination (4 / 11) * hMagneticS - (3 / 11) * hElectricS
  have htS : tS = 16 / 11 := by
    linear_combination hElectricS + hrS
  have hrP : rP = -1 / 5 := by
    linear_combination (1 / 2) * hElectricP - (6 / 25) * hMagneticP
  have htP : tP = 8 / 5 := by
    linear_combination (4 / 5) * hMagneticP + 2 * hrP
  exact ⟨hrS, htS, hrP, htP⟩

/-- The exact reduced Jones boundary problem has the unique coefficient tuple
`(5/11, 16/11, -1/5, 8/5)`. -/
lemma jonesBoundaryRegression_existsUnique_coefficients :
    ∃! coefficients : ℂ × ℂ × ℂ × ℂ,
      let (rS, tS, rP, tP) := coefficients
      PlanarDielectricWaveConfiguration.HasReferencedJointElectricBalance
          (jonesBoundaryRegressionConfiguration rS tS rP tP) ∧
        PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
          (jonesBoundaryRegressionConfiguration rS tS rP tP) := by
  refine ⟨(5 / 11, 16 / 11, -1 / 5, 8 / 5), ?_, ?_⟩
  · exact ⟨jonesBoundaryRegression_exact_hasReferencedJointElectricBalance,
      jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance⟩
  · rintro ⟨rS, tS, rP, tP⟩ ⟨hElectric, hMagnetic⟩
    rcases jonesBoundaryRegression_coefficients_of_balances hElectric hMagnetic with
      ⟨rfl, rfl, rfl, rfl⟩
    rfl

end

end Optics
