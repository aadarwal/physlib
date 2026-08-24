/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelFluxRegression
public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelInterference

/-!
# Fresnel interference regressions

## i. Overview

This file checks incident-reflected normal-interference cancellation and the final superposed-wave
Fresnel balance on the nonzero-stored-phase `3-4-5` interface fixture. The quadrature Jones input
`(1, I)` and reflected output `(5/11, -I/5)` exercise harmonic conjugation and both instantaneous
quadratures. The connected boundary endpoint remains the independently solved real fixture with
Jones data `(1, 1)`, `(5/11, -1/5)`, and `(16/11, 8/5)`.

## ii. Key results

- `fresnelInterferenceRegression_harmonic_ordered_terms`: independently nonzero Hermitian cross
  terms before cancellation.
- `fresnelInterferenceRegression_harmonic_interference_vector`: the surviving purely tangential
  harmonic interference vector.
- `fresnelInterferenceRegression_actual_ordered_terms`: nonzero ordered instantaneous cross terms
  at two phases.
- `jonesBoundaryRegression_exact_hasSuperposedWaveNormalFluxBalance`: the full connected actual-
  field endpoint.
- `jonesBoundaryRegression_exact_hasSuperposedWaveNormalFluxBalance_of_incidenceFrames`: the same
  endpoint with all frame matching and reflected-normal data derived by the canonical wrapper.
- `fresnelInterferenceRegression_superposed_normalFlux_value`: its exact value `5304/3025`.
- `fresnelInterferenceRegression_zeroReflection_unequalFrequency`: the arbitrary-frequency dummy
  zero-reflection branch.
- `fresnelInterferenceRegression_zeroReflection_canonicalSuperposedBalance`: the canonical
  endpoint with unequal-frequency, zero-vector, non-canonical-frame dummy reflected data.

## iii. Table of contents

- A. Fixed-frequency witness and canonical frames
- B. Harmonic and actual ordered interference values
- C. Superposed-wave normal-flux balance
- D. Unequal-frequency zero reflection

## iv. Scope

These are exact stored-point regressions. They do not assert full-vector Poynting additivity,
aperture power, total internal reflection, lossy-media behavior, or scattering unitarity.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Matrix Space Time
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PlanarDielectricWaveConfiguration

noncomputable section

/-!

## A. Fixed-frequency witness and canonical frames

-/

/-- The independently constructed exact Jones boundary fixture has the common carrier frequency
and tangential wave-vector labels required by its reduced fixed-frequency electric boundary. -/
lemma jonesBoundaryRegression_exact_isFixedFrequencyElectricBoundary :
    PlanarDielectricWaveConfiguration.IsFixedFrequencyElectricBoundary
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5)) := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    jonesBoundaryRegressionIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))
  have hTransmitted := jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))
  refine ⟨⟨⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩,
    jonesBoundaryRegression_exact_hasReferencedJointElectricBalance⟩
  · rfl
  · dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
    rw [hTransmitted.waveVector_eq, hIncident.waveVector_eq,
      ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
      ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
      jonesBoundaryRegression_positiveMedium_waveSpeed,
      jonesBoundaryRegression_negativeMedium_waveSpeed]
    ext i
    fin_cases i <;>
      norm_num [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent, jonesBoundaryRegressionPlane,
        OrientedAffineHyperplane.normalVector, Space.basis_repr_apply,
        jonesBoundaryRegressionNormal, jonesBoundaryRegressionIncidentFrame,
        jonesBoundaryRegressionTransmittedFrame, PolarizationFrame.propagationVector,
        jonesBoundaryRegressionIncidentDirection, jonesBoundaryRegressionTransmittedDirection,
        jonesBoundaryRegressionIncidentWave, jonesBoundaryRegressionTransmittedWave,
        ComplexMonochromaticPlaneWave.ofReal_angularFrequency,
        JonesVector.toMaterialPlaneWave_angularFrequency,
        PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
        Matrix.head_cons]
  · rfl
  · dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
    rw [hReflected.waveVector_eq, hIncident.waveVector_eq,
      ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
      ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
      jonesBoundaryRegression_negativeMedium_waveSpeed]
    ext i
    fin_cases i <;>
      norm_num [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent, jonesBoundaryRegressionPlane,
        OrientedAffineHyperplane.normalVector, Space.basis_repr_apply,
        jonesBoundaryRegressionNormal, jonesBoundaryRegressionIncidentFrame,
        jonesBoundaryRegressionReflectedFrame, PolarizationFrame.propagationVector,
        jonesBoundaryRegressionIncidentDirection, jonesBoundaryRegressionReflectedDirection,
        jonesBoundaryRegressionIncidentWave, jonesBoundaryRegressionReflectedWave,
        ComplexMonochromaticPlaneWave.ofReal_angularFrequency,
        JonesVector.toMaterialPlaneWave_angularFrequency,
        PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
        Matrix.head_cons]

/-- The exact incident direction is non-normal to the regression interface. -/
lemma jonesBoundaryRegression_incident_isNonNormalIncidence :
    IsNonNormalIncidence jonesBoundaryRegressionIncidentDirection
      jonesBoundaryRegressionPlane.normal := by
  intro h
  have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  norm_num [IsNonNormalIncidence, jonesBoundaryRegressionIncidentDirection,
    jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal, crossProduct,
    Matrix.cons_val_two, Matrix.head_cons] at hy

/-- The exact reflected direction is non-normal to the regression interface. -/
lemma jonesBoundaryRegression_reflected_isNonNormalIncidence :
    IsNonNormalIncidence jonesBoundaryRegressionReflectedDirection
      jonesBoundaryRegressionPlane.normal := by
  intro h
  have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  norm_num [IsNonNormalIncidence, jonesBoundaryRegressionReflectedDirection,
    jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal, crossProduct,
    Matrix.cons_val_two, Matrix.head_cons] at hy

/-- The exact transmitted direction is non-normal to the regression interface. -/
lemma jonesBoundaryRegression_transmitted_isNonNormalIncidence :
    IsNonNormalIncidence jonesBoundaryRegressionTransmittedDirection
      jonesBoundaryRegressionPlane.normal := by
  intro h
  have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  norm_num [IsNonNormalIncidence, jonesBoundaryRegressionTransmittedDirection,
    jonesBoundaryRegressionPlane, jonesBoundaryRegressionNormal, crossProduct,
    Matrix.cons_val_two, Matrix.head_cons] at hy

private lemma jonesBoundaryRegression_incident_sPolarizationAxis :
    sPolarizationAxis jonesBoundaryRegressionIncidentDirection
      jonesBoundaryRegressionPlane.normal
        jonesBoundaryRegression_incident_isNonNormalIncidence =
      jonesBoundaryRegressionAxisZero := by
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  ext i
  fin_cases i <;>
    norm_num [sPolarizationAxis, NormedSpace.normalize,
      jonesBoundaryRegressionIncidentDirection, jonesBoundaryRegressionPlane,
      jonesBoundaryRegressionNormal, jonesBoundaryRegressionAxisZero, crossProduct,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
      hsqrt25, hsqrt9]

private lemma jonesBoundaryRegression_reflected_sPolarizationAxis :
    sPolarizationAxis jonesBoundaryRegressionReflectedDirection
      jonesBoundaryRegressionPlane.normal
        jonesBoundaryRegression_reflected_isNonNormalIncidence =
      jonesBoundaryRegressionAxisZero := by
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  ext i
  fin_cases i <;>
    norm_num [sPolarizationAxis, NormedSpace.normalize,
      jonesBoundaryRegressionReflectedDirection, jonesBoundaryRegressionPlane,
      jonesBoundaryRegressionNormal, jonesBoundaryRegressionAxisZero, crossProduct,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
      hsqrt25, hsqrt9]

private lemma jonesBoundaryRegression_transmitted_sPolarizationAxis :
    sPolarizationAxis jonesBoundaryRegressionTransmittedDirection
      jonesBoundaryRegressionPlane.normal
        jonesBoundaryRegression_transmitted_isNonNormalIncidence =
      jonesBoundaryRegressionAxisZero := by
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt16 : Real.sqrt 16 = 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  ext i
  fin_cases i <;>
    norm_num [sPolarizationAxis, NormedSpace.normalize,
      jonesBoundaryRegressionTransmittedDirection, jonesBoundaryRegressionPlane,
      jonesBoundaryRegressionNormal, jonesBoundaryRegressionAxisZero, crossProduct,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
      hsqrt25, hsqrt16]

/-- The manually constructed incident regression frame is its canonical incidence frame. -/
lemma jonesBoundaryRegressionIncidentFrame_eq_incidencePolarizationFrame :
    jonesBoundaryRegressionIncidentFrame =
      incidencePolarizationFrame jonesBoundaryRegressionIncidentDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_incident_isNonNormalIncidence := by
  apply PolarizationFrame.ext
  funext i
  fin_cases i
  · change jonesBoundaryRegressionIncidentFrame.axis 0 =
      (incidencePolarizationFrame jonesBoundaryRegressionIncidentDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_incident_isNonNormalIncidence).axis 0
    rw [incidencePolarizationFrame_axis_zero,
      jonesBoundaryRegression_incident_sPolarizationAxis]
    rfl
  · change jonesBoundaryRegressionIncidentFrame.axis 1 =
      (incidencePolarizationFrame jonesBoundaryRegressionIncidentDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_incident_isNonNormalIncidence).axis 1
    rw [incidencePolarizationFrame_axis_one, pPolarizationAxis,
      jonesBoundaryRegression_incident_sPolarizationAxis,
      jonesBoundaryRegressionIncidentFrame, PolarizationFrame.ofAxisZero_axis_one]

/-- The manually constructed reflected regression frame is its canonical incidence frame. -/
lemma jonesBoundaryRegressionReflectedFrame_eq_incidencePolarizationFrame :
    jonesBoundaryRegressionReflectedFrame =
      incidencePolarizationFrame jonesBoundaryRegressionReflectedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_reflected_isNonNormalIncidence := by
  apply PolarizationFrame.ext
  funext i
  fin_cases i
  · change jonesBoundaryRegressionReflectedFrame.axis 0 =
      (incidencePolarizationFrame jonesBoundaryRegressionReflectedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_reflected_isNonNormalIncidence).axis 0
    rw [incidencePolarizationFrame_axis_zero,
      jonesBoundaryRegression_reflected_sPolarizationAxis]
    rfl
  · change jonesBoundaryRegressionReflectedFrame.axis 1 =
      (incidencePolarizationFrame jonesBoundaryRegressionReflectedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_reflected_isNonNormalIncidence).axis 1
    rw [incidencePolarizationFrame_axis_one, pPolarizationAxis,
      jonesBoundaryRegression_reflected_sPolarizationAxis,
      jonesBoundaryRegressionReflectedFrame, PolarizationFrame.ofAxisZero_axis_one]

/-- The manually constructed transmitted regression frame is its canonical incidence frame. -/
lemma jonesBoundaryRegressionTransmittedFrame_eq_incidencePolarizationFrame :
    jonesBoundaryRegressionTransmittedFrame =
      incidencePolarizationFrame jonesBoundaryRegressionTransmittedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_transmitted_isNonNormalIncidence := by
  apply PolarizationFrame.ext
  funext i
  fin_cases i
  · change jonesBoundaryRegressionTransmittedFrame.axis 0 =
      (incidencePolarizationFrame jonesBoundaryRegressionTransmittedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_transmitted_isNonNormalIncidence).axis 0
    rw [incidencePolarizationFrame_axis_zero,
      jonesBoundaryRegression_transmitted_sPolarizationAxis]
    rfl
  · change jonesBoundaryRegressionTransmittedFrame.axis 1 =
      (incidencePolarizationFrame jonesBoundaryRegressionTransmittedDirection
        jonesBoundaryRegressionPlane.normal
          jonesBoundaryRegression_transmitted_isNonNormalIncidence).axis 1
    rw [incidencePolarizationFrame_axis_one, pPolarizationAxis,
      jonesBoundaryRegression_transmitted_sPolarizationAxis,
      jonesBoundaryRegressionTransmittedFrame, PolarizationFrame.ofAxisZero_axis_one]

/-!

## B. Harmonic and actual ordered interference values

-/

/-- The normal harmonic cross term between two aligned Jones phasors, reduced to their Hermitian
coordinate pairings and signed propagation normals. -/
private lemma normalComponent_timeAveragedPoyntingVector_embedJones_propagationCross
    {firstDirection secondDirection : Space.Direction 3}
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame firstDirection)
    (secondFrame : PolarizationFrame secondDirection)
    (firstJones secondJones : JonesVector) (admittance : ℝ)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent
        (timeAveragedPoyntingVector (firstFrame.embedJones firstJones)
          ((admittance : ℂ) • secondFrame.embedJones secondJones.propagationCross)) =
      admittance / 2 *
        (plane.normalComponent secondFrame.propagationVector *
            ((firstJones.components 0).re * (secondJones.components 0).re +
              (firstJones.components 0).im * (secondJones.components 0).im) +
          plane.normalComponent firstFrame.propagationVector *
            ((firstJones.components 1).re * (secondJones.components 1).re +
              (firstJones.components 1).im * (secondJones.components 1).im)) := by
  have hReal := PolarizationFrame.normalComponent_cross_realizeJones_of_axis_zero_eq
    plane planeFrame firstFrame secondFrame firstJones secondJones.propagationCross
      0 0 hFirstAlign hSecondAlign
  have hImag := PolarizationFrame.normalComponent_cross_realizeJones_of_axis_zero_eq
    plane planeFrame firstFrame secondFrame firstJones secondJones.propagationCross
      (-(Real.pi / 2)) (-(Real.pi / 2)) hFirstAlign hSecondAlign
  have hReal' : plane.normalComponent
        (firstFrame.electricReal firstJones ⨯ₑ₃
          secondFrame.electricReal secondJones.propagationCross) =
      plane.normalComponent secondFrame.propagationVector *
          (firstJones.components 0).re * (secondJones.components 0).re +
        plane.normalComponent firstFrame.propagationVector *
          (firstJones.components 1).re * (secondJones.components 1).re := by
    simpa [PolarizationFrame.realizeJones_eq,
      Phasor.realize_eq_re_cos_sub_im_sin] using hReal
  have hImag' : plane.normalComponent
        (firstFrame.electricImag firstJones ⨯ₑ₃
          secondFrame.electricImag secondJones.propagationCross) =
      plane.normalComponent secondFrame.propagationVector *
          (firstJones.components 0).im * (secondJones.components 0).im +
        plane.normalComponent firstFrame.propagationVector *
          (firstJones.components 1).im * (secondJones.components 1).im := by
    simpa [PolarizationFrame.realizeJones_eq,
      Phasor.realize_eq_re_cos_sub_im_sin, Real.cos_neg, Real.sin_neg] using hImag
  have hRealScalar : ComplexWaveVector.realPart
        ((admittance : ℂ) • secondFrame.embedJones secondJones.propagationCross) =
      admittance • secondFrame.electricReal secondJones.propagationCross := by
    ext i
    simp [ComplexWaveVector.realPart, PolarizationFrame.electricReal, Complex.mul_re]
    ring
  have hImagScalar : ComplexWaveVector.imaginaryPart
        ((admittance : ℂ) • secondFrame.embedJones secondJones.propagationCross) =
      admittance • secondFrame.electricImag secondJones.propagationCross := by
    ext i
    simp [ComplexWaveVector.imaginaryPart, PolarizationFrame.electricImag, Complex.mul_im]
    ring
  rw [timeAveragedPoyntingVector_eq_quadrature_cross, hRealScalar, hImagScalar]
  change plane.normalComponent ((1 / 2 : ℝ) •
    (firstFrame.electricReal firstJones ⨯ₑ₃
        (admittance • secondFrame.electricReal secondJones.propagationCross) +
      firstFrame.electricImag firstJones ⨯ₑ₃
        (admittance • secondFrame.electricImag secondJones.propagationCross))) = _
  rw [Space.cross_smul, Space.cross_smul]
  simp only [OrientedAffineHyperplane.normalComponent, inner_smul_right,
    inner_add_right] at hReal' hImag' ⊢
  rw [hReal', hImag']
  ring

/-- The two ordered harmonic normal-interference terms are `-36/55` and `36/55` for the
quadrature fixture. Their nonzero values independently check complex conjugation before their sum
cancels. -/
lemma fresnelInterferenceRegression_harmonic_ordered_terms :
    jonesBoundaryRegressionPlane.normalComponent
        (timeAveragedPoyntingVector
          ((jonesBoundaryRegressionIncidentWave
              fresnelFluxRegressionQuadratureIncidentJones).localElectricPhasor
            jonesBoundaryRegressionPlane.point)
          ((jonesBoundaryRegressionReflectedWave
              fresnelFluxRegressionQuadratureReflectedJones).localMagneticFieldStrengthPhasor
            jonesBoundaryRegressionNegativeMedium
              jonesBoundaryRegressionPlane.point)) = -36 / 55 ∧
    jonesBoundaryRegressionPlane.normalComponent
        (timeAveragedPoyntingVector
          ((jonesBoundaryRegressionReflectedWave
              fresnelFluxRegressionQuadratureReflectedJones).localElectricPhasor
            jonesBoundaryRegressionPlane.point)
          ((jonesBoundaryRegressionIncidentWave
              fresnelFluxRegressionQuadratureIncidentJones).localMagneticFieldStrengthPhasor
            jonesBoundaryRegressionNegativeMedium
              jonesBoundaryRegressionPlane.point)) = 36 / 55 := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureReflectedJones
  rw [hIncident.localElectricPhasor_planePoint,
    hReflected.localMagneticFieldStrengthPhasor_planePoint,
    hReflected.localElectricPhasor_planePoint,
    hIncident.localMagneticFieldStrengthPhasor_planePoint]
  constructor
  · rw [normalComponent_timeAveragedPoyntingVector_embedJones_propagationCross
      jonesBoundaryRegressionPlane jonesBoundaryRegressionPlaneFrame
      jonesBoundaryRegressionIncidentFrame jonesBoundaryRegressionReflectedFrame
      fresnelFluxRegressionQuadratureIncidentJones
      fresnelFluxRegressionQuadratureReflectedJones _ rfl rfl,
      jonesBoundaryRegression_incidentNormalComponent,
      jonesBoundaryRegression_reflectedNormalComponent,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones]
  · rw [normalComponent_timeAveragedPoyntingVector_embedJones_propagationCross
      jonesBoundaryRegressionPlane jonesBoundaryRegressionPlaneFrame
      jonesBoundaryRegressionReflectedFrame jonesBoundaryRegressionIncidentFrame
      fresnelFluxRegressionQuadratureReflectedJones
      fresnelFluxRegressionQuadratureIncidentJones _ rfl rfl,
      jonesBoundaryRegression_incidentNormalComponent,
      jonesBoundaryRegression_reflectedNormalComponent,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones]

/-- For the quadrature fixture, harmonic incident-reflected interference survives tangent to the
interface even though its stored-normal component cancels. Its exact value `(21/55, 0, 0)` makes
the distinction between normal-flux additivity and full-vector additivity explicit. -/
lemma fresnelInterferenceRegression_harmonic_interference_vector :
    timeAveragedPoyntingInterferenceVector
        ((jonesBoundaryRegressionIncidentWave
          fresnelFluxRegressionQuadratureIncidentJones).localElectricPhasor
            jonesBoundaryRegressionPlane.point)
        ((jonesBoundaryRegressionIncidentWave
          fresnelFluxRegressionQuadratureIncidentJones).localMagneticFieldStrengthPhasor
            jonesBoundaryRegressionNegativeMedium jonesBoundaryRegressionPlane.point)
        ((jonesBoundaryRegressionReflectedWave
          fresnelFluxRegressionQuadratureReflectedJones).localElectricPhasor
            jonesBoundaryRegressionPlane.point)
        ((jonesBoundaryRegressionReflectedWave
          fresnelFluxRegressionQuadratureReflectedJones).localMagneticFieldStrengthPhasor
            jonesBoundaryRegressionNegativeMedium jonesBoundaryRegressionPlane.point) =
      WithLp.toLp 2 ![(21 / 55 : ℝ), 0, 0] := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureReflectedJones
  rw [hIncident.localElectricPhasor_planePoint,
    hIncident.localMagneticFieldStrengthPhasor_planePoint,
    hReflected.localElectricPhasor_planePoint,
    hReflected.localMagneticFieldStrengthPhasor_planePoint,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
  ext i
  fin_cases i <;>
    norm_num [timeAveragedPoyntingInterferenceVector, timeAveragedPoyntingVector,
      ComplexMonochromaticPlaneWave.complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, PolarizationFrame.embedJones,
      PolarizationFrame.complexAxis, JonesVector.propagationCross,
      fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones,
      jonesBoundaryRegressionIncidentFrame, jonesBoundaryRegressionReflectedFrame,
      PolarizationFrame.ofAxisZero, jonesBoundaryRegressionAxisZero,
      jonesBoundaryRegressionIncidentDirection, jonesBoundaryRegressionReflectedDirection,
      Space.basis_repr_apply, Fin.sum_univ_two, crossProduct, Matrix.cons_val_two,
      Matrix.head_cons, Complex.mul_re]

/-- The incident-electric/reflected-magnetic ordered normal term, reduced to the two Jones
quadratures of the exact regression fixture. -/
private lemma fresnelInterferenceRegression_incidentReflected_ordered_term (time : Time) :
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionIncidentWave
            fresnelFluxRegressionQuadratureIncidentJones).electricField time
              jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionReflectedWave
              fresnelFluxRegressionQuadratureReflectedJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium time jonesBoundaryRegressionPlane.point) =
      (5 / 2 : ℝ) *
        ((-4 / 5 : ℝ) *
            Phasor.realize (fresnelFluxRegressionQuadratureIncidentJones.components 0)
              ((jonesBoundaryRegressionIncidentWave
                fresnelFluxRegressionQuadratureIncidentJones).angularFrequency * (time : ℝ)) *
            Phasor.realize (fresnelFluxRegressionQuadratureReflectedJones.components 0)
              ((jonesBoundaryRegressionReflectedWave
                fresnelFluxRegressionQuadratureReflectedJones).angularFrequency * (time : ℝ)) +
          (4 / 5 : ℝ) *
            Phasor.realize (fresnelFluxRegressionQuadratureIncidentJones.components 1)
              ((jonesBoundaryRegressionIncidentWave
                fresnelFluxRegressionQuadratureIncidentJones).angularFrequency * (time : ℝ)) *
            Phasor.realize (fresnelFluxRegressionQuadratureReflectedJones.components 1)
              ((jonesBoundaryRegressionReflectedWave
                fresnelFluxRegressionQuadratureReflectedJones).angularFrequency *
                  (time : ℝ))) := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureReflectedJones
  rw [hIncident.electricField_planePoint, hReflected.magneticFieldStrength_planePoint,
    Space.cross_smul, OrientedAffineHyperplane.normalComponent, inner_smul_right,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
  change (5 / 2 : ℝ) * jonesBoundaryRegressionPlane.normalComponent
    (jonesBoundaryRegressionIncidentFrame.realizeJones
        fresnelFluxRegressionQuadratureIncidentJones _ ⨯ₑ₃
      jonesBoundaryRegressionReflectedFrame.realizeJones
        fresnelFluxRegressionQuadratureReflectedJones.propagationCross _) = _
  rw [PolarizationFrame.normalComponent_cross_realizeJones_of_axis_zero_eq
    jonesBoundaryRegressionPlane jonesBoundaryRegressionPlaneFrame
    jonesBoundaryRegressionIncidentFrame jonesBoundaryRegressionReflectedFrame
    fresnelFluxRegressionQuadratureIncidentJones
    fresnelFluxRegressionQuadratureReflectedJones.propagationCross _ _ rfl rfl,
    jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent]
  simp only [JonesVector.propagationCross_components_zero,
    JonesVector.propagationCross_components_one]
  simp [Phasor.realize]
  ring

/-- The reflected-electric/incident-magnetic ordered normal term, reduced to the two Jones
quadratures of the exact regression fixture. -/
private lemma fresnelInterferenceRegression_reflectedIncident_ordered_term (time : Time) :
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionReflectedWave
            fresnelFluxRegressionQuadratureReflectedJones).electricField time
              jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionIncidentWave
              fresnelFluxRegressionQuadratureIncidentJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium time jonesBoundaryRegressionPlane.point) =
      (5 / 2 : ℝ) *
        ((4 / 5 : ℝ) *
            Phasor.realize (fresnelFluxRegressionQuadratureReflectedJones.components 0)
              ((jonesBoundaryRegressionReflectedWave
                fresnelFluxRegressionQuadratureReflectedJones).angularFrequency * (time : ℝ)) *
            Phasor.realize (fresnelFluxRegressionQuadratureIncidentJones.components 0)
              ((jonesBoundaryRegressionIncidentWave
                fresnelFluxRegressionQuadratureIncidentJones).angularFrequency * (time : ℝ)) +
          (-4 / 5 : ℝ) *
            Phasor.realize (fresnelFluxRegressionQuadratureReflectedJones.components 1)
              ((jonesBoundaryRegressionReflectedWave
                fresnelFluxRegressionQuadratureReflectedJones).angularFrequency * (time : ℝ)) *
            Phasor.realize (fresnelFluxRegressionQuadratureIncidentJones.components 1)
              ((jonesBoundaryRegressionIncidentWave
                fresnelFluxRegressionQuadratureIncidentJones).angularFrequency *
                  (time : ℝ))) := by
  have hIncident := jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureIncidentJones
  have hReflected := jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
    fresnelFluxRegressionQuadratureReflectedJones
  rw [hReflected.electricField_planePoint, hIncident.magneticFieldStrength_planePoint,
    Space.cross_smul, OrientedAffineHyperplane.normalComponent, inner_smul_right,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
  change (5 / 2 : ℝ) * jonesBoundaryRegressionPlane.normalComponent
    (jonesBoundaryRegressionReflectedFrame.realizeJones
        fresnelFluxRegressionQuadratureReflectedJones _ ⨯ₑ₃
      jonesBoundaryRegressionIncidentFrame.realizeJones
        fresnelFluxRegressionQuadratureIncidentJones.propagationCross _) = _
  rw [PolarizationFrame.normalComponent_cross_realizeJones_of_axis_zero_eq
    jonesBoundaryRegressionPlane jonesBoundaryRegressionPlaneFrame
    jonesBoundaryRegressionReflectedFrame jonesBoundaryRegressionIncidentFrame
    fresnelFluxRegressionQuadratureReflectedJones
    fresnelFluxRegressionQuadratureIncidentJones.propagationCross _ _ rfl rfl,
    jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent]
  simp only [JonesVector.propagationCross_components_zero,
    JonesVector.propagationCross_components_one]
  simp [Phasor.realize]
  ring

/-- The two ordered actual-field normal-interference terms are separately nonzero and cancel at
the stored interface point. At carrier phases `0` and `pi/2` their exact values are respectively
`(-10/11, 10/11)` and `(-2/5, 2/5)`.

Checking both ordered terms prevents a zero-only cancellation regression from hiding a common
conjugation or sign error. -/
lemma fresnelInterferenceRegression_actual_ordered_terms :
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionIncidentWave
            fresnelFluxRegressionQuadratureIncidentJones).electricField 0
              jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionReflectedWave
              fresnelFluxRegressionQuadratureReflectedJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium 0 jonesBoundaryRegressionPlane.point) =
      -10 / 11 ∧
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionReflectedWave
            fresnelFluxRegressionQuadratureReflectedJones).electricField 0
              jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionIncidentWave
              fresnelFluxRegressionQuadratureIncidentJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium 0 jonesBoundaryRegressionPlane.point) =
      10 / 11 ∧
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionIncidentWave
            fresnelFluxRegressionQuadratureIncidentJones).electricField
              ((Real.pi / 2 : ℝ) : Time) jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionReflectedWave
              fresnelFluxRegressionQuadratureReflectedJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium ((Real.pi / 2 : ℝ) : Time)
              jonesBoundaryRegressionPlane.point) = -2 / 5 ∧
    jonesBoundaryRegressionPlane.normalComponent
        ((jonesBoundaryRegressionReflectedWave
            fresnelFluxRegressionQuadratureReflectedJones).electricField
              ((Real.pi / 2 : ℝ) : Time) jonesBoundaryRegressionPlane.point ⨯ₑ₃
          (jonesBoundaryRegressionIncidentWave
              fresnelFluxRegressionQuadratureIncidentJones).magneticFieldStrength
            jonesBoundaryRegressionNegativeMedium ((Real.pi / 2 : ℝ) : Time)
              jonesBoundaryRegressionPlane.point) = 2 / 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fresnelInterferenceRegression_incidentReflected_ordered_term 0]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones, jonesBoundaryRegressionIncidentWave,
      jonesBoundaryRegressionReflectedWave, Phasor.realize]
  · rw [fresnelInterferenceRegression_reflectedIncident_ordered_term 0]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones, jonesBoundaryRegressionIncidentWave,
      jonesBoundaryRegressionReflectedWave, Phasor.realize]
  · rw [fresnelInterferenceRegression_incidentReflected_ordered_term
      ((Real.pi / 2 : ℝ) : Time)]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones, jonesBoundaryRegressionIncidentWave,
      jonesBoundaryRegressionReflectedWave, Phasor.realize]
  · rw [fresnelInterferenceRegression_reflectedIncident_ordered_term
      ((Real.pi / 2 : ℝ) : Time)]
    norm_num [fresnelFluxRegressionQuadratureIncidentJones,
      fresnelFluxRegressionQuadratureReflectedJones, jonesBoundaryRegressionIncidentWave,
      jonesBoundaryRegressionReflectedWave, Phasor.realize]

/-!

## C. Superposed-wave normal-flux balance

-/

/-- The independently solved exact boundary fixture satisfies the connected normal-flux law for
the actual superposed incident-plus-reflected fields at every period origin. -/
lemma jonesBoundaryRegression_exact_hasSuperposedWaveNormalFluxBalance (startTime : Time) :
    PlanarDielectricWaveConfiguration.HasSuperposedWaveNormalFluxBalance
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5))
      startTime := by
  exact PlanarDielectricWaveConfiguration.fresnel_superposedWave_normalFlux_balance
    jonesBoundaryRegression_exact_isFixedFrequencyElectricBoundary
    jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
    jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5)))
    (by rfl) (by rfl) (by rfl)
    (Or.inr (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_incidentNormalComponent,
        jonesBoundaryRegression_reflectedNormalComponent]
      norm_num))
    (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_incidentNormalComponent]
      norm_num)
    (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_transmittedNormalComponent]
      norm_num)
    startTime

/-- The canonical-incidence wrapper recovers the exact fixture's superposed actual-field
normal-flux balance without a supplied common plane frame, three common-plane axis equalities, or
exact reflected normal relation. -/
lemma jonesBoundaryRegression_exact_hasSuperposedWaveNormalFluxBalance_of_incidenceFrames
    (startTime : Time) :
    PlanarDielectricWaveConfiguration.HasSuperposedWaveNormalFluxBalance
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5))
      startTime := by
  exact
    PlanarDielectricWaveConfiguration.fresnel_superposedWave_normalFlux_balance_of_incidenceFrames
      jonesBoundaryRegression_exact_isFixedFrequencyElectricBoundary
      jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
      (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
        jonesBoundaryRegressionIncidentJones)
      (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
        (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))))
      (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
        (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5)))
      jonesBoundaryRegression_incident_isNonNormalIncidence
      jonesBoundaryRegression_transmitted_isNonNormalIncidence
      jonesBoundaryRegressionIncidentFrame_eq_incidencePolarizationFrame
      jonesBoundaryRegressionTransmittedFrame_eq_incidencePolarizationFrame
      (fun _ ↦ ⟨jonesBoundaryRegression_reflected_isNonNormalIncidence,
        jonesBoundaryRegressionReflectedFrame_eq_incidencePolarizationFrame⟩)
      (by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_incidentNormalComponent]
        norm_num)
      (fun _ ↦ by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_reflectedNormalComponent]
        norm_num)
      (by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_transmittedNormalComponent]
        norm_num)
      startTime

/-- The exact superposed negative-side normal mean flux is the independently checked transmitted
value `5304/3025`, at every period origin. -/
lemma fresnelInterferenceRegression_superposed_normalFlux_value (startTime : Time) :
    let configuration :=
      jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5)
    configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.incident.angularFrequency,
          ThreeDimension.poyntingVector
            (configuration.incident.electricField + configuration.reflected.electricField)
            (configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium +
              configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) = 5304 / 3025 := by
  dsimp only
  have hBalance :=
    jonesBoundaryRegression_exact_hasSuperposedWaveNormalFluxBalance startTime
  rw [PlanarDielectricWaveConfiguration.HasSuperposedWaveNormalFluxBalance] at hBalance
  rw [hBalance]
  have hTransmitted := jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
    (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))
  dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
  rw [show (jonesBoundaryRegressionIncidentWave
      jonesBoundaryRegressionIncidentJones).angularFrequency =
        (jonesBoundaryRegressionTransmittedWave
          (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5))).angularFrequency by rfl]
  rw [hTransmitted.normalComponent_intervalAverage_poyntingVector_planePoint]
  rw [jonesBoundaryRegression_transmittedNormalComponent]
  rw [JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.intensity_eq_sum_normSq, Fin.sum_univ_two,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  norm_num [jonesBoundaryRegressionTransmittedJones, Complex.normSq]

/-!

## D. Unequal-frequency zero reflection

-/

/-- A deliberately zero reflected carrier with dummy angular frequency `2`, distinct from the
incident carrier frequency `1`. -/
def fresnelInterferenceRegressionZeroReflectedWave : ComplexMonochromaticPlaneWave where
  angularFrequency := 2
  angularFrequency_pos := by norm_num
  waveVector := 0
  electricAmplitude := 0

/-- The exact negative-side incident wave paired with a zero reflected wave whose dummy carrier
frequency and normal direction do not satisfy the active-reflection relations. -/
def fresnelInterferenceRegressionZeroConfiguration : PlanarDielectricWaveConfiguration where
  interface := jonesBoundaryRegressionInterface
  incident := jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones
  reflected := fresnelInterferenceRegressionZeroReflectedWave
  transmitted := jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones

/-- A matched-medium configuration with the same active incident and transmitted wave and the
unequal-frequency zero reflected dummy carrier. -/
def fresnelInterferenceRegressionZeroMatchedConfiguration :
    PlanarDielectricWaveConfiguration where
  interface := fresnelAmplitudeRegressionMatchedInterface
  incident := jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones
  reflected := fresnelInterferenceRegressionZeroReflectedWave
  transmitted := jonesBoundaryRegressionIncidentWave jonesBoundaryRegressionIncidentJones

/-- The matched zero-reflection fixture satisfies electric phase matching and the referenced
joint-electric balance while leaving the reflected frequency and wave vector arbitrary. -/
lemma fresnelInterferenceRegressionZeroMatched_isFixedFrequencyElectricBoundary :
    fresnelInterferenceRegressionZeroMatchedConfiguration.IsFixedFrequencyElectricBoundary := by
  constructor
  · exact ⟨⟨rfl, rfl⟩, Or.inl rfl⟩
  · rw [PlanarDielectricWaveConfiguration.HasReferencedJointElectricBalance]
    dsimp only [fresnelInterferenceRegressionZeroMatchedConfiguration,
      fresnelAmplitudeRegressionMatchedInterface]
    have hZero :=
      (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude_eq_zero_iff
        jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
          fresnelInterferenceRegressionZeroReflectedWave).2 rfl
    rw [hZero]
    simp

/-- The matched zero-reflection fixture satisfies the referenced tangential magnetic balance. -/
lemma fresnelInterferenceRegressionZeroMatched_hasMagneticBalance :
    PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
      fresnelInterferenceRegressionZeroMatchedConfiguration := by
  rw [PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance]
  dsimp only [fresnelInterferenceRegressionZeroMatchedConfiguration,
    fresnelAmplitudeRegressionMatchedInterface]
  have hZero :=
    referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
      jonesBoundaryRegressionPlane jonesBoundaryRegressionNegativeMedium
        fresnelInterferenceRegressionZeroReflectedWave rfl
  rw [hZero]
  simp

/-- The canonical superposed-flux wrapper preserves a zero reflected carrier whose frequency is
unequal, whose wave vector is zero, and whose supplied frame is the non-canonical plane-normal
frame. -/
lemma fresnelInterferenceRegression_zeroReflection_canonicalSuperposedBalance
    (startTime : Time) :
    fresnelInterferenceRegressionZeroMatchedConfiguration.reflected.waveVector = 0 ∧
      ¬ IsNonNormalIncidence jonesBoundaryRegressionPlane.normal
        jonesBoundaryRegressionPlane.normal ∧
      fresnelInterferenceRegressionZeroMatchedConfiguration.reflected.angularFrequency ≠
        fresnelInterferenceRegressionZeroMatchedConfiguration.incident.angularFrequency ∧
      fresnelInterferenceRegressionZeroMatchedConfiguration.HasSuperposedWaveNormalFluxBalance
        startTime := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hNonNormal
    apply hNonNormal
    ext i
    fin_cases i <;> simp [crossProduct] <;> ring
  · norm_num [fresnelInterferenceRegressionZeroMatchedConfiguration,
      fresnelInterferenceRegressionZeroReflectedWave, jonesBoundaryRegressionIncidentWave,
      ComplexMonochromaticPlaneWave.ofReal_angularFrequency,
      JonesVector.toMaterialPlaneWave_angularFrequency]
  · exact
      PlanarDielectricWaveConfiguration.fresnel_superposedWave_normalFlux_balance_of_incidenceFrames
          (configuration := fresnelInterferenceRegressionZeroMatchedConfiguration)
          (incidentDirection := jonesBoundaryRegressionIncidentDirection)
          (reflectedDirection := jonesBoundaryRegressionPlane.normal)
          (transmittedDirection := jonesBoundaryRegressionIncidentDirection)
          (incidentFrame := jonesBoundaryRegressionIncidentFrame)
          (reflectedFrame := jonesBoundaryRegressionPlaneFrame)
          (transmittedFrame := jonesBoundaryRegressionIncidentFrame)
          (incidentJones := jonesBoundaryRegressionIncidentJones)
          (reflectedJones := JonesVector.ofComponents 0 0)
          (transmittedJones := jonesBoundaryRegressionIncidentJones)
          fresnelInterferenceRegressionZeroMatched_isFixedFrequencyElectricBoundary
          fresnelInterferenceRegressionZeroMatched_hasMagneticBalance
          (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
            jonesBoundaryRegressionIncidentJones)
          (Or.inl ⟨rfl, by
            ext i
            fin_cases i <;> rfl⟩)
          (by simpa only [fresnelInterferenceRegressionZeroMatchedConfiguration,
              fresnelAmplitudeRegressionMatchedInterface] using
            (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
              jonesBoundaryRegressionIncidentJones))
          jonesBoundaryRegression_incident_isNonNormalIncidence
          jonesBoundaryRegression_incident_isNonNormalIncidence
          jonesBoundaryRegressionIncidentFrame_eq_incidencePolarizationFrame
          jonesBoundaryRegressionIncidentFrame_eq_incidencePolarizationFrame
          (fun hActive ↦ (hActive rfl).elim)
          (by
            dsimp only [fresnelInterferenceRegressionZeroMatchedConfiguration,
              fresnelAmplitudeRegressionMatchedInterface]
            rw [jonesBoundaryRegression_incidentNormalComponent]
            norm_num)
          (fun hActive ↦ (hActive rfl).elim)
          (by
            dsimp only [fresnelInterferenceRegressionZeroMatchedConfiguration,
              fresnelAmplitudeRegressionMatchedInterface]
            rw [jonesBoundaryRegression_incidentNormalComponent]
            norm_num)
          startTime

/-- The own-period interference bridge accepts a zero reflected field with unequal dummy frequency
and without the active opposite-normal relation. -/
lemma fresnelInterferenceRegression_zeroReflection_unequalFrequency (startTime : Time) :
    let configuration := fresnelInterferenceRegressionZeroConfiguration
    configuration.reflected.angularFrequency ≠ configuration.incident.angularFrequency ∧
      configuration.interface.plane.normalComponent
          (⨍ time in startTime.val..startTime.val +
              2 * Real.pi / configuration.incident.angularFrequency,
            ThreeDimension.poyntingVector
              (configuration.incident.electricField + configuration.reflected.electricField)
              (configuration.incident.magneticFieldStrength
                  configuration.interface.negativeMedium +
                configuration.reflected.magneticFieldStrength
                  configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) =
        configuration.interface.plane.normalComponent
            (⨍ time in startTime.val..startTime.val +
                2 * Real.pi / configuration.incident.angularFrequency,
              ThreeDimension.poyntingVector configuration.incident.electricField
                (configuration.incident.magneticFieldStrength
                  configuration.interface.negativeMedium)
                (time : Time) configuration.interface.plane.point) +
          configuration.interface.plane.normalComponent
            (⨍ time in startTime.val..startTime.val +
                2 * Real.pi / configuration.reflected.angularFrequency,
              ThreeDimension.poyntingVector configuration.reflected.electricField
                (configuration.reflected.magneticFieldStrength
                  configuration.interface.negativeMedium)
                (time : Time) configuration.interface.plane.point) := by
  dsimp only
  constructor
  · norm_num [fresnelInterferenceRegressionZeroConfiguration,
      fresnelInterferenceRegressionZeroReflectedWave, jonesBoundaryRegressionIncidentWave,
      ComplexMonochromaticPlaneWave.ofReal_angularFrequency,
      JonesVector.toMaterialPlaneWave_angularFrequency]
  · exact
      incidentReflected_normalComponent_intervalAverage_poyntingVector_add_ownPeriods
        (configuration := fresnelInterferenceRegressionZeroConfiguration)
        jonesBoundaryRegressionPlaneFrame
        (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
          jonesBoundaryRegressionIncidentJones)
        (Or.inl ⟨rfl, by
          ext i
          fin_cases i <;> rfl⟩)
        rfl rfl (Or.inl rfl) (Or.inl rfl) startTime

end

end Optics
