/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryMagnetic
public import Physlib.Optics.Interfaces.PlanarDielectric.ElectricFixedFrequency

/-!
# Fixed-frequency tangential magnetic balance at a planar dielectric boundary

## i. Overview

This file reduces the zero-free-surface-current tangential magnetic boundary law for the explicit
three-wave planar dielectric configuration to an equality of complex amplitudes referenced at the
interface plane's stored point.

The core result needs only transmitted frequency matching and the alternative that the reflected
referenced tangential magnetic amplitude is zero or its frequency matches. It evaluates the
ordinary real boundary law at the stored point for all times and recovers the complete complex
amplitude from two carrier quadratures. The convenient wrapper receives the existing
`IsElectricPhaseMatched` predicate, although its tangential wave-vector conditions are not used by
this stored-point result.

Free surface charge remains arbitrary. No transversality, material dispersion, Maxwell equation,
electric amplitude balance, or noncancellation guard is required. Unguarded convention statement
(review only): no propagation direction or carrier branch is assigned. No Fresnel coefficient,
observable, or power statement is required. A reflected wave with zero electric amplitude has zero
tangential magnetic amplitude and retains arbitrary dummy frequency and wave-vector data.

## ii. Key results

- `HasReferencedTangentialMagneticFieldStrengthBalance`: the stored-point-referenced complex
  tangential-`H` amplitude equation.
- `IsLocalBoundary.hasReferencedTangentialMagneticFieldStrengthBalance_of_frequencyMatching`: the
  direct fixed-frequency reduction from the actual zero-current boundary law.
- `IsLocalBoundary.hasReferencedTangentialMagneticFieldStrengthBalance`: the convenient electric
  phase-matching wrapper.

## iii. Table of contents

- A. Referenced tangential magnetic balance
- B. Recovery of complex amplitudes
- C. Zero-current boundary reduction

## iv. References

The reduction connects Physlib's existing local boundary, complex carrier, and fixed-frequency
electric APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Time
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Referenced tangential magnetic balance

-/

/-- The stored-point-referenced tangential magnetic-field-strength amplitude balance for the
three-wave planar dielectric configuration.

The incident and reflected amplitudes use the negative-side medium, while the transmitted
amplitude uses the positive-side medium. -/
def HasReferencedTangentialMagneticFieldStrengthBalance
    (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted =
    referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.incident +
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.reflected

/-!

## B. Recovery of complex amplitudes

-/

private lemma eq_of_temporal_realPart_eq
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency)
    (first second : EuclideanSpace ℂ (Fin 3))
    (h : ∀ t : Time,
      ComplexWaveVector.realPart
          (Complex.exp
            ((((angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) • first) =
        ComplexWaveVector.realPart
          (Complex.exp
            ((((angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) • second)) :
    first = second := by
  ext i
  apply Complex.ext
  · have hzero := congrArg (fun v ↦ v i) (h 0)
    simpa [ComplexWaveVector.realPart] using hzero
  · have hquarter := congrArg (fun v ↦ v i)
      (h ((Real.pi / (2 * angularFrequency) : ℝ) : Time))
    have hphase :
        angularFrequency * (Real.pi / (2 * angularFrequency)) = Real.pi / 2 := by
      field_simp [ne_of_gt hFrequency]
    rw [hphase] at hquarter
    have hneg : -(first i).im = -(second i).im := by
      simpa [ComplexWaveVector.realPart, Complex.mul_re] using hquarter
    exact neg_injective hneg

private lemma mediumTangentialMagneticFieldStrengthData_point_eq_of_zero_or_frequency_eq
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (angularFrequency : ℝ)
    (hAmplitudeOrFrequency :
      referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave = 0 ∨
        wave.angularFrequency = angularFrequency)
    (t : Time) :
    mediumTangentialMagneticFieldStrengthData plane medium wave t plane.point =
      ComplexWaveVector.realPart
        (Complex.exp
          ((((angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) •
            referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave) := by
  rcases hAmplitudeOrFrequency with hAmplitude | hFrequency
  · rw [mediumTangentialMagneticFieldStrengthData_point, hAmplitude]
    simp [ComplexWaveVector.realPart]
  · rw [mediumTangentialMagneticFieldStrengthData_point, hFrequency]

/-!

## C. Zero-current boundary reduction

-/

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity configuration.interface.plane}

/-- A full local boundary with zero free surface current equates the actual ordinary real
incident-plus-reflected and transmitted tangential magnetic-field-strength data. -/
lemma tangentialMagneticFieldStrengthData
    (h : configuration.IsLocalBoundary surfaceCharge 0)
    (t : Time) (x : configuration.interface.plane.carrier) :
    mediumTangentialMagneticFieldStrengthData configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident t x +
        mediumTangentialMagneticFieldStrengthData configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected t x =
      mediumTangentialMagneticFieldStrengthData configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted t x := by
  have hField :=
    IsPlanarMacroscopicBoundary.tangentialMagneticFieldStrength_eq_of_surfaceCurrent_eq_zero
      h t x rfl
  have hField' := congrArg Subtype.val hField
  simpa only [negativeTrace, positiveTrace, PlanarMacroscopicTrace.ofFields, Pi.add_apply,
    mediumTangentialMagneticFieldStrengthData,
    Space.OrientedAffineHyperplane.coe_projectionToTangent,
    Space.OrientedAffineHyperplane.tangentialProjection_add] using hField'

/-- A zero-current local boundary and sufficient stored-point carrier matching give the referenced
complex tangential magnetic-field-strength amplitude balance.

The reflected alternative permits either a zero referenced tangential magnetic amplitude or a
matched frequency. -/
lemma hasReferencedTangentialMagneticFieldStrengthBalance_of_frequencyMatching
    (h : configuration.IsLocalBoundary surfaceCharge 0)
    (hTransmittedFrequency :
      configuration.transmitted.angularFrequency = configuration.incident.angularFrequency)
    (hReflectedAmplitudeOrFrequency :
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected = 0 ∨
        configuration.reflected.angularFrequency = configuration.incident.angularFrequency) :
    configuration.HasReferencedTangentialMagneticFieldStrengthBalance := by
  let planePoint : configuration.interface.plane.carrier :=
    ⟨configuration.interface.plane.point, configuration.interface.plane.point_mem_carrier⟩
  have hReal : ∀ t : Time,
      ComplexWaveVector.realPart
          (Complex.exp
            ((((configuration.incident.angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) •
            (referencedMediumTangentialMagneticFieldStrengthAmplitude
                  configuration.interface.plane configuration.interface.negativeMedium
                  configuration.incident +
              referencedMediumTangentialMagneticFieldStrengthAmplitude
                configuration.interface.plane configuration.interface.negativeMedium
                  configuration.reflected)) =
        ComplexWaveVector.realPart
          (Complex.exp
            ((((configuration.incident.angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) •
            referencedMediumTangentialMagneticFieldStrengthAmplitude
              configuration.interface.plane configuration.interface.positiveMedium
                configuration.transmitted) := by
    intro t
    have ht := h.tangentialMagneticFieldStrengthData t planePoint
    change _ = _ at ht
    rw [mediumTangentialMagneticFieldStrengthData_point_eq_of_zero_or_frequency_eq
          _ _ _ _ (Or.inr rfl),
      mediumTangentialMagneticFieldStrengthData_point_eq_of_zero_or_frequency_eq
        _ _ _ _ hReflectedAmplitudeOrFrequency,
      mediumTangentialMagneticFieldStrengthData_point_eq_of_zero_or_frequency_eq
        _ _ _ _ (Or.inr hTransmittedFrequency)] at ht
    ext i
    have hti := congrArg (fun v ↦ v i) ht
    simpa [ComplexWaveVector.realPart, Complex.mul_re] using hti
  exact (eq_of_temporal_realPart_eq configuration.incident.angularFrequency
    configuration.incident.angularFrequency_pos _ _ hReal).symm

/-- A zero-current local boundary plus the existing electric phase-matching predicate gives the
stored-point-referenced tangential magnetic-field-strength amplitude balance. -/
lemma hasReferencedTangentialMagneticFieldStrengthBalance
    (h : configuration.IsLocalBoundary surfaceCharge 0)
    (hPhase : configuration.IsElectricPhaseMatched) :
    configuration.HasReferencedTangentialMagneticFieldStrengthBalance := by
  apply h.hasReferencedTangentialMagneticFieldStrengthBalance_of_frequencyMatching hPhase.1.1
  rcases hPhase.2 with hZero | hMatched
  · exact Or.inl
      (referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
        configuration.interface.plane configuration.interface.negativeMedium
          configuration.reflected hZero)
  · exact Or.inr hMatched.1

end IsLocalBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
