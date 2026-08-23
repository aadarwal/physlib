/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryExponent

/-!
# Joint electric boundary amplitudes of complex plane waves

## i. Overview

This file uses the neutral complex-wave-vector hyperplane decomposition to package the tangential
electric amplitude together with the scalar normal electric-displacement amplitude of one off-shell
complex-amplitude plane-wave candidate relative to an oriented affine hyperplane and a homogeneous
isotropic medium. This joint amplitude vanishes exactly when the stored electric amplitude
vanishes, because the medium permittivity is nonzero.
It is therefore suitable for stating the electromagnetic noncancellation hypotheses needed by
later boundary-exponent collision results; tangential `E` alone would not detect a purely normal
electric amplitude. The zero criterion is per wave. Contributions from distinct wave labels may
cancel, so this result alone gives no labelwise conclusion from a boundary equality. A nonzero
complex amplitude also need not give a nonzero ordinary real value at a selected single sample;
later harmonic uniqueness uses all boundary parameters.

The complex joint amplitude is calculation data, not a physical complex field or a replacement for
the ordinary real macroscopic boundary trace. Its componentwise real realization is proved equal
to the actual ordinary real tangential electric field and normal electric displacement. On the
affine plane, the carrier factorization from `ComplexBoundaryExponent` gives a positive-rate
exponential character multiplying the amplitude referenced to the plane's stored point. That
referencing preserves the exact zero criterion because the spatial factor never vanishes.
For an attenuating wave, the reference factor can change the amplitude's modulus, so this is not
merely phase referencing and does not define a canonical, reference-point-independent amplitude.

The supplied medium contributes only its real scalar permittivity; its permeability is unused. This
does not assert that the wave satisfies Maxwell equations or material dispersion in that medium.
The construction states no boundary equality, surface-source condition, interface side,
incident/reflected/transmitted role, frequency or tangential-wave-vector conservation, outgoing or
decay branch, Fresnel coefficient, irradiance, or power result. It does not encode all four
macroscopic boundary laws: the magnetic and remaining electric data stay in
`PlanarMacroscopicTrace`.

## ii. Key results

- `ComplexMonochromaticPlaneWave.mediumJointElectricTraceAmplitude_eq_zero_iff`: the joint
  tangential-`E` and normal-`D` calculation amplitude detects exactly the electric amplitude.
- `ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude_eq_zero_iff`:
  affine-point referencing preserves that criterion.
- `ComplexMonochromaticPlaneWave.mediumJointElectricFieldData_eq_realPart_smul_amplitude`: the
  ordinary real joint field data is the real realization of the carrier-weighted amplitude.
- `ComplexMonochromaticPlaneWave.mediumJointElectricFieldData_tangent_vadd_point`: exact boundary
  factorization using the referenced amplitude and boundary exponent.

## iii. Table of contents

- A. Medium-dependent joint electric amplitudes
- B. Ordinary real joint electric field data
- C. Affine-plane realization

## iv. References

The construction uses Physlib's existing complex-carrier, homogeneous-medium, and oriented affine
hyperplane APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Medium-dependent joint electric amplitudes

-/

/-- The coefficient type for tangential electric amplitude paired with scalar normal
electric-displacement amplitude. -/
abbrev JointElectricTraceAmplitude := EuclideanSpace ℂ (Fin 3) × ℂ

/-- The medium-dependent joint electric trace amplitude of one complex plane-wave candidate.

The first entry is tangential `E0`. The second is `epsilon * (n dot E0)`, the scalar normal
amplitude of `D0 = epsilon E0` in the supplied homogeneous isotropic medium. -/
def mediumJointElectricTraceAmplitude (plane : OrientedAffineHyperplane 3)
    (medium : HomogeneousIsotropicMedium) (wave : ComplexMonochromaticPlaneWave) :
    JointElectricTraceAmplitude :=
  (ComplexWaveVector.hyperplaneTangentialProjection plane wave.electricAmplitude,
    (medium.ε : ℂ) *
      ComplexWaveVector.hyperplaneNormalComponent plane wave.electricAmplitude)

/-- A medium-dependent joint electric trace amplitude vanishes exactly when the electric
amplitude vanishes. -/
lemma mediumJointElectricTraceAmplitude_eq_zero_iff
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) :
    mediumJointElectricTraceAmplitude plane medium wave = 0 ↔
      wave.electricAmplitude = 0 := by
  constructor
  · intro h
    have htangent :
        ComplexWaveVector.hyperplaneTangentialProjection plane wave.electricAmplitude = 0 :=
      congrArg Prod.fst h
    have hnormalScaled :
        (medium.ε : ℂ) *
            ComplexWaveVector.hyperplaneNormalComponent plane wave.electricAmplitude = 0 :=
      congrArg Prod.snd h
    have hε : (medium.ε : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr medium.ε_ne_zero
    have hnormal :
        ComplexWaveVector.hyperplaneNormalComponent plane wave.electricAmplitude = 0 :=
      (mul_eq_zero.mp hnormalScaled).resolve_left hε
    rw [← ComplexWaveVector.hyperplaneTangentialProjection_add_normal
        plane wave.electricAmplitude,
      htangent, hnormal]
    simp
  · rintro h
    simp [mediumJointElectricTraceAmplitude, h,
      ComplexWaveVector.hyperplaneTangentialProjection,
      ComplexWaveVector.hyperplaneNormalComponent]

/-- The medium-dependent joint electric trace amplitude referenced to the oriented hyperplane's
stored affine point. -/
def referencedMediumJointElectricTraceAmplitude
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) : JointElectricTraceAmplitude :=
  wave.waveVector.spatialFactor plane.point •
    mediumJointElectricTraceAmplitude plane medium wave

/-- Affine-point carrier referencing preserves the criterion that the electric amplitude is zero. -/
lemma referencedMediumJointElectricTraceAmplitude_eq_zero_iff
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) :
    referencedMediumJointElectricTraceAmplitude plane medium wave = 0 ↔
      wave.electricAmplitude = 0 := by
  rw [referencedMediumJointElectricTraceAmplitude, smul_eq_zero,
    or_iff_right (wave.waveVector.spatialFactor_ne_zero plane.point),
    mediumJointElectricTraceAmplitude_eq_zero_iff]

/-!

## B. Ordinary real joint electric field data

-/

/-- Take componentwise real parts of a complex joint electric trace amplitude. -/
def realPartJointElectricTraceAmplitude (z : JointElectricTraceAmplitude) :
    EuclideanSpace ℝ (Fin 3) × ℝ :=
  (ComplexWaveVector.realPart z.1, z.2.re)

/-- The actual ordinary-real tangential electric field and scalar normal electric displacement of
one complex plane-wave candidate relative to a supplied oriented plane and homogeneous isotropic
medium.

The formula is defined at every spatial point. Its affine-plane specialization below supplies the
reduced boundary data used by the later collision argument; it is not a replacement for
`PlanarMacroscopicTrace`. -/
def mediumJointElectricFieldData (plane : OrientedAffineHyperplane 3)
    (medium : HomogeneousIsotropicMedium) (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) : EuclideanSpace ℝ (Fin 3) × ℝ :=
  (plane.tangentialProjection (wave.electricField t x),
    plane.normalComponent (wave.electricDisplacement medium t x))

private lemma normalComponent_realPart_smul
    (plane : OrientedAffineHyperplane 3) (c : ℂ) (z : EuclideanSpace ℂ (Fin 3)) :
    plane.normalComponent (ComplexWaveVector.realPart (c • z)) =
      (c * ComplexWaveVector.hyperplaneNormalComponent plane z).re := by
  rw [Space.OrientedAffineHyperplane.normalComponent, PiLp.inner_apply,
    ComplexWaveVector.hyperplaneNormalComponent, ComplexWaveVector.bilinearDot, Finset.mul_sum,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ComplexWaveVector.ofReal_apply, ComplexWaveVector.realPart_apply,
    PiLp.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.im_ofReal_mul, RCLike.inner_apply, conj_trivial]
  ring

private lemma tangentialProjection_realPart_smul
    (plane : OrientedAffineHyperplane 3) (c : ℂ) (z : EuclideanSpace ℂ (Fin 3)) :
    plane.tangentialProjection (ComplexWaveVector.realPart (c • z)) =
      ComplexWaveVector.realPart
        (c • ComplexWaveVector.hyperplaneTangentialProjection plane z) := by
  ext i
  rw [Space.OrientedAffineHyperplane.tangentialProjection, PiLp.sub_apply,
    PiLp.smul_apply, normalComponent_realPart_smul]
  simp only [ComplexWaveVector.realPart_apply, PiLp.smul_apply, smul_eq_mul,
    ComplexWaveVector.hyperplaneTangentialProjection, PiLp.sub_apply,
    ComplexWaveVector.ofReal_apply,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The ordinary real joint electric field data is the componentwise real realization of the
shared carrier multiplying its medium-dependent complex trace amplitude. -/
lemma mediumJointElectricFieldData_eq_realPart_smul_amplitude
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    mediumJointElectricFieldData plane medium wave t x =
      realPartJointElectricTraceAmplitude
        (wave.carrier t x • mediumJointElectricTraceAmplitude plane medium wave) := by
  apply Prod.ext
  · exact tangentialProjection_realPart_smul plane
      (wave.carrier t x) wave.electricAmplitude
  · rw [mediumJointElectricFieldData, realPartJointElectricTraceAmplitude,
      mediumJointElectricTraceAmplitude]
    simp only [Prod.smul_snd, smul_eq_mul]
    rw [electricDisplacement,
      HomogeneousIsotropicMedium.electricDisplacement_apply,
      Space.OrientedAffineHyperplane.normalComponent, inner_smul_right]
    change medium.ε *
        plane.normalComponent
          (ComplexWaveVector.realPart (wave.carrier t x • wave.electricAmplitude)) = _
    rw [normalComponent_realPart_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im]
    ring

/-!

## C. Affine-plane realization

-/

private lemma carrier_smul_mediumJointElectricTraceAmplitude_tangent_vadd_point
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (v : plane.tangentSubmodule) :
    wave.carrier t ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ plane.point) •
        mediumJointElectricTraceAmplitude plane medium wave =
      Complex.exp (wave.boundaryExponent plane (t, v)) •
        referencedMediumJointElectricTraceAmplitude plane medium wave := by
  rw [carrier_tangent_vadd_point]
  simp [referencedMediumJointElectricTraceAmplitude, smul_smul]

/-- The actual ordinary real tangential-`E` and normal-`D` data on the affine plane is the real
realization of one positive-rate exponential character with its affine-point-referenced
medium-dependent joint amplitude. -/
lemma mediumJointElectricFieldData_tangent_vadd_point
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (v : plane.tangentSubmodule) :
    mediumJointElectricFieldData plane medium wave t
        ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ plane.point) =
      realPartJointElectricTraceAmplitude
        (Complex.exp (wave.boundaryExponent plane (t, v)) •
          referencedMediumJointElectricTraceAmplitude plane medium wave) := by
  rw [mediumJointElectricFieldData_eq_realPart_smul_amplitude,
    carrier_smul_mediumJointElectricTraceAmplitude_tangent_vadd_point]

end ComplexMonochromaticPlaneWave

end
end ThreeDimension
end Electromagnetism
