/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexAmplitude
public import Physlib.Optics.HarmonicFlux.ComplexMaterialWave
public import Physlib.Optics.HarmonicFlux.ModePower

/-!
# Maxwell-qualified propagating harmonic mode profiles

## i. Overview

This file connects the abstract measured harmonic profiles used by the Optics normalization layer
to a family of complex plane-wave carriers in one homogeneous isotropic medium. Every carrier has
the same stored positive angular frequency, zero wave-vector attenuation, bilinear electric
transversality, and material dispersion. Consequently every member is an ordinary-real,
source-free macroscopic Maxwell solution.

A supplied profile-coordinate map selects spatial sample points. The resulting electric and
magnetic-field-strength phasors are exactly the local phasors of the physical carrier. Their
abstract integrated mean normal flux is therefore the integral of the actual one-period mean
Poynting flux of that carrier.

The coordinate map and measure remain separate data. This file does not claim that an arbitrary
map parameterizes an aperture or that an arbitrary supplied measure is pulled-back geometric
area. Complex-coefficient synthesis and its Maxwell qualification are separate follow-ups.

## ii. Key results

- `PropagatingHarmonicModeFamily`: common-frequency propagating on-shell carrier data.
- `PropagatingHarmonicModeFamily.modeProfile`: its local harmonic field profile.
- `wave_phaseVector_norm_mul_waveSpeed`: the zero-attenuation positive dispersion branch.
- `wave_isMacroscopicMaxwellSolution`: every stored wave solves the fixed-medium equations.
- `intervalAverage_poyntingVector_eq_modeProfile`: the actual local one-period connector.
- `integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux`: its measured integral.

## iii. Table of contents

- A. Common-frequency propagating mode families
- B. Local harmonic profiles and Maxwell qualification
- C. Actual one-period normal-flux integration

## iv. References

This physical connector is Physlib-original relative to the audited HOL optics corpus. It proves
only the stated finite-carrier/profile relation and introduces no modal completeness, boundary
condition, interface role, reciprocity, or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open Electromagnetism ThreeDimension
open ClassicalMechanics MeasureTheory Space Time
open scoped Interval Real

noncomputable section

/-!

## A. Common-frequency propagating mode families

-/

/-- A family of zero-attenuation transverse plane-wave carriers sharing one positive frequency
and one homogeneous isotropic material shell.

Zero attenuation supplies the propagating, rather than evanescent, branch. Dispersion and
transversality are stored as proof obligations, not inferred from the name. The family need not be
complete or flux normalized. -/
structure PropagatingHarmonicModeFamily (ι : Type*) where
  /-- The common homogeneous isotropic medium. -/
  medium : HomogeneousIsotropicMedium
  /-- The common positive angular frequency. -/
  angularFrequency : ℝ
  /-- Positivity of the common angular frequency, including for an empty mode family. -/
  angularFrequency_pos : 0 < angularFrequency
  /-- The complex-amplitude plane-wave carrier assigned to each mode label. -/
  wave : ι → ComplexMonochromaticPlaneWave
  /-- Every carrier has the declared common angular frequency. -/
  commonAngularFrequency : ∀ i, (wave i).angularFrequency = angularFrequency
  /-- Every carrier has zero spatial attenuation. -/
  zeroAttenuation : ∀ i, (wave i).waveVector.attenuationVector = 0
  /-- Every electric amplitude is complex-bilinearly transverse. -/
  isTransverse : ∀ i, (wave i).IsTransverse
  /-- Every carrier lies on the common material dispersion shell. -/
  isDispersionMatched : ∀ i, (wave i).IsDispersionMatched medium

namespace PropagatingHarmonicModeFamily

variable {ι A : Type*} (family : PropagatingHarmonicModeFamily ι)

/-!

## B. Local harmonic profiles and Maxwell qualification

-/

/-- The local electric and magnetic-field-strength phasors of one mode, sampled through a
supplied profile-coordinate map. -/
def modeProfile (point : A → Space) (i : ι) : HarmonicFieldProfile A :=
  fun a ↦ ((family.wave i).localElectricPhasor (point a),
    (family.wave i).localMagneticFieldStrengthPhasor family.medium (point a))

@[simp]
lemma modeProfile_electricPhasor (point : A → Space) (i : ι) (a : A) :
    (family.modeProfile point i).electricPhasor a =
      (family.wave i).localElectricPhasor (point a) := rfl

@[simp]
lemma modeProfile_magneticFieldStrengthPhasor (point : A → Space) (i : ι) (a : A) :
    (family.modeProfile point i).magneticFieldStrengthPhasor a =
      (family.wave i).localMagneticFieldStrengthPhasor family.medium (point a) := rfl

/-- Every stored mode lies on the positive propagating branch
`‖phaseVector‖ * waveSpeed = angularFrequency`. -/
lemma wave_phaseVector_norm_mul_waveSpeed (i : ι) :
    ‖(family.wave i).waveVector.phaseVector‖ * family.medium.waveSpeed =
      family.angularFrequency := by
  rw [← family.commonAngularFrequency i]
  exact (family.isDispersionMatched i).phaseVector_norm_mul_waveSpeed
    (family.zeroAttenuation i)

/-- Every stored mode is a source-free macroscopic Maxwell solution in the family's medium. -/
lemma wave_isSourceFreeMacroscopicMaxwell (i : ι) :
    IsSourceFreeMacroscopicMaxwell (family.wave i).electricField
      ((family.wave i).electricDisplacement family.medium)
      (family.wave i).magneticInduction
      ((family.wave i).magneticFieldStrength family.medium) :=
  (family.wave i).isSourceFreeMacroscopicMaxwell family.medium
    (family.isTransverse i) (family.isDispersionMatched i)

/-- Every stored mode is a fixed-medium macroscopic Maxwell solution. -/
lemma wave_isMacroscopicMaxwellSolution (i : ι) :
    family.medium.IsMacroscopicMaxwellSolution (family.wave i).electricField
      ((family.wave i).electricDisplacement family.medium)
      (family.wave i).magneticInduction
      ((family.wave i).magneticFieldStrength family.medium) 0 0 :=
  (family.wave i).isMacroscopicMaxwellSolution family.medium
    (family.isTransverse i) (family.isDispersionMatched i)

/-!

## C. Actual one-period normal-flux integration

-/

/-- At every profile coordinate, the actual one-period mean Poynting vector of a stored wave is
the closed harmonic-flux expression of its associated mode profile. -/
lemma intervalAverage_poyntingVector_eq_modeProfile (point : A → Space) (i : ι)
    (startTime : Time) (a : A) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / family.angularFrequency,
      poyntingVector (family.wave i).electricField
        ((family.wave i).magneticFieldStrength family.medium) (time : Time) (point a)) =
      timeAveragedPoyntingVector ((family.modeProfile point i).electricPhasor a)
        ((family.modeProfile point i).magneticFieldStrengthPhasor a) := by
  have h := (family.wave i).intervalAverage_poyntingVector_eq_localPhasors
    family.medium startTime (point a)
  rw [family.commonAngularFrequency i] at h
  exact h

/-- Integrating the actual one-period mean normal Poynting flux over a supplied profile measure
gives the abstract integrated mean normal flux of the corresponding physical mode profile.

This equality does not interpret the supplied measure as geometric area. Physical normalization
also requires the self-integrability carried by `IsApertureFluxOrthonormal`. -/
lemma integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux
    [MeasurableSpace A] (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (point : A → Space) (i : ι) (startTime : Time) :
    (∫ a, plane.normalComponent
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi / family.angularFrequency,
        poyntingVector (family.wave i).electricField
          ((family.wave i).magneticFieldStrength family.medium)
          (time : Time) (point a)) ∂measure) =
      HarmonicFieldProfile.integratedMeanNormalFlux measure plane
        (family.modeProfile point i) := by
  rw [HarmonicFieldProfile.integratedMeanNormalFlux]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [family.intervalAverage_poyntingVector_eq_modeProfile point i startTime a]
  rfl

end PropagatingHarmonicModeFamily

end

end Optics
