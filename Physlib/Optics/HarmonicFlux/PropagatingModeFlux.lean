/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingModeRealization

/-!
# Actual one-period flux of synthesized propagating modes

## i. Overview

The existing one-period harmonic-average theorem identifies the actual instantaneous Poynting
vector of Maxwell-qualified synthesized fields with their closed phasor expression. Integrating
its stored-normal component over a supplied profile measure recovers exactly
`HarmonicFieldProfile.integratedMeanNormalFlux` of the restricted synthesized profile.

The measure is still supplied rather than inferred from geometry. This file does not assert mode
orthogonality, normalization, completeness, or a geometric aperture-area interpretation.

## ii. Key results

- `intervalAverage_poyntingVector_eq_synthesizedProfile`: the actual local mean-flux connector.
- `integratedActualMeanNormalFlux`: the measured actual one-period normal flux.
- `integral_intervalAverage_normalFlux_eq_modeSynthesis`: the measured actual-field identity.

## iii. Table of contents

- A. Actual local one-period flux
- B. Measured actual normal flux

## iv. References

This is Physlib-original normalization infrastructure. It introduces no interface role,
reciprocity, omitted-channel completeness, or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open MeasureTheory Space Time
open scoped Interval Real

noncomputable section

namespace PropagatingHarmonicModeFamily

variable {ι A : Type*} [Fintype ι] (family : PropagatingHarmonicModeFamily ι)

/-!

## A. Actual local one-period flux

-/

/-- The actual one-period Poynting mean of the synthesized Maxwell fields is the closed harmonic
expression of their coherent phasor profile. -/
lemma intervalAverage_poyntingVector_eq_synthesizedProfile
    (amplitude : ModeAmplitude ι) (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / family.angularFrequency,
      poyntingVector (family.synthesizedElectricField amplitude)
        (family.synthesizedMagneticFieldStrength amplitude) (time : Time) x) =
      timeAveragedPoyntingVector
        ((family.synthesizedProfile amplitude).electricPhasor x)
        ((family.synthesizedProfile amplitude).magneticFieldStrengthPhasor x) := by
  apply intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector
    ((family.synthesizedProfile amplitude).electricPhasor x)
    ((family.synthesizedProfile amplitude).magneticFieldStrengthPhasor x)
    family.angularFrequency family.angularFrequency_pos startTime x
  · exact fun time ↦ family.synthesizedElectricField_eq_realize amplitude time x
  · exact fun time ↦ family.synthesizedMagneticFieldStrength_eq_realize amplitude time x

/-!

## B. Measured actual normal flux

-/

/-- The actual one-period mean normal Poynting flux of synthesized fields, integrated over a
supplied measured profile-coordinate domain. -/
def integratedActualMeanNormalFlux [MeasurableSpace A] (measure : Measure A)
    (plane : OrientedAffineHyperplane 3) (point : A → Space)
    (amplitude : ModeAmplitude ι) (startTime : Time) : ℝ :=
  ∫ a, plane.normalComponent
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / family.angularFrequency,
      poyntingVector (family.synthesizedElectricField amplitude)
        (family.synthesizedMagneticFieldStrength amplitude)
        (time : Time) (point a)) ∂measure

/-- Integrating the actual one-period mean normal flux of the synthesized Maxwell fields recovers
the abstract integrated mean normal flux of the profile restricted through a supplied point map. -/
lemma integral_intervalAverage_normalFlux_eq_modeSynthesis
    [MeasurableSpace A] (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (point : A → Space) (amplitude : ModeAmplitude ι) (startTime : Time) :
    family.integratedActualMeanNormalFlux measure plane point amplitude startTime =
      HarmonicFieldProfile.integratedMeanNormalFlux measure plane
        (HarmonicFieldProfile.modeSynthesis (family.modeProfile point) amplitude) := by
  rw [integratedActualMeanNormalFlux]
  rw [HarmonicFieldProfile.integratedMeanNormalFlux]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [family.intervalAverage_poyntingVector_eq_synthesizedProfile amplitude startTime (point a)]
  simp [HarmonicFieldProfile.meanNormalFluxDensity, synthesizedProfile,
    HarmonicFieldProfile.modeSynthesis, modeProfile,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor]

end PropagatingHarmonicModeFamily

end

end Optics
