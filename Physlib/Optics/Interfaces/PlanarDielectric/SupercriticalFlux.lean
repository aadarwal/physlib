/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell
public import Physlib.Optics.HarmonicFlux.PositiveNormalDecay
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalCarrier

/-!
# Maxwell and harmonic flux for supercritical transmitted carriers

## i. Overview

This file gives the canonical positive-normal-decay transmitted carrier its first
electromagnetic and flux consequences. A carrier satisfying
`IsPositiveNormalDecayTransmittedCandidate` is already dispersion matched to the positive-side
medium. Adding bilinear electric transversality therefore proves that its ordinary-real fields
solve the source-free macroscopic Maxwell equations in that medium.

The same hypotheses also force the actual one-period mean Poynting vector to have zero component
along the interface's stored normal at every spatial point. The flux cancellation itself uses
only transversality and positive-normal-decay geometry; the candidate's material shell is used by
the separate Maxwell result.

## ii. Key results

- `IsPositiveNormalDecayTransmittedCandidate.isMacroscopicMaxwellSolution`: positive-medium
  source-free Maxwell qualification.
- Zero stored-normal one-period mean flux:
  `normalComponent_intervalAverage_poyntingVector_eq_zero`.

## iii. Table of contents

- A. Positive-medium Maxwell qualification
- B. Stored-normal harmonic flux

## iv. Scope

The transmitted name records the configuration slot and the selected positive-normal-decay
branch. These results do not prove any interface boundary-amplitude law, Fresnel coefficient,
reflected-wave balance, outgoing radiation condition, or total internal reflection. Zero mean
normal flux does not mean zero field, zero stored energy, zero tangential flux, or pointwise zero
normal Poynting vector. The statement is local flux density, not aperture-integrated or modal
power, and the globally defined carrier still grows on the opposite side of the interface.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace
  MeasureTheory Space Time
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open scoped Interval Real

noncomputable section

namespace PlanarDielectricWaveConfiguration
namespace IsPositiveNormalDecayTransmittedCandidate

variable {configuration : PlanarDielectricWaveConfiguration}
  {wave : ComplexMonochromaticPlaneWave}

/-!

## A. Positive-medium Maxwell qualification

-/

/-- A bilinearly transverse positive-normal-decay transmitted candidate is a source-free
macroscopic Maxwell solution in the interface's positive-side medium.

The candidate predicate supplies material dispersion but no electric transversality; the latter
is therefore an explicit hypothesis. Zero electric amplitude remains allowed. -/
lemma isMacroscopicMaxwellSolution
    (h : configuration.IsPositiveNormalDecayTransmittedCandidate wave)
    (hTransverse : wave.IsTransverse) :
    configuration.interface.positiveMedium.IsMacroscopicMaxwellSolution
      wave.electricField
      (wave.electricDisplacement configuration.interface.positiveMedium)
      wave.magneticInduction
      (wave.magneticFieldStrength configuration.interface.positiveMedium) 0 0 := by
  exact wave.isMacroscopicMaxwellSolution configuration.interface.positiveMedium
    hTransverse h.isDispersionMatched

/-!

## B. Stored-normal harmonic flux

-/

/-- A bilinearly transverse positive-normal-decay transmitted candidate has zero actual
one-period mean Poynting component along the interface's stored normal at every point and period
start.

This averaged conclusion does not assert pointwise zero normal flux. Its algebra does not use the
candidate's material-dispersion clause, although that clause combines with transversality in
`isMacroscopicMaxwellSolution`. -/
lemma normalComponent_intervalAverage_poyntingVector_eq_zero
    (h : configuration.IsPositiveNormalDecayTransmittedCandidate wave)
    (hTransverse : wave.IsTransverse) (startTime : Time) (x : Space) :
    configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
        poyntingVector wave.electricField
          (wave.magneticFieldStrength configuration.interface.positiveMedium)
          (time : Time) x) = 0 := by
  have hRadicand : configuration.transmittedNormalRadicand < 0 :=
    h.2.normalRoot_data.1
  let data := configuration.positiveNormalDecayTransmittedData hRadicand
  have hWaveVector : wave.waveVector = data.waveVector := by
    calc
      wave.waveVector = configuration.positiveNormalDecayTransmittedWaveVector :=
        h.2.eq_positiveNormalDecayTransmittedWaveVector
      _ = data.waveVector :=
        (configuration.positiveNormalDecayTransmittedData_waveVector hRadicand).symm
  have hzero :=
    inner_normalVector_intervalAverage_poyntingVector_eq_zero_of_positiveNormalDecay wave
      configuration.interface.positiveMedium data hWaveVector hTransverse startTime x
  have hnormal : data.normalVector = configuration.interface.plane.normalVector := by
    simpa only [data] using
      configuration.positiveNormalDecayTransmittedData_normalVector hRadicand
  rw [hnormal] at hzero
  exact hzero

end IsPositiveNormalDecayTransmittedCandidate
end PlanarDielectricWaveConfiguration

end
end Optics
