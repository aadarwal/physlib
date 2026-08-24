/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryMagnetic
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFlux
public import Physlib.Optics.Polarization.PositiveNormalDecayFrame

/-!
# Polarization of negative-radicand transmitted carriers

## i. Overview

This file equips the canonical positive-normal-decay transmitted wave vector on the negative-
radicand branch of a planar dielectric interface with the complex-bilinear `s`/`p` frame from
`PositiveNormalDecayPolarizationFrame`. The positive material wavenumber is

`beta = omega / v_2`,

and the strict negative-radicand hypothesis supplies positive decay data. Under the separate
incident hypotheses already proved in `SupercriticalTransmission`, this is the branch selected by
strict sine-supercritical incidence. Thus

```text
s = normalize (n cross q), p = (K cross s) / beta,
```

where `q` is the incident tangential phase vector and `K` is the canonical transmitted complex
wave vector. The full-vector `p` axis has fixed-plane tangential coefficient
`-I * sqrt (-radicand) / beta` and normal coefficient `|q| / beta`.

A raw Jones vector can be embedded as the electric amplitude of the canonical transmitted
carrier. The resulting candidate is automatically bilinearly transverse and dispersion matched,
and its compatible magnetic-induction amplitude obeys the material-wavenumber quarter-turn.
No boundary condition chooses the Jones amplitudes here, and no outgoing, total-internal-
reflection, irradiance, or power claim is made.

## ii. Key results

- `PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame`: the
  canonical complex-bilinear negative-radicand `s`/`p` frame.
- `positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent`:
  the fixed-plane `p` factor `-I * sqrt (-radicand) / beta`.
- `PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedJonesCandidate`: the canonical
  carrier with a raw Jones-coordinate electric amplitude.
- `positiveNormalDecayTransmittedJonesCandidate_isTransverse`:
  automatic bilinear transversality.
- `positiveNormalDecayTransmittedJonesCandidate_magneticAmplitude`:
  the positive-medium inverse-speed magnetic-induction-amplitude quarter-turn.
- `positiveNormalDecayTransmittedJonesCandidate_tangentialElectricAmplitude` and
  `positiveNormalDecayTransmittedJonesCandidate_tangentialMagneticFieldStrengthAmplitude`:
  fixed-plane electric and magnetic-field-strength coordinates.
- `positiveNormalDecayTransmittedJonesCandidate_isMacroscopicMaxwellSolution`:
  the negative-radicand positive-medium Maxwell solution.
- `positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero`:
  zero stored-normal one-period mean flux.

## iii. Table of contents

- A. Canonical negative-radicand polarization frame
- B. Raw Jones-amplitude carrier family

## iv. References

The construction specializes Physlib's independently defined positive-normal-decay carrier and
complex-bilinear polarization-frame APIs. No external formal-development source is copied or
translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension MeasureTheory Space Time
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open scoped Interval Real

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Canonical negative-radicand polarization frame

-/

/-- The complex-bilinear `s`/`p` frame of the canonical positive-normal-decay transmitted wave
vector, normalized by the positive-medium material wavenumber `omega / v_2`. -/
noncomputable def positiveNormalDecayTransmittedPolarizationFrame
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    PositiveNormalDecayPolarizationFrame configuration.interface.plane.normal where
  data := configuration.positiveNormalDecayTransmittedData hRadicand
  waveNumber := configuration.incident.angularFrequency /
    configuration.interface.positiveMedium.waveSpeed
  waveNumber_pos := div_pos configuration.incident.angularFrequency_pos
    configuration.interface.positiveMedium.waveSpeed_pos
  bilinearSquare := by
    have hScale :
        (configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed) ^ 2 =
          configuration.interface.positiveMedium.ε *
            configuration.interface.positiveMedium.μ *
              configuration.incident.angularFrequency ^ 2 := by
      rw [div_pow, configuration.interface.positiveMedium.waveSpeed_sq]
      field_simp [configuration.interface.positiveMedium.ε_ne_zero,
        configuration.interface.positiveMedium.μ_ne_zero]
    calc
      bilinearDot (configuration.positiveNormalDecayTransmittedData hRadicand).waveVector
          (configuration.positiveNormalDecayTransmittedData hRadicand).waveVector =
        bilinearDot configuration.positiveNormalDecayTransmittedWaveVector
          configuration.positiveNormalDecayTransmittedWaveVector := by
            rw [configuration.positiveNormalDecayTransmittedData_waveVector hRadicand]
      _ = ((configuration.interface.positiveMedium.ε *
            configuration.interface.positiveMedium.μ *
            configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) :=
        configuration.bilinearDot_positiveNormalDecayTransmittedWaveVector_self hRadicand.le
      _ = ((configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed : ℝ) : ℂ) ^ 2 := by
        exact_mod_cast hScale.symm

@[simp]
lemma positiveNormalDecayTransmittedPolarizationFrame_waveNumber
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).waveNumber =
      configuration.incident.angularFrequency /
        configuration.interface.positiveMedium.waveSpeed := rfl

@[simp]
lemma positiveNormalDecayTransmittedPolarizationFrame_decayRate
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).data.decayRate =
      Real.sqrt (-configuration.transmittedNormalRadicand) := rfl

/-- The frame's decay data represents the canonical transmitted complex wave vector. -/
lemma positiveNormalDecayTransmittedPolarizationFrame_waveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).data.waveVector =
      configuration.positiveNormalDecayTransmittedWaveVector :=
  configuration.positiveNormalDecayTransmittedData_waveVector hRadicand

/-- The normalized transmitted normal component is
`-I * sqrt (-transmittedNormalRadicand) / (omega / v_2)`. -/
lemma positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane =
      -Complex.I *
        ((Real.sqrt (-configuration.transmittedNormalRadicand) /
          (configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed) : ℝ) : ℂ) := by
  exact (configuration.positiveNormalDecayTransmittedPolarizationFrame
    hRadicand).normalizedWaveVectorNormalComponent_eq_neg_I_mul configuration.interface.plane

/-!

## B. Raw Jones-amplitude carrier family

-/

/-- The canonical positive-normal-decay transmitted carrier whose electric amplitude is a raw
Jones vector embedded in the complex-bilinear transmitted `s`/`p` frame.

The Jones data is not selected by boundary equations and its standard intensity is not asserted
to equal the Hermitian norm or power of the embedded field. It is a carrier amplitude at the
coordinate origin, not Jones data referenced to the interface's stored affine point. -/
noncomputable def positiveNormalDecayTransmittedJonesCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (J : JonesVector) : ComplexMonochromaticPlaneWave :=
  configuration.positiveNormalDecayTransmittedCandidate
    ((configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).embedJones J)

@[simp]
lemma positiveNormalDecayTransmittedJonesCandidate_angularFrequency
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).angularFrequency =
      configuration.incident.angularFrequency :=
  rfl

@[simp]
lemma positiveNormalDecayTransmittedJonesCandidate_electricAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate
      hRadicand J).electricAmplitude =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).embedJones J :=
  rfl

@[simp]
lemma positiveNormalDecayTransmittedJonesCandidate_waveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).waveVector =
      configuration.positiveNormalDecayTransmittedWaveVector :=
  rfl

/-- The embedded Jones carrier is bilinearly transverse to the canonical complex wave vector. -/
lemma positiveNormalDecayTransmittedJonesCandidate_isTransverse
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).IsTransverse := by
  rw [IsTransverse,
    configuration.positiveNormalDecayTransmittedJonesCandidate_waveVector hRadicand J,
    configuration.positiveNormalDecayTransmittedJonesCandidate_electricAmplitude hRadicand J,
    ← configuration.positiveNormalDecayTransmittedPolarizationFrame_waveVector hRadicand]
  exact (configuration.positiveNormalDecayTransmittedPolarizationFrame
    hRadicand).bilinearDot_waveVector_embedJones J

/-- The embedded Jones carrier is dispersion matched to the interface's positive-side medium. -/
lemma positiveNormalDecayTransmittedJonesCandidate_isDispersionMatched
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate
      hRadicand J).IsDispersionMatched configuration.interface.positiveMedium := by
  rw [IsDispersionMatched,
    configuration.positiveNormalDecayTransmittedJonesCandidate_waveVector hRadicand J]
  exact configuration.bilinearDot_positiveNormalDecayTransmittedWaveVector_self hRadicand.le

/-- The compatible magnetic-induction amplitude `B0` is the positive-medium inverse wave speed
times the embedded Jones quarter-turn. -/
lemma positiveNormalDecayTransmittedJonesCandidate_magneticAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    (configuration.positiveNormalDecayTransmittedJonesCandidate
      hRadicand J).magneticAmplitude =
      (configuration.interface.positiveMedium.waveSpeed : ℂ)⁻¹ •
        (configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).embedJones J.propagationCross := by
  rw [magneticAmplitude,
    configuration.positiveNormalDecayTransmittedJonesCandidate_waveVector hRadicand J,
    configuration.positiveNormalDecayTransmittedJonesCandidate_electricAmplitude hRadicand J,
    ← configuration.positiveNormalDecayTransmittedPolarizationFrame_waveVector hRadicand,
    (configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).complexCross_waveVector_embedJones, smul_smul]
  congr 1
  rw [configuration.positiveNormalDecayTransmittedJonesCandidate_angularFrequency hRadicand J,
    configuration.positiveNormalDecayTransmittedPolarizationFrame_waveNumber hRadicand]
  push_cast
  field_simp [configuration.incident.angularFrequency_ne_zero,
    configuration.interface.positiveMedium.waveSpeed_ne_zero]

/-- The tangential electric amplitude has fixed-plane coordinates
`(J_s, (-I alpha / beta) J_p)`. -/
lemma positiveNormalDecayTransmittedJonesCandidate_tangentialElectricAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    hyperplaneTangentialProjection configuration.interface.plane
        (configuration.positiveNormalDecayTransmittedJonesCandidate
          hRadicand J).electricAmplitude =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).planeFrame.embedJones
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).tangentialJones configuration.interface.plane J) := by
  rw [configuration.positiveNormalDecayTransmittedJonesCandidate_electricAmplitude hRadicand J]
  exact (configuration.positiveNormalDecayTransmittedPolarizationFrame
    hRadicand).hyperplaneTangentialProjection_embedJones configuration.interface.plane J

/-- The positive-medium tangential magnetic-field-strength amplitude has fixed-plane coordinates
`Y_2 (-J_p, (-I alpha / beta) J_s)`. -/
lemma positiveNormalDecayTransmittedJonesCandidate_tangentialMagneticFieldStrengthAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    mediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.positiveMedium
        (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J) =
      ((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) •
        (configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).planeFrame.embedJones
            (JonesVector.ofComponents (-J.components 1)
              ((configuration.positiveNormalDecayTransmittedPolarizationFrame
                hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane *
                  J.components 0)) := by
  rw [mediumTangentialMagneticFieldStrengthAmplitude,
    configuration.positiveNormalDecayTransmittedJonesCandidate_magneticAmplitude hRadicand J,
    hyperplaneTangentialProjection_smul,
    (configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).hyperplaneTangentialProjection_embedJones_propagationCross,
    smul_smul]
  congr 1
  norm_cast
  rw [← mul_inv, configuration.interface.positiveMedium.μ_mul_waveSpeed]

/-- Zero incident tangential attenuation promotes the embedded Jones carrier to the connected
positive-normal-decay transmitted-candidate specification. -/
lemma positiveNormalDecayTransmittedJonesCandidate_spec_of_radicand_neg
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    configuration.IsPositiveNormalDecayTransmittedCandidate
      (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J) := by
  exact configuration.positiveNormalDecayTransmittedCandidate_spec_of_radicand_neg _
    hIncidentTangentialAttenuation hRadicand

/-- The negative-radicand Jones carrier is a source-free macroscopic Maxwell solution in the
positive medium. -/
lemma positiveNormalDecayTransmittedJonesCandidate_isMacroscopicMaxwellSolution
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector) :
    configuration.interface.positiveMedium.IsMacroscopicMaxwellSolution
      (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).electricField
      ((configuration.positiveNormalDecayTransmittedJonesCandidate
        hRadicand J).electricDisplacement configuration.interface.positiveMedium)
      (configuration.positiveNormalDecayTransmittedJonesCandidate
        hRadicand J).magneticInduction
      ((configuration.positiveNormalDecayTransmittedJonesCandidate
        hRadicand J).magneticFieldStrength configuration.interface.positiveMedium) 0 0 := by
  exact (configuration.positiveNormalDecayTransmittedJonesCandidate
    hRadicand J).isMacroscopicMaxwellSolution configuration.interface.positiveMedium
      (configuration.positiveNormalDecayTransmittedJonesCandidate_isTransverse hRadicand J)
      (configuration.positiveNormalDecayTransmittedJonesCandidate_isDispersionMatched hRadicand J)

/-- The negative-radicand Jones carrier has zero actual one-period mean Poynting component along
the stored interface normal at every point and period start. -/
lemma positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (J : JonesVector)
    (startTime : Time) (x : Space) :
    configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi /
          (configuration.positiveNormalDecayTransmittedJonesCandidate
            hRadicand J).angularFrequency,
        poyntingVector
          (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).electricField
          ((configuration.positiveNormalDecayTransmittedJonesCandidate
            hRadicand J).magneticFieldStrength configuration.interface.positiveMedium)
          (time : Time) x) = 0 := by
  let frame := configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand
  have hWaveVector :
      (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J).waveVector =
        frame.data.waveVector := by
    rw [configuration.positiveNormalDecayTransmittedJonesCandidate_waveVector hRadicand J,
      configuration.positiveNormalDecayTransmittedPolarizationFrame_waveVector hRadicand]
  have hzero :=
    inner_normalVector_intervalAverage_poyntingVector_eq_zero_of_positiveNormalDecay
      (configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand J)
      configuration.interface.positiveMedium frame.data hWaveVector
      (configuration.positiveNormalDecayTransmittedJonesCandidate_isTransverse hRadicand J)
      startTime x
  have hNormal : frame.data.normalVector = configuration.interface.plane.normalVector := by
    change (configuration.positiveNormalDecayTransmittedData hRadicand).normalVector = _
    exact configuration.positiveNormalDecayTransmittedData_normalVector hRadicand
  rw [hNormal] at hzero
  change inner ℝ configuration.interface.plane.normalVector _ = 0
  exact hzero

end PlanarDielectricWaveConfiguration

end

end Optics
