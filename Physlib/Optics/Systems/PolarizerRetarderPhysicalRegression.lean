/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PolarizerModeNormalizationRegression
public import Physlib.Optics.Polarization.MaterialWaveRegression
public import Physlib.Optics.Systems.PolarizerRetarderPhysical

/-!
# Physical polarizer-retarder regression

## i. Overview

This regression begins with the exact P1b horizontal `harmonicWaveX` amplitude-phase data, passes
it through a `pi / 4` analyzer and a positive zero-axis quarter-wave plate, and checks the same
output at Jones, material-carrier, irradiance, and modal-coordinate layers.

The exact negative-`I` output phase pins the positive-time retarder convention. Separate negative
controls reject the opposite phase and an exchange of the transverse output coordinates.

## ii. Key results

- `polarizerRetarderPhysicalRegression_inputCarrier_eq`: the P1b carrier is the normalized-mode
  input carrier.
- `polarizerRetarderPhysicalRegression_outputJones_eq`: exact ordered Jones output.
- `polarizerRetarderPhysicalRegression_outputElectricAmplitude`: exact spatial carrier amplitude.
- `polarizerRetarderPhysicalRegression_irradiances`: input and output irradiances.
- `polarizerRetarderPhysicalRegression_modePowers`: input and output modal powers.

## iii. Table of contents

- A. Connected P1b input
- B. Ordered Jones and material carrier
- C. Irradiance and modal power
- D. Convention-negative controls

## iv. References

The fixture uses the exact impedance-one-half medium from the E3b normalization regression. It is
a pure coherent singleton model, not a partially polarized state, a complete scattering device,
or a model of the rejected polarization, absorption, heating, or internal fields.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Space

noncomputable section

/-!

## A. Connected P1b input

-/

/-- The P1b amplitude-phase input used by the connected regression. -/
def polarizerRetarderPhysicalRegressionInputJones : JonesVector :=
  JonesVector.ofAmplitudePhase materialWaveRegressionAmplitude
    materialWaveRegressionPhaseOffset

/-- The connected P1b input is horizontal. -/
lemma polarizerRetarderPhysicalRegression_inputJones_eq :
    polarizerRetarderPhysicalRegressionInputJones = JonesVector.horizontal :=
  materialWaveRegression_jones

/-- The exact free-space material data is the impedance-one-half normalization medium. -/
lemma polarizerRetarderPhysicalRegression_medium_eq :
    materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium =
      polarizerModeNormalizationRegressionMedium := rfl

/-- The fixed P1b frame is the frame used by the normalization fixture. -/
lemma polarizerRetarderPhysicalRegression_frame_eq :
    harmonicWaveXPolarizationFrame = polarizerModeNormalizationRegressionFrame := rfl

/-- Wave number two in the exact free space has angular frequency one. -/
lemma polarizerRetarderPhysicalRegression_angularFrequency :
    harmonicWaveXAngularFrequency materialWaveRegressionFreeSpace 2 = 1 := by
  rw [harmonicWaveXAngularFrequency, FreeSpace.c_val]
  norm_num [materialWaveRegressionFreeSpace]
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

/-- The P1b material carrier is exactly the singleton normalized-mode input carrier. -/
lemma polarizerRetarderPhysicalRegression_inputCarrier_eq :
    ComplexMonochromaticPlaneWave.ofReal
      (polarizerRetarderPhysicalRegressionInputJones.toMaterialPlaneWave
        materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium
        harmonicWaveXPolarizationFrame
        (harmonicWaveXAngularFrequency materialWaveRegressionFreeSpace 2)
        (harmonicWaveXAngularFrequency_pos materialWaveRegressionFreeSpace (by norm_num))) =
      (MaterialJonesMode.linearPolarizationFamily 0
        materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium
        harmonicWaveXPolarizationFrame
        (harmonicWaveXAngularFrequency materialWaveRegressionFreeSpace 2)
        (harmonicWaveXAngularFrequency_pos materialWaveRegressionFreeSpace
          (by norm_num))).wave () := by
  rw [polarizerRetarderPhysicalRegression_inputJones_eq,
    ← JonesVector.linearPolarization_zero]
  rfl

/-!

## B. Ordered Jones and material carrier

-/

/-- The exact ordered Jones output of the analyzer and positive quarter-wave plate. -/
def polarizerRetarderPhysicalRegressionOutputJones : JonesVector :=
  ((JonesMatrix.quarterWavePlate 0).comp
    (JonesMatrix.linearPolarizer ((Real.pi / 4 : ℝ) : Real.Angle))).act
      polarizerRetarderPhysicalRegressionInputJones

/-- The ordered output has equal magnitude and the negative-`I` second component. -/
lemma polarizerRetarderPhysicalRegression_outputJones_eq :
    polarizerRetarderPhysicalRegressionOutputJones =
      JonesVector.ofComponents (1 / 2) (-Complex.I / 2) := by
  rw [polarizerRetarderPhysicalRegressionOutputJones,
    polarizerRetarderPhysicalRegression_inputJones_eq,
    JonesMatrix.quarterWavePlate_zero_comp_linearPolarizer_pi_div_four_act_horizontal]
  ext i
  fin_cases i
  · simp [JonesVector.scale, JonesVector.minusIQuadrature, JonesVector.ofComponents]
    rw [← Complex.ofReal_mul, JonesVector.unitEqualAmplitude_mul_self]
    norm_num
  · simp [JonesVector.scale, JonesVector.minusIQuadrature, JonesVector.ofComponents]
    rw [show -((JonesVector.unitEqualAmplitude : ℂ) *
      (Complex.I * JonesVector.unitEqualAmplitude)) =
        -Complex.I * ((JonesVector.unitEqualAmplitude : ℂ) *
          JonesVector.unitEqualAmplitude) by ring]
    rw [← Complex.ofReal_mul, JonesVector.unitEqualAmplitude_mul_self]
    apply Complex.ext <;> norm_num

/-- The complete output carrier has spatial electric amplitude `(0, 1/2, -I/2)`. -/
lemma polarizerRetarderPhysicalRegression_outputElectricAmplitude :
    ((MaterialJonesMode.polarizerRetarderOutputFamily 0
      ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame
      1 (by norm_num)).scaledWave
        (JonesMatrix.linearPolarizerOutputAmplitude 1
          ((Real.pi / 4 : ℝ) : Real.Angle) 0) ()).electricAmplitude =
      WithLp.toLp 2 ![(0 : ℂ), 1 / 2, -Complex.I / 2] := by
  rw [JonesMatrix.linearRetarder_comp_linearPolarizer_scaledWave_eq]
  rw [JonesVector.ofReal_toMaterialPlaneWave_electricAmplitude]
  have hInput :
      JonesVector.scale 1 (JonesVector.linearPolarization 0) =
        polarizerRetarderPhysicalRegressionInputJones := by
    rw [JonesVector.linearPolarization_zero,
      polarizerRetarderPhysicalRegression_inputJones_eq]
    ext i
    fin_cases i <;> simp [JonesVector.scale]
  rw [hInput]
  change polarizerModeNormalizationRegressionFrame.embedJones
      polarizerRetarderPhysicalRegressionOutputJones = _
  rw [polarizerRetarderPhysicalRegression_outputJones_eq]
  ext i
  fin_cases i <;>
    simp [PolarizationFrame.embedJones_apply, polarizerModeNormalizationRegressionFrame,
      polarizerModeNormalizationRegressionDirection]

/-!

## C. Irradiance and modal power

-/

/-- The connected input has irradiance one and the ordered output has irradiance one half. -/
lemma polarizerRetarderPhysicalRegression_irradiances :
    polarizerRetarderPhysicalRegressionInputJones.materialPlaneWaveIrradiance
        polarizerModeNormalizationRegressionMedium = 1 ∧
      polarizerRetarderPhysicalRegressionOutputJones.materialPlaneWaveIrradiance
        polarizerModeNormalizationRegressionMedium = 1 / 2 := by
  rw [polarizerRetarderPhysicalRegression_inputJones_eq,
    polarizerRetarderPhysicalRegression_outputJones_eq]
  constructor <;>
    norm_num [JonesVector.materialPlaneWaveIrradiance,
      JonesVector.intensity_eq_sum_normSq, JonesVector.horizontal,
      JonesVector.ofComponents, polarizerModeNormalizationRegressionMedium_waveImpedance,
      Complex.normSq]

/-- The connected input coordinate has power one and the analyzer output coordinate has power one
half. -/
lemma polarizerRetarderPhysicalRegression_modePowers :
    (MaterialJonesMode.amplitude 1).power = 1 ∧
      (JonesMatrix.linearPolarizerOutputAmplitude 1
        ((Real.pi / 4 : ℝ) : Real.Angle) 0).power = 1 / 2 := by
  constructor
  · rw [MaterialJonesMode.amplitude_power]
    norm_num [Complex.normSq]
  · rw [JonesMatrix.linearPolarizer_malus_modePower, MaterialJonesMode.amplitude_power]
    norm_num [Complex.normSq]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num

/-!

## D. Convention-negative controls

-/

/-- The positive-quarter-wave output does not have the opposite `I` phase. -/
lemma polarizerRetarderPhysicalRegression_output_ne_plusI :
    polarizerRetarderPhysicalRegressionOutputJones ≠
      JonesVector.ofComponents (1 / 2) (Complex.I / 2) := by
  rw [polarizerRetarderPhysicalRegression_outputJones_eq]
  intro h
  have hComponent := congrArg (fun J : JonesVector => J.components 1) h
  norm_num [Complex.ext_iff] at hComponent

/-- The positive-quarter-wave output does not exchange its two transverse coordinates. -/
lemma polarizerRetarderPhysicalRegression_output_ne_swapped :
    polarizerRetarderPhysicalRegressionOutputJones ≠
      JonesVector.ofComponents (-Complex.I / 2) (1 / 2) := by
  rw [polarizerRetarderPhysicalRegression_outputJones_eq]
  intro h
  have hComponent := congrArg (fun J : JonesVector => J.components 0) h
  norm_num [Complex.ext_iff] at hComponent

end

end Optics
