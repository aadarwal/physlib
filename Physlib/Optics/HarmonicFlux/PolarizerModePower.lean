/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.MaterialJonesMode
public import Physlib.Optics.HarmonicFlux.Polarizer
public import Physlib.Optics.HarmonicFlux.PropagatingModePower

/-!
# Malus' law for normalized propagating modal power

## i. Overview

This file transports the ideal linear-polarizer Jones action through the explicit singleton
material-Jones carrier bridge and the propagating-mode normalization theorem. A linear Jones axis
defines a singleton Maxwell-qualified family. For modal input coordinate `z`, the analyzer output
coordinate is the signed coherent amplitude `z cos (input - analyzer)`.

The carrier theorem first proves that this output coordinate realizes exactly the material plane
wave constructed from the Jones-matrix output. Its squared coordinate power then obeys Malus'
cosine-squared law. Finally, when the input and output measured profiles are separately proved
incident- and outgoing-flux orthonormal, E3b identifies those modal powers with the corresponding
actual integrated one-period Poynting fluxes. The role signs are independently pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`, together with
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal` and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`.

## ii. Key results

- `MaterialJonesMode.linearPolarizationFamily`: a linear Jones axis as a singleton Maxwell family.
- `JonesMatrix.linearPolarizer_scaledWave_eq`: the modal output is the actual Jones output carrier.
- `JonesMatrix.linearPolarizer_malus_modePower`: cosine-squared modal-coordinate power.
- `JonesMatrix.linearPolarizer_malus_integratedActualMeanNormalFlux`: the E3b flux transport.

## iii. Table of contents

- A. Linear-polarization singleton families
- B. Analyzer carrier and modal power
- C. Actual normalized Poynting flux

## iv. References

The modal identity alone is coordinate algebra. Its electromagnetic interpretation uses the two
explicit `IsApertureFluxOrthonormal` hypotheses in section C and remains restricted to these
singleton synthesis images. The input and output planes may have opposite outward normals. The
ideal zero-thickness analyzer still models no reflected, absorbed, thermal, or internal field and
supplies no complete-device passivity or modal-completeness result. Inputs are pure scaled linear
Jones states; partially polarized states and coherency-matrix mixtures are not modeled here.

-/

@[expose] public section

namespace Optics

open Electromagnetism MeasureTheory Space Time

noncomputable section

namespace MaterialJonesMode

/-!

## A. Linear-polarization singleton families

-/

/-- A framed linear Jones axis, without an implicit flux-normalization claim, as a singleton
propagating Maxwell family. -/
def linearPolarizationFamily (axis : Real.Angle) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) :
    PropagatingHarmonicModeFamily Unit :=
  family (JonesVector.linearPolarization axis) medium frame angularFrequency hFrequency

end MaterialJonesMode

namespace JonesMatrix

/-!

## B. Analyzer carrier and modal power

-/

/-- The singleton modal coordinate after a linear analyzer acts on a scaled linear input. -/
def linearPolarizerOutputAmplitude (z : ℂ) (analyzer input : Real.Angle) :
    ModeAmplitude Unit :=
  MaterialJonesMode.amplitude (z * (Real.Angle.cos (input - analyzer) : ℂ))

/-- The analyzer output modal carrier is exactly the material wave constructed from the Jones
matrix acting on the input Jones data. -/
lemma linearPolarizer_scaledWave_eq (z : ℂ) (analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) :
    (MaterialJonesMode.linearPolarizationFamily analyzer medium frame angularFrequency
      hFrequency).scaledWave (linearPolarizerOutputAmplitude z analyzer input) () =
      Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.ofReal
        (((linearPolarizer analyzer).act
          (JonesVector.scale z (JonesVector.linearPolarization input))).toMaterialPlaneWave
            medium frame angularFrequency hFrequency) := by
  rw [linearPolarizerOutputAmplitude, MaterialJonesMode.linearPolarizationFamily,
    MaterialJonesMode.scaledWave_eq, linearPolarizer_act_scaled_linearPolarization]

/-- The analyzer output coordinate obeys Malus' cosine-squared modal-power identity.

This statement gains electromagnetic meaning only after the family normalization hypotheses in
`linearPolarizer_malus_integratedActualMeanNormalFlux` are supplied. -/
lemma linearPolarizer_malus_modePower (z : ℂ) (analyzer input : Real.Angle) :
    (linearPolarizerOutputAmplitude z analyzer input).power =
      (MaterialJonesMode.amplitude z).power *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [linearPolarizerOutputAmplitude, MaterialJonesMode.amplitude_power,
    MaterialJonesMode.amplitude_power, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-!

## C. Actual normalized Poynting flux

-/

/-- Under separate incident and outgoing flux-normalization proofs, the analyzer's actual output
flux is the negative input normal flux times the squared axis cosine.

The sign converting the incident plane's outward-normal flux to positive incident power is pinned
by `polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`, together with
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal` and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`. -/
lemma linearPolarizer_malus_integratedActualMeanNormalFlux
    {Ain Aout : Type*} [MeasurableSpace Ain] [MeasurableSpace Aout]
    (z : ℂ) (analyzer input : Real.Angle) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency)
    {inputMeasure : Measure Ain} {inputPlane : OrientedAffineHyperplane 3}
    {inputPoint : Ain → Space} {outputMeasure : Measure Aout}
    {outputPlane : OrientedAffineHyperplane 3} {outputPoint : Aout → Space}
    (hInput : HarmonicFieldProfile.IsApertureFluxOrthonormal inputMeasure inputPlane .incident
      ((MaterialJonesMode.linearPolarizationFamily input medium frame angularFrequency
        hFrequency).modeProfile inputPoint))
    (hOutput : HarmonicFieldProfile.IsApertureFluxOrthonormal outputMeasure outputPlane .outgoing
      ((MaterialJonesMode.linearPolarizationFamily analyzer medium frame angularFrequency
        hFrequency).modeProfile outputPoint))
    (startTime : Time) :
    (MaterialJonesMode.linearPolarizationFamily analyzer medium frame angularFrequency
      hFrequency).integratedActualMeanNormalFlux outputMeasure outputPlane outputPoint
          (linearPolarizerOutputAmplitude z analyzer input) startTime =
      -(MaterialJonesMode.linearPolarizationFamily input medium frame angularFrequency
        hFrequency).integratedActualMeanNormalFlux inputMeasure inputPlane inputPoint
            (MaterialJonesMode.amplitude z) startTime *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  calc
    _ = (linearPolarizerOutputAmplitude z analyzer input).power :=
      (MaterialJonesMode.linearPolarizationFamily analyzer medium frame angularFrequency
        hFrequency).outgoing_integratedActualMeanNormalFlux_eq_power hOutput _ _
    _ = (MaterialJonesMode.amplitude z).power *
        Real.Angle.cos (input - analyzer) ^ 2 :=
      linearPolarizer_malus_modePower z analyzer input
    _ = _ := by
      rw [(MaterialJonesMode.linearPolarizationFamily input medium frame angularFrequency
        hFrequency).incident_integratedActualMeanNormalFlux_eq_neg_power hInput]

end JonesMatrix

end

end Optics
