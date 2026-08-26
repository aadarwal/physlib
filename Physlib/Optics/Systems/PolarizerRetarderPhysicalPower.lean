/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.PolarizerRetarderPhysical

/-!
# Normalized aperture flux for a polarizer-retarder chain

## i. Overview

This file transports the physical polarizer-retarder carrier through the E3b aperture-flux
normalization theorem. The ideal retarder changes the output Jones state but leaves the analyzer's
singleton modal coordinate unchanged. Under separate incident and outgoing normalization proofs,
the actual integrated one-period Poynting flux therefore obeys the analyzer's cosine-squared law.

## ii. Key results

- `JonesMatrix.linearRetarder_comp_linearPolarizer_malus_integratedActualMeanNormalFlux`: the
  normalized actual-flux Malus law for the complete ordered carrier.

## iii. Table of contents

- A. Actual normalized aperture flux

## iv. References

Both normalization hypotheses are load-bearing. Neither raw Jones unitarity nor the singleton
coordinate identity by itself identifies modal power with electromagnetic aperture power. The
result is restricted to the selected pure-state synthesis images and does not model rejected
polarization, absorption, heating, or a complete scattering device.
-/

@[expose] public section

namespace Optics

open Electromagnetism MeasureTheory Space Time

noncomputable section

namespace JonesMatrix

/-!

## A. Actual normalized aperture flux

-/

/-- Under separate incident and outgoing flux-normalization proofs, the actual output flux of the
polarizer-retarder chain is the negative input normal flux times the squared analyzer cosine.

The sign converts the incident plane's outward-normal flux to positive incident power. -/
lemma linearRetarder_comp_linearPolarizer_malus_integratedActualMeanNormalFlux
    {Ain Aout : Type*} [MeasurableSpace Ain] [MeasurableSpace Aout]
    (z : ℂ) (retarderAxis retardance analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency)
    {inputMeasure : Measure Ain} {inputPlane : OrientedAffineHyperplane 3}
    {inputPoint : Ain → Space}
    {outputMeasure : Measure Aout} {outputPlane : OrientedAffineHyperplane 3}
    {outputPoint : Aout → Space}
    (hInput : HarmonicFieldProfile.IsApertureFluxOrthonormal inputMeasure inputPlane .incident
      ((MaterialJonesMode.linearPolarizationFamily input medium frame angularFrequency
        hFrequency).modeProfile inputPoint))
    (hOutput : HarmonicFieldProfile.IsApertureFluxOrthonormal outputMeasure outputPlane .outgoing
      ((MaterialJonesMode.polarizerRetarderOutputFamily
        retarderAxis retardance analyzer medium frame angularFrequency
        hFrequency).modeProfile outputPoint))
    (startTime : Time) :
    let outputFamily := MaterialJonesMode.polarizerRetarderOutputFamily
      retarderAxis retardance analyzer medium frame angularFrequency hFrequency
    outputFamily.integratedActualMeanNormalFlux outputMeasure outputPlane outputPoint
        (linearPolarizerOutputAmplitude z analyzer input) startTime =
      -(MaterialJonesMode.linearPolarizationFamily input medium frame angularFrequency
        hFrequency).integratedActualMeanNormalFlux inputMeasure inputPlane inputPoint
          (MaterialJonesMode.amplitude z) startTime *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  dsimp only
  calc
    _ = (linearPolarizerOutputAmplitude z analyzer input).power :=
      (MaterialJonesMode.polarizerRetarderOutputFamily
        retarderAxis retardance analyzer medium frame angularFrequency
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
