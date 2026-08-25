/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.GeometricAperture
public import Physlib.Optics.HarmonicFlux.PropagatingModePower

/-!
# Geometric-aperture flux of normalized propagating modes

## i. Overview

This file instantiates the physical propagating-mode power bridge with a justified geometric area
measure. A `GeometricAperture` supplies a measurable region in an oriented affine plane and the
ambient two-dimensional Hausdorff measure restricted to that region. The profile point map is the
identity on ambient `Space`, with points outside the aperture ignored by measure restriction.

For a common-positive-frequency, zero-attenuation, transverse, dispersion-matched finite carrier
family that is flux-orthonormal on this area measure, the actual integrated one-period Poynting
flux of every coherent synthesis equals signed `ModeAmplitude.power`.

The result remains restricted to the supplied finite synthesis image. It does not assert modal
completeness, absence of omitted channels, an interface boundary law, reciprocity, or device
losslessness.

## ii. Key results

- `integratedGeometricApertureFlux`: actual one-period flux through geometric aperture area.
- `outgoing_integratedGeometricApertureFlux_eq_power`: outgoing flux equals modal power.
- `incident_integratedGeometricApertureFlux_eq_neg_power`: incident flux has opposite sign.

## iii. Table of contents

- A. Actual geometric-aperture flux
- B. Normalized modal-power identities

## iv. References

This is a Physlib-original connector relative to the audited HOL optics corpus. The geometric
measure is Mathlib's normalized two-dimensional Hausdorff measure.
-/

@[expose] public section

namespace Optics

open Time

noncomputable section

namespace PropagatingHarmonicModeFamily

variable {ι : Type*} [Fintype ι] (family : PropagatingHarmonicModeFamily ι)

/-!

## A. Actual geometric-aperture flux

-/

/-- Actual integrated one-period mean normal Poynting flux through a geometric aperture. -/
def integratedGeometricApertureFlux (aperture : GeometricAperture)
    (amplitude : ModeAmplitude ι) (startTime : Time) : ℝ :=
  family.integratedActualMeanNormalFlux aperture.areaMeasure aperture.plane id amplitude startTime

/-!

## B. Normalized modal-power identities

-/

/-- On an outgoing flux-orthonormal Maxwell family, actual geometric-aperture flux equals modal
coordinate power. -/
lemma outgoing_integratedGeometricApertureFlux_eq_power
    {aperture : GeometricAperture}
    (h : HarmonicFieldProfile.IsApertureFluxOrthonormal aperture.areaMeasure
      aperture.plane .outgoing (family.modeProfile id))
    (amplitude : ModeAmplitude ι) (startTime : Time) :
    family.integratedGeometricApertureFlux aperture amplitude startTime = amplitude.power := by
  simpa [integratedGeometricApertureFlux] using
    family.outgoing_integratedActualMeanNormalFlux_eq_power h amplitude startTime

/-- On an incident flux-orthonormal Maxwell family, the negative actual geometric-aperture flux
equals modal coordinate power. -/
lemma incident_integratedGeometricApertureFlux_eq_neg_power
    {aperture : GeometricAperture}
    (h : HarmonicFieldProfile.IsApertureFluxOrthonormal aperture.areaMeasure
      aperture.plane .incident (family.modeProfile id))
    (amplitude : ModeAmplitude ι) (startTime : Time) :
    -family.integratedGeometricApertureFlux aperture amplitude startTime = amplitude.power := by
  simpa [integratedGeometricApertureFlux] using
    family.incident_integratedActualMeanNormalFlux_eq_neg_power h amplitude startTime

end PropagatingHarmonicModeFamily

end

end Optics
