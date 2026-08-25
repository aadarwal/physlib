/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingModeFlux

/-!
# Actual Poynting flux and normalized modal power

## i. Overview

This file composes the physical propagating-mode connector with the abstract measured-profile
normalization theorem. If the profiles of a finite common-frequency Maxwell family are pairwise
integrable, mutually flux-orthogonal, and unit normalized for a declared incident or outgoing
role, then the actual integrated one-period normal Poynting flux of the synthesized fields is
exactly the corresponding signed `ModeAmplitude.power`.

The conclusion is electromagnetic for the stored Maxwell fields and the supplied measure. It is
restricted to the finite synthesis image and does not assert modal completeness. The measure is
not called geometric area without a separate parameterization-and-Jacobian theorem.

## ii. Key results

- `outgoing_integratedActualMeanNormalFlux_eq_power`: actual outgoing flux equals modal power.
- `incident_integratedActualMeanNormalFlux_eq_neg_power`: actual incident flux has the opposite
  stored-normal sign.

## iii. Table of contents

- A. Outgoing normalized families
- B. Incident normalized families

## iv. References

This is Physlib-original normalization infrastructure relative to the audited HOL optics corpus.
It introduces no completeness, interface-boundary, reciprocity, or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open MeasureTheory Space Time

noncomputable section

namespace PropagatingHarmonicModeFamily

variable {ι A : Type*} [Fintype ι] (family : PropagatingHarmonicModeFamily ι)

/-!

## A. Outgoing normalized families

-/

/-- For a Maxwell-qualified family declared outgoing and normalized by the supplied measured
profile, the actual integrated one-period normal Poynting flux equals modal coordinate power. -/
lemma outgoing_integratedActualMeanNormalFlux_eq_power
    [MeasurableSpace A] {measure : Measure A} {plane : OrientedAffineHyperplane 3}
    {point : A → Space}
    (h : HarmonicFieldProfile.IsApertureFluxOrthonormal measure plane .outgoing
      (family.modeProfile point))
    (amplitude : ModeAmplitude ι) (startTime : Time) :
    family.integratedActualMeanNormalFlux measure plane point amplitude startTime =
      amplitude.power := by
  rw [family.integral_intervalAverage_normalFlux_eq_modeSynthesis]
  exact h.outgoing_modeSynthesis_power amplitude

/-!

## B. Incident normalized families

-/

/-- For a Maxwell-qualified family declared incident and normalized by the supplied measured
profile, the negative actual integrated normal flux equals modal coordinate power. -/
lemma incident_integratedActualMeanNormalFlux_eq_neg_power
    [MeasurableSpace A] {measure : Measure A} {plane : OrientedAffineHyperplane 3}
    {point : A → Space}
    (h : HarmonicFieldProfile.IsApertureFluxOrthonormal measure plane .incident
      (family.modeProfile point))
    (amplitude : ModeAmplitude ι) (startTime : Time) :
    -family.integratedActualMeanNormalFlux measure plane point amplitude startTime =
      amplitude.power := by
  rw [family.integral_intervalAverage_normalFlux_eq_modeSynthesis]
  exact h.incident_modeSynthesis_power amplitude

end PropagatingHarmonicModeFamily

end

end Optics
