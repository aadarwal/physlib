/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.ElectricConservation

/-!
# Fixed-frequency reduction of a planar electric boundary

## i. Overview

This file packages the fixed-frequency electric calculation problem earned from the primitive
three-wave boundary traces. The transmitted wave shares the incident angular frequency and full
complex hyperplane-tangential wave-vector projection. A reflected wave either shares both or has
zero electric amplitude and keeps arbitrary dummy frequency and wave-vector data. The reduced
amplitude equation uses the stored-plane-point-referenced joint tangential-`E`/normal-`D`
coefficients, with the incident and reflected terms formed in the negative-side medium and the
transmitted term formed in the positive-side medium.

The phase-matching and amplitude-balance predicates are separate so later geometric and amplitude
calculations can request their weakest hypotheses. Their conjunction is the fixed-frequency
electric boundary predicate. Under the exact nonzero incident-key aggregate, the primitive
zero-charge electric boundary implies this reduced predicate. Conversely, the reduced predicate
reconstructs the primitive electric boundary without a nonzero guard. Thus the guard derives label
matching only in the primitive-to-reduced direction; it is not hidden inside the reduced problem.

This equivalence concerns only tangential `E` and normal `D`. It reconstructs neither magnetic
boundary law and gives no equivalence with a full local boundary. Unguarded convention statement
(review only): it assigns no propagation direction and selects no normal wave-vector branch. It
assigns no on-shell or Maxwell condition, material dispersion, Snell or Fresnel law, observable,
irradiance, or power result.

## ii. Key results

- `PlanarDielectricWaveConfiguration.IsElectricPhaseMatched`: the transmitted label and every
  nonzero reflected electric label have the incident frequency and complex tangential projection.
- `PlanarDielectricWaveConfiguration.HasReferencedJointElectricBalance`: the reduced
  stored-point-referenced joint electric amplitude equation.
- `PlanarDielectricWaveConfiguration.IsFixedFrequencyElectricBoundary`: their conjunction.
- `PlanarDielectricWaveConfiguration.isElectricBoundary_iff_isFixedFrequencyElectricBoundary`:
  the guarded equivalence with the primitive two-law electric trace predicate.

## iii. Table of contents

- A. Reduced electric boundary predicates
- B. Primitive boundary to fixed-frequency reduction
- C. Fixed-frequency reduction to primitive boundary
- D. Guarded equivalence and full-boundary wrapper

## iv. References

This module specializes Physlib's exact electric boundary coefficient identity and conditional
label-matching results. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Reduced electric boundary predicates

-/

/-- The transmitted wave and every nonzero reflected electric wave have the incident angular
frequency and complex hyperplane-tangential wave-vector projection.

The reflected alternative is nonexclusive. A reflected candidate with zero electric amplitude
keeps unconstrained frequency and wave-vector labels. -/
def IsElectricPhaseMatched (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  (configuration.transmitted.angularFrequency = configuration.incident.angularFrequency ∧
    ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
        configuration.transmitted.waveVector =
      ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
        configuration.incident.waveVector) ∧
    (configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.angularFrequency = configuration.incident.angularFrequency ∧
        ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.reflected.waveVector =
          ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector))

/-- The stored-point-referenced joint tangential-`E`/normal-`D` amplitude balance for a planar
dielectric interface.

The incident and reflected amplitudes use the negative-side medium, while the transmitted
amplitude uses the positive-side medium. This is not an equality of raw electric phasors. -/
def HasReferencedJointElectricBalance
    (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  referencedMediumJointElectricTraceAmplitude configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted =
    referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.incident +
      referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.reflected

/-- The reduced fixed-frequency electric boundary problem: transmitted and active-reflected phase
matching together with the stored-point-referenced joint electric amplitude balance. -/
def IsFixedFrequencyElectricBoundary
    (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  configuration.IsElectricPhaseMatched ∧
    configuration.HasReferencedJointElectricBalance

/-!

## B. Primitive boundary to fixed-frequency reduction

-/

namespace IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A zero-charge electric boundary with a nonzero incident-key aggregate satisfies the reduced
fixed-frequency electric boundary problem. -/
lemma isFixedFrequencyElectricBoundary
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.IsFixedFrequencyElectricBoundary := by
  have hTransmitted :=
    h.transmitted_angularFrequency_tangentialProjection_eq_incident hAggregate
  have hReflected :=
    h.reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentialProjection_eq_incident
      hAggregate
  have hMatching := h.jointElectricBoundaryLabelMatching hAggregate
  exact ⟨⟨hTransmitted, hReflected⟩, hMatching.2.2⟩

end IsElectricBoundary

/-!

## C. Fixed-frequency reduction to primitive boundary

-/

namespace IsFixedFrequencyElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A reduced fixed-frequency electric boundary reconstructs the primitive zero-charge electric
boundary without a noncancellation hypothesis. -/
lemma isElectricBoundary (h : configuration.IsFixedFrequencyElectricBoundary) :
    configuration.IsElectricBoundary 0 := by
  classical
  rcases h with ⟨⟨hTransmitted, hReflected⟩, hBalance⟩
  change
    referencedMediumJointElectricTraceAmplitude configuration.interface.plane
          configuration.interface.positiveMedium configuration.transmitted =
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.incident +
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.reflected at hBalance
  have hTransmittedExponent :
      configuration.transmitted.boundaryExponent configuration.interface.plane =
        configuration.incident.boundaryExponent configuration.interface.plane :=
    (boundaryExponent_eq_iff_angularFrequency_and_tangentialProjection_eq
      configuration.interface.plane configuration.transmitted configuration.incident).mpr
        hTransmitted
  apply isElectricBoundary_iff_jointElectricBoundaryCoefficients_eq_zero.mpr
  rw [jointElectricBoundaryCoefficients, hTransmittedExponent]
  rcases hReflected with hReflectedZero | hReflectedMatched
  · have hReflectedAmplitude :
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.reflected = 0 :=
      (referencedMediumJointElectricTraceAmplitude_eq_zero_iff
        configuration.interface.plane configuration.interface.negativeMedium
          configuration.reflected).mpr hReflectedZero
    have hBalance' :
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.positiveMedium configuration.transmitted =
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.incident := by
      simpa [hReflectedAmplitude] using hBalance
    rw [hReflectedAmplitude, Finsupp.single_zero, add_zero, hBalance', sub_self]
  · have hReflectedExponent :
        configuration.reflected.boundaryExponent configuration.interface.plane =
          configuration.incident.boundaryExponent configuration.interface.plane :=
      (boundaryExponent_eq_iff_angularFrequency_and_tangentialProjection_eq
        configuration.interface.plane configuration.reflected configuration.incident).mpr
          hReflectedMatched
    rw [hReflectedExponent, ← Finsupp.single_add, hBalance, sub_self]

end IsFixedFrequencyElectricBoundary

/-!

## D. Guarded equivalence and full-boundary wrapper

-/

variable {configuration : PlanarDielectricWaveConfiguration}

/-- Under the exact incident-key noncancellation guard, the primitive zero-charge electric
boundary is equivalent to the reduced fixed-frequency electric boundary problem.

The guard is used only from left to right. -/
lemma isElectricBoundary_iff_isFixedFrequencyElectricBoundary
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.IsElectricBoundary 0 ↔
      configuration.IsFixedFrequencyElectricBoundary :=
  ⟨fun h ↦ h.isFixedFrequencyElectricBoundary hAggregate,
    fun h ↦ h.isElectricBoundary⟩

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A full zero-free-charge local boundary with a nonzero incident-key aggregate inherits the
reduced fixed-frequency electric boundary problem through its electric projection. -/
lemma isFixedFrequencyElectricBoundary
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.IsFixedFrequencyElectricBoundary :=
  h.isElectricBoundary.isFixedFrequencyElectricBoundary hAggregate

end IsLocalBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
