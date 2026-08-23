/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.Planar
public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryAmplitude
public import Physlib.Optics.Interfaces.PlanarDielectric.Basic

/-!
# Plane-wave data at a planar dielectric boundary

## i. Overview

This file assembles three independently parameterized complex-carrier plane-wave candidates at a
planar dielectric interface. Their complex data constructs ordinary real electromagnetic fields.
For the boundary trace assigned to the negative side, the incident and reflected field values are
added and use the interface's negative-side medium for `D` and `H`. For the trace assigned to the
positive side, the transmitted field values use the positive-side medium. The resulting values are
restricted pointwise to the interface plane and connected to the generic macroscopic boundary
laws.

The two electric laws are exposed separately from the full four-law boundary predicate. At zero
free surface charge they are equivalent to equality of the joint ordinary-real tangential-`E` and
normal-`D` field data. Restricting that equality to the affine plane and applying the single-wave
factorization gives an exact equality of three positive-rate boundary-character realizations. A
full local boundary projects to this electric predicate while the free surface current remains
arbitrary. The reverse bridge reconstructs only the two electric laws, not either magnetic law,
and makes no noncancellation or frequency-conservation claim.

The incident, reflected, and transmitted names are trace-membership labels, not stored propagation
hypotheses. The incident and reflected labels are symmetric in the negative trace. The structure
has no fourth slot labeled as a wave incident from the positive side, but that omission does not
prove one-sided illumination. In particular, the structure assumes no common frequency,
tangential wave-vector matching, nonzero amplitude, transversality, material dispersion, Maxwell
equation, incoming or outgoing direction, decay branch, Fresnel coefficient, irradiance, or power
normalization. Those facts must be supplied or derived separately. A zero-electric-amplitude
candidate retains unconstrained frequency and wave-vector data. Incident and reflected field
values may also cancel, so a local boundary hypothesis alone gives no labelwise conservation law.

The traces below are pointwise restrictions of globally defined explicit plane-wave fields. They
are not analytic one-sided traces of fields defined only on open half-spaces, and the local
boundary predicates are stipulated rather than derived from integral Maxwell equations.

## ii. Key results

- `PlanarDielectricWaveConfiguration`: independent incident, reflected, and transmitted wave data.
- `PlanarDielectricWaveConfiguration.negativeTrace`: the incident-plus-reflected real trace in
  the negative-side medium.
- `PlanarDielectricWaveConfiguration.positiveTrace`: the transmitted real trace in the
  positive-side medium.
- `PlanarDielectricWaveConfiguration.IsElectricBoundary`: the explicit two-law electric boundary
  predicate with supplied free surface charge.
- `PlanarDielectricWaveConfiguration.IsLocalBoundary`: the explicit local boundary predicate with
  free electric surface sources.
- `PlanarDielectricWaveConfiguration.IsSourceFreeLocalBoundary`: its zero-free-surface-source
  specialization.
- `PlanarDielectricWaveConfiguration.IsElectricBoundary.jointElectricFieldData_iff`: exact
  equivalence between the zero-charge electric laws and joint field-data equality.
- `isElectricBoundary_iff_jointElectricBoundaryCharacter_sum_eq`: exact equivalence with the
  all-parameter boundary-character identity.

## iii. Table of contents

- A. Independent three-wave configurations
- B. Ordinary real boundary traces
- C. Local boundary predicates
- D. Electric boundary projection and exact trace bridge

## iv. References

This construction connects existing Physlib plane-wave, medium, and planar-boundary APIs. No
external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Time
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

/-!

## A. Independent three-wave configurations

-/

/-- Three independently parameterized complex-carrier plane-wave candidates assigned to a planar
dielectric interface.

The wave-role names carry no stored propagation, phase-matching, Maxwell, or nonvanishing
hypothesis. They specify which trace contains each wave. There is no fourth positive-trace wave
slot, but this omission is not an incoming-direction predicate. Each wave keeps its own positive
angular frequency and complex wave vector. -/
structure PlanarDielectricWaveConfiguration where
  /-- The oriented interface and its negative- and positive-side media. -/
  interface : PlanarDielectricInterface
  /-- The wave candidate labeled incident on the negative side. -/
  incident : ComplexMonochromaticPlaneWave
  /-- The wave candidate labeled reflected on the negative side. -/
  reflected : ComplexMonochromaticPlaneWave
  /-- The wave candidate labeled transmitted on the positive side. -/
  transmitted : ComplexMonochromaticPlaneWave

namespace PlanarDielectricWaveConfiguration

/-!

## B. Ordinary real boundary traces

-/

/-- The ordinary real incident-plus-reflected boundary trace, with both constitutive field pairs
formed using the interface's negative-side medium. -/
def negativeTrace (configuration : PlanarDielectricWaveConfiguration) :
    PlanarMacroscopicTrace configuration.interface.plane :=
  PlanarMacroscopicTrace.ofFields configuration.interface.plane
    (configuration.incident.electricField + configuration.reflected.electricField)
    (configuration.incident.electricDisplacement configuration.interface.negativeMedium +
      configuration.reflected.electricDisplacement configuration.interface.negativeMedium)
    (configuration.incident.magneticInduction + configuration.reflected.magneticInduction)
    (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium +
      configuration.reflected.magneticFieldStrength configuration.interface.negativeMedium)

/-- The ordinary real transmitted boundary trace, with constitutive fields formed using the
interface's positive-side medium. -/
def positiveTrace (configuration : PlanarDielectricWaveConfiguration) :
    PlanarMacroscopicTrace configuration.interface.plane :=
  PlanarMacroscopicTrace.ofFields configuration.interface.plane
    configuration.transmitted.electricField
    (configuration.transmitted.electricDisplacement configuration.interface.positiveMedium)
    configuration.transmitted.magneticInduction
    (configuration.transmitted.magneticFieldStrength configuration.interface.positiveMedium)

/-!

## C. Local boundary predicates

-/

/-- The two electric boundary laws for the explicit three-wave dielectric configuration, with a
supplied free electric surface charge.

This predicate contains tangential-`E` continuity and the normal-`D` jump only. It does not contain
either magnetic law or a free surface current. -/
def IsElectricBoundary (configuration : PlanarDielectricWaveConfiguration)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity configuration.interface.plane) : Prop :=
  IsPlanarElectricBoundary configuration.negativeTrace configuration.positiveTrace surfaceCharge

/-- The explicit local macroscopic boundary condition for a three-wave dielectric configuration
with supplied free electric surface charge and current.

This predicate states the pointwise laws; it does not assert that they follow from integral
Maxwell equations. -/
def IsLocalBoundary (configuration : PlanarDielectricWaveConfiguration)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity configuration.interface.plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane) : Prop :=
  IsPlanarMacroscopicBoundary configuration.negativeTrace configuration.positiveTrace
    surfaceCharge surfaceCurrent

/-- The explicit local macroscopic boundary condition for a three-wave dielectric configuration
with no free electric surface charge or current.

This does not exclude bound polarization charge, bulk sources, or material response. -/
def IsSourceFreeLocalBoundary (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  IsSourceFreePlanarMacroscopicBoundary configuration.negativeTrace configuration.positiveTrace

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity configuration.interface.plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A full local boundary satisfies its two electric boundary laws. -/
lemma isElectricBoundary
    (h : configuration.IsLocalBoundary surfaceCharge surfaceCurrent) :
    configuration.IsElectricBoundary surfaceCharge :=
  IsPlanarMacroscopicBoundary.isPlanarElectricBoundary h

end IsLocalBoundary

namespace IsElectricBoundary

/-!

## D. Electric boundary projection and exact trace bridge

-/

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A zero-free-surface-charge electric boundary has equal incident-plus-reflected and transmitted
joint tangential-electric and normal-electric-displacement field data at every boundary point.

No magnetic boundary law or free surface current is present in the hypothesis. -/
lemma jointElectricFieldData (h : configuration.IsElectricBoundary 0)
    (t : Time) (x : configuration.interface.plane.carrier) :
    mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident t x +
        mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected t x =
      mediumJointElectricFieldData configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted t x := by
  apply Prod.ext
  · have he :=
      IsPlanarElectricBoundary.tangentialElectricField h t x
    have he' := congrArg Subtype.val he
    simpa only [negativeTrace, positiveTrace, PlanarMacroscopicTrace.ofFields,
      Space.OrientedAffineHyperplane.coe_projectionToTangent, Pi.add_apply,
      mediumJointElectricFieldData, Prod.fst_add,
      Space.OrientedAffineHyperplane.tangentialProjection_add] using he'
  · have hd :
        configuration.interface.plane.normalComponent
            (configuration.negativeTrace.electricDisplacement t x) =
          configuration.interface.plane.normalComponent
            (configuration.positiveTrace.electricDisplacement t x) := by
      have hdJump := IsPlanarElectricBoundary.normalElectricDisplacement h t x
      exact (sub_eq_zero.mp (by simpa using hdJump)).symm
    simpa only [negativeTrace, positiveTrace, PlanarMacroscopicTrace.ofFields, Pi.add_apply,
      mediumJointElectricFieldData, Prod.snd_add,
      Space.OrientedAffineHyperplane.normalComponent, inner_add_right] using hd

/-- The zero-charge electric boundary laws are equivalent to equality of the actual joint
tangential-electric and normal-electric-displacement field data at every boundary point. -/
lemma jointElectricFieldData_iff :
    configuration.IsElectricBoundary 0 ↔
      ∀ (t : Time) (x : configuration.interface.plane.carrier),
        mediumJointElectricFieldData configuration.interface.plane
              configuration.interface.negativeMedium configuration.incident t x +
            mediumJointElectricFieldData configuration.interface.plane
              configuration.interface.negativeMedium configuration.reflected t x =
          mediumJointElectricFieldData configuration.interface.plane
            configuration.interface.positiveMedium configuration.transmitted t x := by
  constructor
  · exact fun h ↦ h.jointElectricFieldData
  · intro h t x
    constructor
    · apply Subtype.ext
      have he := congrArg Prod.fst (h t x)
      simpa only [negativeTrace, positiveTrace, PlanarMacroscopicTrace.ofFields,
        Space.OrientedAffineHyperplane.coe_projectionToTangent, Pi.add_apply,
        mediumJointElectricFieldData, Prod.fst_add,
        Space.OrientedAffineHyperplane.tangentialProjection_add] using he
    · have hd :
          configuration.interface.plane.normalComponent
              (configuration.negativeTrace.electricDisplacement t x) =
            configuration.interface.plane.normalComponent
              (configuration.positiveTrace.electricDisplacement t x) := by
        simpa only [negativeTrace, positiveTrace, PlanarMacroscopicTrace.ofFields, Pi.add_apply,
          mediumJointElectricFieldData, Prod.snd_add,
          Space.OrientedAffineHyperplane.normalComponent, inner_add_right] using
            congrArg Prod.snd (h t x)
      exact sub_eq_zero.mpr hd.symm

/-- A zero-free-surface-charge electric boundary gives equality of the three positive-rate
ordinary-real boundary-character realizations, with each joint amplitude referenced to the
interface's stored point. -/
lemma jointElectricBoundaryCharacter_sum_eq
    (h : configuration.IsElectricBoundary 0)
    (p : ComplexMonochromaticPlaneWave.BoundaryParameter configuration.interface.plane) :
    realPartJointElectricTraceAmplitude
          (Complex.exp (configuration.incident.boundaryExponent
              configuration.interface.plane p) •
            referencedMediumJointElectricTraceAmplitude configuration.interface.plane
              configuration.interface.negativeMedium configuration.incident) +
        realPartJointElectricTraceAmplitude
          (Complex.exp (configuration.reflected.boundaryExponent
              configuration.interface.plane p) •
            referencedMediumJointElectricTraceAmplitude configuration.interface.plane
              configuration.interface.negativeMedium configuration.reflected) =
      realPartJointElectricTraceAmplitude
        (Complex.exp (configuration.transmitted.boundaryExponent
            configuration.interface.plane p) •
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.positiveMedium configuration.transmitted) := by
  rcases p with ⟨t, v⟩
  let x : configuration.interface.plane.carrier :=
    ⟨(v : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point,
      configuration.interface.plane.tangent_vadd_point_mem_carrier v
        ((configuration.interface.plane.mem_tangentSubmodule v).mp v.property)⟩
  have hdata := h.jointElectricFieldData t x
  change
    mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident t
            ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point) +
        mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected t
            ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point) =
      mediumJointElectricFieldData configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted t
          ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point) at hdata
  simpa only [mediumJointElectricFieldData_tangent_vadd_point] using hdata

end IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- The zero-charge electric boundary laws are equivalent to the all-parameter identity of the
three ordinary-real boundary-character realizations. -/
lemma isElectricBoundary_iff_jointElectricBoundaryCharacter_sum_eq :
    configuration.IsElectricBoundary 0 ↔
      ∀ p : ComplexMonochromaticPlaneWave.BoundaryParameter
          configuration.interface.plane,
        realPartJointElectricTraceAmplitude
              (Complex.exp (configuration.incident.boundaryExponent
                  configuration.interface.plane p) •
                referencedMediumJointElectricTraceAmplitude configuration.interface.plane
                  configuration.interface.negativeMedium configuration.incident) +
            realPartJointElectricTraceAmplitude
              (Complex.exp (configuration.reflected.boundaryExponent
                  configuration.interface.plane p) •
                referencedMediumJointElectricTraceAmplitude configuration.interface.plane
                  configuration.interface.negativeMedium configuration.reflected) =
          realPartJointElectricTraceAmplitude
            (Complex.exp (configuration.transmitted.boundaryExponent
                configuration.interface.plane p) •
              referencedMediumJointElectricTraceAmplitude configuration.interface.plane
                configuration.interface.positiveMedium configuration.transmitted) := by
  constructor
  · exact fun h ↦ h.jointElectricBoundaryCharacter_sum_eq
  · intro h
    apply IsElectricBoundary.jointElectricFieldData_iff.mpr
    intro t x
    obtain ⟨v, hv, hx⟩ :=
      configuration.interface.plane.exists_tangent_vadd_eq_of_mem_carrier x x.property
    let vTangent : configuration.interface.plane.tangentSubmodule :=
      ⟨v, (configuration.interface.plane.mem_tangentSubmodule v).mpr hv⟩
    have hCharacter := h (t, vTangent)
    rw [hx]
    change
      mediumJointElectricFieldData configuration.interface.plane
            configuration.interface.negativeMedium configuration.incident t
              ((vTangent : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point) +
          mediumJointElectricFieldData configuration.interface.plane
            configuration.interface.negativeMedium configuration.reflected t
              ((vTangent : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point) =
        mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.positiveMedium configuration.transmitted t
            ((vTangent : EuclideanSpace ℝ (Fin 3)) +ᵥ configuration.interface.plane.point)
    rw [mediumJointElectricFieldData_tangent_vadd_point,
      mediumJointElectricFieldData_tangent_vadd_point,
      mediumJointElectricFieldData_tangent_vadd_point]
    exact hCharacter

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A zero-free-surface-charge full local boundary has equal joint electric field data. -/
lemma jointElectricFieldData (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (t : Time) (x : configuration.interface.plane.carrier) :
    mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident t x +
        mediumJointElectricFieldData configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected t x =
      mediumJointElectricFieldData configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted t x :=
  h.isElectricBoundary.jointElectricFieldData t x

/-- A zero-free-surface-charge full local boundary gives the joint electric boundary-character
identity; the free surface current remains arbitrary. -/
lemma jointElectricBoundaryCharacter_sum_eq
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (p : ComplexMonochromaticPlaneWave.BoundaryParameter configuration.interface.plane) :
    realPartJointElectricTraceAmplitude
          (Complex.exp (configuration.incident.boundaryExponent
              configuration.interface.plane p) •
            referencedMediumJointElectricTraceAmplitude configuration.interface.plane
              configuration.interface.negativeMedium configuration.incident) +
        realPartJointElectricTraceAmplitude
          (Complex.exp (configuration.reflected.boundaryExponent
              configuration.interface.plane p) •
            referencedMediumJointElectricTraceAmplitude configuration.interface.plane
              configuration.interface.negativeMedium configuration.reflected) =
      realPartJointElectricTraceAmplitude
        (Complex.exp (configuration.transmitted.boundaryExponent
            configuration.interface.plane p) •
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.positiveMedium configuration.transmitted) :=
  h.isElectricBoundary.jointElectricBoundaryCharacter_sum_eq p

end IsLocalBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
