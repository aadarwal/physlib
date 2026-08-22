/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.Planar
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic
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
- `PlanarDielectricWaveConfiguration.IsLocalBoundary`: the explicit local boundary predicate with
  free electric surface sources.
- `PlanarDielectricWaveConfiguration.IsSourceFreeLocalBoundary`: its zero-free-surface-source
  specialization.

## iii. Table of contents

- A. Independent three-wave configurations
- B. Ordinary real boundary traces
- C. Local boundary predicates

## iv. References

This construction connects existing Physlib plane-wave, medium, and planar-boundary APIs. No
external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension

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

end PlanarDielectricWaveConfiguration

end
end Optics
