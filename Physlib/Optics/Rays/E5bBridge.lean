/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.Snell
public import Physlib.Optics.Rays.Basic

/-!
# Bridging paraxial rays to the exact interface geometry

## i. Overview

This is the one module in the ray development that may import
`Physlib.Optics.Interfaces.PlanarDielectric`. It answers `goal.md` §H.5 R1's fourth bullet: the
relationship between the signed meridional ray angle of `Physlib.Optics.Rays.Basic` and the exact
geometric directions of the planar-dielectric interface theory.

The two sides measure angles differently, and the difference is not a single sign.

- The ray side uses a *signed* difference `Optics.MeridionalRay.signedIncidenceAngle`, an arbitrary
  real, measured against one normal angle.
- The interface side uses Mathlib's *unoriented* vector angle, valued in `[0, π]`, measured
  against a side normal — and it measures the incident and transmitted angles into the **positive**
  side while measuring the reflected angle into the **negative** side.

So the two are not related by an equality of reals. What is true, and what this file proves, is
that both are determined by the same inner product: the cosine of either angle is the inner product
of the unit propagation direction with the unit side normal. `Optics.cos_angleToSide_of_norm_eq_one`
is that statement on the interface side; `Optics.MeridionalRay.cos_signedIncidenceAngle` is the
corresponding one already proved on the ray side. Equality of the *angles* then needs an explicit
range hypothesis, and every result below that asserts one carries it.

Section A builds the ambient direction of a meridional ray from a side normal and a unit tangent,
which is what makes the correspondence constructive rather than assumed. Sections C and D then
carry the two physical laws across, and section E states the refraction results about a ray rather
than about the interface's own phase angles.

What the refraction results do and do not say, precisely. The small-angle bound of
`Physlib.Optics.Rays.Basic` was stated against a Snell law written down by hand, and
`Optics.abs_paraxialSnell_sub_le_snellLaw` re-establishes it with that hypothesis discharged. The
provenance is exactly this: the Snell law is derived from the supplied electric phase-matching
predicate together with material dispersion matching and zero attenuation. That predicate is
itself **stipulated**, not derived from the integral Maxwell equations — the interface modules say
so of their own boundary predicates — so this is a reduction to a stated boundary condition, not
to Maxwell. Maxwell enters only through the half-space plane-wave solutions.

Separately, and independently of that: nothing here says ray refraction is derived from Maxwell.
The paraxial law being bounded remains a model law, and a phase direction remains a phase
direction.

Explicit non-claims. A phase direction is not a ray: the interface theory is careful that its
phase angles assert nothing about group velocity, energy flux, or outgoing behaviour, and nothing
here upgrades them. The correspondence is geometric only. Nothing here derives the *paraxial*
interface laws for curved surfaces, which remain model laws, and nothing here assigns a field,
power, or polarization to a ray.

The tangent vector of section A is a parameter. Section F constructs a *canonical* one by
normalising the tangential projection of the incident phase vector, and its non-normal-incidence
hypothesis is what that canonical construction needs: at normal incidence the projection vanishes
and there is nothing to normalise. It is **not** a condition for a plane of incidence, or a
realising ray, to exist. At normal incidence
`Optics.realisesIncidentPhaseDirection_of_tangentialProjection_eq_zero` shows that *every* tangent
realises the incident direction, because the tangential term of the ambient direction vanishes
identically. The plane is *undetermined*, not absent, and that theorem is the precise form of the
statement.

Section G shows the same canonical tangent serves the transmitted and, away from the interface
theory's zero-amplitude alternative, the reflected phase vectors, via the plane-of-incidence
results of `Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry`. That is a statement about
spans of phase vectors; it assigns no ray, direction of travel, or outgoing role to the transmitted
or reflected labels.

## ii. Key results

- `Optics.cos_angleToSide_of_norm_eq_one`: a unit vector's side-relative cosine is its inner
  product with the side normal.
- `Optics.angleToSide_meridionalDirection`: the ambient direction built at signed angle `α` has
  interface-side angle exactly `α`, under the range hypothesis `α ∈ [0, π]`.
- `Optics.vectorReflection_meridionalDirection`: hyperplane reflection maps the direction at angle
  `α` to the direction at the same angle on the opposite side.
- `Optics.angleToSide_vectorReflection_meridionalDirection`: measured into the outgoing side, the
  reflected ray makes the same angle — the exact content of the folded plane-mirror law.
- `Optics.exactRefractionAngle_incidentPhaseAngle`: the transmitted phase angle *is* the ray
  development's exact refraction angle of the incident phase angle.
- `Optics.abs_paraxialSnell_sub_le_snellLaw`: the paraxial refraction law holds to within the
  cubic bound of `Physlib.Optics.Rays.Basic`, against the *derived* Snell law.
- `Optics.RealisesIncidentPhaseDirection` and
  `Optics.abs_paraxialSnell_sub_le_snellLaw_meridional`: the same bound, stated about the ray.
- `Optics.exists_realisesIncidentPhaseDirection`: away from normal incidence, a realising tangent
  and ray exist and are constructed.
- `Optics.transmitted_phaseVector_mem_meridionalPlaneSpan`: the constructed meridional plane
  contains the transmitted phase vector too, so one plane serves all three waves.

## iii. Table of contents

- A. Meridional directions at an oriented interface
- B. The incidence-angle correspondence
- C. Reflection
- D. Refraction
- E. Refraction stated about a ray
- F. Existence of the realising ray
- G. One meridional plane for all three waves

## iv. References

- `Physlib.Optics.Rays.Basic`, section F, which names this bridge and fixes the ray-side objects.
- `Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry` for the side-relative phase angles
  and `Physlib.Optics.Interfaces.PlanarDielectric.Snell` for the derived Snell law.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real Space

/-!

## A. Meridional directions at an oriented interface

-/

/-- The cosine of a unit vector's side-relative angle is its inner product with the unit side
normal.

This is the interface-side half of the bridge. The ray-side half is
`Optics.MeridionalRay.cos_signedIncidenceAngle`, and the two have the same shape, which is what
makes the correspondence possible at all.
-/
lemma cos_angleToSide_of_norm_eq_one {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    Real.cos (plane.angleToSide side v) = inner ℝ (plane.sideNormalVector side) v := by
  have hcos := plane.cos_angleToSide_mul_norm side v
  rw [hv, mul_one] at hcos
  rw [hcos, OrientedAffineHyperplane.sideNormalVector, real_inner_smul_left,
    OrientedAffineHyperplane.normalComponent]

/-- The ambient unit direction of a meridional ray that makes the signed angle `α` with the normal
into `side`, in the plane spanned by that normal and a supplied unit tangent.

The tangent is a parameter, not a construction: which meridional plane a ray lies in is data the
configuration must supply.
-/
def meridionalDirection {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  Real.cos α • plane.sideNormalVector side + Real.sin α • tangent

/-- A tangent with vanishing normal component is orthogonal to either side normal. -/
lemma inner_sideNormalVector_of_normalComponent_eq_zero {d : ℕ}
    (plane : OrientedAffineHyperplane d) (side : OrientedAffineHyperplane.Side)
    (tangent : EuclideanSpace ℝ (Fin d)) (htangent : plane.normalComponent tangent = 0) :
    inner ℝ (plane.sideNormalVector side) tangent = 0 := by
  rw [OrientedAffineHyperplane.sideNormalVector, real_inner_smul_left,
    ← OrientedAffineHyperplane.normalComponent, htangent, mul_zero]

/-- A meridional direction is a unit vector. -/
lemma norm_meridionalDirection {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ)
    (htangentNorm : ‖tangent‖ = 1) (htangentNormal : plane.normalComponent tangent = 0) :
    ‖meridionalDirection plane side tangent α‖ = 1 := by
  have horth : inner ℝ (Real.cos α • plane.sideNormalVector side) (Real.sin α • tangent) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_sideNormalVector_of_normalComponent_eq_zero plane side tangent htangentNormal]
    ring
  have hsq : ‖meridionalDirection plane side tangent α‖ ^ 2 = 1 := by
    rw [meridionalDirection, pow_two,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      norm_smul, norm_smul, htangentNorm, plane.sideNormalVector_norm, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, ← pow_two, ← pow_two, sq_abs, sq_abs,
      Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (meridionalDirection plane side tangent α), hsq]

/-- The side-relative cosine of a meridional direction is the cosine of its signed angle. -/
lemma cos_angleToSide_meridionalDirection {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ)
    (htangentNorm : ‖tangent‖ = 1) (htangentNormal : plane.normalComponent tangent = 0) :
    Real.cos (plane.angleToSide side (meridionalDirection plane side tangent α)) = Real.cos α := by
  rw [cos_angleToSide_of_norm_eq_one plane side _
      (norm_meridionalDirection plane side tangent α htangentNorm htangentNormal),
    meridionalDirection, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_sideNormalVector_of_normalComponent_eq_zero plane side tangent htangentNormal,
    real_inner_self_eq_norm_sq, plane.sideNormalVector_norm]
  ring

/-!

## B. The incidence-angle correspondence

-/

/-- **The incidence-angle correspondence.** The ambient direction built at signed angle `α` has
interface-side angle exactly `α`.

The range hypothesis is not removable. The interface-side angle is unoriented and lives in
`[0, π]`, so it can only equal a signed ray angle that already lies there; outside that range the
cosines still agree and the angles do not.
-/
theorem angleToSide_meridionalDirection {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ)
    (htangentNorm : ‖tangent‖ = 1) (htangentNormal : plane.normalComponent tangent = 0)
    (hlower : 0 ≤ α) (hupper : α ≤ π) :
    plane.angleToSide side (meridionalDirection plane side tangent α) = α := by
  refine Real.injOn_cos ⟨?_, ?_⟩ ⟨hlower, hupper⟩ ?_
  · exact InnerProductGeometry.angle_nonneg _ _
  · exact InnerProductGeometry.angle_le_pi _ _
  · exact cos_angleToSide_meridionalDirection plane side tangent α htangentNorm htangentNormal

/-- **The signed ray angle is the interface-side angle**, for a meridional ray whose ambient
direction is the one built from its signed incidence angle. -/
theorem angleToSide_meridionalDirection_signedIncidenceAngle {d : ℕ}
    (plane : OrientedAffineHyperplane d) (side : OrientedAffineHyperplane.Side)
    (tangent : EuclideanSpace ℝ (Fin d)) (r : MeridionalRay) (normalAngle : ℝ)
    (htangentNorm : ‖tangent‖ = 1) (htangentNormal : plane.normalComponent tangent = 0)
    (hlower : 0 ≤ r.signedIncidenceAngle normalAngle)
    (hupper : r.signedIncidenceAngle normalAngle ≤ π) :
    plane.angleToSide side
        (meridionalDirection plane side tangent (r.signedIncidenceAngle normalAngle)) =
      r.signedIncidenceAngle normalAngle :=
  angleToSide_meridionalDirection plane side tangent _ htangentNorm htangentNormal hlower hupper

/-!

## C. Reflection

-/

/-- Hyperplane reflection maps the meridional direction at signed angle `α` into `side` to the
meridional direction at the *same* angle into the opposite side. -/
theorem vectorReflection_meridionalDirection {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ)
    (htangentNormal : plane.normalComponent tangent = 0) :
    plane.vectorReflection (meridionalDirection plane side tangent α) =
      meridionalDirection plane side.opposite tangent α := by
  have hcomponent : plane.normalComponent (meridionalDirection plane side tangent α) =
      Real.cos α * side.sign := by
    rw [meridionalDirection, OrientedAffineHyperplane.normalComponent, inner_add_right,
      real_inner_smul_right, real_inner_smul_right,
      ← OrientedAffineHyperplane.normalComponent, ← OrientedAffineHyperplane.normalComponent,
      plane.normalComponent_sideNormalVector, htangentNormal]
    ring
  rw [OrientedAffineHyperplane.vectorReflection_eq_sub_two_smul_normalVector, hcomponent,
    meridionalDirection, meridionalDirection, OrientedAffineHyperplane.sideNormalVector_opposite,
    OrientedAffineHyperplane.sideNormalVector]
  module

/-- **The folded plane-mirror law is exact.** Measured into the outgoing side, the reflected ray
makes the same angle as the incident ray made with the incoming side.

This is what the folded reflection convention of `Physlib.Optics.Rays.Basic` encodes. There a plane
mirror acts as the identity on `(height, angle)` because the axis is re-referenced to the outgoing
direction; here that re-referencing is the exchange of sides, and the angle is preserved exactly,
with no small-angle approximation.
-/
theorem angleToSide_vectorReflection_meridionalDirection {d : ℕ}
    (plane : OrientedAffineHyperplane d) (side : OrientedAffineHyperplane.Side)
    (tangent : EuclideanSpace ℝ (Fin d)) (α : ℝ) (htangentNorm : ‖tangent‖ = 1)
    (htangentNormal : plane.normalComponent tangent = 0) (hlower : 0 ≤ α) (hupper : α ≤ π) :
    plane.angleToSide side.opposite
        (plane.vectorReflection (meridionalDirection plane side tangent α)) = α := by
  rw [vectorReflection_meridionalDirection plane side tangent α htangentNormal]
  exact angleToSide_meridionalDirection plane side.opposite tangent α htangentNorm htangentNormal
    hlower hupper

/-!

## D. Refraction

-/

/-- **The paraxial refraction bound, with its Snell hypothesis discharged.**

`Optics.abs_paraxialSnell_sub_le` bounds the deviation of the paraxial refraction law from exact
Snell refraction by an explicit cubic term. In `Physlib.Optics.Rays.Basic` its Snell hypothesis was
supplied by hand. Here the same bound is obtained with that hypothesis discharged by
`IsElectricPhaseMatched.snellLaw_refractiveIndexRelativeTo`.

The provenance is exactly that and no more: the Snell law is derived from the supplied electric
phase-matching predicate together with material dispersion matching and zero attenuation. That
predicate is stipulated rather than derived from the integral Maxwell equations, so this is a
reduction to a stated boundary condition, not to Maxwell.

The refractive indices are relative to a common reference medium, and their nonnegativity is
discharged rather than assumed.
-/
theorem abs_paraxialSnell_sub_le_snellLaw
    {configuration : PlanarDielectricWaveConfiguration}
    (h : configuration.IsElectricPhaseMatched)
    (reference : Electromagnetism.HomogeneousIsotropicMedium)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0) :
    |configuration.interface.negativeMedium.refractiveIndexRelativeTo reference *
          configuration.incidentPhaseAngle -
        configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
          configuration.transmittedPhaseAngle| ≤
      (configuration.interface.negativeMedium.refractiveIndexRelativeTo reference *
            |configuration.incidentPhaseAngle| ^ 3 +
          configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
            |configuration.transmittedPhaseAngle| ^ 3) / 6 :=
  abs_paraxialSnell_sub_le
    (configuration.interface.negativeMedium.refractiveIndexRelativeTo_pos reference).le
    (configuration.interface.positiveMedium.refractiveIndexRelativeTo_pos reference).le
    (h.snellLaw_refractiveIndexRelativeTo reference hIncidentDispersion hTransmittedDispersion
      hIncidentAttenuation hTransmittedAttenuation)

/-- **The derived Snell law reproduces the ray development's exact refraction angle.**

`Optics.exactRefractionAngle` was introduced in `Physlib.Optics.Rays.Basic` by solving the sine
form of Snell refraction algebraically, with the Snell law itself written down by hand. Here it is
identified with the transmitted phase angle of a configuration whose Snell law is *derived* from
electric phase matching.

The range hypothesis is the principal-branch condition that `Real.arcsin` inverts: it selects the
transmitted branch, which the algebra alone cannot do.
-/
theorem exactRefractionAngle_incidentPhaseAngle
    {configuration : PlanarDielectricWaveConfiguration}
    (h : configuration.IsElectricPhaseMatched)
    (reference : Electromagnetism.HomogeneousIsotropicMedium)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0)
    (hlower : -(π / 2) ≤ configuration.transmittedPhaseAngle)
    (hupper : configuration.transmittedPhaseAngle ≤ π / 2) :
    exactRefractionAngle
        (configuration.interface.negativeMedium.refractiveIndexRelativeTo reference)
        (configuration.interface.positiveMedium.refractiveIndexRelativeTo reference)
        configuration.incidentPhaseAngle = configuration.transmittedPhaseAngle := by
  have hSnell := h.snellLaw_refractiveIndexRelativeTo reference hIncidentDispersion
    hTransmittedDispersion hIncidentAttenuation hTransmittedAttenuation
  have hTransmittedIndex :
      configuration.interface.positiveMedium.refractiveIndexRelativeTo reference ≠ 0 :=
    (configuration.interface.positiveMedium.refractiveIndexRelativeTo_pos reference).ne'
  have hratio :
      configuration.interface.negativeMedium.refractiveIndexRelativeTo reference /
            configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
          Real.sin configuration.incidentPhaseAngle =
        Real.sin configuration.transmittedPhaseAngle := by
    field_simp
    linarith [hSnell]
  rw [exactRefractionAngle, hratio, Real.arcsin_sin hlower hupper]

/-!

## E. Refraction stated about a ray

-/

/-- A side-relative angle is unchanged by positive rescaling, because the underlying unoriented
angle is. -/
lemma angleToSide_smul_of_pos {d : ℕ} (plane : OrientedAffineHyperplane d)
    (side : OrientedAffineHyperplane.Side) (v : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 < c) :
    plane.angleToSide side (c • v) = plane.angleToSide side v := by
  rw [OrientedAffineHyperplane.angleToSide, OrientedAffineHyperplane.angleToSide,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hc]

/-- A meridional ray *realises* a configuration's incident phase direction when the configuration's
incident phase vector points along the ray's ambient direction.

Only the direction is constrained, so the positive scale factor is existentially part of the data:
a phase vector carries a magnitude that a ray does not.
-/
def RealisesIncidentPhaseDirection (configuration : PlanarDielectricWaveConfiguration)
    (r : MeridionalRay) (normalAngle : ℝ) (tangent : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    configuration.incident.waveVector.phaseVector =
      c • meridionalDirection configuration.interface.plane .positive tangent
        (r.signedIncidenceAngle normalAngle)

/-- **The realising ray's signed incidence angle is the configuration's incident phase angle.** -/
theorem incidentPhaseAngle_eq_signedIncidenceAngle
    {configuration : PlanarDielectricWaveConfiguration} {r : MeridionalRay} {normalAngle : ℝ}
    {tangent : EuclideanSpace ℝ (Fin 3)}
    (hrealises : RealisesIncidentPhaseDirection configuration r normalAngle tangent)
    (htangentNorm : ‖tangent‖ = 1)
    (htangentNormal : configuration.interface.plane.normalComponent tangent = 0)
    (hlower : 0 ≤ r.signedIncidenceAngle normalAngle)
    (hupper : r.signedIncidenceAngle normalAngle ≤ π) :
    configuration.incidentPhaseAngle = r.signedIncidenceAngle normalAngle := by
  obtain ⟨c, hc, hphase⟩ := hrealises
  rw [PlanarDielectricWaveConfiguration.incidentPhaseAngle,
    ClassicalMechanics.ComplexWaveVector.phaseAngleToSide, hphase,
    angleToSide_smul_of_pos _ _ _ hc]
  exact angleToSide_meridionalDirection_signedIncidenceAngle _ _ _ r normalAngle htangentNorm
    htangentNormal hlower hupper

/-- **The configuration's transmitted phase angle is the ray development's exact refraction of the
realising ray's angle.** -/
theorem transmittedPhaseAngle_eq_exactRefractionAngle_signedIncidenceAngle
    {configuration : PlanarDielectricWaveConfiguration} {r : MeridionalRay} {normalAngle : ℝ}
    {tangent : EuclideanSpace ℝ (Fin 3)}
    (h : configuration.IsElectricPhaseMatched)
    (reference : Electromagnetism.HomogeneousIsotropicMedium)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0)
    (hTransmittedLower : -(π / 2) ≤ configuration.transmittedPhaseAngle)
    (hTransmittedUpper : configuration.transmittedPhaseAngle ≤ π / 2)
    (hrealises : RealisesIncidentPhaseDirection configuration r normalAngle tangent)
    (htangentNorm : ‖tangent‖ = 1)
    (htangentNormal : configuration.interface.plane.normalComponent tangent = 0)
    (hlower : 0 ≤ r.signedIncidenceAngle normalAngle)
    (hupper : r.signedIncidenceAngle normalAngle ≤ π) :
    exactRefractionAngle
        (configuration.interface.negativeMedium.refractiveIndexRelativeTo reference)
        (configuration.interface.positiveMedium.refractiveIndexRelativeTo reference)
        (r.signedIncidenceAngle normalAngle) = configuration.transmittedPhaseAngle := by
  rw [← incidentPhaseAngle_eq_signedIncidenceAngle hrealises htangentNorm htangentNormal hlower
    hupper]
  exact exactRefractionAngle_incidentPhaseAngle h reference hIncidentDispersion
    hTransmittedDispersion hIncidentAttenuation hTransmittedAttenuation hTransmittedLower
    hTransmittedUpper

/-- **The paraxial refraction bound, about a ray.**

This is `Optics.abs_paraxialSnell_sub_le_snellLaw` with the interface's own incident phase angle
replaced by the signed incidence angle of a ray that realises the incident phase direction. It is
the form in which the bound is a statement about the ray development rather than about the
interface theory alone.

It says no more about provenance than `Optics.abs_paraxialSnell_sub_le_snellLaw` does: the Snell
law is reduced to a stipulated electric phase-matching predicate, not to Maxwell, and the paraxial
law being bounded remains a model law.
-/
theorem abs_paraxialSnell_sub_le_snellLaw_meridional
    {configuration : PlanarDielectricWaveConfiguration} {r : MeridionalRay} {normalAngle : ℝ}
    {tangent : EuclideanSpace ℝ (Fin 3)}
    (h : configuration.IsElectricPhaseMatched)
    (reference : Electromagnetism.HomogeneousIsotropicMedium)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0)
    (hrealises : RealisesIncidentPhaseDirection configuration r normalAngle tangent)
    (htangentNorm : ‖tangent‖ = 1)
    (htangentNormal : configuration.interface.plane.normalComponent tangent = 0)
    (hlower : 0 ≤ r.signedIncidenceAngle normalAngle)
    (hupper : r.signedIncidenceAngle normalAngle ≤ π) :
    |configuration.interface.negativeMedium.refractiveIndexRelativeTo reference *
          r.signedIncidenceAngle normalAngle -
        configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
          configuration.transmittedPhaseAngle| ≤
      (configuration.interface.negativeMedium.refractiveIndexRelativeTo reference *
            |r.signedIncidenceAngle normalAngle| ^ 3 +
          configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
            |configuration.transmittedPhaseAngle| ^ 3) / 6 := by
  rw [← incidentPhaseAngle_eq_signedIncidenceAngle hrealises htangentNorm htangentNormal hlower
    hupper]
  exact abs_paraxialSnell_sub_le_snellLaw h reference hIncidentDispersion hTransmittedDispersion
    hIncidentAttenuation hTransmittedAttenuation

/-!

## F. Existence of the realising ray

-/

/-- The canonical unit tangent singled out by a phase vector that is not normally incident.

At normal incidence the tangential projection vanishes and this is the junk value `0`. The
non-normal-incidence hypothesis carried below is what *this* construction needs, since it
normalises that projection. It is not a condition for a meridional plane to exist: a normal phase
vector lies in infinitely many, so the plane is undetermined rather than absent.
-/
def incidenceTangent (plane : OrientedAffineHyperplane 3) (k : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  ‖plane.tangentialProjection k‖⁻¹ • plane.tangentialProjection k

/-- Away from normal incidence the singled-out tangent is a unit vector. -/
lemma norm_incidenceTangent (plane : OrientedAffineHyperplane 3) (k : EuclideanSpace ℝ (Fin 3))
    (h : plane.tangentialProjection k ≠ 0) : ‖incidenceTangent plane k‖ = 1 := by
  rw [incidenceTangent, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

/-- The singled-out tangent lies in the interface. -/
lemma normalComponent_incidenceTangent (plane : OrientedAffineHyperplane 3)
    (k : EuclideanSpace ℝ (Fin 3)) :
    plane.normalComponent (incidenceTangent plane k) = 0 := by
  rw [incidenceTangent, OrientedAffineHyperplane.normalComponent, real_inner_smul_right,
    ← OrientedAffineHyperplane.normalComponent, plane.normalComponent_tangentialProjection,
    mul_zero]

/-- The meridional ray singled out by a phase vector: it sits on the axis and carries the phase
vector's own angle to the positive side. -/
def incidenceRay (plane : OrientedAffineHyperplane 3) (k : EuclideanSpace ℝ (Fin 3)) :
    MeridionalRay :=
  ⟨0, 0, plane.angleToSide .positive k⟩

lemma incidenceRay_signedIncidenceAngle (plane : OrientedAffineHyperplane 3)
    (k : EuclideanSpace ℝ (Fin 3)) :
    (incidenceRay plane k).signedIncidenceAngle 0 = plane.angleToSide .positive k := by
  rw [MeridionalRay.signedIncidenceAngle, incidenceRay, sub_zero]

/-- The constructed tangent and ray really do realise the incident phase direction.

The scale factor is the phase vector's norm, which is what the construction discards: a ray has a
direction and no magnitude.
-/
theorem realisesIncidentPhaseDirection_incidenceRay
    (configuration : PlanarDielectricWaveConfiguration)
    (h : configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector ≠ 0) :
    RealisesIncidentPhaseDirection configuration
      (incidenceRay configuration.interface.plane
        configuration.incident.waveVector.phaseVector) 0
      (incidenceTangent configuration.interface.plane
        configuration.incident.waveVector.phaseVector) := by
  set plane := configuration.interface.plane with hplane
  set k := configuration.incident.waveVector.phaseVector with hk
  have hkne : k ≠ 0 := by
    intro hzero
    apply h
    rw [hzero]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  have hnorm : 0 < ‖k‖ := norm_pos_iff.mpr hkne
  have hproj : ‖plane.tangentialProjection k‖ ≠ 0 := norm_ne_zero_iff.mpr h
  refine ⟨‖k‖, hnorm, ?_⟩
  have hcos : ‖k‖ * Real.cos (plane.angleToSide .positive k) = plane.normalComponent k := by
    have hraw := plane.cos_angleToSide_mul_norm .positive k
    rw [OrientedAffineHyperplane.Side.sign_positive, one_mul] at hraw
    linarith [hraw]
  have hsin : ‖k‖ * Real.sin (plane.angleToSide .positive k) =
      ‖plane.tangentialProjection k‖ := by
    have hraw := plane.sin_angleToSide_mul_norm .positive k
    linarith [hraw]
  rw [meridionalDirection, incidenceRay_signedIncidenceAngle,
    OrientedAffineHyperplane.sideNormalVector_positive, incidenceTangent, smul_add, smul_smul,
    smul_smul, hcos, hsin, smul_smul, mul_inv_cancel₀ hproj, one_smul, add_comm]
  exact (plane.tangentialProjection_add_normal k).symm

/-- **At normal incidence every tangent realises the incident direction.**

This is the precise content of the claim that a normally incident phase vector determines no
meridional plane. Its tangential projection vanishes, so the tangential term of the ambient
direction is identically zero and the realisation predicate constrains the tangent not at all —
no unit-norm or in-interface hypothesis is even needed. Existence of a realising ray therefore
never depended on non-normal incidence; only the *canonical* choice of tangent does.
-/
theorem realisesIncidentPhaseDirection_of_tangentialProjection_eq_zero
    {configuration : PlanarDielectricWaveConfiguration}
    (tangent : EuclideanSpace ℝ (Fin 3))
    (hk : configuration.incident.waveVector.phaseVector ≠ 0)
    (hnormal : configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector = 0) :
    RealisesIncidentPhaseDirection configuration
      (incidenceRay configuration.interface.plane
        configuration.incident.waveVector.phaseVector) 0 tangent := by
  set plane := configuration.interface.plane with hplane
  set k := configuration.incident.waveVector.phaseVector with hkdef
  have hnorm : 0 < ‖k‖ := norm_pos_iff.mpr hk
  refine ⟨‖k‖, hnorm, ?_⟩
  have hsin : ‖k‖ * Real.sin (plane.angleToSide .positive k) = 0 := by
    have hraw := plane.sin_angleToSide_mul_norm .positive k
    rw [hnormal, norm_zero] at hraw
    linarith [hraw]
  have hcos : ‖k‖ * Real.cos (plane.angleToSide .positive k) = plane.normalComponent k := by
    have hraw := plane.cos_angleToSide_mul_norm .positive k
    rw [OrientedAffineHyperplane.Side.sign_positive, one_mul] at hraw
    linarith [hraw]
  have hdecomp := plane.tangentialProjection_add_normal k
  rw [hnormal, zero_add] at hdecomp
  rw [meridionalDirection, incidenceRay_signedIncidenceAngle,
    OrientedAffineHyperplane.sideNormalVector_positive, smul_add, smul_smul, smul_smul, hcos,
    hsin, zero_smul, add_zero]
  exact hdecomp.symm

/-- **Existence of the realising ray.** Away from normal incidence, a configuration determines a
unit tangent in its interface and a meridional ray that realises its incident phase direction,
with the signed incidence angle already in the range the bridge results need.

This is what makes the hypothesis of section E discharge-able rather than an assumption about the
configuration. The conclusion is packaged in exactly the form
`Optics.abs_paraxialSnell_sub_le_snellLaw_meridional` consumes.
-/
theorem exists_realisesIncidentPhaseDirection
    (configuration : PlanarDielectricWaveConfiguration)
    (h : configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector ≠ 0) :
    ∃ (tangent : EuclideanSpace ℝ (Fin 3)) (r : MeridionalRay) (normalAngle : ℝ),
      ‖tangent‖ = 1 ∧
        configuration.interface.plane.normalComponent tangent = 0 ∧
        RealisesIncidentPhaseDirection configuration r normalAngle tangent ∧
        0 ≤ r.signedIncidenceAngle normalAngle ∧
        r.signedIncidenceAngle normalAngle ≤ π :=
  ⟨incidenceTangent configuration.interface.plane
      configuration.incident.waveVector.phaseVector,
    incidenceRay configuration.interface.plane configuration.incident.waveVector.phaseVector, 0,
    norm_incidenceTangent _ _ h, normalComponent_incidenceTangent _ _,
    realisesIncidentPhaseDirection_incidenceRay configuration h,
    by
      rw [incidenceRay_signedIncidenceAngle]
      exact InnerProductGeometry.angle_nonneg _ _,
    by
      rw [incidenceRay_signedIncidenceAngle]
      exact InnerProductGeometry.angle_le_pi _ _⟩

/-!

## G. One meridional plane for all three waves

-/

/-- The meridional plane singled out by a phase vector: the real span of the constructed tangent
and the interface normal. -/
def meridionalPlaneSpan (plane : OrientedAffineHyperplane 3) (k : EuclideanSpace ℝ (Fin 3)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  Submodule.span ℝ {incidenceTangent plane k, plane.normalVector}

/-- Away from normal incidence the constructed tangent spans the same plane with the normal as the
phase vector itself does.

This is what lets the interface theory's plane-of-incidence results be read as statements about
the constructed meridional plane: they are phrased with the incident phase vector, and this
identifies that span with the one built from the ray's tangent.
-/
lemma meridionalPlaneSpan_eq (plane : OrientedAffineHyperplane 3)
    (k : EuclideanSpace ℝ (Fin 3)) (h : plane.tangentialProjection k ≠ 0) :
    meridionalPlaneSpan plane k = Submodule.span ℝ {k, plane.normalVector} := by
  have hproj : ‖plane.tangentialProjection k‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have htangent : incidenceTangent plane k ∈ Submodule.span ℝ {k, plane.normalVector} := by
    refine Submodule.mem_span_pair.mpr
      ⟨‖plane.tangentialProjection k‖⁻¹,
        -(‖plane.tangentialProjection k‖⁻¹ * plane.normalComponent k), ?_⟩
    rw [incidenceTangent, OrientedAffineHyperplane.tangentialProjection]
    module
  have hk : k ∈ Submodule.span ℝ {incidenceTangent plane k, plane.normalVector} := by
    refine Submodule.mem_span_pair.mpr
      ⟨‖plane.tangentialProjection k‖, plane.normalComponent k, ?_⟩
    rw [incidenceTangent, smul_smul, mul_inv_cancel₀ hproj, one_smul]
    exact plane.tangentialProjection_add_normal k
  apply le_antisymm
  · rw [meridionalPlaneSpan, Submodule.span_le, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨htangent, Submodule.subset_span (by simp)⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, meridionalPlaneSpan]
    exact ⟨hk, Submodule.subset_span (by simp)⟩

/-- The incident phase vector lies in the meridional plane it determines. -/
lemma mem_meridionalPlaneSpan_self (plane : OrientedAffineHyperplane 3)
    (k : EuclideanSpace ℝ (Fin 3)) (h : plane.tangentialProjection k ≠ 0) :
    k ∈ meridionalPlaneSpan plane k := by
  rw [meridionalPlaneSpan_eq plane k h]
  exact Submodule.subset_span (by simp)

/-- **The transmitted phase vector lies in the meridional plane built from the incident one.**

The interface theory proves the plane-of-incidence law with the incident phase vector; combined
with `Optics.meridionalPlaneSpan_eq` it becomes a statement about the plane the ray construction
actually uses.
-/
theorem transmitted_phaseVector_mem_meridionalPlaneSpan
    {configuration : PlanarDielectricWaveConfiguration}
    (h : configuration.IsElectricPhaseMatched)
    (hTangential : configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector ≠ 0) :
    configuration.transmitted.waveVector.phaseVector ∈
      meridionalPlaneSpan configuration.interface.plane
        configuration.incident.waveVector.phaseVector := by
  rw [meridionalPlaneSpan_eq _ _ hTangential]
  exact h.transmitted_phaseVector_mem_incidencePlane

/-- **One meridional plane serves all three waves.**

The reflected alternative is the interface theory's own: a reflected candidate with zero electric
amplitude keeps unconstrained wave-vector data and is not placed in any plane. That disjunction is
preserved rather than discharged.
-/
theorem reflected_electricAmplitude_eq_zero_or_phaseVectors_mem_meridionalPlaneSpan
    {configuration : PlanarDielectricWaveConfiguration}
    (h : configuration.IsElectricPhaseMatched)
    (hTangential : configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector ≠ 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.waveVector.phaseVector ∈
          meridionalPlaneSpan configuration.interface.plane
            configuration.incident.waveVector.phaseVector ∧
        configuration.transmitted.waveVector.phaseVector ∈
          meridionalPlaneSpan configuration.interface.plane
            configuration.incident.waveVector.phaseVector) := by
  rw [meridionalPlaneSpan_eq _ _ hTangential]
  exact h.reflected_electricAmplitude_eq_zero_or_phaseVectors_mem_incidencePlane

end

end Optics
