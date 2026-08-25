# R lane handoff — the ray-to-interface bridge

Branch: `optics/r-e5b-bridge`, branched from `optics/development` at `9bc5aefd`.
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-r-ray-optics`.

This lane answers `goal.md` §H.5 R1's fourth bullet, which R1–R5 deliberately left open. It is the
one place the ray layering rule is lifted: `Physlib/Optics/Rays/E5bBridge.lean` may import
`Physlib.Optics.Interfaces.PlanarDielectric`.

---

## Commits

| Commit | Contents |
|---|---|
| `de4be782` | Side-convention docstring fix, already merged as `48015bbf` |
| `23d3b6fe` | The refraction results stated about a ray |
| `f5b8c2b7` | R5 corrective slice: withhold RS-04, RS-06, RS-07 by name |
| `f8ce8a8c` | Meridional-plane existence, and the provenance correction below |
| (this one) | One meridional plane for all three waves, and the C2 corrections |

## Registrations needed in `Physlib.lean`

```
public import Physlib.Optics.Rays.E5bBridge
public import Physlib.Optics.Rays.E5bBridgeRegression
```

`E5bBridge` sorts after `BasicRegression` and before `Gaussian`.

## Files added

- `Physlib/Optics/Rays/E5bBridge.lean`
- `Physlib/Optics/Rays/E5bBridgeRegression.lean`

## Gates

- `lake-lock build` of both modules — clean, no warnings.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true` on each — zero output.
- Batteries declaration linters, all 14, over 34 declarations — passed.
- `module_doc_lint`, `style_lint` and the `regex_lint` paren rule, reimplemented as text checks —
  clean.
- No `sorry`, `axiom`, `native_decide`, `nolint`, or `set_option maxHeartbeats`.

The one-time dependency build was
`lake-lock build Physlib.Optics.Interfaces.PlanarDielectric.Snell` (3555 jobs), not
`AngularGeometry` as the lane brief said — see the corrections below.

---

## Three corrections to the lane brief, checked against the source before building

**1. The side convention was stated backwards.** The brief said `AngularGeometry`'s
`incidentPhaseAngle` is measured from the negative-side normal. From the definitions
(`AngularGeometry.lean` lines 88, 97, 105):

| Declaration | Side |
|---|---|
| `incidentPhaseAngle` | **positive** |
| `transmittedPhaseAngle` | **positive** |
| `reflectedPhaseAngle` | **negative** |

Only the reflected angle uses the negative side. The same false claim was in this lane's own R1
hook docstring, written from memory, and had reached the integration branch; commit `de4be782`
corrects it. The real work of the bridge is reconciling *two different* side choices with the
single normal angle used on the ray side, not flipping one sign.

**2. The build target was wrong.** `snellLaw_refractiveIndexRelativeTo` is in
`Interfaces/PlanarDielectric/Snell.lean`, not `AngularGeometry.lean`. `Snell.lean` imports
`AngularGeometry`, so building `Snell` is a superset and still one target; building only
`AngularGeometry` would have left the refraction item unbuildable.

**3. The incidence correspondence cannot be an equality of reals.** `phaseAngleToSide` is
Mathlib's *unoriented* vector angle, valued in `[0, π]`, assigning `π / 2` to a zero vector;
`signedIncidenceAngle` is a signed real difference. The bridge therefore goes through the cosine
identity, and every result asserting an equality of angles carries an explicit range hypothesis.
This is what the merged hook docstring already said, so the brief was inconsistent with the code it
targeted; the merged code was followed.

---

## Declarations added

### `Physlib.Optics.Rays.E5bBridge`

Section A, meridional directions:

- `Optics.cos_angleToSide_of_norm_eq_one` — the interface-side half of the bridge: a unit vector's
  side-relative cosine is its inner product with the side normal. The ray-side half,
  `MeridionalRay.cos_signedIncidenceAngle`, already had the same shape.
- `Optics.meridionalDirection` — the ambient direction of a ray at signed angle `α`, built from a
  side normal and a supplied unit tangent.
- `Optics.inner_sideNormalVector_of_normalComponent_eq_zero`,
  `Optics.norm_meridionalDirection`, `Optics.cos_angleToSide_meridionalDirection`.

Section B, the incidence correspondence:

- `Optics.angleToSide_meridionalDirection` — the constructed direction has interface-side angle
  exactly `α`, under `0 ≤ α ≤ π`.
- `Optics.angleToSide_meridionalDirection_signedIncidenceAngle` — the same for a `MeridionalRay`'s
  signed incidence angle.

Section C, reflection:

- `Optics.vectorReflection_meridionalDirection` — hyperplane reflection maps the direction at angle
  `α` into one side to the direction at the *same* angle into the opposite side.
- `Optics.angleToSide_vectorReflection_meridionalDirection` — measured into the outgoing side, the
  reflected ray makes the same angle. This is the exact content of the folded plane-mirror law:
  re-referencing the axis *is* the exchange of sides.

Section D, refraction (see the provenance correction below before quoting these):

- `Optics.exactRefractionAngle_incidentPhaseAngle` — the transmitted phase angle **is** the ray
  development's `exactRefractionAngle` of the incident phase angle.
- `Optics.abs_paraxialSnell_sub_le_snellLaw` — the paraxial refraction law holds to within R1's
  cubic bound, with the Snell hypothesis **discharged** by
  `IsElectricPhaseMatched.snellLaw_refractiveIndexRelativeTo` rather than supplied by hand. The
  refractive-index positivity is discharged too, via `refractiveIndexRelativeTo_pos`.

Section E, refraction stated about a ray:

- `Optics.angleToSide_smul_of_pos`, `Optics.RealisesIncidentPhaseDirection`,
  `Optics.incidentPhaseAngle_eq_signedIncidenceAngle`,
  `Optics.transmittedPhaseAngle_eq_exactRefractionAngle_signedIncidenceAngle`,
  `Optics.abs_paraxialSnell_sub_le_snellLaw_meridional`.

Section F, existence of the realising ray:

- `Optics.incidenceTangent`, `Optics.norm_incidenceTangent`,
  `Optics.normalComponent_incidenceTangent`, `Optics.incidenceRay`,
  `Optics.incidenceRay_signedIncidenceAngle`,
  `Optics.realisesIncidentPhaseDirection_incidenceRay`,
  `Optics.exists_realisesIncidentPhaseDirection`.

  The construction decomposes the incident phase vector into its normal component and tangential
  projection, takes the tangent to be the normalised projection and the ray angle to be the phase
  vector's own `angleToSide`, and the scale factor is the phase vector's norm — which is exactly
  what a ray discards. The conclusion is packaged with the range facts, so it plugs directly into
  section E.

  **The hypothesis is that the tangential projection is nonzero, that is, not normal incidence.**
  This is a fact about the physics, not a formalisation gap: at exactly normal incidence every unit
  tangent in the interface serves equally and there is no plane of incidence to construct.

  E5b's `transmitted_phaseVector_mem_incidencePlane` does **not** supply this. It is a membership
  statement — the transmitted phase vector lies in the span of the incident phase vector and the
  normal — not a construction of a tangent. It is complementary, and section G below uses it.

- `Optics.realisesIncidentPhaseDirection_of_tangentialProjection_eq_zero` — at normal incidence
  *every* tangent realises the incident direction, with no unit-norm or in-interface hypothesis
  needed at all, because the tangential term of the ambient direction vanishes identically. This
  is the precise form of "the plane is undetermined, not absent", and it establishes that
  existence never depended on non-normal incidence; only the canonical choice of tangent does.

Section G, one meridional plane for all three waves:

- `Optics.meridionalPlaneSpan`, `Optics.meridionalPlaneSpan_eq` (the span built from the canonical
  tangent is the span built from the phase vector), `Optics.mem_meridionalPlaneSpan_self`.
- `Optics.transmitted_phaseVector_mem_meridionalPlaneSpan` and
  `Optics.reflected_electricAmplitude_eq_zero_or_phaseVectors_mem_meridionalPlaneSpan` — the
  constructed plane contains the transmitted and, away from the interface theory's own
  zero-amplitude alternative, the reflected phase vectors. That disjunction is preserved, not
  discharged.

  This is a statement about **spans of phase vectors**. It assigns no ray, direction of travel, or
  outgoing role to the transmitted or reflected labels.

### `Physlib.Optics.Rays.E5bBridgeRegression`

`Optics.e5bBridgeRegressionNormal`, `.e5bBridgeRegressionPlane`, `.e5bBridgeRegressionTangent`,
`.e5bBridgeRegressionTangent_norm`, `.e5bBridgeRegressionTangent_normalComponent`,
`.e5bBridgeRegressionAngle`, `.e5bBridgeRegression_cos`, `.e5bBridgeRegression_sin`,
`.e5bBridgeRegressionAngle_mem`, `.e5bBridgeRegression_direction`,
`.e5bBridgeRegression_direction_norm`, `.e5bBridgeRegression_angleToSide`,
`.e5bBridgeRegression_reflected_direction`, `.e5bBridgeRegression_reflected_angleToSide`.

The fixture is the exact `3-4-5` direction `(3/5, 0, 4/5)` against a third-coordinate normal — the
same numbers the `Physlib.Optics.Polarization` incidence-frame regressions use, rebuilt here so
this file depends only on the bridge. It pins the convention to **coordinates**: the constructed
direction is checked to be `(3/5, 0, 4/5)` and the reflected direction `(3/5, 0, -4/5)`, so a side
or sign error shows up as a changed coordinate rather than as a changed name.

---

## What this closes, and what it does not

**A provenance correction to this note's own earlier wording.** An earlier version of this file,
and of the module documentation, said the paraxial bound "rests on the interface theory rather than
on a stipulated law", and reports from this lane said the Snell law was derived from Maxwell.
**That was false and has been corrected in the module documentation and in both refraction
docstrings.** The error was this lane's: it verified what
`snellLaw_refractiveIndexRelativeTo` *consumes* and asserted the provenance of the whole chain
without checking whether what it consumes is itself derived. It is not. The interface modules say
so of their own predicates, verbatim:

- `Interfaces/PlanarDielectric/WaveBoundary.lean` — "the local boundary predicates are stipulated
  rather than derived from integral Maxwell equations".
- `Electromagnetism/ThreeDimension/BoundaryConditions/Planar.lean` — "These declarations state
  local boundary conditions but do not derive them from integral Maxwell equations".

The accurate statement, now in the module doc: the Snell law is derived from the supplied electric
phase-matching predicate together with material dispersion matching and zero attenuation; that
predicate is stipulated, not derived from the integral Maxwell equations, so this is a reduction to
a **stated boundary condition**, not to Maxwell. Maxwell enters only through the half-space
plane-wave solutions. Closing it to Maxwell waits on E4b.

The correction had to be made twice. The first attempt was applied to the two docstrings but not
to the module overview, because the editing script asserted on a later hunk and discarded its
earlier edits before writing — and the result was not re-checked by grep. The review caught the
surviving sentence. The gate run for this commit now greps the file for the phrase explicitly, so
that failure mode is covered rather than trusted.

**Closes:** `goal.md` §H.5 R1 bullet 4. The ledger row GO-02 recorded the paraxial law as
"postulated" in the source with a Physlib target of "stronger — limit or explicit assumption **+ EM
bridge**". The limit and the explicit cubic bound were delivered in R1; the bridge is this lane.
**The GO-02 row must use the corrected wording above** — "the paraxial bound's Snell hypothesis is
discharged against the interface theory's stipulated phase-matching predicate", never "derived from
Maxwell".

**Does not close, and is not claimed:**

1. **A phase direction is not a ray.** The interface theory is explicit that its phase angles assert
   nothing about group velocity, energy flux, or outgoing behaviour. Nothing here upgrades them.
   The correspondence is geometric only.
2. **Non-normal incidence is needed for the *canonical* tangent, not for existence.** Section F
   normalises the tangential projection, which is why it needs that projection nonzero. It is not
   a condition for a meridional plane or a realising ray to exist: at normal incidence every
   tangent realises the incident direction, so the plane is *undetermined*, not absent. An earlier
   version of this note and of the module doc said non-normality was "the condition under which a
   plane of incidence exists at all", which is false and has been corrected.
3. **Curved surfaces are untouched.** The paraxial laws for spherical surfaces remain model laws.
   This bridge covers the *planar* interface only, which is the one E5b models.
4. **No field, power, or polarization** is assigned to a ray anywhere in the ray development.
5. The refraction results are about the interface theory's phase angles. Relating them to a
   `MeridionalRay`'s signed angle in a specific configuration additionally needs the range guard of
   section B, applied per configuration; the fixture shows that being done, the general theorems do
   not assume it silently.
