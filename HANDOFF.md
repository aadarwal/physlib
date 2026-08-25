# R lane handoff — geometrical optics (rays, ABCD, imaging, Gaussian beams, resonators)

Branch: `optics/r-ray-optics` (off `optics/development`).
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-r-ray-optics`.
Home: `Physlib/Optics/Rays/`. Imports only Mathlib and `Physlib.Optics.Basic`; nothing from
`Polarization/`, `Components/`, `Interfaces/`, `Network/`, or `Electromagnetism/`.

The conductor owns `optics/development`, `Physlib.lean`, `API-map.yaml`, `goal.md` and `tbd.md`.
This lane edits none of them; the registrations it needs are listed below.

---

## Status

| Slice | Module | State |
|---|---|---|
| R1 physical and paraxial rays | `Physlib.Optics.Rays.Basic` (+ `BasicRegression`) | done |
| R2 ray-transfer components and systems | `Physlib.Optics.Rays.Transfer` | not started |
| R3 imaging and cardinal points | `Physlib.Optics.Rays.Imaging` | not started |
| R4 Gaussian beams and the complex ABCD law | `Physlib.Optics.Rays.Gaussian` | not started |
| R5 optical resonators | `Physlib.Optics.Rays.Resonator` | not started |

## Gates run for R1

- `lake-lock build Physlib.Optics.Rays.Basic Physlib.Optics.Rays.BasicRegression` — clean, no
  warnings.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true <each file>` — zero output.
- Batteries declaration linters (all 14, module-scoped over 198 declarations) — passed. Verified
  to have teeth with a deliberately undocumented `def`, which the run rejected.
- `module_doc_lint` and `style_lint` rules, plus the `regex_lint` unneeded-parentheses rule,
  reimplemented as text checks and run over both files — clean. Validated against
  `Physlib/Optics/Systems/PolarizerRetarder.lean` (clean) and
  `Physlib/Optics/Network/TwoPortChain.lean` (correctly reported).
- No `sorry`, `axiom`, `native_decide`, `nolint`, or `set_option maxHeartbeats`.

The shipped `runPhyslibLinters`, `module_doc_lint` and `style_lint` executables read their target
list from the built `Physlib` olean, so they cannot see a module that is not yet in
`Physlib.lean`. Running them over the whole registry stays a merge-time gate on the integration
branch.

---

## Registrations needed in `Physlib.lean`

Insert in sorted position (they sort between `Physlib.Optics.Polarization.*` and
`Physlib.Optics.Systems.*`):

```
public import Physlib.Optics.Rays.Basic
public import Physlib.Optics.Rays.BasicRegression
```

## Files added

- `Physlib/Optics/Rays/Basic.lean` (569 lines)
- `Physlib/Optics/Rays/BasicRegression.lean` (218 lines)

---

## Declarations added by R1

### `Physlib.Optics.Rays.Basic`

Section A, paraxial ray coordinates:

- `Optics.ParaxialRay` — structure, the reduced meridional coordinate `(height, angle)`.
- `Optics.ParaxialRay.toVec`, `.ofVec`, `.vecEquiv` — the `![height, angle]` column-vector view
  that every ray-transfer matrix will act on.
- `Optics.ParaxialRay.toVec_zero`, `.toVec_one`, `.ofVec_height`, `.ofVec_angle`,
  `.ofVec_toVec`, `.toVec_ofVec` — simp lemmas.

Section B, meridional physical rays:

- `Optics.MeridionalRay` — structure, a physical ray in a meridional plane: base point plus
  signed angle to the axis.
- `Optics.MeridionalRay.direction`, `.basePoint`, `.transport`, `.toParaxial`.
- `Optics.MeridionalRay.norm_direction` — the propagation direction is a unit vector.
- `Optics.MeridionalRay.basePoint_transport` — exact transport moves the base point along the
  unit direction by arclength `d / cos angle`.
- simp lemmas `.direction_zero`, `.direction_one`, `.basePoint_zero`, `.basePoint_one`,
  `.transport_angle`, `.transport_height`, `.transport_axialPosition`, `.toParaxial_height`,
  `.toParaxial_angle`.

Section C, homogeneous gaps:

- `Optics.ParaxialGap` — structure `(index, length)`; the ray-optical free-space section. Named
  to avoid `Physlib.Electromagnetism.Dynamics.Basic.FreeSpace`, which is already taken.
- `Optics.ParaxialGap.IsValid` — `0 < index` and `0 ≤ length`.
- `Optics.ParaxialGap.transport`, `.RayBehavior`.
- `Optics.ParaxialGap.rayBehavior_iff_eq_transport`, `.exists_rayBehavior`,
  `.rayBehavior_unique` — the relational law is exactly the graph of the transport map.
- simp lemmas `.transport_height`, `.transport_angle`.

Section D, interfaces:

- `Optics.ParaxialInterface` — inductive with six constructors: `planeRefracting`,
  `sphericalRefracting`, `planeMirror`, `sphericalMirror`, `phaseConjugate`, `prescribed`.
- `Optics.ParaxialInterface.IsValid`, `.RayBehavior`.
- `Optics.ParaxialInterface.index_pos_left`, `.index_pos_right`.
- `Optics.ParaxialInterface.exists_rayBehavior`, `.rayBehavior_unique` — a valid interface has a
  well-defined action on ray coordinates. R2 realises that action as a matrix rather than
  assuming one.

Section E, the paraxial regime:

- `Optics.tendsto_tan_sub_self_div` — `(tan θ - θ) / θ → 0` on the punctured neighbourhood of `0`.
- `Optics.abs_paraxialSnell_sub_le` — exact Snell implies paraxial Snell up to
  `(n₀ |θ₀|³ + n₁ |θ₁|³) / 6`.
- `Optics.exactRefractionAngle`, `Optics.sin_exactRefractionAngle` — the exactly refracted angle
  and the Snell law it satisfies away from total internal reflection.
- `Optics.tendsto_exactRefractionAngle_div` — the exact angle ratio tends to `n₀ / n₁` on the
  axis, which is the paraxial law.
- `Optics.ParaxialGap.tendsto_transport_height_error` — the paraxial gap law reproduces exact
  rectilinear transport to first order in the ray angle.

### `Physlib.Optics.Rays.BasicRegression`

`Optics.raysBasicRegressionGap`, `.raysBasicRegressionGap_isValid`,
`Optics.raysBasicRegressionRay`, `Optics.raysBasicRegression_transport`,
`.raysBasicRegression_transport_rayBehavior`, `.raysBasicRegression_planeRefracting`,
`.raysBasicRegression_planeRefracting_isValid`, `.raysBasicRegression_planeRefracting_unique`,
`.raysBasicRegression_sphericalRefracting_converging`,
`.raysBasicRegression_sphericalRefracting_angle_neg`,
`.raysBasicRegression_sphericalMirror_focal`,
`.raysBasicRegression_phaseConjugate_ne_planeMirror`,
`.raysBasicRegression_prescribed_isValid`, `.raysBasicRegression_prescribed_not_isValid`,
`.raysBasicRegression_transport_length_zero`, `.raysBasicRegression_planeRefracting_matched`,
`.raysBasicRegression_sphericalRefracting_matched`,
`.raysBasicRegression_exactRefractionAngle_matched`,
`.raysBasicRegression_paraxial_height_lt_exact`, `.raysBasicRegression_snellBound`.

---

## goal.md milestone rows satisfied

`goal.md` §H.5 R1 has four bullets. R1 as delivered covers:

- *physical ray, oriented interface incidence, reflection, and refraction* — partial.
  `MeridionalRay` supplies the physical ray with a unit direction and exact rectilinear
  transport. Refraction is covered exactly at a plane surface by `exactRefractionAngle` and
  `sin_exactRefractionAngle`. Exact incidence and reflection at a general **oriented** interface
  are **not** covered; that geometry is E5b's and sits in the `Interfaces/` lane this branch may
  not import. Flagged as an open bridge below.
- *paraxial ray coordinate with the approximation stated as a model assumption or a proved
  limit* — done, and done in the stronger of the two forms. The paraxial laws are stated as model
  laws, and section E additionally proves the limit and an explicit cubic error bound.
- *free-space and plane/spherical-interface behavior* — done at the behavior level
  (`ParaxialGap.RayBehavior`, `ParaxialInterface.RayBehavior`, existence and uniqueness). The
  matrices are R2's.
- *relationship to E5b's exact geometric directions* — **not** done. See open items.

`goal.md` §I.3 regressions: none of R-01 to R-04 is an R1 row; they land in R2 (R-01), R3 (R-02),
R4 (R-03) and R5 (R-04). The §I.3 closing requirement of "zero/identity limits and
parameter-boundary behavior for every named physical component" is met for the R1 components by
section C of `BasicRegression`.

---

## Parity-ledger input (`~/src/aadarwal/physlib-parity/PARITY-LEDGER.md` §3)

Proposed updates. The human audit owns the final wording; these are the facts.

**GO-01** (Thesis'15 Defs. 3.1–3.5 pp. 41–42) — partially satisfied.
Lean: `Optics.ParaxialGap`, `Optics.ParaxialGap.IsValid`, `Optics.ParaxialInterface`,
`Optics.ParaxialInterface.IsValid`, in `Physlib.Optics.Rays.Basic`.
Valid free space `0 < n ∧ 0 ≤ d` retained exactly. All six interface constructors present;
spherical constructors require a nonzero radius as in the source. Valid *component*, valid
*system* and `head_index` are R2, not yet done, so the row is not yet closed.
Class: **parity**, with one strengthening — the source's `unknown a b c d` escape hatch is
`prescribed a b c d` here and its validity predicate additionally requires
`a * d - b * c = n₀ / n₁`, which the source does not impose.

**GO-02** (Thesis'15 Def. 3.6 p. 43 and Def. 3.7 p. 44) — satisfied, and strengthened.
Lean: `Optics.ParaxialGap.RayBehavior`, `Optics.ParaxialInterface.RayBehavior`, plus
`exists_rayBehavior` and `rayBehavior_unique` for both.
The source postulates the paraxial law and lists deriving it as future work (Thesis'15
pp. 124–125). This lane states it as a model law **and** proves the small-angle bridge:
`Optics.abs_paraxialSnell_sub_le` (explicit cubic error), `Optics.tendsto_exactRefractionAngle_div`
(the exact angle ratio has the paraxial ratio as its limit) and
`Optics.ParaxialGap.tendsto_transport_height_error` (the paraxial free-space law is exact to first
order). Regression `Optics.raysBasicRegression_paraxial_height_lt_exact` fixes the sign of the
error.
Class: **parity of coverage, Physlib stronger** — exactly the target the ledger already records
for this row, for the planar-refraction and free-space cases. The bridge for *curved* surfaces is
**not** proved and is not claimed.

**Convention divergence to record.** This lane uses the Saleh & Teich folded reflection
convention: after a mirror the axis is re-referenced to the new propagation direction, so a plane
mirror acts as the identity on `(height, angle)` and a mirror does not change the refractive
index. The source (Thesis'15 Def. 3.7 case C2) uses the unfolded convention, in which a plane
mirror sends `θ` to `-θ`. The two differ by one angle reversal. The folded convention was chosen
because it makes `det M = n₀ / n₁` hold uniformly across the refracting and reflecting components
and because it is the convention in which the two-mirror stability condition `0 ≤ g₁ g₂ ≤ 1` is
stated; R2 will carry an explicit bridge lemma to the unfolded form so the GO-03 row can be
matched entry by entry rather than up to an undocumented sign.

**Determinant-law exception to record.** `phaseConjugate` has determinant `-1`, not `n₀ / n₁`.
Phase conjugation reverses the wavefront and is not an ordinary ray-transfer operation. R2 will
state the index-ratio determinant law for the other five constructors and state the
phase-conjugate value separately, rather than weakening the law to `|det| = n₀ / n₁`.

---

## Open items and explicit non-claims

1. **No ray-to-field bridge.** Nothing here connects a ray to `Physlib.Optics.Polarization` or to
   `Physlib.Electromagnetism`. A ray carries a position and a direction and no field, irradiance,
   power or polarization.
2. **No exact geometry for curved surfaces.** The spherical refracting and reflecting laws are
   paraxial *model* laws. The small-angle bridge is proved for plane refraction and free-space
   transport only. Deriving the curved-surface laws from an exact surface geometry is open.
3. **`goal.md` §H.5 R1 bullet 4 is not addressed.** Relating the paraxial angle to E5b's exact
   geometric directions needs `Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry`, which
   this branch may not import under its layering rule. This is a genuine cross-lane bridge and
   needs a decision by the conductor about which module owns it. Recorded, not silently dropped.
4. Observation, not a request: `module_doc_lint`'s template is exact, and several already-merged
   files under `Physlib/Optics/Network/` use different section-4 headings while not appearing in
   `scripts/MetaPrograms/module_doc_no_lint.txt`. R-lane files use the strict template.
