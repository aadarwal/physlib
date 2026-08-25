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
| R2 ray-transfer components and systems | `Rays.Transfer` (+ `TransferRegression`) | done |
| R3 imaging and cardinal points | `Rays.Imaging` (+ `ImagingRegression`) | done |
| R4 Gaussian beams and the complex ABCD law | `Rays.Gaussian` (+ `GaussianRegression`) | done |
| R5 optical resonators | `Physlib.Optics.Rays.Resonator` | not started |

## Gates run, all four modules

- `lake-lock build` of all four modules — clean, no warnings.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true <each file>` — zero output.
- Batteries declaration linters (all 14, module-scoped over 711 declarations) — passed. Verified
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
public import Physlib.Optics.Rays.Gaussian
public import Physlib.Optics.Rays.GaussianRegression
public import Physlib.Optics.Rays.Imaging
public import Physlib.Optics.Rays.ImagingRegression
public import Physlib.Optics.Rays.Transfer
public import Physlib.Optics.Rays.TransferRegression
```

Note the sort order: `Gaussian` and `Imaging` come before `Transfer`.

## Files added

- `Physlib/Optics/Rays/Basic.lean`
- `Physlib/Optics/Rays/BasicRegression.lean`
- `Physlib/Optics/Rays/Transfer.lean`
- `Physlib/Optics/Rays/TransferRegression.lean`
- `Physlib/Optics/Rays/Imaging.lean`
- `Physlib/Optics/Rays/ImagingRegression.lean`
- `Physlib/Optics/Rays/Gaussian.lean`
- `Physlib/Optics/Rays/GaussianRegression.lean`

## Sync with `optics/development`

`optics/development` was merged into this branch after R4 (merge commit below), bringing the
conductor's post-review changes `2647af48` and `d10f5d32`. Conflicts in `Rays/Basic.lean` and
`Rays/Transfer.lean` were resolved **in the conductor's favour**, as instructed. One non-conflicting
addition of this lane was kept, because it postdates the review and the parity lane asked for it:
`Optics.angleReversal_mul_self`, with its docstring rewritten into the corrected terminology.

What the sync changed on this lane's side:

- **`Optics.composedIsValid_objectImageFrame` gained two hypotheses.** `ComposedIsValid` is now a
  conjunction that includes `ComposedIndicesCompatible`, so the object-image frame now also
  requires `objectGap.index = ParaxialSystem.headIndex cs exitGap` and
  `exitGap.index = imageGap.index`. This is a strengthening in the right direction: object space
  must be the medium the system is entered from and image space the medium it is left into, which
  is exactly what GO-06's explicit index positivity is about. The R3 ledger note stands.
- **`Optics.thickLens_principalDistances` now names `thickLensSystem`** in its `hM` hypothesis,
  instead of spelling out the two-component list. No change in content.
- Nothing in R4 changed. `Rays/Gaussian.lean` and `Rays/GaussianRegression.lean` compiled against
  the new API unchanged.
- The terminology correction landed: the prose no longer calls the thesis convention "unfolded",
  and `unfoldedTransferMatrix` is now `outputAngleReversedTransferMatrix`. This lane's own prose
  in `TransferRegression.lean` was updated to match.
- The lane's centre-of-curvature note lost its "derived by the parity lane, not stated by the
  thesis" provenance in the conductor's rewrite. That provenance belongs in the parity ledger
  rather than in the module doc, and is recorded in the GO-03 row below.

**Registration still needed.** `optics/development` already registers `Rays.Basic`,
`Rays.BasicRegression`, `Rays.Transfer` and `Rays.TransferRegression`. The four modules from R3
and R4 are still unregistered; see the list above.

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

### `Physlib.Optics.Rays.Transfer`

Section A, matrices and their action:

- `Optics.RayTransferMatrix` — `Matrix (Fin 2) (Fin 2) ℝ` in the fixed `![height, angle]`
  ordering.
- `Optics.rayTransfer` with `rayTransfer_height`, `rayTransfer_angle`, `rayTransfer_of_fin_two`,
  `rayTransfer_mul`, `rayTransfer_one`.

Section B, component matrices derived from component laws:

- `Optics.ParaxialGap.transferMatrix`, `.transferMatrix_rayBehavior`,
  `.rayBehavior_iff_transferMatrix`.
- `Optics.ParaxialInterface.transferMatrix`, `.transferMatrix_rayBehavior`,
  `.rayBehavior_iff_transferMatrix`.

Section C, the determinant law:

- `Optics.ParaxialGap.det_transferMatrix`, `Optics.ParaxialInterface.det_transferMatrix`,
  `Optics.ParaxialInterface.det_transferMatrix_phaseConjugate`.

Section D, the unfolded reflection convention:

- `Optics.angleReversal`, `Optics.ParaxialInterface.unfoldedTransferMatrix`,
  `.unfoldedTransferMatrix_planeMirror`, `.unfoldedTransferMatrix_sphericalMirror`,
  `.det_unfoldedTransferMatrix`, and `Optics.rayTransfer_unfoldedTransferMatrix`.

Sections E to G, ordered and composed systems:

- `Optics.ParaxialComponent` — a gap followed by an interface.
- `Optics.ParaxialSystem.headIndex`, `.IsValid`, `.matrix`, `.RayBehavior`, `.headIndex_pos`.
- `Optics.ParaxialSystem.rayBehavior_iff_matrix` — the system ray-transfer theorem.
- `Optics.ParaxialSystem.det_matrix` — the telescoped determinant law.
- `Optics.ParaxialSystem.composedMatrix`, `.ComposedIsValid`, `.ComposedRayBehavior`,
  `.composedRayBehavior_iff_composedMatrix`.

Section H, lenses:

- `Optics.thinLensMatrix`, `Optics.det_thinLensMatrix`.
- `Optics.thickLens_matrix`, `Optics.thinLens_matrix`, `Optics.thinLens_matrix_eq_thinLensMatrix`.

### `Physlib.Optics.Rays.TransferRegression`

`Optics.transferRegressionLens`, `.transferRegressionLens_isValid`, `.transferRegressionFirst`,
`.transferRegressionSecond`, `.transferRegressionExit`, `.transferRegression_isValid`,
`.transferRegression_matrix`, `.transferRegression_matrix_swapped`,
`.transferRegression_order_matters`, `.transferRegression_det_blind_to_order`,
`.transferRegression_ray_order_matters`, `.transferRegressionSymmetricTwoLens`,
`.transferRegressionSymmetricTwoLens_isValid`, `.transferRegression_symmetricTwoLens_matrix`,
`.transferRegression_symmetricTwoLens_symmetric`, `.transferRegression_symmetricTwoLens_det`,
`.transferRegressionTwoFocalLengths`, `.transferRegressionTwoFocalLengths_isValid`,
`.transferRegression_imaging_twoFocalLengths`, `.transferRegression_imaging_twoFocalLengths_ray`,
`.transferRegressionIndexStep`, `.transferRegressionIndexStep_isValid`,
`.transferRegressionIndexStep_matrix`, `.transferRegression_det_indexStep`,
`.transferRegression_det_indexStep_law`, `.transferRegression_unfolded_det`,
`.transferRegression_unfolded_sphericalMirror`, `.transferRegression_matrix_nil`,
`.transferRegression_composedMatrix_nil`, `.transferRegression_thinLens_matched`,
`.transferRegression_thinLens_biconvex`.

### `Physlib.Optics.Rays.Imaging`

Section A, translations and the object-image frame:

- `Optics.translationMatrix` with its four entry lemmas and
  `Optics.translationMatrix_eq_transferMatrix` (a gap matrix does not depend on its index).
- `Optics.shiftedMatrix` with `shiftedMatrix_zero_zero`, `_zero_one`, `_one_zero`, `_one_one` and
  `Optics.det_shiftedMatrix`.
- `Optics.shiftedMatrix_eq_bracketed`, `Optics.composedMatrix_objectImageFrame`,
  `Optics.composedIsValid_objectImageFrame` — the GO-06 object-image frame.

Section B, conjugate planes and magnification:

- `Optics.IsConjugate`, `Optics.isConjugate_iff_entry_zero_one_eq_zero`.
- `Optics.transverseMagnification`, `Optics.angularMagnification`,
  `Optics.height_eq_transverseMagnification_mul`, `Optics.angle_eq_angularMagnification_mul`.
- `Optics.transverseMagnification_mul_angularMagnification` — the Lagrange invariant.

Sections C to E, cardinal points, each as specification, definition, theorem, uniqueness:

- `Optics.effectiveFocalLength`; `Optics.IsBackFocalDistance`, `Optics.backFocalDistance`,
  `Optics.isBackFocalDistance_backFocalDistance`, `Optics.isBackFocalDistance_unique`;
  `Optics.IsFrontFocalDistance`, `Optics.frontFocalDistance`,
  `Optics.isFrontFocalDistance_frontFocalDistance`, `Optics.isFrontFocalDistance_unique`.
- `Optics.ArePrincipalDistances`, `Optics.objectPrincipalDistance`,
  `Optics.imagePrincipalDistance`, `Optics.arePrincipalDistances`,
  `Optics.arePrincipalDistances_unique`.
- `Optics.AreNodalDistances`, `Optics.objectNodalDistance`, `Optics.imageNodalDistance`,
  `Optics.areNodalDistances`, `Optics.areNodalDistances_unique`.
- `Optics.nodal_eq_principal_of_det_eq_one`.

Sections F and G, imaging equations and the thick lens:

- `Optics.newton_imaging_equation`, `Optics.newton_imaging_equation_of_det_eq_one`.
- `Optics.thinLensMatrix_isConjugate_iff`, `Optics.thinLensMatrix_imaging_iff`,
  `Optics.thinLensMatrix_transverseMagnification`, `Optics.thinLensMatrix_focalDistances`,
  `Optics.thinLensMatrix_principalDistances`.
- `Optics.imagePrincipalDistance_eq_effectiveFocalLength_mul`,
  `Optics.objectPrincipalDistance_eq_effectiveFocalLength_mul`,
  `Optics.thickLens_principalDistances`.

### `Physlib.Optics.Rays.ImagingRegression`

`Optics.imagingRegression_thinLensMatrix_entries`, `.imagingRegression_thinLensMatrix_power`,
`.imagingRegression_thinLens_focalDistances`, `.imagingRegression_thinLens_isBackFocalDistance`,
`.imagingRegression_thinLens_not_isBackFocalDistance`,
`.imagingRegression_thinLens_cardinalPoints`,
`.imagingRegression_twoFocalLengths_isConjugate`,
`.imagingRegression_twoFocalLengths_magnification`, `.imagingRegression_newton`,
`.imagingRegression_effectiveFocalLength`, `.imagingRegressionSurface`,
`.imagingRegressionSurface_entries`, `.imagingRegressionSurface_power`,
`.imagingRegressionSurface_det`, `.imagingRegression_sphericalSurface_nodal_at_centre`,
`.imagingRegression_sphericalSurface_nodal_ne_principal`,
`.imagingRegression_sphericalSurface_areNodalDistances`,
`.imagingRegression_objectImageFrame`, `.imagingRegression_objectImageFrame_isValid`.

Added to `Physlib.Optics.Rays.Transfer` for the convention guard:
`Optics.angleReversal_mul_self`. Added to `Physlib.Optics.Rays.TransferRegression`:
`Optics.transferRegressionRoundTrip`, `.transferRegressionRoundTrip_isValid`,
`.transferRegression_roundTrip_matrix`, `.transferRegression_roundTrip_trace`,
`.transferRegression_roundTrip_det`, `.transferRegression_roundTrip_negated_radii`,
`.transferRegression_twoReversals`.

### `Physlib.Optics.Rays.Gaussian`

Section A, the beam parameter:

- `Optics.GaussianBeam` — wavelength and complex beam parameter, with `0 < wavelength` and
  `0 < q.im` as structure fields.
- `Optics.GaussianBeam.q_ne_zero`, `.normSq_q_pos`, `.rayleighRange`, `.rayleighRange_pos`,
  `.waistRadius`, `.waistRadius_pos`, `.rayleighRange_eq`.

Section B, derived beam quantities:

- `Optics.GaussianBeam.beamRadius`, `.beamRadius_pos`, `.wavefrontCurvature`, `.inv_q_eq`,
  `.wavefrontRadius`, `.wavefrontRadius_mul_wavefrontCurvature`.
- `Optics.GaussianBeam.IsAtWaist`, `.beamRadius_of_isAtWaist`, `.wavefrontCurvature_of_isAtWaist`.

Section C, the complex ABCD law:

- `Optics.abcdDenominator`, `Optics.abcdTransform`, with `abcdDenominator_re`,
  `abcdDenominator_im`.
- `Optics.abcdDenominator_ne_zero` — the denominator proof.
- `Optics.im_abcdTransform`, `Optics.im_abcdTransform_pos` — the domain proof.
- `Optics.GaussianBeam.transform` with `transform_wavelength`, `transform_q`, and
  `.beamRadius_transform_of_entries`.

Section D, free propagation and the waist:

- `Optics.det_translationMatrix`, `Optics.det_translationMatrix_pos`,
  `Optics.abcdTransform_translationMatrix`.
- `Optics.GaussianBeam.transform_translationMatrix_q`, `.transform_translationMatrix_wavelength`,
  `.rayleighRange_transform_translationMatrix`, `.waistRadius_transform_translationMatrix`.
- `Optics.GaussianBeam.beamRadius_translation_of_isAtWaist`,
  `.wavefrontRadius_translation_of_isAtWaist`.
- `Optics.GaussianBeam.outputWaistDistance`, `.isAtWaist_transform_outputWaistDistance`,
  `.transform_q_of_isAtWaist`, `.outputWaistDistance_of_isAtWaist`,
  `.waistRadius_sq_transform_of_isAtWaist`, `.waistRadius_sq_at_outputWaist`.

Section E, the paraxial Helmholtz equation:

- `Optics.waistBeamParameter` with `_re`, `_im`, `waistBeamParameter_ne_zero`.
- `Optics.gaussianExponentCoefficient`, `Optics.gaussianExponentCoefficient_eq`,
  `Optics.gaussianAmplitude`, `Optics.gaussianAmplitude_comm`.
- `Optics.SatisfiesParaxialHelmholtz`.
- `Optics.hasDerivAt_gaussianAmplitude_transverse`,
  `Optics.hasDerivAt_deriv_gaussianAmplitude_transverse`,
  `Optics.deriv_deriv_gaussianAmplitude_transverse`,
  `Optics.hasDerivAt_gaussianAmplitude_axial`.
- `Optics.gaussianAmplitude_satisfiesParaxialHelmholtz`.

### `Physlib.Optics.Rays.GaussianRegression`

`Optics.gaussianRegressionBeam`, `.gaussianRegressionBeam_isAtWaist`,
`.gaussianRegressionBeam_rayleighRange`, `.gaussianRegression_beamRadius_at_waist`,
`.gaussianRegression_wavefrontCurvature_at_waist`,
`.gaussianRegression_beamRadius_at_rayleighRange`,
`.gaussianRegression_not_isAtWaist_after_propagation`,
`.gaussianRegression_thinLens_beamRadius`, `.gaussianRegression_denominator_ne_zero`,
`.gaussianRegression_phaseConjugate_leaves_domain`,
`.gaussianRegression_singular_not_isValid`, `.gaussianRegression_singular_would_be_junk`,
`.gaussianRegression_helmholtz`, `.gaussianRegression_waistBeamParameter`.

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

`goal.md` §H.5 R2 has four bullets, all covered:

- *free propagation, refraction, thin/thick lenses, and plane/spherical mirrors* — done. The
  lenses are derived, not stipulated: `thickLens_matrix` and `thinLens_matrix` are system
  matrices of two-surface systems, so the lensmaker's equation is a theorem about the surface
  laws.
- *validity predicates and component matrices* — done, with the matrix proved to be the unique
  realisation of each component's relational law.
- *arbitrary ordered system and matrix fold* — done, `ParaxialSystem.matrix`.
- *component, system, and composed-system ray-transfer theorems* — done,
  `ParaxialInterface.rayBehavior_iff_transferMatrix`, `ParaxialSystem.rayBehavior_iff_matrix`,
  `ParaxialSystem.composedRayBehavior_iff_composedMatrix`.

The `det = n₀ / n₁` law asked for in the lane brief is
`ParaxialInterface.det_transferMatrix`, with the phase-conjugate exception separate, and the
system-level telescoped form is `ParaxialSystem.det_matrix`.

`goal.md` §I.3 regressions: **R-01 is done** — `transferRegression_order_matters` and
`transferRegression_ray_order_matters`. The sentinel is built so that neither the determinant nor
the `A` entry detects the swap (`transferRegression_det_blind_to_order` proves this), so only a
genuine order check catches it. R-02, R-03 and R-04 land in R3, R4 and R5. The §I.3 closing
requirement of "zero/identity limits and parameter-boundary behavior for every named physical
component" is met for the R1 components by section C of `BasicRegression` and for the R2
components by section F of `TransferRegression`.

`goal.md` §H.5 R3 has four bullets:

- *imaging condition and transverse/angular magnification* — done, with the imaging condition
  proved equivalent to its behavioural specification and the Lagrange invariant relating the two
  magnifications to the determinant.
- *principal, nodal, and focal points with nondegeneracy assumptions* — done. Each is
  specification, definition, theorem, uniqueness, and each carries `M 1 0 ≠ 0` explicitly: an
  afocal system has no finite cardinal points and the theorems say nothing about one rather than
  dividing by zero.
- *thin-lens and lens-maker specializations* — done. The lensmaker's equation is R2's
  `thinLens_matrix`; the thin-lens imaging equation, magnification, focal and principal distances
  are `thinLensMatrix_*` here. Newton's equation is proved in general and specialised.
- *a representative ophthalmic or telescope subsystem after source/model review* — **not** done,
  and deliberately. The brief conditions it on a source and model review that has not happened, so
  inventing a fixture would be worse than leaving the row open. GO-12 and GB-07 stay open.

**R-02 is done**: `imagingRegression_thinLens_isBackFocalDistance` is the positive half and
`imagingRegression_thinLens_not_isBackFocalDistance` the negative half, which is what stops the
specification being vacuous. The sharpest fixture is
`imagingRegression_sphericalSurface_nodal_at_centre`: a single spherical refracting surface has
both nodal points at its centre of curvature and both principal points at the vertex, which
separates two notions that coincide for every system in a single medium and checks the distance
sign convention at the same time.

`goal.md` §H.5 R4 has five bullets, four done:

- *wavelength, waist, Rayleigh range, and complex `q` parameter* — done.
- *physically valid domain and free-propagation law* — done. The domain is a field of
  `GaussianBeam`, not a side condition, and `im_abcdTransform_pos` proves it is preserved.
- *Gaussian solution of the paraxial wave/Helmholtz equation* — done, for the transverse-Laplacian
  form with the `exp (- i k z)` carrier, stated explicitly in `SatisfiesParaxialHelmholtz`. The
  parity lane has since confirmed this **matches the source exactly** (Defs. 4.3–4.5, Eq. 4.4), so
  GB-02 is parity and needs no convention-mapping row. One typing divergence is recorded in the
  module doc and runs *against* this development: the source quantifies its verification over
  complex `x`, `y`, `z`, an artifact of its complex-differentiation tactic, so it asserts strictly
  more instances than the real-coordinate statement here.
- *ABCD transformation with denominator and domain proofs* — done, and in the strong form: the
  denominator condition is **proved**, not assumed. See the ledger note on GB-04 below.
- *output waist and location formulas* — done, `outputWaistDistance_of_isAtWaist` and
  `waistRadius_sq_at_outputWaist`.

**R-03 is done**, both halves on the same beam: `gaussianRegression_helmholtz` is the wave-equation
half and the propagation, thin-lens, denominator, and domain lemmas are the ABCD half. Two
sentinels are about hypotheses rather than values:
`gaussianRegression_phaseConjugate_leaves_domain` shows the positive-determinant hypothesis is
necessary — the phase-conjugating mirror carries a physical beam parameter out of the domain — and
`gaussianRegression_singular_not_isValid` with `gaussianRegression_singular_would_be_junk` shows
the singular matrix is rejected by validity and exactly what would go wrong without that.

Of the three regressions named in the lane brief, the **symmetric two-lens system** is done here
(`transferRegression_symmetricTwoLens_matrix` with its `A = D` symmetry and unit determinant),
and the **thin-lens `2f` configuration** has its matrix here
(`transferRegression_imaging_twoFocalLengths`, `B = 0` and `A = -1`) with the imaging reading due
in R3. The **confocal cavity** is R5.

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

**GO-03** (Thesis'15 Thms. 3.4–3.5 p. 46 + Table 3.1 p. 47) — satisfied.
Lean: `Optics.ParaxialGap.transferMatrix`, `Optics.ParaxialInterface.transferMatrix`, with
`rayBehavior_iff_transferMatrix` for each. Hypotheses `0 < n₀`, `0 < n₁` and interface validity
retained. Matrices are Saleh and Teich table 1.4-1 in the folded reflection convention; the map to
the unfolded convention the source uses is `Optics.ParaxialInterface.unfoldedTransferMatrix`, with
`unfoldedTransferMatrix_planeMirror` and `unfoldedTransferMatrix_sphericalMirror` giving the
explicit entries. **Entry-by-entry comparison with Table 3.1 additionally needs that table's
radius-sign convention, which is a human-audit item and is not asserted here.**
Class: **parity**, with a documented convention map.

**GO-04** (Thesis'15 Def. 3.9 p. 48 + Thm. 3.6 p. 49) — satisfied, regression **R-01** done.
Lean: `Optics.ParaxialSystem.matrix` and `Optics.ParaxialSystem.rayBehavior_iff_matrix`.
The source's reverse fold order is reproduced: later components multiply on the left. Hypotheses
`is_valid_optical_system` and `is_valid_ray_in_system` correspond to `ParaxialSystem.IsValid` and
`ParaxialSystem.RayBehavior`.
Class: **parity**.

**GO-05** (Thesis'15 Defs. 3.10–3.12 pp. 49–50 + Thm. 3.7 p. 51) — satisfied.
Lean: `Optics.ParaxialSystem.composedMatrix`, `.ComposedIsValid`, `.ComposedRayBehavior`,
`.composedRayBehavior_iff_composedMatrix`, with the same `composed_system (sys :: cs) =
composed_system cs ** system_composition sys` fold order.
Class: **parity**.

**GO-06** (Thesis'15 Def. 3.13 + Thm. 3.8 pp. 53–54) — satisfied, after the parity lane's reading
of the thesis resolved what the row contains. It is a *specialisation*, not new generality: the
three-element composed system `[free space (nᵢ, d₀); sys; free space (n_t, dₙ)]`.
Lean: `Optics.composedMatrix_objectImageFrame` builds it as an instance of
`ParaxialSystem.composedMatrix` and proves its matrix is `Optics.shiftedMatrix`;
`Optics.composedIsValid_objectImageFrame` carries the validity, including the positivity of the
two bracketing indices that Thm. 3.8 states explicitly. The source's closed form
`[[A + C dₙ, A d₀ + B + C d₀ dₙ + D dₙ], [C, C d₀ + D]]` is
`Optics.shiftedMatrix_zero_zero`, `_zero_one`, `_one_zero`, `_one_one` entry for entry. The
imaging condition as the vanishing upper-right entry is
`Optics.isConjugate_iff_entry_zero_one_eq_zero`.
Class: **parity**.

**GO-07 to GO-10** (Thesis'15 Def. 3.14 p. 54, Defs. 3.15–3.20 and Thms. 3.9–3.11 pp. 55–59) —
satisfied, regression **R-02** done. Lean: `Optics.transverseMagnification`,
`Optics.angularMagnification`, and the three specification-definition-theorem-uniqueness groups
for focal, principal, and nodal distances. The source's three-step pattern is reproduced and
extended with uniqueness, which the source does not state. The nondegeneracy hypothesis
`M 1 0 ≠ 0` is explicit throughout.
Class: **parity**, strengthened by the uniqueness results.

**GO-11 second half** (Thesis'15 Thm. 3.12 pp. 59–60) — satisfied.
Lean: `Optics.thickLens_principalDistances`. Table 3.2 (principal points of common components) is
covered only for the thin lens (`Optics.thinLensMatrix_principalDistances`) and the single
spherical surface (`Optics.imagingRegression_sphericalSurface_nodal_at_centre`); the rest of that
table is not claimed.

**GO-12** (Thesis'15 Def. 3.22 + Thm. 3.13 p. 63, myopia corrective setup) — **not** addressed.
`goal.md` §R3 conditions this case study on a source and model review that has not happened.
Not claimed.

**GO-11** (Thesis'15 Def. 3.21 + Thm. 3.12 pp. 59–60) — half satisfied. The thick-lens **matrix**
is `Optics.thickLens_matrix`, derived from two spherical surfaces separated by a gap rather than
stipulated, so its lower-left entry is a proved lensmaker's equation with thickness. The thick
lens's **principal points** (Thm. 3.12) and Table 3.2 are R3 work.

**A Physlib addition with no source row.** `Optics.ParaxialSystem.det_matrix` proves the system
determinant telescopes to `headIndex / exitGap.index` under an explicit no-phase-conjugation
hypothesis. The source states component matrices and uses `det M = 1` for resonators; it does not
state the general index-ratio law. Class: **stronger Physlib theorem**.

**GO-03 convention, resolved by the parity lane (2026-08-25).** The parity lane's reading of
Table 3.1 p. 47 and Def. 3.7 case C4 p. 44 confirms the thesis's spherical mirror is
`!![1, 0; -2/R, 1]`, with `D = +1` and `det = +1`. That is the **folded** matrix this lane uses,
so `Optics.ParaxialInterface.transferMatrix` agrees with the source entry for entry for the
mirrors, and the refracting entry `(n₀ - n₁) / (n₁ R)` agrees as well. The centre-of-curvature
rule (positive `R` when the centre lies on the outgoing side) is **derived** by the parity lane
from those entries; the thesis never states it. It is recorded as derived in the
`Physlib.Optics.Rays.Basic` module documentation.

`Optics.ParaxialInterface.unfoldedTransferMatrix` is therefore not a correction but a second,
explicit-reversal bookkeeping: it equals the thesis matrix post-composed with `diag (1, -1)`.
Identical physics, opposite bookkeeping. The factorisation is what is stated; entry-by-entry
equality with a thesis table entry is **not** claimed for the unfolded form.

**The double-counting guard, added at the parity lane's request.** The thesis does two
compensating things: `det = +1` mirrors *and* negating `R` on unfolding (`sign_cor_interface`,
p. 97). A treatment that keeps the reversal explicit, as this one does, must not also negate the
radii, or the reversal is counted twice — and a single-mirror check cannot see it.
`Optics.transferRegression_roundTrip_trace` proves the two-mirror round-trip trace is
`4 g₁ g₂ - 2` with `gᵢ = 1 - d / Rᵢ`, and
`Optics.transferRegression_roundTrip_negated_radii` shows that for `d = 1`, `R₁ = R₂ = 2` the
correct trace is `-1`, inside the stable band, while the doubly-counted convention gives `7`,
outside it. `Optics.angleReversal_mul_self` records that an even number of explicit reversals is
the identity.

**Knock-on for R5, from the parity lane.** Thesis Thm. 5.7's stability criterion assumes
`det M = 1`. In the folded convention used here mirrors have `det = n₀ / n₁ = 1`, so the
criterion applies directly; `Optics.transferRegression_roundTrip_det` proves the round trip has
unit determinant. The unfolded `det = -1` form satisfies the hypothesis only for an even number
of reversals. This will be stated explicitly in R5.

**GB-01 to GB-03** (Thesis'15 Defs. 4.1–4.7, Thms. 4.1–4.4, Lemmas 1–2, pp. 68–74) — satisfied
except for beam intensity. Lean: `Optics.GaussianBeam` and its derived quantities;
`Optics.gaussianAmplitude_satisfiesParaxialHelmholtz` is Thm. 4.2. Beam intensity (Def. 4.7,
Thm. 4.4) is **not** formalised: this lane assigns no power or irradiance to a beam. The source's
`z ≠ 0` side condition on the wavefront radius is reproduced as `q.re ≠ 0` on
`Optics.GaussianBeam.wavefrontRadius_mul_wavefrontCurvature`; the curvature itself needs no side
condition and is the primitive here.

**GB-04** (Thesis'15 Defs. 4.8–4.10 + Thms. 4.5–4.7, pp. 76–79) — satisfied, and **stronger than
the row previously recorded**. The parity lane has corrected its own earlier note: the source's
omission of `C q + D ≠ 0` is sound rather than sloppy, because the condition is derivable from
`0 < Im q` plus matrix nondegeneracy. This lane derives it, in
`Optics.abcdDenominator_ne_zero`, rather than assuming it, which is what `goal.md` §R4's
"denominator and domain proofs" asks for. `Optics.im_abcdTransform_pos` is the domain half.
Class: **parity, strengthened** — the hypothesis is discharged, not added.

**A gap in the source closed here.** The source's free-form interface constructor is
unconditionally valid, so it admits a singular matrix, and with a total division the ABCD law
would then assert `q' = 0`. `ParaxialInterface.prescribed` carries the index-ratio determinant
condition, so the singular case is rejected; `Optics.gaussianRegression_singular_not_isValid` and
`Optics.gaussianRegression_singular_would_be_junk` exhibit both halves. The parity lane records
that whether the source's beam predicate admits that constructor at all is **UNVERIFIED** from
the thesis text, so this is recorded as a Physlib improvement rather than as a defect found in the
source.

**A hypothesis-placement divergence the ledger must record.** The source embeds its positivity
conditions inside its beam predicates (Defs. 4.9–4.10). This lane puts them in the fields of
`Optics.GaussianBeam`. The two are therefore **not statement-for-statement comparable**: theorems
here carry fewer explicit hypotheses because the structure carries them. This is a deliberate
choice, flagged at the parity lane's request.

**GB-05 and GB-06** (Thesis'15 Def. 4.11 + Thms. 4.8–4.10, pp. 84–86) — satisfied. The
quasi-optical frame is `Optics.shiftedMatrix` from R3, already proved to be the composed system
bracketed by free space. Thm. 4.10's `[H4]` is, in real terms, exactly `C q + D ≠ 0` at the waist,
which is discharged here rather than assumed. **Thm. 4.10 constrains the beam to be at its waist
at both ends**; this lane keeps the input-waist hypothesis and *derives* the output waist
(`isAtWaist_transform_outputWaistDistance`), so `Optics.GaussianBeam.waistRadius_sq_at_outputWaist`
is strictly stronger than the source statement. Neither restriction is dropped silently.

**GB-07** (Thesis'15 Def. 4.13 + Thm. 4.13, APEX telescope) — **not** addressed. The source's
hypotheses sit in an opaque `SHeFI_constraints` bundle that the thesis never unfolds, so a parity
claim here would not be auditable. Not claimed, per the parity lane's recommendation.

**Convention divergence to record.** This lane uses the Saleh & Teich folded reflection
convention: after a mirror the axis is re-referenced to the new propagation direction, so a plane
mirror acts as the identity on `(height, angle)` and a mirror does not change the refractive
index. The source (Thesis'15 Def. 3.7 case C2) uses the unfolded convention, in which a plane
mirror sends `θ` to `-θ`. The two differ by one angle reversal. The folded convention was chosen
because it makes `det M = n₀ / n₁` hold uniformly across the refracting and reflecting components
and because it is the convention in which the two-mirror stability condition `0 ≤ g₁ g₂ ≤ 1` is
stated. The bridge lemma is `Optics.ParaxialInterface.unfoldedTransferMatrix` with its two entry
lemmas and `Optics.rayTransfer_unfoldedTransferMatrix`, which states that the unfolded action is
the folded one with the outgoing angle reversed. Approved by the controller on 2026-08-25.

Superseded in part by the GO-03 resolution above: the parity lane's thesis reading shows the
**folded** convention is the source's own, so the folded matrices are the parity match and the
unfolded form is an additional explicit-reversal bookkeeping rather than a correction.

**Determinant-law exception to record.** `phaseConjugate` has determinant `-1`, not `n₀ / n₁`.
Phase conjugation reverses the wavefront and is not an ordinary ray-transfer operation.
`Optics.ParaxialInterface.det_transferMatrix` carries the hypothesis `i ≠ phaseConjugate` and
`Optics.ParaxialInterface.det_transferMatrix_phaseConjugate` states the exceptional value, rather
than weakening the law to `|det| = n₀ / n₁`. Approved by the controller on 2026-08-25.

---

## Open items and explicit non-claims

1. **No ray-to-field bridge.** Nothing here connects a ray to `Physlib.Optics.Polarization` or to
   `Physlib.Electromagnetism`. A ray carries a position and a direction and no field, irradiance,
   power or polarization.
2. **No exact geometry for curved surfaces.** The spherical refracting and reflecting laws are
   paraxial *model* laws. The small-angle bridge is proved for plane refraction and free-space
   transport only. Deriving the curved-surface laws from an exact surface geometry is open.
3. **`goal.md` §H.5 R1 bullet 4 is owned elsewhere.** Relating the paraxial angle to E5b's exact
   geometric directions needs `Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry`, which
   this branch may not import under its layering rule. Per the controller's decision of
   2026-08-25 the bridge module is assigned to the conductor after this lane merges. The ray-side
   objects it needs are gathered in section F of `Rays/Basic.lean` under
   `Optics.MeridionalRay.incidenceAngle`, with `Optics.surfaceNormal` and
   `Optics.MeridionalRay.cos_incidenceAngle`; the docstring names the target module and flags the
   angle-sign map as the first thing the bridge must fix.
5. **GO-06 is not claimed.** See the ledger note above: closing it needs the thesis text.
6. **No diffraction, aperture, or finite-beam content.** A system that is geometrically well
   behaved under these matrices may still be unusable physically.
4. Observation, not a request: `module_doc_lint`'s template is exact, and several already-merged
   files under `Physlib/Optics/Network/` use different section-4 headings while not appearing in
   `scripts/MetaPrograms/module_doc_no_lint.txt`. R-lane files use the strict template.
