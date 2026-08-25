/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Gaussian

/-!
# Optical resonators and their stability

## i. Overview

Stability here is what the source makes it: a statement that the ray stays bounded under
arbitrarily many round trips, with the bounds chosen before the number of round trips. It is not a
trace inequality. The trace inequality is a *criterion*, and
`Optics.isStable_of_abs_trace_lt_two` is the theorem that it implies boundedness.

The proof is by a conserved quantity rather than by diagonalisation. A unimodular ray-transfer
matrix preserves the quadratic form `C y² + (D - A) y θ - B θ²` exactly, and
`Optics.rayInvariant_rayTransfer` proves the general version of this: the form is multiplied by
the determinant. When the trace is subcritical that form is definite, and
`Optics.stabilityForm_eq` rewrites it as a sum of two squares with positive coefficients whose
value is conserved. Both ray coordinates are then bounded by it directly.

Strict versus non-strict, stated precisely. The theorem is `|A + D| < 2`, strictly. At
`|A + D| = 2` the criterion decides nothing, and both outcomes occur: the confocal cavity has
round-trip matrix exactly `-1` and is stable, while the plane-parallel cavity is a shear and is
not. Both are exhibited in `Physlib.Optics.Rays.ResonatorRegression`. So the familiar
`0 ≤ g₁ g₂ ≤ 1` is the closure of the stable region, and the theorem proved here covers its
interior `0 < g₁ g₂ < 1`; the endpoints must be decided one at a time, and this file does not
claim them in general.

Reflection bookkeeping. The round trips here are built in the folded convention of
`Physlib.Optics.Rays.Basic`, which the parity lane confirms is the source's own. The direction
reversal at a mirror is therefore already inside the mirror matrix, and the radii are **not**
negated on the reversed leg: doing both would count the same reversal twice.
`Optics.resonatorRegression_negated_radii_not_isStable` makes that load-bearing,
by showing the doubly-counted convention turns a stable cavity into an unstable one. Because the
folded mirrors have determinant `1`, the determinant hypothesis of the stability theorem is met
directly.

Explicit non-claims. There is no field, power, loss, gain, or mode-volume content here, and no
diffraction: a resonator that is stable in this sense confines rays, which is not the same as
supporting a low-loss mode. Nothing is claimed about resonance frequencies or longitudinal modes.

## ii. Key results

- `Optics.IsStable`: stability as boundedness of the ray under arbitrarily many round trips.
- `Optics.rayInvariant_rayTransfer`: the conserved quadratic form, up to the determinant.
- `Optics.isStable_of_abs_trace_lt_two`: the trace criterion implies stability.
- `Optics.twoMirror_trace`: the two-mirror round-trip trace is `4 g₁ g₂ - 2`.
- `Optics.isStable_twoMirror`: a two-mirror cavity with `0 < g₁ g₂ < 1` is stable.
- `Optics.exists_gaussian_eigenmode`: a subcritical resonator has a Gaussian eigenmode, whose
  beam parameter is a root of the same quadratic that the ray invariant is built from.

## iii. Table of contents

- A. Stability as boundedness
- B. The conserved quadratic form
- C. The trace criterion
- D. Two-mirror resonators
- E. Gaussian eigenmodes

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 10, for the
  resonator stability condition and the `g` parameters.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 5, definition 5.5 and theorems 5.6 to 5.7, for the
  boundedness definition of stability and the trace criterion.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real

/-!

## A. Stability as boundedness

-/

/-- The ray coordinate after `n` round trips of a resonator whose round-trip matrix is `M`. -/
def roundTripRay (M : RayTransferMatrix) (r : ParaxialRay) (n : ℕ) : ParaxialRay :=
  rayTransfer (M ^ n) r

@[simp]
lemma roundTripRay_zero (M : RayTransferMatrix) (r : ParaxialRay) : roundTripRay M r 0 = r := by
  rw [roundTripRay, pow_zero, rayTransfer_one]

lemma roundTripRay_succ (M : RayTransferMatrix) (r : ParaxialRay) (n : ℕ) :
    roundTripRay M r (n + 1) = rayTransfer M (roundTripRay M r n) := by
  rw [roundTripRay, roundTripRay, pow_succ', rayTransfer_mul]

/-- **Stability of a resonator**, in the source's sense: for every incoming ray there are bounds,
chosen in advance, that the height and the angle never exceed however many round trips the ray
makes.

This is a statement about the ray, not about the matrix. The trace criterion of section C is a
sufficient condition for it, and is not the definition.
-/
def IsStable (M : RayTransferMatrix) : Prop :=
  ∀ r : ParaxialRay, ∃ heightBound angleBound : ℝ, ∀ n : ℕ,
    |(roundTripRay M r n).height| ≤ heightBound ∧
      |(roundTripRay M r n).angle| ≤ angleBound

/-!

## B. The conserved quadratic form

-/

/-- The quadratic form in the ray coordinates that a ray-transfer matrix scales by its
determinant. -/
def rayInvariant (M : RayTransferMatrix) (r : ParaxialRay) : ℝ :=
  M 1 0 * r.height ^ 2 + (M 1 1 - M 0 0) * r.height * r.angle - M 0 1 * r.angle ^ 2

/-- **The ray invariant is scaled by the determinant.**

No hypothesis is needed: this is an identity. For a unimodular matrix, which is what a resonator
round trip is, the form is conserved exactly.
-/
lemma rayInvariant_rayTransfer (M : RayTransferMatrix) (r : ParaxialRay) :
    rayInvariant M (rayTransfer M r) = M.det * rayInvariant M r := by
  rw [rayInvariant, rayInvariant, Matrix.det_fin_two, rayTransfer_height, rayTransfer_angle]
  ring

/-- For a unimodular matrix the ray invariant is conserved under every number of round trips. -/
lemma rayInvariant_roundTripRay (M : RayTransferMatrix) (hdet : M.det = 1) (r : ParaxialRay)
    (n : ℕ) : rayInvariant M (roundTripRay M r n) = rayInvariant M r := by
  induction n with
  | zero => rw [roundTripRay_zero]
  | succ n ih => rw [roundTripRay_succ, rayInvariant_rayTransfer, hdet, one_mul, ih]

/-- The trace of a ray-transfer matrix. -/
def rayTrace (M : RayTransferMatrix) : ℝ := M 0 0 + M 1 1

/-- The combination of the ray coordinates that the invariant controls: a sum of two squares
whose second coefficient is positive exactly when the trace is subcritical. -/
def stabilityForm (M : RayTransferMatrix) (r : ParaxialRay) : ℝ :=
  (2 * M 1 0 * r.height + (M 1 1 - M 0 0) * r.angle) ^ 2 +
    (4 - rayTrace M ^ 2) * r.angle ^ 2

/-- For a unimodular matrix the stability form is four times `C` times the ray invariant. -/
lemma stabilityForm_eq (M : RayTransferMatrix) (hdet : M.det = 1) (r : ParaxialRay) :
    stabilityForm M r = 4 * M 1 0 * rayInvariant M r := by
  rw [stabilityForm, rayInvariant, rayTrace, Matrix.det_fin_two] at *
  linear_combination (-4 * r.angle ^ 2) * hdet

/-- For a unimodular matrix the stability form is conserved under every number of round trips. -/
lemma stabilityForm_roundTripRay (M : RayTransferMatrix) (hdet : M.det = 1) (r : ParaxialRay)
    (n : ℕ) : stabilityForm M (roundTripRay M r n) = stabilityForm M r := by
  rw [stabilityForm_eq M hdet, stabilityForm_eq M hdet, rayInvariant_roundTripRay M hdet]

/-- The stability form is nonnegative when the trace is subcritical, being a sum of two
nonnegative terms. -/
lemma stabilityForm_nonneg (M : RayTransferMatrix) (htr : |rayTrace M| < 2) (r : ParaxialRay) :
    0 ≤ stabilityForm M r := by
  have h4 : 0 < 4 - rayTrace M ^ 2 := by
    have := abs_lt.mp htr
    nlinarith [this.1, this.2]
  have hsq : (0 : ℝ) ≤ (2 * M 1 0 * r.height + (M 1 1 - M 0 0) * r.angle) ^ 2 := sq_nonneg _
  rw [stabilityForm]
  nlinarith [sq_nonneg r.angle]

/-!

## C. The trace criterion

-/

/-- A unimodular matrix with subcritical trace has a nonzero lower-left entry.

If it were zero the matrix would be triangular with `A D = 1`, and then
`(A + D) ^ 2 - 4 = (A - D) ^ 2 ≥ 0`, so the trace could not be subcritical.
-/
lemma entry_one_zero_ne_zero_of_abs_rayTrace_lt_two (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : M 1 0 ≠ 0 := by
  intro hC
  rw [Matrix.det_fin_two, hC, mul_zero, sub_zero] at hdet
  obtain ⟨hlow, hhigh⟩ := abs_lt.mp htr
  rw [rayTrace] at hlow hhigh
  nlinarith [sq_nonneg (M 0 0 - M 1 1)]

/-- **The trace criterion for resonator stability.**

A resonator whose round-trip matrix is unimodular and has strictly subcritical trace is stable in
the boundedness sense of `Optics.IsStable`. The hypotheses are exactly the source's: unit
determinant and a strict trace bound.
-/
theorem isStable_of_abs_trace_lt_two (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : IsStable M := by
  have hC : M 1 0 ≠ 0 := entry_one_zero_ne_zero_of_abs_rayTrace_lt_two M hdet htr
  have h4 : 0 < 4 - rayTrace M ^ 2 := by
    obtain ⟨hlow, hhigh⟩ := abs_lt.mp htr
    nlinarith [hlow, hhigh]
  intro r
  set E := stabilityForm M r with hE
  have hEnonneg : 0 ≤ E := stabilityForm_nonneg M htr r
  refine ⟨(√E + |M 1 1 - M 0 0| * √(E / (4 - rayTrace M ^ 2))) / (2 * |M 1 0|),
    √(E / (4 - rayTrace M ^ 2)), fun n => ?_⟩
  have hcons : stabilityForm M (roundTripRay M r n) = E := stabilityForm_roundTripRay M hdet r n
  set s := roundTripRay M r n with hs
  have hangleSq : (4 - rayTrace M ^ 2) * s.angle ^ 2 ≤ E := by
    rw [← hcons, stabilityForm]
    nlinarith [sq_nonneg (2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle)]
  have hangle : |s.angle| ≤ √(E / (4 - rayTrace M ^ 2)) := by
    rw [show |s.angle| = √(s.angle ^ 2) from (Real.sqrt_sq_eq_abs s.angle).symm]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ h4]
    nlinarith [hangleSq]
  have hmixSq : (2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle) ^ 2 ≤ E := by
    rw [← hcons, stabilityForm]
    nlinarith [sq_nonneg s.angle, h4]
  have hmix : |2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle| ≤ √E := by
    rw [show |2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle| =
      √((2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle) ^ 2) from
      (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt hmixSq
  refine ⟨?_, hangle⟩
  have habsC : 0 < |M 1 0| := abs_pos.mpr hC
  rw [le_div_iff₀ (by positivity)]
  have hexpand : |s.height| * (2 * |M 1 0|) = |2 * M 1 0 * s.height| := by
    rw [abs_mul, abs_mul]
    simp
    ring
  rw [hexpand]
  calc |2 * M 1 0 * s.height|
      = |(2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle) - (M 1 1 - M 0 0) * s.angle| := by
        ring_nf
    _ ≤ |2 * M 1 0 * s.height + (M 1 1 - M 0 0) * s.angle| + |(M 1 1 - M 0 0) * s.angle| :=
        abs_sub _ _
    _ ≤ √E + |M 1 1 - M 0 0| * √(E / (4 - rayTrace M ^ 2)) := by
        rw [abs_mul]
        gcongr

/-!

## D. Two-mirror resonators

-/

/-- The `g` parameter of a mirror of radius `R` in a resonator of length `d`. -/
def gParameter (d R : ℝ) : ℝ := 1 - d / R

/-- A two-mirror resonator round trip: traverse the cavity, reflect off the far mirror, traverse
back, reflect off the near mirror.

The mirrors are the folded-convention ones, so the direction reversal is already inside each
mirror matrix and the radii are **not** negated on the return leg.
-/
def twoMirrorRoundTrip (d R₁ R₂ : ℝ) : List ParaxialComponent :=
  [⟨⟨1, d⟩, ParaxialInterface.sphericalMirror R₂⟩,
    ⟨⟨1, d⟩, ParaxialInterface.sphericalMirror R₁⟩]

/-- The two-mirror round trip is a valid system for a nonnegative cavity length and nonzero mirror
radii. -/
lemma twoMirrorRoundTrip_isValid (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.IsValid (twoMirrorRoundTrip d R₁ R₂) ⟨1, 0⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [twoMirrorRoundTrip, ParaxialSystem.headIndex, hd, hR₁, hR₂]

/-- The two-mirror round-trip matrix. -/
lemma twoMirror_matrix (d R₁ R₂ : ℝ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (twoMirrorRoundTrip d R₁ R₂) ⟨1, 0⟩ =
      !![1 - 2 * d / R₂, 2 * d - 2 * d ^ 2 / R₂;
        -2 / R₁ + 4 * d / (R₁ * R₂) - 2 / R₂,
        1 - 2 * d / R₂ - 4 * d / R₁ + 4 * d ^ 2 / (R₁ * R₂)] := by
  simp only [twoMirrorRoundTrip, ParaxialSystem.matrix,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **The two-mirror round-trip trace is `4 g₁ g₂ - 2`.**

This is where the reflection bookkeeping has to be right. The folded mirrors already contain the
direction reversal, so the radii keep their signs on the return leg; negating them as well would
compute the round trip of the negated radii, which
`Optics.resonatorRegression_negated_radii_not_isStable` shows changes a stable cavity into an
unstable one.
-/
theorem twoMirror_trace (d R₁ R₂ : ℝ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    rayTrace (ParaxialSystem.matrix (twoMirrorRoundTrip d R₁ R₂) ⟨1, 0⟩) =
      4 * gParameter d R₁ * gParameter d R₂ - 2 := by
  rw [rayTrace, twoMirror_matrix d R₁ R₂ hR₁ hR₂, gParameter, gParameter]
  norm_num
  field_simp
  ring_nf

/-- The two-mirror round trip is unimodular, so the determinant hypothesis of the stability
criterion is met directly in the folded convention. -/
theorem twoMirror_det (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    (ParaxialSystem.matrix (twoMirrorRoundTrip d R₁ R₂) ⟨1, 0⟩).det = 1 := by
  rw [ParaxialSystem.det_matrix _ _ (twoMirrorRoundTrip_isValid d R₁ R₂ hd hR₁ hR₂)
    (by
      intro c hc
      fin_cases hc <;> exact fun h => ParaxialInterface.noConfusion h)]
  norm_num [ParaxialSystem.headIndex, twoMirrorRoundTrip]

/-- **The two-mirror stability condition.** A two-mirror resonator with `0 < g₁ g₂ < 1` is stable.

The bounds are strict, and that is not a technicality. At `g₁ g₂ = 0` and `g₁ g₂ = 1` the trace
criterion says nothing, and the two endpoints behave differently: the confocal cavity is stable
and the plane-parallel cavity is not. `Physlib.Optics.Rays.ResonatorRegression` proves both.
-/
theorem isStable_twoMirror (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0)
    (hlow : 0 < gParameter d R₁ * gParameter d R₂)
    (hhigh : gParameter d R₁ * gParameter d R₂ < 1) :
    IsStable (ParaxialSystem.matrix (twoMirrorRoundTrip d R₁ R₂) ⟨1, 0⟩) := by
  refine isStable_of_abs_trace_lt_two _ (twoMirror_det d R₁ R₂ hd hR₁ hR₂) ?_
  rw [twoMirror_trace d R₁ R₂ hR₁ hR₂]
  rw [abs_lt]
  constructor <;> linarith

/-!

## E. Gaussian eigenmodes

-/

/-- The ray invariant is the eigenmode quadratic evaluated at the ray's height-to-angle ratio,
scaled by the squared angle.

This is the precise sense in which the ray and Gaussian views of a resonator are the same
calculation: the quadratic whose roots are the Gaussian eigenmode parameters is the quadratic
whose value on a ray is conserved.
-/
lemma rayInvariant_eq_ratio (M : RayTransferMatrix) (r : ParaxialRay) (h : r.angle ≠ 0) :
    rayInvariant M r =
      r.angle ^ 2 * (M 1 0 * (r.height / r.angle) ^ 2 +
        (M 1 1 - M 0 0) * (r.height / r.angle) - M 0 1) := by
  rw [rayInvariant]
  field_simp

/-- The complex beam parameter of the Gaussian eigenmode of a subcritical resonator. -/
def gaussianEigenparameter (M : RayTransferMatrix) : ℂ :=
  ((M 0 0 - M 1 1) / (2 * M 1 0) : ℝ) +
    (√(4 - rayTrace M ^ 2) / (2 * |M 1 0|) : ℝ) * Complex.I

/-- The eigenmode parameter lies in the physical domain. -/
lemma im_gaussianEigenparameter_pos (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : 0 < (gaussianEigenparameter M).im := by
  have hC : M 1 0 ≠ 0 := entry_one_zero_ne_zero_of_abs_rayTrace_lt_two M hdet htr
  have h4 : 0 < 4 - rayTrace M ^ 2 := by
    obtain ⟨hlow, hhigh⟩ := abs_lt.mp htr
    nlinarith [hlow, hhigh]
  rw [gaussianEigenparameter]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  exact div_pos (Real.sqrt_pos.mpr h4) (by positivity)

/-- A beam parameter built from the two defining relations is a root of the eigenmode quadratic.

The relations are stated in cleared form, with no division, so that the algebra below is a
polynomial identity in the matrix entries and the two real parts of the parameter.
-/
lemma quadratic_of_relations (M : RayTransferMatrix) (u v : ℝ) (hC : M 1 0 ≠ 0)
    (hu : 2 * M 1 0 * u = M 0 0 - M 1 1)
    (hv : 4 * M 1 0 ^ 2 * v ^ 2 = 4 - (M 0 0 + M 1 1) ^ 2)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) :
    (M 1 0 : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 +
      ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * ((u : ℂ) + (v : ℂ) * Complex.I) - (M 0 1 : ℂ) = 0 := by
  have h4C : (4 : ℝ) * M 1 0 ≠ 0 := by simpa using hC
  refine Complex.ext ?_ ?_ <;>
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.zero_re, Complex.zero_im, mul_one, mul_zero, add_zero, zero_add,
      sub_zero]
  · apply mul_left_cancel₀ h4C
    linear_combination (2 * M 1 0 * u - M 0 0 + M 1 1) * hu - hv + 4 * hdet
  · linear_combination v * hu

/-- The eigenmode parameter is a root of the eigenmode quadratic. -/
lemma quadratic_gaussianEigenparameter (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) :
    (M 1 0 : ℂ) * gaussianEigenparameter M ^ 2 +
      ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * gaussianEigenparameter M - (M 0 1 : ℂ) = 0 := by
  have hC : M 1 0 ≠ 0 := entry_one_zero_ne_zero_of_abs_rayTrace_lt_two M hdet htr
  have habsne : |M 1 0| ≠ 0 := abs_ne_zero.mpr hC
  have h4 : 0 < 4 - rayTrace M ^ 2 := by
    obtain ⟨hlow, hhigh⟩ := abs_lt.mp htr
    nlinarith [hlow, hhigh]
  have hsq : √(4 - rayTrace M ^ 2) ^ 2 = 4 - rayTrace M ^ 2 := Real.sq_sqrt h4.le
  have habs : |M 1 0| ^ 2 = M 1 0 ^ 2 := sq_abs _
  have hdetEq : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have hu : 2 * M 1 0 * ((M 0 0 - M 1 1) / (2 * M 1 0)) = M 0 0 - M 1 1 := by field_simp
  have hv : 4 * M 1 0 ^ 2 * (√(4 - rayTrace M ^ 2) / (2 * |M 1 0|)) ^ 2 =
      4 - (M 0 0 + M 1 1) ^ 2 := by
    rw [div_pow, hsq, mul_pow, habs, rayTrace]
    field_simp
    ring
  rw [gaussianEigenparameter]
  exact quadratic_of_relations M _ _ hC hu hv hdetEq

/-- **A subcritical resonator has a Gaussian eigenmode.**

The round trip fixes a beam parameter in the physical domain, so the resonator supports a Gaussian
mode that reproduces itself. Its parameter is a root of the same quadratic whose value on a ray is
the conserved `Optics.rayInvariant`, which is the agreement between the ray and Gaussian pictures
that `goal.md` §H.5 R5 asks for.
-/
theorem abcdTransform_gaussianEigenparameter (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) :
    abcdTransform M (gaussianEigenparameter M) = gaussianEigenparameter M := by
  have him := im_gaussianEigenparameter_pos M hdet htr
  have hden := abcdDenominator_ne_zero M (gaussianEigenparameter M) him (by rw [hdet]; norm_num)
  have hq := quadratic_gaussianEigenparameter M hdet htr
  rw [abcdTransform, div_eq_iff hden, abcdDenominator]
  linear_combination -hq

/-- A subcritical resonator supports a Gaussian mode that reproduces itself on a round trip. -/
theorem exists_gaussian_eigenmode (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : ∃ q : ℂ, 0 < q.im ∧ abcdTransform M q = q :=
  ⟨gaussianEigenparameter M, im_gaussianEigenparameter_pos M hdet htr,
    abcdTransform_gaussianEigenparameter M hdet htr⟩

end

end Optics
