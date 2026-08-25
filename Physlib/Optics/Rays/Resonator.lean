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

Stability here is a matrix-level analogue of the source's bounded-ray condition: the ray stays
bounded under arbitrarily many powers of one round-trip matrix, with the bounds chosen before the
number of round trips. It is not a trace inequality. The trace inequality is a *criterion*, and
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

Reflection bookkeeping. The round trips here take `R₁` and `R₂` directly as the local signed
radii at their two respective mirror encounters in the folded convention fixed by
`Physlib.Optics.Rays.Basic`; they do not implement a generic reverse-list traversal.
`Optics.resonatorRegression_negated_radii_not_isStable` shows that negating those supplied radii
instead produces a different, unstable cavity. It does not identify that altered model with an
explicit output-angle coordinate reversal: such an identification would require a separate
covariance theorem for propagation and reflection. Because folded mirrors have determinant `1`,
the determinant hypothesis of the stability theorem is met directly.

Explicit non-claims. There is no field, power, loss, gain, or mode-volume content here, and no
diffraction: a resonator that is stable in this sense confines rays, which is not the same as
supporting a low-loss mode. Nothing is claimed about resonance frequencies or longitudinal modes.
The explicit eigenparameter formula is a totalized algebraic candidate outside the strict trace
domain; only the proof-gated eigenbeam is given physical meaning.
Generic source-style reverse-list unfolding, its validity predicate, and its connection to matrix
powers remain open, so this file does not claim literal parity with the source stability predicate.
Three further source results are withheld by name and are not formalised here: the
Sylvester-Chebyshev matrix-power form of a unimodular round trip, the fibre-ring-laser
Fabry-Perot analyses in the two transverse planes with their stability ranges, and the
phase-conjugate resonator and nonlinear-map chaos results.

## ii. Key results

- `Optics.IsStable`: stability as boundedness of the ray under arbitrarily many round trips.
- `Optics.IsFixedRay` and `Optics.IsFixedBeam`: named matrix-level fixed-point predicates.
- `Optics.rayInvariant_rayTransfer`: the conserved quadratic form, up to the determinant.
- `Optics.isStable_of_abs_trace_lt_two`: the trace criterion implies stability.
- `Optics.twoMirror_trace`: the two-mirror round-trip trace is `4 g₁ g₂ - 2`.
- `Optics.isStable_twoMirror`: a two-mirror cavity with `0 < g₁ g₂ < 1` is stable.
- `Optics.gaussianEigenbeam`: a subcritical resonator has a proof-gated Gaussian eigenbeam, whose
  beam parameter is a root of the same quadratic that the ray invariant is built from.
- `Optics.transform_gaussianEigenbeam`: the full beam, including its wavelength, is fixed by one
  round trip.

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
  Concordia University, 2015, chapter 5, definition 5.5 and theorem 5.7, for the source
  boundedness predicate and trace criterion to which the matrix-level results here are related.

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

/-- **Matrix-level stability of a resonator:** for every incoming ray there are bounds, chosen in
advance, that the height and the angle never exceed however many matrix round trips the ray makes.

This is a statement about every ray under powers of one matrix. The trace criterion of section C
is a sufficient condition for it, and is not the definition. A future source-parity bridge must
relate source-style unfolded resonator lists and their validity antecedent to these powers.
-/
def IsStable (M : RayTransferMatrix) : Prop :=
  ∀ r : ParaxialRay, ∃ heightBound angleBound : ℝ, ∀ n : ℕ,
    |(roundTripRay M r n).height| ≤ heightBound ∧
      |(roundTripRay M r n).angle| ≤ angleBound

/-- A paraxial ray is fixed by one application of a round-trip matrix. -/
def IsFixedRay (M : RayTransferMatrix) (r : ParaxialRay) : Prop := rayTransfer M r = r

/-- A Gaussian beam is fixed by a round-trip matrix when the determinant preserves its wavelength
and the complex ABCD action preserves its beam parameter. -/
def IsFixedBeam (M : RayTransferMatrix) (b : GaussianBeam) : Prop :=
  M.det = 1 ∧ abcdTransform M b.q = b.q

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

A round-trip matrix that is unimodular and has strictly subcritical trace is stable in the
boundedness sense of `Optics.IsStable`. This is the matrix-level algebraic core related to the
source criterion; it does not supply the source's unfolded-system validity theorem.
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
    norm_num
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

The locally folded model takes `R₁` and `R₂` directly as the signed radii at their respective
mirror encounters; this definition does not implement generic reverse-list unfolding.
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

This is where the signed-radius convention has to be applied consistently. Negating both stored
radii computes the round trip of a different cavity, which
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
lemma twoMirror_det (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
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

/-- The totalized algebraic candidate for a subcritical resonator's Gaussian eigenparameter.

Outside the hypotheses `M.det = 1` and `|rayTrace M| < 2`, division by the lower-left entry and
the square root are merely totalized real operations. In particular this candidate is zero for
the stable boundary matrices `1` and `-1`, where the physical fixed parameter is nonunique.
-/
def gaussianEigenparameterCandidate (M : RayTransferMatrix) : ℂ :=
  ((M 0 0 - M 1 1) / (2 * M 1 0) : ℝ) +
    (√(4 - rayTrace M ^ 2) / (2 * |M 1 0|) : ℝ) * Complex.I

/-- The eigenmode parameter lies in the physical domain. -/
lemma im_gaussianEigenparameterCandidate_pos (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : 0 < (gaussianEigenparameterCandidate M).im := by
  have hC : M 1 0 ≠ 0 := entry_one_zero_ne_zero_of_abs_rayTrace_lt_two M hdet htr
  have h4 : 0 < 4 - rayTrace M ^ 2 := by
    obtain ⟨hlow, hhigh⟩ := abs_lt.mp htr
    nlinarith [hlow, hhigh]
  rw [gaussianEigenparameterCandidate]
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
lemma quadratic_gaussianEigenparameterCandidate (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) :
    (M 1 0 : ℂ) * gaussianEigenparameterCandidate M ^ 2 +
      ((M 1 1 : ℂ) - (M 0 0 : ℂ)) * gaussianEigenparameterCandidate M - (M 0 1 : ℂ) = 0 := by
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
  rw [gaussianEigenparameterCandidate]
  exact quadratic_of_relations M _ _ hC hu hv hdetEq

/-- **A subcritical resonator has a physical fixed Gaussian beam parameter.**

The round trip fixes a parameter in the upper half-plane. It is a root of the same quadratic whose
value on a ray is the conserved `Optics.rayInvariant`. The later `gaussianEigenbeam` construction
lifts this parameter to a complete stored beam.
-/
lemma abcdTransform_gaussianEigenparameterCandidate (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) :
    abcdTransform M (gaussianEigenparameterCandidate M) =
      gaussianEigenparameterCandidate M := by
  have him := im_gaussianEigenparameterCandidate_pos M hdet htr
  have hden := abcdDenominator_ne_zero M (gaussianEigenparameterCandidate M) him
    (by rw [hdet]; norm_num)
  have hq := quadratic_gaussianEigenparameterCandidate M hdet htr
  rw [abcdTransform, div_eq_iff hden, abcdDenominator]
  linear_combination -hq

/-- A subcritical resonator has a physical Gaussian eigenparameter. -/
lemma exists_gaussian_eigenparameter (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) : ∃ q : ℂ, 0 < q.im ∧ abcdTransform M q = q :=
  ⟨gaussianEigenparameterCandidate M, im_gaussianEigenparameterCandidate_pos M hdet htr,
    abcdTransform_gaussianEigenparameterCandidate M hdet htr⟩

/-- A Gaussian eigenbeam of a subcritical resonator, at any positive wavelength. Both the
physical beam domain and the fixed-point equation are certified by the strict trace hypotheses. -/
def gaussianEigenbeam (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) (wavelength : ℝ) (hWavelength : 0 < wavelength) : GaussianBeam where
  wavelength := wavelength
  q := gaussianEigenparameterCandidate M
  wavelength_pos := hWavelength
  q_im_pos := im_gaussianEigenparameterCandidate_pos M hdet htr

/-- **The complete Gaussian eigenbeam is fixed by one resonator round trip.** Because the
round-trip determinant is one, both its wavelength and its complex beam parameter are unchanged. -/
lemma transform_gaussianEigenbeam (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) (wavelength : ℝ) (hWavelength : 0 < wavelength) :
    (gaussianEigenbeam M hdet htr wavelength hWavelength).transform M
        (show 0 < M.det by rw [hdet]; norm_num) =
      gaussianEigenbeam M hdet htr wavelength hWavelength := by
  apply GaussianBeam.ext
  · simp [GaussianBeam.transform, gaussianEigenbeam, hdet]
  · simp [GaussianBeam.transform, gaussianEigenbeam,
      abcdTransform_gaussianEigenparameterCandidate M hdet htr]

/-- A subcritical resonator supports a complete Gaussian beam that reproduces itself after one
round trip. -/
theorem exists_gaussian_eigenbeam (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) :
    ∃ b : GaussianBeam,
      b.transform M (show 0 < M.det by rw [hdet]; norm_num) = b :=
  ⟨gaussianEigenbeam M hdet htr 1 one_pos,
    transform_gaussianEigenbeam M hdet htr 1 one_pos⟩

/-- The proof-gated Gaussian eigenbeam satisfies the named fixed-beam predicate. -/
lemma isFixedBeam_gaussianEigenbeam (M : RayTransferMatrix) (hdet : M.det = 1)
    (htr : |rayTrace M| < 2) (wavelength : ℝ) (hWavelength : 0 < wavelength) :
    IsFixedBeam M (gaussianEigenbeam M hdet htr wavelength hWavelength) :=
  ⟨hdet, abcdTransform_gaussianEigenparameterCandidate M hdet htr⟩

/-- **The strict trace criterion gives both bounded-ray stability and a fixed Gaussian beam.**

This is the combined matrix-level result behind regression R-04. It keeps determinant one and the
strict trace domain explicit and reaches the named ray-stability and fixed-beam predicates.
-/
lemma isStable_and_exists_isFixedBeam_of_abs_trace_lt_two (M : RayTransferMatrix)
    (hdet : M.det = 1) (htr : |rayTrace M| < 2) :
    IsStable M ∧ ∃ b : GaussianBeam, IsFixedBeam M b := by
  refine ⟨isStable_of_abs_trace_lt_two M hdet htr,
    gaussianEigenbeam M hdet htr 1 one_pos, ?_⟩
  exact isFixedBeam_gaussianEigenbeam M hdet htr 1 one_pos

end

end Optics
