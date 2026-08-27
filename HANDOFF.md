# E4b neutral coordinate constant-jump handoff

## Cutoff identity

- Development sync target: `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38`.
- Sync merge: `db3a8d14`.
- Gated source before this handoff-only child:
  `25237354e18310f1f85881d0491a89d913963ea3`.
- `Physlib.lean` is unchanged. Its restored SHA-256 is
  `f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20`.
- The source delta is exactly the seven files listed below. This handoff is the
  cutoff-only child.

## Scope and goal resolution

This slice is neutral distribution infrastructure for one exact model: a field
which is zero on the negative side and constant on the positive side of an
origin coordinate hyperplane. It proves that the distributional derivative in
the stored inward `+e_i` direction is the constant-coefficient sheet on that
hyperplane. It also identifies the sheet with the coordinate transport of the
generic hyperplane pushforward of a constant tangential distribution.

The E4b status remains `in progress` at `goal.md:2832`. This slice does **not**
prove the variable-trace derivative formula on an arbitrary oriented affine
plane, a weak or measure-valued Maxwell equation, or the finite-sheet premise.
It does not change any E4b completion checkbox.

## Files and registration request

- `Physlib/SpaceAndTime/Space/DistributionCoordinates.lean` (new, 101 lines):
  coordinate transport of Euclidean tempered distributions to `Space`, with
  coordinate-derivative covariance.
- `Physlib/SpaceAndTime/Space/OrientedAffineHyperplane.lean` (registered,
  additive `+23/-0`): standard positive coordinate directions and their origin
  hyperplanes.
- `Physlib/SpaceAndTime/Space/OrientedAffineHyperplaneConstantJump.lean` (new,
  226 lines): coordinate Heaviside and delta distributions, the constant sheet,
  its generic-pushforward bridge, and the independent sidewise realization.
- `Physlib/SpaceAndTime/Space/OrientedAffineHyperplaneConstantJumpRegression.lean`
  (new, 318 lines): direct one-dimensional coefficient/sign anchors and an
  asymmetric two-dimensional coordinate sentinel.
- `Physlib/Optics/API-map.yaml`, `goal.md`, and `tbd.md`: honest scope and
  residual-work wording; no E4b completion flip.

Please register these imports in repository-sorted order:

```lean
public import Physlib.SpaceAndTime.Space.DistributionCoordinates
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneConstantJump
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneConstantJumpRegression
```

`DistributionCoordinates` sorts after `DistOfFunction`.
`OrientedAffineHyperplaneConstantJump` and its regression sort after
`OrientedAffineHyperplane` and before `OrientedAffineHyperplaneCrossProduct`.

## Registered-module drift

`Physlib/SpaceAndTime/Space/OrientedAffineHyperplane.lean` receives exactly four
additive declarations; no existing declaration or proof is changed:

- `Space.OrientedAffineHyperplane.coordinateDirection`;
- `Space.OrientedAffineHyperplane.coordinateHyperplane`;
- `Space.OrientedAffineHyperplane.coordinateDirection_unit`;
- `Space.OrientedAffineHyperplane.signedNormalCoordinate_coordinateHyperplane`.

No other registered Lean module changes.

## Production declarations

### Coordinate transport

- `Space.basisCoordinateSchwartz`;
- `Space.basisCoordinateSchwartz_apply`;
- `Space.distributionOfEuclideanCoordinates`;
- `Space.distributionOfEuclideanCoordinates_apply`;
- `Space.distDeriv_distributionOfEuclideanCoordinates_apply`.

### Constant coordinate jump

- `Space.coordinateHeavisideDistribution`;
- `Space.coordinateHyperplaneDeltaDistribution`;
- `Space.coordinateHeavisideDistribution_apply`;
- `Space.coordinateHyperplaneDeltaDistribution_apply`;
- `Space.basis_repr_basis_eq_coordinateNormalEmbedding`;
- `Space.distDeriv_coordinateHeavisideDistribution`;
- `Space.coordinatePositiveConstantDistribution`;
- `Space.coordinateHyperplaneSheet`;
- `Space.coordinateHyperplaneSheet_eq_pushforward_const`;
- `Space.distDeriv_coordinatePositiveConstantDistribution`;
- `Space.OrientedAffineHyperplane.coordinatePositiveConstantField`;
- `Space.OrientedAffineHyperplane.coordinatePositiveConstantField_isDistBounded`;
- `Space.OrientedAffineHyperplane.distOfSidewiseFunction_coordinatePositiveConstant`;
- `Space.OrientedAffineHyperplane.distDeriv_coordinatePositiveConstant`.

## Exact mathematical content

`distributionOfEuclideanCoordinates` composes a Euclidean tempered distribution
with the pullback of Schwartz tests along `Space.basis.repr.symm`. The derivative
covariance lemma is proved by the Fréchet chain rule and the orthonormal-basis
equivalence; it is not an equality by definitional transport.

For `i : Fin d.succ`, the selected positive half-space is literally
`{x : Space d.succ | 0 < x i}`. The normal direction is `Space.basis i`, so the
orientation convention is load-bearing. Transport of the Euclidean Heaviside
derivative gives

```text
distDeriv i (coordinateHeavisideDistribution d i)
  = coordinateHyperplaneDeltaDistribution d i.
```

Scalar extension gives the same formula for an arbitrary coefficient `c` in a
complete real normed space. The independently defined sidewise field uses zero
on `.negative` and `c` on `.positive`; the existing strict-half-space
distribution API ignores carrier and off-side values. Its derivative is then the
same selected sheet.

`coordinateHyperplaneSheet_eq_pushforward_const` connects that sheet to
`Physlib.Distribution.coordinateHyperplanePushforward` applied to the constant
tangential distribution. Thus this slice reuses the already reviewed generic
pushforward rather than introducing a second surface-density construction.

## Independent regression audit

The regression imports production only as definitions and low-level calculus
infrastructure. It contains zero uses of the five production identification
lemmas

```text
distDeriv_coordinatePositiveConstant
distOfSidewiseFunction_coordinatePositiveConstant
coordinateHyperplaneSheet_eq_pushforward_const
distDeriv_coordinatePositiveConstantDistribution
distDeriv_coordinateHeavisideDistribution
```

The one-dimensional Gaussian fixture expands both sides separately:

- `constantJumpRegression_raw_positiveDerivative` rewrites the sidewise
  distribution and derivative definitions, changes variables to the real
  half-line, applies the one-dimensional FTC, and obtains `7`;
- `constantJumpRegression_raw_sheet` expands the transported delta and boundary
  integral independently and obtains `7`;
- `constantJumpRegression_raw_agreement` compares those two already independent
  values;
- `constantJumpRegression_raw_negativeDerivative` repeats the derivative
  expansion in direction `-e_0` and obtains `-7`.

The `Fin 2` test is asymmetric in the selected coordinate:

- `constantJumpRegression_selectedSheet_eq_zero` gives zero on one coordinate
  hyperplane;
- `constantJumpRegression_otherSheet_pos` proves the swapped-coordinate sheet
  is strictly positive;
- `constantJumpRegression_wrongCoordinate_ne` rejects the coordinate swap.

This catches coefficient, derivative-sign, and selected-coordinate errors. It
does not claim to test a variable trace or a rotated affine plane.

## Gate evidence

All Lean commands were run serially under `lake-lock` with temporary public
registration, then `Physlib.lean` was restored byte-for-byte:

- targeted warning-as-error build: PASS, 3180 jobs;
- root warning-as-error build after temporary registration: PASS, 5014 jobs;
- `check_file_imports`: PASS;
- `sorry_lint`: PASS;
- `runPhyslibLinters`: PASS for Physlib and QuantumInfo after reaching the
  `unusedArguments` fixed point;
- static checks: zero `sorry`/`axiom`/`native_decide`/`maxHeartbeats`, zero
  `theorem`, maximum 100 codepoints, no production import or use of the
  regression module, and `git diff --check` clean.

The fixed-point pass removed one redundant `[NormedSpace ℝ F]` binder from
`coordinatePositiveConstantField_isDistBounded`; no statement body, value,
proof, or name changed.

## Reviewer map

1. Read `DistributionCoordinates.lean` to verify the direction of the basis
   pullback and derivative covariance.
2. Read sections A and B of `OrientedAffineHyperplaneConstantJump.lean` to
   verify the `+e_i` convention, pushforward bridge, and independent sidewise
   realization.
3. Audit the one-dimensional raw derivative/sheet proofs and the `Fin 2`
   coordinate sentinel in the regression.
4. Check `goal.md`, `tbd.md`, and the API-map row for the retained arbitrary-plane,
   weak-Maxwell, and finite-sheet non-claims.
