# CROW convention map for Heebner et al. Table 1

## Status and scope

This document fixes the comparison contract between the CROW example in
`Physlib/Optics/Examples/CROW.lean` and row (a) of Table 1 in Heebner, Chak,
Pereira, Sipe, and Boyd, *JOSA B* 21(10), 1818-1832 (2004),
doi:10.1364/JOSAB.21.001818. It is a convention map, not a numerical comparison.

**Convention mapping written; numeric Table-1 parity deferred to slice 1B; NO verdict.**

The source pages and formulas cited below were checked against the primary PDF. The human author
must still certify the source transcription and the proposed mapping before publication.

## Source coordinates

Figure 1(a) and Eq. (1) order the bulk boundary state as `(A_j, B_j)`: `A_j` is the lower,
right-going field and `B_j` is the upper, left-going field at the left boundary of a unit cell.
The output state is `(A_(j+1), B_(j+1))` in the same order at the right boundary. These are
internal fields at repeated bulk-cell cuts in an infinite periodic sequence. They are not the
input and output fields of a finite bus-access device.

Figure 3 orders the local coupler inputs as `(E_1, E_2)` and outputs as `(E_3, E_4)`, with

```text
(E_3, E_4)^T = [[r, i t], [i t, r]] (E_1, E_2)^T.
```

Here `r` is the real self-coupling coefficient, `t` is the real cross-coupling coefficient, and
the paper imposes `r^2 + t^2 = 1` when coupling loss is neglected. Table 1 then gives the CROW
bulk transfer matrix in terms of one pair `(r, t)` and two full resonator phases `phi_1, phi_2`.

## Physlib coordinates

`DirectionalCoupler` orders a left-to-right local input as `(leftFirst, leftSecond)` and its
output as `(rightFirst, rightSecond)`. In those coordinates its mixing matrix is

```text
[[throughAmplitude, -i crossAmplitude],
 [-i crossAmplitude, throughAmplitude]].
```

Thus the coefficient-name map is

```text
r  <-> throughAmplitude
t  <-> crossAmplitude.
```

The sign of the quadrature factor is a gauge difference. With `D = diag(1, -1)`,

```text
D [[r, i t], [i t, r]] D = [[r, -i t], [-i t, r]].
```

Accordingly, the candidate local field map leaves the first arm unchanged and negates the second
arm at both sides of every coupler. Slice 1B must apply this gauge consistently across connected
cell boundaries; it must not compare the two printed matrices entrywise before that transport.

At a bulk cut, Physlib's forward-travel field is the candidate for `A_j` and its return-travel
field is the candidate for `B_j`. The exact extraction must use the incident/outgoing coordinates
selected by `crowRegressionForwardArcChannel`, `crowRegressionReturnArcChannel`, and
`crowRegressionCouplerChannel`. In contrast, `crowRegressionExternalChannel` selects the four
finite boundary fields `leftInput`, `leftOutput`, `rightInput`, and `rightOutput`. None of those
four boundary labels is identified directly with every repeated `A_j` or `B_j`.

## Phase map

For one Physlib ring, the full accumulated carrier phase is the sum, modulo `2 * pi`, of its
forward- and return-half-arc `carrierPathPhase` values. This sum is the candidate for the
corresponding Table-1 full-ring phase `phi_1` or `phi_2`. Physlib propagation uses
`exp(-i phase)` under its positive-time convention. Table 1 contains both positive and negative
half-phase exponents because it is a left-to-right transfer matrix mixing counterpropagating
boundary fields. Therefore those signs are not compared term by term; slice 1B must first derive
the scattering-to-transfer conversion in the pinned `(A, B)` order.

## Preconditions for any slice-1B Table-1 comparison

The domain differences below are preconditions, not observations to resolve after running the
comparison. No exact or numerical Table-1 comparison may run until the slice-1B fixture and its
coordinate proofs satisfy all four conditions.

1. **Uniformity delta.** Table 1 uses one bulk coupler pair `(r, t)`, whereas
   `CROW.Parameters` permits one coupler per interface. Slice 1B must use a separate fixture with
   one pinned Pythagorean pair at every compared bulk interface. Its half-arcs must also have
   unit amplitude, matching the displayed loss-neglecting construction. The slice-1 regression
   remains deliberately nonuniform, with `(3/5, 4/5)` at both ends, `(5/13, 12/13)` in the
   middle, and half-arc amplitude `1/2`; it is not a Table-1 comparison fixture.
2. **End-boundary delta.** Table 1 supplies a bulk unit-cell matrix for an infinite periodic
   sequence. Physlib's example is a finite CROW with four exposed end channels. Before comparing
   a finite response, slice 1B must state and prove the left and right access matrices, identify
   the bulk-cell range, and prove the end-boundary readout.
3. **Phase structure.** Table 1 advances `(A_j, B_j)` using signed half-phase factors, while
   Physlib propagation supplies directed scattering relations. Slice 1B must pin the two
   half-arc phases, prove their sum is the corresponding full-ring `phi_1` or `phi_2`, and derive
   the scattering-to-transfer conversion in the stated `(A, B)` order before comparing entries.
4. **Coupler convention.** The source uses `+i t` and Physlib uses `-i crossAmplitude`.
   Slice 1B must prove the `r`/`t` coefficient map and transport the `D = diag(1, -1)` gauge
   consistently through every compared cell boundary. It must also prove the internal-field
   extraction; no external channel is silently identified with every repeated `A_j` or `B_j`.

## Exact lossless-coupler compatibility

The existing regression proves

```text
(3/5)^2 + (4/5)^2 = 1
(5/13)^2 + (12/13)^2 = 1.
```

Hence both concrete coupler parameter pairs satisfy the paper's Pythagorean coupling condition
inside the existing `DirectionalCoupler` convention after the gauge map above. This statement is
only about the algebraic coupler coefficients. It does not turn the half-amplitude propagation
fixture into a physical loss model or establish global losslessness.

## Slice-1B comparison contract

Slice 1B must discharge all four preconditions above before it runs exact parity. It must then
record which of three outcomes fired: agreement, ours-wrong, or table-wrong. Each outcome is
publishable evidence. Any disagreement is a finding to investigate, not a mismatch to explain
away. This document records none of those outcomes.
