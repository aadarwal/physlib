# HANDOFF — lane N5F/N5H

Branch: `optics/n5f-n5h` (branched from `optics/development` at `48015bbf`, most recently merged
through `9a9e273b`).
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-n5f-n5h`.
Source parity: Physlib-original. The HOL corpus has no parameterized-compilation or hierarchical
flattening development; there is no source file to mirror and no parity row to claim.

## Files added

| File | Contract | Status |
|---|---|---|
| `Physlib/Mathematics/LinearAlgebra/Matrix/Analytic.lean` | prerequisite | see below |
| `Physlib/Optics/Network/ParameterizedResponse.lean` | N5F slices 1–3 | see below |
| `Physlib/Optics/Network/ParameterizedResponseRegression.lean` | N5F regressions | see below |
| `Physlib/Optics/Network/Hierarchical.lean` | N5H slices 4-6 | see below |
| `Physlib/Optics/Network/HierarchicalRegression.lean` | N-08 fixture | gate green |

This lane modifies no existing Lean source module. `Physlib.lean` is restored byte-for-byte after
each registration gate and is never committed by this lane; this handoff is updated to record the
fixture. Changes to other tracked files in the branch came from merging `optics/development`.

## Gate evidence

The shipped declaration linters resolve declarations through the `Physlib` module registry, so
they cannot see an unregistered module. To make the gate real, the five registrations below were
added to `Physlib.lean` **temporarily**, the gate was run, and the file was then restored
byte-for-byte and never committed (`git diff Physlib.lean` is empty at the cutoff). With the
modules registered:

```
lake build Physlib                → exit 0, no errors, no warnings
lake exe check_file_imports       → exit 0
lake exe sorry_lint               → exit 0
lake exe runPhyslibLinters        → exit 0, "Linting passed for Physlib."
```

Additional checks run directly on the five files: no `sorry`, `axiom`, `native_decide`,
`maxHeartbeats`, or `Lean.ofReduceBool`; every line at most 100 characters; a docstring on every
declaration; `scripts/lint-style.py` clean.

## Registrations the conductor must apply at merge

Add to `Physlib.lean`, in the existing alphabetical blocks:

```
public import Physlib.Mathematics.LinearAlgebra.Matrix.Analytic
public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Network.HierarchicalRegression
public import Physlib.Optics.Network.ParameterizedResponse
public import Physlib.Optics.Network.ParameterizedResponseRegression
```

`Physlib/Mathematics/LinearAlgebra/Matrix/Analytic.lean` is deliberately Optics-free and
Mathlib-shaped (root-namespace lemma names mirroring Mathlib's `continuousAt_matrix_inv`). It is a
candidate for a separate small upstream PR.

## Public names other lanes should bind

### N5F — `Optics.ParameterizedComponentFamily` / `Optics.ParameterizedNetlist`

Structure fields (stable): `components`, `Connection`, `connections`; component-family fields
`Component`, `portFamily`, `scattering`, `IsValidAt`.

Bind these, not their unfoldings:

- `ParameterizedComponentFamily.evaluate` — the fixed-frequency family at one parameter.
- `ParameterizedComponentFamily.validityDomain` — where every component's stored model is claimed.
- `ParameterizedNetlist.compile` — the `N4`/`N5` flat netlist at one parameter.
- `ParameterizedNetlist.scatteringTransform`, `.routingTransform`, `.inputExposure`,
  `.outputReadout`, `.feedbackOperator` — parameter-uniform types (the wiring-derived three do not
  depend on the parameter, proved by `compile_routingTransform` etc.).
- `ParameterizedNetlist.solveDomain` — algebraic (`1 - C * S` invertible).
- `ParameterizedNetlist.responseDomain` — physical (`solveDomain ∩ validityDomain`).
- `ParameterizedNetlist.response` — proof-gated; takes `value ∈ responseDomain`.
- `ParameterizedNetlist.unguardedResponse` — the same formula written with Mathlib's total matrix
  inverse, so that regularity can be stated as a function of the parameter. Its meaning has three
  regions: outside `solveDomain` it is Mathlib's junk inverse and means nothing; on
  `solveDomain \ validityDomain` it is a genuine algebraic inverse and the exact `N5` block
  formula, but not every component model is claimed valid there, so it is not a physical
  response; on
  `responseDomain` it is the response. **Never quote it as a response without a
  `responseDomain` hypothesis**; use `unguardedResponse_eq_blockFormula` (algebraic, solve gate)
  or `unguardedResponse_eq_response` (physical gate).
- `ParameterizedNetlist.mem_compileBehavior_iff_unguardedResponse` — the `N-10` commutation
  statement, gated on `solveDomain`, which is the domain goal.md asks for.
- `ParameterizedNetlist.mem_compileBehavior_iff_response` — its physical corollary on
  `responseDomain`.
- `ParameterizedNetlist.continuousAt_unguardedResponse`,
  `ParameterizedNetlist.analyticAt_unguardedResponse_entry` — regularity **of the algebraic
  total-inverse formula**, each requiring a `solveDomain` hypothesis and a corresponding hypothesis
  on the stored component entries (`ComponentEntriesContinuousAt` / `ComponentEntriesAnalyticAt`).
  These are not claims that a physical response is continuous or analytic; that follows only after
  restricting to `responseDomain`.

For the validation harness (SAX comparison): the object to compare against a simulator sweep is
`unguardedResponse` restricted to `responseDomain`, entry `(Outgoing.mk out, Incident.mk inp)`
where `out`/`inp` are `ExternalChannel`s. The response domain is the honest sweep domain: points
outside it have no proved response.

### N5H — `Optics.PortConnectionFamily` extensions and `Optics.HierarchicalNetlist`

- `PortConnectionFamily.externalPortModeFamily` — the boundary port family a stage exposes.
- `PortConnectionFamily.boundaryChannelEquiv` — boundary channels are external channels.
- `PortConnection.liftBoundary` — an outer connection on ambient ports, mode equivalence verbatim.
- `PortConnectionFamily.append` — two-stage wiring; **takes no well-posedness hypothesis**.
- `PortConnectionFamily.appendChannelEquiv`, `.appendUnconnectedPortEquiv`,
  `.appendExternalChannelEquiv`, `.append_mateEquiv_inl`, `.append_mateEquiv_inr`.
- `PortConnectionFamily.closeBehavior` / `.mem_closeBehavior_iff` and
  `FlatNetlist.behavior_eq_closeBehavior` — wiring an abstract oriented boundary behavior,
  singular-safe, with `FlatNetlist.behavior` exhibited as an instance.
- `PortConnectionFamily.append_incidentAssembly_apply_inner` / `_apply_outer` / `_apply_external`
  — the flattened incident assembly stage by stage.
- `HierarchicalNetlist`, `.innerNetlist`, `.flatten`, `.flattenExternalChannelEquiv`,
  `.flattenConnectedChannelEquiv`.
- `FlatNetlist.packagedScattering` and `FlatNetlist.toOrientedModeTransform_packagedScattering`:
  a verified subsystem as one scattering component, gated on well-posedness and using only the
  canonical `Incident.channelEquiv` / `Outgoing.channelEquiv` endpoint pairing.
- `hierarchicalRegression_mem_flatten_behavior` — the hand-expanded `165` response satisfies the
  flattened netlist's component, incident-assembly, and readout equations directly.
- `hierarchicalRegression_mem_outerClosure` — the canonically relabelled same external pair
  satisfies the outer closure's three membership equations and the inner netlist's own behavior.
- `hierarchicalRegression_flatten_output_forced` — every flattened solution forces
  `y(output) = 165 * u(input)`.
- `hierarchicalRegression_misLifted_not_mem_flatten_behavior` — the explicit response with `165`
  placed on the wrong external port is rejected.

## goal.md rows

- H.3 N5F bullets 1–4 (parameter families with pointwise validity; pointwise compilation to the
  fixed-frequency N4 equations; algebraic solve domain and physical response domain by
  intersection; response function with evaluation commuting with compilation and elimination) and
  bullet 5 (continuity/analyticity under corresponding hypotheses on component data and
  inverse-domain control).
- H.3 N5H bullets 1–2 (hierarchical network; relational flattening preserving typed external
  ports, mode compatibility, and conventions, with no well-posedness assumption to flatten).
- H.3 N5H bullet 4 (functional packaging of a child as a scattering component only after that
  child's well-posedness and external-channel pairing have been proved).
- H.3 N5H bullet 3 (equality between hierarchical relational semantics and the semantics of the
  flattened netlist) as a theorem, and bullet 5 in the narrower form actually proved: congruence
  under a fixed inner wiring. The stronger reuse statement and literal three-stage associativity
  are both withheld; see below.
- I.3 row **N-10** — `parameterizedResponseRegression_mem_compileBehavior_iff_solve`, gated on the
  well-posed domain as goal.md requires; `parameterizedResponseRegression_mem_compileBehavior_iff`
  is its response-domain corollary.
- I.3 row **N-08 — CLAIMED**. `hierarchicalRegression_mem_flatten_behavior` and
  `hierarchicalRegression_mem_outerClosure` establish the same hand-expanded external pair from
  the two semantics' own equations without invoking either semantic equality theorem. The forcing
  lemma and `hierarchicalRegression_misLifted_not_mem_flatten_behavior` supply the required
  subsystem-boundary/port-lift negative control. In particular,
  `hierarchicalRegression_incidentAssembly_apply_outputLink` exercises the outer port lift by
  mating the third component's link input to the second component's remaining boundary output.

## Explicit non-claims

- `Param` is an abstract index type. No physical angular frequency, Laplace variable, delay
  variable `q`, or `Z` variable is named, and no relation between them is asserted (invariant E.8).
- `IsValidAt` is supplied data recording where a component's own model is *claimed* to hold. It is
  never proved, and it is deliberately not the algebraic solve condition; the regression proves
  both inclusions of `responseDomain` strict.
- No resonance condition, free-spectral-range statement, linewidth, or spectral observable is
  derived. Those belong to the system milestone and must be derived from `response`.
- No passivity, losslessness, reciprocity, causality, rationality in any variable, or
  electromagnetic normalization is asserted anywhere in this lane (invariants E.6, E.9).
- `unguardedResponse` outside `solveDomain` is Mathlib's junk inverse and is never a response.
- Literal three-stage associativity of `append` is not proved, and is withheld explicitly in the
  `Hierarchical` module doc as well as here. Everything proved about hierarchical semantics is
  relational and unconditional: `closeBehavior_append`, `flatten_behavior_eq`, and
  `closeBehavior_append_congr` carry no well-posedness, invertibility, or functionality hypothesis
  on either stage.

## Worktree note for other lanes

Seeding this worktree needed no cold build: `cp -Rc <optics-development>/.lake/build .lake/build`
is an APFS clone (about two seconds, no extra disk), and a single `lake-lock build` then confirmed
all 3067 jobs up to date. After merging `optics/development`, `rsync -a --ignore-existing
<optics-development>/.lake/build/ .lake/build/` pulls in only the newly built modules in about a
second, so a sync costs no rebuild either.

## Remaining in this lane

- Literal three-stage associativity of `append`, and the stronger subsystem-reuse statement that
  the inner connection *family* may be replaced by a different family with the same boundary
  relation. Both need the same missing machinery: transport of a `PortConnectionFamily` along an
  equivalence of port families. What is proved instead is
  `PortConnectionFamily.closeBehavior_append_congr`: with both connection families held fixed, the
  flattened relation depends on the inner components only through the inner stage's closed
  relation. The module doc withholds both stronger statements explicitly.
- N5F slice 3 could be strengthened from `ContinuousAt`/`AnalyticAt` at a point to `ContinuousOn`/
  `AnalyticOnNhd` on an open subset of the solve domain; the pointwise forms are what is proved.

## Changes requested to existing modules

None. Nothing in `Physlib/Optics/Network/` needed modification.
