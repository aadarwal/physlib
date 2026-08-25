# HANDOFF — lane N5F/N5H

Branch: `optics/n5f-n5h` (branched from `optics/development` at `48015bbf`).
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-n5f-n5h`.
Source parity: Physlib-original. The HOL corpus has no parameterized-compilation or hierarchical
flattening development; there is no source file to mirror and no parity row to claim.

## Files added

| File | Contract | Status |
|---|---|---|
| `Physlib/Mathematics/LinearAlgebra/Matrix/Analytic.lean` | prerequisite | see below |
| `Physlib/Optics/Network/ParameterizedResponse.lean` | N5F slices 1–3 | see below |
| `Physlib/Optics/Network/ParameterizedResponseRegression.lean` | N5F regressions | see below |
| `Physlib/Optics/Network/Hierarchical.lean` | N5H slice 4 | see below |

No existing file was edited. `Physlib.lean`, `Physlib/Optics/API-map.yaml`, `goal.md`, and
`tbd.md` are untouched in every commit.

## Gate evidence

Batch 1 was gated after merging `optics/development` (`7fbad549`) into this branch. The shipped
declaration linters resolve declarations through the `Physlib` module registry, so they cannot see
an unregistered module. To make the gate real, the four registrations below were added to
`Physlib.lean` **temporarily**, the gate was run, and the file was then restored byte-for-byte and
never committed (`git diff Physlib.lean` is empty at the cutoff). With the modules registered:

```
lake build Physlib                → exit 0, no errors, no warnings
lake exe check_file_imports       → exit 0
lake exe sorry_lint               → exit 0
lake exe runPhyslibLinters        → exit 0, "Linting passed for Physlib."
```

Additional checks run directly on the four files: no `sorry`, `axiom`, `native_decide`,
`maxHeartbeats`, or `Lean.ofReduceBool`; every line at most 100 characters; a docstring on every
declaration; `scripts/lint-style.py` clean.

## Registrations the conductor must apply at merge

Add to `Physlib.lean`, in the existing alphabetical blocks:

```
public import Physlib.Mathematics.LinearAlgebra.Matrix.Analytic
public import Physlib.Optics.Network.Hierarchical
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
  inverse, so that regularity can be stated as a function of the parameter. **Never quote this as
  a response without a `solveDomain`/`responseDomain` hypothesis**; use
  `unguardedResponse_eq_blockFormula` (solve gate) or `unguardedResponse_eq_response` (physical
  gate).
- `ParameterizedNetlist.mem_compileBehavior_iff_response` — the `N-10` commutation statement.
- `ParameterizedNetlist.continuousAt_unguardedResponse`,
  `ParameterizedNetlist.analyticAt_unguardedResponse_entry` — regularity, each requiring a
  `solveDomain` hypothesis and a corresponding hypothesis on the stored component entries
  (`ComponentEntriesContinuousAt` / `ComponentEntriesAnalyticAt`).

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
  `.appendExternalChannelEquiv`.
- `HierarchicalNetlist`, `.innerNetlist`, `.flatten`, `.flattenExternalChannelEquiv`,
  `.flattenConnectedChannelEquiv`.
- `FlatNetlist.packagedScattering` and `FlatNetlist.toOrientedModeTransform_packagedScattering`:
  a verified subsystem as one scattering component, gated on well-posedness and using only the
  canonical `Incident.channelEquiv` / `Outgoing.channelEquiv` endpoint pairing.

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
- I.3 row **N-10** — `parameterizedResponseRegression_mem_compileBehavior_iff`.
- I.3 row **N-08** is *not* claimed; see "Remaining in this lane".

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
- N5H flattening asserts nothing yet about semantics; see "Remaining" below.

## Worktree note for other lanes

Seeding this worktree needed no cold build: `cp -Rc <optics-development>/.lake/build .lake/build`
is an APFS clone (about two seconds, no extra disk), and a single `lake-lock build` then confirmed
all 3067 jobs up to date. After merging `optics/development`, `rsync -a --ignore-existing
<optics-development>/.lake/build/ .lake/build/` pulls in only the newly built modules in about a
second, so a sync costs no rebuild either.

## Remaining in this lane

- N5H slice 5, semantics half: equality of hierarchical relational semantics with
  flattened-netlist semantics (goal.md `N-08`). The packaging half of slice 5 is done
  (`FlatNetlist.packagedScattering` and its `toBehavior` agreement). What is missing needs a
  family-level `closeBehavior` -- the singular-safe closure of an abstract oriented boundary
  behavior by a connection family, which `FlatNetlist.behavior` is already definitionally an
  instance of -- together with three bridge identities in amplitude form:

  ```text
  (inner.append outer).partialRouting b
      = inner.partialRouting b + E_in^inner (outer.partialRouting (E_out^inner b))
  (inner.append outer).externalIncidentInjection = E_in^inner ∘ E_in^outer ∘ (external relabel)
  (inner.append outer).externalOutgoingReadout   = (external relabel) ∘ E_out^outer ∘ E_out^inner
  ```

  each provable coordinatewise from `PortConnectionFamily.partialRouting_apply_internal`,
  `partialRouting_apply_of_incident_not_mem_range`, and the `appendChannelEquiv` /
  `appendExternalChannelEquiv` transports in this file.
- N5H slice 6: associativity/invariance of `append` for reusing a verified subsystem.
- N5F slice 3 could be strengthened from `ContinuousAt`/`AnalyticAt` at a point to `ContinuousOn`/
  `AnalyticOnNhd` on an open subset of the solve domain; the pointwise forms are what is proved.

## Changes requested to existing modules

None. Nothing in `Physlib/Optics/Network/` needed modification.
