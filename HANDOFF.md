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
`tbd.md` are untouched.

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

## goal.md rows

- H.3 N5F bullets 1–4 (parameter families with pointwise validity; pointwise compilation to the
  fixed-frequency N4 equations; algebraic solve domain and physical response domain by
  intersection; response function with evaluation commuting with compilation and elimination) and
  bullet 5 (continuity/analyticity under corresponding hypotheses on component data and
  inverse-domain control).
- H.3 N5H bullets 1–2 (hierarchical network; relational flattening preserving typed external
  ports, mode compatibility, and conventions, with no well-posedness assumption to flatten).
- I.3 row **N-10** — `parameterizedResponseRegression_mem_compileBehavior_iff`.

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

## Remaining in this lane

- N5H slice 5: equality of hierarchical relational semantics with flattened-netlist semantics
  (goal.md `N-08`), and functional packaging of a well-posed child as a scattering component.
  The three bridge identities this needs, in amplitude form, are

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
