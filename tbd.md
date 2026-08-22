# Optics upstream-readiness ledger

This fork-only file records work that must be resolved before any Optics branch is proposed to
upstream Physlib. It is not part of the proposed public API and should be removed from an upstream
PR unless maintainers explicitly ask to retain it.

## Human obligations

- [ ] A human author has read every changed line and can certify that each definition, statement,
  proof step, and physical interpretation means what it claims, as required by `AI-POLICY.md` 1.7.
- [ ] A human has independently verified every bibliography entry, page range, URL, and claim made
  from a source, as required by `AI-POLICY.md` 2.1.
- [ ] A human has checked the contribution against `AGENTS.md`, `docs/ReviewGuidelines.md`, and
  `docs/ReviewChecklist.md` rather than treating a successful build as certification.
- [ ] All communication with maintainers and reviewers is conducted by the human author, as
  required by `AI-POLICY.md` 3.1.
- [ ] The human author has confirmed the copyright header, author list, commit-signing policy, and
  intended commit history before opening a PR.

## Upstream scope and consultation

- [ ] Discuss the proposed Optics ownership boundary and v0.1 milestone with Physlib maintainers
  and the existing Optics contributors on Zulip.
- [ ] Treat `Physlib/Optics/API-map.yaml` as a domain roadmap. Split the circuit, interface,
  ray-optics, Fourier-optics, and quantum bridges into focused API maps before implementing those
  tracks upstream.
- [ ] Keep upstream PRs small and stackable: roadmap documentation first, modal foundations next,
  then one coherent component or representation per PR.
- [ ] Decide with maintainers whether the scattering wrapper belongs with modal foundations or in
  a separate typed-port PR. It intentionally has no multiplication instance.
- [ ] Rebase every proposed PR onto the then-current `upstream/master` and remove this file from the
  upstream diff.

## Electromagnetic prerequisites

- [ ] Preserve the existing real electromagnetic fields and potentials as foundational. Add a
  proved real harmonic wave to phasor to Jones correspondence instead of an alternative complex
  field foundation.
- [ ] State a harmonic, zero-static-component, zero-mean, or equivalent hypothesis wherever a
  transversality result would otherwise admit an arbitrary constant background.
- [ ] Add homogeneous isotropic constitutive data in Electromagnetism with explicit assumptions
  about dispersion, conductivity, and anisotropy; do not present the first model as universal.
- [ ] Develop the local-domain, oriented-surface, trace or restriction, integral-vector-calculus,
  and electromagnetic boundary-condition APIs needed for reflection, refraction, and waveguides.
- [ ] Prove the bridge from propagating field modes and complex amplitudes to time-averaged
  Poynting flux. Until then, modal power and losslessness are terms internal to the stated
  power-normalization convention, not field-level energy theorems.

## Modal and network semantics

- [x] Use `EuclideanSpace ℂ ι` for finite power-orthogonal amplitude families so the canonical
  norm and inner product are the required `L²` ones.
- [x] Keep one-way `ModeTransform` cascade separate from reflective multiport interconnection.
- [x] Wrap `ScatteringMatrix` without a coercion or multiplication instance, preventing accidental
  use of matrix multiplication as physical feedback composition.
- [x] Define convention-free modal relabeling and unit-complex coordinate rephasing, including
  covariance and preservation of modal power, passivity, and losslessness.
- [ ] Define typed incident and outgoing channels, time-reversed channel pairing, and port
  reference planes before defining reciprocity; coordinate rephasing alone does not supply these
  physical conventions.
- [ ] Add the electromagnetic normalization theorem before equating modal unitary or passive
  predicates with physical losslessness or passivity.
- [ ] Supply an induced operator-norm bridge before expressing passivity as a matrix norm bound;
  the ambient norm inherited by the raw matrix alias is not that operator norm.
- [ ] Represent component behavior independently of invertibility. For network equations
  `b = S a` and `a = C b + E u`, define well-posedness by unique solvability of
  `(1 - C * S) a = E u`; a contraction estimate may be sufficient but must not be necessary.
- [ ] Derive Redheffer and Mason formulas from the common linear-equation semantics rather than
  making either formula the foundational composition rule.
- [ ] Use the delay convention `q = exp (-s * τ) = z⁻¹` and state region-of-convergence,
  nondegeneracy, stability, and dispersion hypotheses explicitly.

## Source and license checks

- [ ] Confirm the license of every Concordia HOL Light script before adapting any implementation.
  Until confirmed, use those scripts only as architectural and theorem-selection references; no
  source text or proof code has been copied into this branch.
- [ ] If code or API ideas are adapted from SAX or another software project, record the exact file,
  revision, and compatible license in the relevant PR.
- [ ] Record exact source pages for Fresnel power factors, total internal reflection, polarization
  conventions, microring dispersion, and every other nontrivial physics claim used in code.

## Validation before an upstream proposal

- [ ] Run `lake exe cache get` and `lake build` from a clean checkout of the proposed branch.
- [ ] Run `lake exe lint_all` and distinguish new failures from failures reproducible on the exact
  upstream base commit.
- [ ] Run `uv run --with pyyaml python3 scripts/api_map_linter.py --repo .` and confirm every
  completed requirement resolves to the declarations it lists.
- [ ] Commit first, then run `./scripts/lint-style.sh`, because the style linter reads committed
  state.
- [ ] Run `git diff --check`, warnings-as-errors elaboration for changed Lean files, forbidden-term
  searches, import-order checks, and spelling checks.
- [ ] Add new physics vocabulary to `scripts/MetaPrograms/spellingWords.txt` only when the spelling
  checker actually reports it.
- [ ] Reproduce and document any repository-wide baseline lint failures instead of presenting them
  as failures introduced by Optics or claiming a completely clean gate.

## Milestone gates

- [ ] Optics v0.1 connects a monochromatic real plane wave to phasor and Jones data, derives Stokes
  data, implements polarizers and wave plates, and proves Malus' law from shared definitions.
- [ ] The interface slice proves reflection, Snell, Fresnel amplitudes, total internal reflection,
  and lossless energy-flux balance from electromagnetic boundary conditions rather than assuming
  those conclusions.
- [ ] Integrated-photonic circuit work receives a focused design review covering ports, behaviors,
  well-posed network elimination, directional couplers, Mach-Zehnder interferometers, microrings,
  transfer functions, and signal-flow calculations before promotion from the fork.
- [ ] Ray optics, Fourier optics, and bosonic quantum-optics bridges remain later milestones with
  separate ownership and dependency reviews.
