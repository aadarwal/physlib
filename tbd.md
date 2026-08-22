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
- [ ] Propose `Physlib.Mathematics.MatrixRank` as a neutral prerequisite PR, independently of
  Optics. Its finite-rank criteria support the Poincare classification but are not optical facts.
- [ ] Propose `Physlib.Mathematics.LinearAlgebra.Matrix.SelfAdjoint` as a neutral prerequisite PR,
  independently of deterministic Mueller optics. Preserve
  `Lorentz.SL2C.toSelfAdjointMap'` as a compatibility alias and do not introduce a Relativity
  import into Optics.
- [ ] Preserve the Poincare work as reviewable stacked concepts: normalized closed-ball
  equivalences first, determinant/rank boundary-versus-interior classification second, and the
  unit-Jones global-phase quotient third. The combined fork history is intentionally broader than
  any single proposed upstream PR.
- [ ] Split the 583-line fork-side `JonesPoincare` implementation before an upstream proposal:
  normalized unit-Jones action, coherency, and exact phase fibers first; constructive sphere
  representatives, quotient equivalence, and canonical-axis regressions second. Keep the private
  algebraic charts out of the public API.
- [ ] Preserve deterministic Mueller work as reviewable stacked concepts: neutral self-adjoint
  congruence; Jones scaling/unitarity and minimal Pauli/Stokes/coherency bridges; transported raw
  Mueller action and commuting squares; trace/reality; identity/cascade/scalar algebra; unitary
  consequences; and convention regressions. The combined fork milestone is intentionally larger
  than one upstream PR.
- [ ] Preserve ideal-linear-polarizer work as reviewable stacked concepts: angle-parametrized
  linear Jones states and overlap; rank-one Jones projection and transmission/extinction;
  contraction, sequential action, and Malus' law; then coherency/Stokes/Mueller connections and
  convention regressions. The combined fork milestone is intentionally larger than one upstream
  PR, and the neutral `MatrixRank` prerequisite should land first.
- [ ] Preserve ideal-retarder work as a reviewable stack: rotated linear-basis coordinates and the
  equal-amplitude relative-phase family; raw Jones retarder phase, spectral matrix, algebra,
  unitarity, and action; wave-plate specializations; canonical regressions; then a separate
  coherency/Stokes/Mueller bridge. Do not import the sibling polarizer implementation merely to
  reuse its private projector proof structure.
- [ ] Treat a topological upgrade of the Jones phase quotient as a separate design and proof
  package. Do not call the algebraic equivalence a homeomorphism or assert a continuously varying
  global Jones representative without the required quotient-topology and continuity theorems.
- [ ] Decide with maintainers whether the scattering wrapper belongs with modal foundations or in
  a separate typed-port PR. It intentionally has no multiplication instance.
- [ ] Rebase every proposed PR onto the then-current `upstream/master` and remove this file from the
  upstream diff.

## Electromagnetic prerequisites

- [ ] Human-check that E0 changes only the public exposure boundary: the existing
  `gaussLawElectric`, `gaussLawMagnetic`, `ampereLaw`, and `faradayLaw` declarations and proofs
  remain unchanged. Certify their present scope as pointwise, potential-derived, three-dimensional
  laws with free-space constants and allowed sources, not material-medium, integral, or boundary
  equations.
- [ ] Preserve the existing real electromagnetic fields and potentials as foundational. Add a
  proved real harmonic wave to phasor to Jones correspondence instead of an alternative complex
  field foundation.
- [ ] State a harmonic, zero-static-component, zero-mean, or equivalent hypothesis wherever a
  transversality result would otherwise admit an arbitrary constant background.
- [ ] Human-check E1a's homogeneous isotropic constitutive data and its explicit exclusions for
  dispersion, conductivity, anisotropy, inhomogeneity, nonlinearity, and material loss; do not
  present the first model as universal.
- [ ] Confirm E1a's temporary raw-real convention: all constants and fields use one fixed coherent
  rationalized unit system, physical dimensions are not encoded, and the `E`/`D`/`B`/`H` role
  abbreviations are definitionally equal rather than type-safe field kinds. Confirm that `ε` and
  `μ` denote absolute material constants rather than relative permittivity and permeability. A
  later dimensional refactor must not be described as already enforced here.
- [ ] Preserve `FreeSpace` as the authoritative vacuum constants API and use only its one-way
  specialization to `HomogeneousIsotropicMedium`. Do not promote the unconstrained legacy
  `EMSystem`, extend a material medium from `FreeSpace`, or revive the deleted bundled
  `OpticalMedium`/`ChargedMedium` architecture.
- [ ] Split E1a before an upstream proposal: semantic field roles, medium constants, constitutive
  maps, and `IsConstitutive` first; wave speed, impedance, refractive indices, and the `FreeSpace`
  parameter specialization second. Stack the macroscopic predicate and the E0 vacuum bridge as
  separate later PR concepts.
- [ ] Human-check E1b's rationalized macroscopic equations and signs: `div D = ρFree`, `div B = 0`,
  `curl H = JFree + ∂ₜ D`, and `curl E = -∂ₜ B`. Confirm that free sources are the only explicit
  right-hand-side material sources, while bound polarization and magnetization response remains
  absorbed into `D` and `H`; source-free means only that the free sources vanish.
- [ ] Human-check that joint field differentiability is intentionally part of
  `IsMacroscopicMaxwell`: Physlib's differential operators are totalized, and the hypotheses are
  what justify the proved divergence, curl, and time-derivative superposition laws.
- [ ] Human-check the one-way E0 bridge and its scaling: `D = ε₀ E`, `H = μ₀⁻¹ B`,
  `ε₀ (ρ / ε₀) = ρ`, and `μ₀⁻¹ (μ₀ J + μ₀ ε₀ ∂ₜ E) = J + ∂ₜ (ε₀ E)`. Confirm that E0's Lorentz
  current is being interpreted as the free source in this specialization and that no converse,
  global-potential reconstruction, gauge reconstruction, or free/bound decomposition is claimed.
- [ ] Keep E1b's upstream concepts separate: magnetic-field regularity in Kinematics, the generic
  macroscopic predicate and fixed-medium connector in `MacroscopicMaxwellEquations`, and the
  potential-derived vacuum result in `MacroscopicMaxwellBridge`.
- [ ] Independently verify the Jackson, *Classical Electrodynamics*, third edition, section 6.6
  citation used by the E1b module docs before any upstream PR, as required by `AI-POLICY.md`.
- [ ] Human-check E2a's off-shell carrier design: angular frequency `ω > 0` and scalar wave number
  `κ > 0` are independent, propagation sign is represented only by `direction`, phase velocity is
  `ω / κ`, and the classical wave-equation results are at that phase velocity rather than at the
  supplied medium's wave speed. Material dispersion is deliberately a later predicate.
- [ ] Human-check the E2a phase and quadrature convention:
  `θ = ω t - κ ⟪x, direction.unit⟫`,
  `E = cos θ • electricReal - sin θ • electricImag`, and therefore a later complex amplitude is
  `electricReal + I * electricImag` under `Re (z * exp (I * θ))`. Confirm that omitting a separate
  phase offset is intentional because it is redundant with a rotation of the two quadratures.
- [ ] Human-check that E2a builds in the propagating candidate
  `B = (κ / ω) • (n × E)` and must not later describe that relation as independently derived from
  Maxwell equations. Electric transversality is a separate predicate, magnetic transversality is
  structural, zero electric amplitude remains allowed, and the converse dispersion theorem uses
  an explicit nonzero-amplitude hypothesis.
- [ ] Human-check E2b's positive material branch and constructor: `IsDispersionMatched` means
  exactly `ω = κ * medium.waveSpeed`, `inMedium` treats angular frequency as primary and defines
  `κ = ω / medium.waveSpeed`, and the positivity hypotheses—not an unsigned square-root
  convention—select the positive branch.
- [ ] Human-check E2b's differential signs and cross-product order: magnetic induction remains the
  built-in `B = (κ / ω) n × E`; Faraday and magnetic Gauss are structural; electric Gauss requires
  transversality; Ampère--Maxwell additionally requires material dispersion; and the derived
  on-shell relations are `B = v⁻¹ n × E` and `H = Z⁻¹ n × E`.
- [ ] Human-check the E2b converse boundary: Maxwell forces transversality even when both electric
  quadratures vanish, but it forces dispersion only under
  `electricReal ≠ 0 ∨ electricImag ≠ 0`. With both quadratures zero, all constructed fields vanish
  and solve Maxwell for arbitrary positive `ω` and `κ`, so no stronger converse is valid.
- [ ] Human-check E2c's proof-bearing frame orientation: for propagation vector `n`, the ordered
  axes satisfy `axis 0 × axis 1 = n`, hence `n × axis 0 = axis 1` and
  `n × axis 1 = -axis 0`. Confirm that this is only mathematical orientation and does not assign
  observer-dependent right/left circular names.
- [ ] Human-check E2c's complex-amplitude convention and coherent phase law:
  `A = electricReal + I * electricImag`, realization is
  `Re (A * exp (I * θ)) = cos θ • electricReal - sin θ • electricImag`, and multiplying every
  Jones coordinate by `exp (I * φ)` translates all realized fields by time `φ / ω`. Check the
  positive/negative-`I` algebraic sign regressions against the existing provisional third-Stokes
  convention before assigning handedness names.
- [ ] Human-check E2c's material field formulas: `B = v⁻¹ n × E` is represented by Jones
  coordinates `(-J₁, J₀)`, `H = Z⁻¹ n × E`, and the connected constructor proves the
  complete source-free macroscopic Maxwell predicate for the supplied homogeneous isotropic
  medium without a nonzero-amplitude hypothesis.
- [ ] Human-check E2c's fixed-vacuum regression frame and signs: propagation is coordinate zero,
  Jones axes are coordinates one and two, the material wave number reduces to the supplied
  positive `κ`, carrier phases agree, and the complete `E` and `B` fields equal the existing
  potential-derived `harmonicWaveX` fields. The comparison intentionally proves field equality,
  not equality of potentials or gauges.
- [ ] Human-check E2d's non-normal incidence convention: for oriented interface normal `n` and
  propagation direction `k`, `IsNonNormalIncidence` means exactly `n × k ≠ 0`,
  `s = normalize (n × k)`, `p = k × s`, and Jones axes are ordered `(s, p)`. This includes
  grazing geometry, excludes both parallel and antiparallel normal incidence, and does not by
  itself classify a wave as incident, reflected, or transmitted.
- [ ] Human-check that E2d's Jones coordinates are full unit-vector electric-field amplitudes, not
  tangential `p` amplitudes. The exact `(3/5, 0, 4/5)` regression gives
  `s = (0, 1, 0)` and `p = (-4/5, 0, 3/5)`. With a selected `(0, 1, 0)` tangent at normal
  incidence, forward and backward propagation share `s` while their `p` axes are negatives. A
  later full-vector Fresnel convention therefore generally has the normal-incidence scalar sign
  `r_p = -r_s` even though the physical reflected tangential vectors have the same sign.
- [ ] Before E4/E5, confirm that the planar-interface normal points from incident medium 1 toward
  transmitted medium 2, and independently confirm whether every public Fresnel `p` coefficient
  scales a full electric-vector axis or a tangential component. The present incidence-frame API
  fixes neither interface-side roles nor a tangential-amplitude conversion.
- [ ] Human-check E2e's complex-wavevector convention: the carrier uses
  `exp (I * (ω t - K·x))`, the pairing `K·x` and dispersion square `K·K` are complex-bilinear
  rather than Hermitian, `K = q - I a`, and `a = α n` with `α > 0` gives amplitude decay
  `exp (-α u)` at increasing positive-normal depth. With `q ⊥ n`, confirm that the bilinear
  square is `K·K = ‖q‖² - α²`, and independently check that the exact
  `(waveNumber, 0, -I * decayRate)` regression pins the intended sign.
- [ ] Preserve E2e's current semantic boundary: `PositiveNormalDecayWaveVector` proves local decay
  geometry only. It does not choose an interface half-space or square-root branch, label a field
  transmitted or outgoing, prove complex Maxwell equations, or assign power flow. Split a future
  upstream stack into complex-vector/bilinear foundations, phase--attenuation spatial factors,
  positive-normal decay, and coordinate regressions.
- [ ] Split the fork-side E2a implementation before an upstream proposal: carrier data,
  geometry, and electric realization first; compatible magnetic induction and transversality
  second; regularity, wave equations, and the homogeneous-medium constitutive bridge third.
  Preserve E2b's fork-side split into `Dispersion`, forward `Maxwell`, and `Converse`; propose those
  as separate upstream concepts after the intrinsic profile-calculus additions to `Basic`. Then
  place complex phasor/Jones realization in an Optics-owned bridge. Do not add physical-power,
  handedness, evanescence, finite-beam, group-velocity, potential, or gauge claims to E2a/E2b.
- [ ] Split E2c into reviewable upstream concepts: scalar coherent-phase realization laws in
  `Polarization.Basic`; oriented local frame geometry and Jones embedding in `Polarization.Frame`;
  the material-wave connector and its Maxwell endpoint; then the fixed-vacuum regression. Decide
  with maintainers whether the larger frame file should be split again. Do not add a global
  continuously varying frame over the direction sphere, inverse coordinate extraction, frame
  rotation covariance, electromagnetic power, gauge reconstruction, evanescence, or circular
  handedness to this upstream slice; design each as a separate follow-up where needed.
- [ ] Split E2d before an upstream proposal: the neutral `Space.inner_cross_cross` identity first;
  `PolarizationFrame.ofAxisZero` and its two projection lemmas second; the non-normal incidence
  predicate, axes, frame, and Jones decomposition third; and exact sign regressions last. Do not
  introduce an interface point, half-space, incoming/outgoing predicate, reflected or transmitted
  direction, Fresnel coefficient, power claim, or canonical normal-incidence tangent choice in
  these geometry PRs.
- [ ] Develop the local-domain, oriented-surface, trace or restriction, integral-vector-calculus,
  and electromagnetic boundary-condition APIs needed for reflection, refraction, and waveguides.
- [ ] Prove the bridge from propagating field modes and complex amplitudes to time-averaged
  Poynting flux. Until then, modal power and losslessness are terms internal to the stated
  power-normalization convention, not field-level energy theorems.

## Polarization conventions

- [ ] Human-check the third Stokes-coordinate sign against the selected optics reference, the
  existing `Re (z * exp (I * (ωt - kx)))` carrier convention, and Jones coordinate order.
- [ ] Record whether the observer looks along propagation or into the beam before assigning
  right/left circular names. Until then use only “positive/negative third Stokes coordinate.”
- [ ] Verify which algebraic positive/negative-`I` quadrature Jones state receives each right/left
  circular name, using reconstructed real-field rotation, before completing regression P-04b.
- [ ] Human-check the P4 trace factor, Stokes-ordered Pauli permutation, Jones cascade direction,
  and `diag(1, I)` regression before proposing any deterministic Mueller PR. Keep the current
  algebraic names until the observer and retarder-axis conventions are certified.
- [ ] Human-check the P5a convention that a linear Jones axis is
  `(cos θ, sin θ)`, positive angle runs from the first declared Jones coordinate toward the
  second without an observer-direction claim, the raw Jones state changes sign under `θ + π`,
  and its projector is `π`-periodic.
- [ ] Human-check the signed coherent factor `cos (input - analyzer)`, the `M.comp N` cascade order,
  the doubled Stokes direction `(cos (2θ), sin (2θ), 0)`, the induced Mueller factor `1 / 2`,
  and the exact `π / 4` half-intensity regression before proposing any polarizer PR.
- [ ] Human-check P6a's retarder convention against a page-verified optics source and the existing
  carrier realization: `axis` is a reference principal axis with eigenvalue one, its orthogonal
  axis has `linearRetarderPhase retardance = exp (-I * retardance)`, and positive retardance is a
  lag because realization changes `carrierPhase` to `carrierPhase - retardance`.
- [ ] Human-check that `quarterWavePlate` means positive retardance `π / 2` and therefore gives
  `diag(1, -I)` at zero axis, while `negativeQuarterWavePlate` gives `diag(1, I)`; retain the
  positive/negative-`I` quadrature names until the observer convention assigns handedness.
- [ ] Decide with maintainers whether the common-phase gauge with reference-axis eigenvalue one is
  the desired public Jones API. It deliberately omits physical propagation/reference-plane phase;
  do not replace it by a determinant-one half-angle formula on `Real.Angle`, whose half is not
  globally canonical.
- [ ] Do not rename P6a's `axis` to `fastAxis` or `slowAxis` until material birefringence,
  propagation direction, and sign conventions are human-certified. Independently check P6b-1's
  algebraic polarization block: at zero axis, positive retardance must send
  `(S₁, S₂, S₃)` to
  `(S₁, cos δ * S₂ + sin δ * S₃, -sin δ * S₂ + cos δ * S₃)`;
  positive quarter-wave retardance must give `(S₁, S₃, -S₂)`; and the negative
  quarter-wave plate must agree with the established `diag(1, I)` Mueller regression. The Lean
  API records these coordinates but deliberately withholds an observer-oriented
  Poincare-sphere rotation claim until this gate is certified.
- [ ] Human-check P6b-2's ordered system convention: in `M.comp N`, `N` acts first, so
  `(quarterWavePlate 0).comp (linearPolarizer (pi / 4))` sends the horizontal unit Jones input to
  `unitEqualAmplitude` times `minusIQuadrature`. This simultaneously checks the positive analyzer
  amplitude and negative third Stokes coordinate; it is not yet a circular-handedness, irradiance,
  detector-power, or modal-power statement.

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
- [ ] Keep P5a's contraction and Malus results explicitly about squared raw Jones intensity and
  raw Stokes coordinates. No irradiance, Poynting-flux, normalized-modal-power, or electromagnetic
  passivity corollary exists until P5b/E3b supplies the field-normalization bridge.
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

- [ ] Create and human-verify the source-to-Lean parity ledger required by `goal.md` B.5. Every
  mandatory row must record a source theorem/definition and page, public Lean target, regression
  ID, convention map, hypothesis delta, and proof status.
- [ ] Confirm the license of every Concordia HOL Light script before adapting any implementation.
  Until confirmed, use those scripts only as architectural and theorem-selection references; no
  source text or proof code has been copied into this branch.
- [ ] If code or API ideas are adapted from SAX or another software project, record the exact file,
  revision, and compatible license in the relevant PR.
- [ ] Record exact source pages for Fresnel power factors, total internal reflection, polarization
  conventions, microring dispersion, and every other nontrivial physics claim used in code.
- [ ] Audit field versus power attenuation, amplitude versus power coupling coefficients, phasor
  time sign, chain direction and port ordering, `z` versus `q = z⁻¹`, dB/logarithm conventions,
  rejection-ratio parentheses, and strict versus non-strict stability inequalities.
- [ ] Record every source hypothesis strengthened, corrected, or rejected by a Lean theorem.
- [ ] Repair or independently reverify the vector-calculus Zulip reference in
  `Physlib/Optics/API-map.yaml`: its current `Physlib` archive path is stale and the cited message
  range was not recovered from the older `PhysLean` archive during the E1 audit.
- [ ] Replace source decimal examples by exact values or certified intervals before using them as
  regression evidence.

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
- [ ] Repair or update `scripts/MetaPrograms/spelling.lean` for the repository's Lean 4.33 string
  API before relying on the official spelling executable. It currently fails at
  `Char.isWhitespace`/`String.Slice`; P4 and E2e used exact differential emulations and added only
  the resulting new vocabulary. E2e's differential added `alpha`, `attenuation`,
  `attenuationvector`, `decayrate`, `envelope`, `kappa`, `omega`, `phasevector`, and `wavenumber`.
- [ ] Reproduce and document any repository-wide baseline lint failures instead of presenting them
  as failures introduced by Optics or claiming a completely clean gate.

## Milestone gates

- [ ] Optics v0.1 connects a monochromatic real plane wave to phasor and Jones data, derives Stokes
  data, implements polarizers and wave plates, and proves Malus' law from shared definitions.
- [ ] The interface slice proves reflection, Snell, Fresnel amplitudes, total internal reflection,
  and lossless energy-flux balance from electromagnetic boundary conditions rather than assuming
  those conclusions.
- [ ] Integrated-photonic circuit work receives a focused design review covering ports, behaviors,
  two-port chain semantics, certified netlist compilation, well-posed network elimination,
  directional couplers, Mach-Zehnder interferometers, physical microring realization, transfer
  functions, coherent/incoherent observables, and signal-flow calculations before promotion from
  the fork.
- [ ] Any integrated-photonics parity claim includes the named DCDR and periodic-cascade/lattice
  suites plus a cross-semantics theorem, not merely generic network infrastructure.
- [ ] R1--R5 is described as a foundational ray/beam milestone unless a separately audited ledger
  includes every named source case study required for extended HOL-suite parity. Fourier optics and
  bosonic quantum-optics bridges remain later milestones with separate ownership and dependency
  reviews.
