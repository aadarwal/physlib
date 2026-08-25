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
- [ ] Split the fork-side Jones boundary scalarization before an upstream proposal: neutral
  complex projection linearity first; common planar-frame geometry second; the stored-point
  material Jones connector third; the four unsolved boundary equations fourth; and the exact
  nonzero-reference-point sign regression last. The combined fork milestone is intentionally
  larger than one upstream PR.
- [ ] Split the fork-side Fresnel amplitude milestone before an upstream proposal: real coefficient
  definitions and denominator-free scalar algebra first; the connected referenced-balance theorem
  second; and exact normal, grazing, zero-field, and nonzero-phase regressions last. Keep the
  reflected-root selection wrapper and all flux results in later coherent proposals.
- [ ] Split the fork-side Fresnel flux milestone before an upstream proposal: the generic harmonic
  zero-phasor helper and material-irradiance rewrite in their existing upstream-owned files first;
  the referenced complex-material-wave local flux bridge second; scalar normal-admittance power
  ratios and channel conservation third; arbitrary-Jones and irradiance balance fourth; and the
  connected separate-wave actual-flux endpoint fifth. Keep each exact regression with the concept
  it checks rather than collecting the regressions into one combined proposal. Keep the now-built
  incident-reflected interference milestone in a later coherent proposal: generic aligned-frame
  cross geometry, instantaneous referenced-field connectors and guarded period replacement,
  pointwise/common-interval normal cancellation, the fixed-frequency superposed-field endpoint,
  and their exact regressions should remain reviewable in that order.
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
- [ ] Human-check E3s against the shared cross-product and curl orientation: for real
  three-dimensional fields the sign is
  `div (f × g) = g · curl f - f · curl g`, and both pointwise differentiability hypotheses are
  needed because the derivative API is totalized. Confirm that the neutral SpaceAndTime result is
  not itself an electromagnetic energy or flux theorem. Before upstreaming E3a, independently
  verify that substituting the macroscopic Maxwell signs gives
  `div (E × H) = -E · JFree - E · ∂ₜ D - H · ∂ₜ B`, with source-free conservation only as a
  corollary after the fixed nondispersive constitutive-law step.
- [ ] Human-check E3a's stored-energy convention and factors: in the fixed positive homogeneous
  isotropic nondispersive model,
  `u = 1 / 2 * (ε E · E + μ H · H) = 1 / 2 * (E · D + B · H)`, and therefore
  `∂ₜ u = E · ∂ₜ D + H · ∂ₜ B`. Confirm that the nonnegativity result depends on the medium's
  strict positivity fields and that no claim is made for lossy, conducting, dispersive,
  anisotropic, inhomogeneous, or nonlinear media.
- [ ] Human-check E3a's local source semantics: only `JFree t x = 0` is needed for pointwise field
  energy conservation, while the named source-free corollary sets both free charge and free
  current to zero. Bound material response remains represented by `D` and `H`. Neither result is
  an integrated conservation law, boundary-flux theorem, time average, irradiance, or modal-power
  statement.
- [ ] Human-check the explicit real-vacuum endpoint derived from source-free `IsExtrema`:
  `u₀ = 1 / 2 * (ε₀ E · E + μ₀⁻¹ B · B)` and `S₀ = μ₀⁻¹ (E × B)`. Confirm the inverse permeability,
  cross-product order, positive divergence sign on the left, zero right-hand side, and absence of
  an extra factor of `c` under the repository's rationalized convention. Zero Lorentz current is
  interpreted as both zero free charge and zero free current.
- [ ] Keep E3a as stacked upstream concepts even though they are integrated on the fork: first the
  generic real-field energy module (with the Maxwell work identity and fixed-medium theorem), then
  the single potential-derived vacuum endpoint in `MacroscopicMaxwellBridge`. Because the generic
  module exceeds the usual 200-line review heuristic including documentation, ask whether its
  sourced-work and constitutive-energy halves should be separate upstream PRs before opening one.
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
- [ ] Human-check E4a's fork-side planar-interface convention before upstreaming:
  `PlanarDielectricInterface` assigns medium 1 to the geometric negative side and medium 2 to the
  geometric positive side, so the stored normal points from medium 1 toward medium 2; equal media
  are allowed. Independently confirm whether every later public Fresnel `p` coefficient scales a
  full electric-vector axis or a tangential component. The interface type intentionally fixes only
  medium-side assignment, not wave roles, boundary laws, or a tangential-amplitude conversion.
- [ ] Human-check E4a's pointwise macroscopic boundary convention before upstreaming. For the
  stored normal `n` from the negative trace to the positive trace, the fork uses
  `n · (D_positive - D_negative) = surfaceCharge` and
  `n × (H_positive - H_negative) = surfaceCurrent`, with continuous tangential `E` and normal `B`.
  The surface sources are free electric charge and an intrinsically tangent free electric current;
  no magnetic surface sources are modeled. Setting them to zero proves continuity of tangential
  `E` and `H` and normal `D` and `B`, but does not remove bound polarization charge, bulk sources,
  or material response. `PlanarMacroscopicTrace` is pointwise carrier data obtained honestly from
  globally defined fields, not yet an analytic one-sided trace, and these local laws are stipulated
  rather than derived from integral Maxwell equations until E4b.
- [ ] Human-check E4a's three-wave boundary assembly before upstreaming. Confirm that the three
  complex-carrier candidates are off shell and retain independent positive frequencies and complex
  wave vectors. `negativeTrace` is the pointwise plane restriction of the globally defined
  incident-plus-reflected fields, with `D` and `H` formed in the negative medium;
  `positiveTrace` is the corresponding transmitted trace in the positive medium. These are not
  half-space restrictions or analytic one-sided traces. The role words are labels only, and the
  absence of a positive-side incoming slot does not establish one-sided illumination. The local
  predicates stipulate rather than derive the macroscopic laws. If
  `reflected.electricAmplitude = 0`, its frequency and wave vector remain unconstrained dummy data,
  so every later reflected-conservation result must retain the zero-amplitude disjunction. Confirm
  that the zero-free-surface-charge joint electric consequence combines exactly tangential `E` and
  scalar normal `D`, with incident plus reflected in the negative medium equal to transmitted in
  the positive medium. The free surface current remains arbitrary because neither magnetic law is
  used. Its boundary-character form must use each wave's independent exponent and stored-point
  referenced amplitude; it proves no noncancellation, exponent equality, or conservation by itself.
- [ ] Human-check the neutral oriented-affine-hyperplane convention before assigning media. Its
  stored normal points from the geometric negative side toward the positive side; the positive
  side normal is `n`, the negative side normal is `-n`; signed normal coordinate is positive on
  the positive side; the carrier is contained in both closed half-spaces and neither open half-space.
  The tangent submodule is exactly the kernel of the real-linear normal component, and its bundled
  projection agrees definitionally with the existing explicit tangential projection. Confirm that
  two vectors have equal tangential projections exactly when their real inner products agree
  against every element of that tangent submodule; the universal quantifier is essential, and
  normal components remain invisible. The geometry itself assigns no incident, reflected,
  transmitted, outgoing, decay, or power role. Its immediate E5a consumer uses
  `Time × plane.tangentSubmodule` as the real module underlying an interface exponent functional,
  with the time probe `(1, 0)` recovering the positive angular frequency.
  Add a Mathlib `AffineSubspace`/surface-measure bridge only when an actual trace or integration
  consumer needs it; the present carrier is deliberately the exact zero set used by pointwise
  boundary laws.
- [ ] Human-check the neutral side-relative angle and real vector-reflection conventions before
  upstreaming. `Side.opposite` must exchange the positive and negative side normals, and
  `angleToSide side v` must use Mathlib's unoriented Euclidean angle between `v` and the unit
  normal pointing into `side`. Confirm the deliberate total convention that a zero vector has
  angle `π / 2`; no physical direction may be inferred from that value. Verify the cosine and sine
  identities against respectively the signed normal component and tangential-projection norm.
  Confirm that `vectorReflection` preserves the tangential projection and norm, negates the normal
  component, is involutive, sends each side normal to the opposite side normal, and preserves the
  side-relative angle only after the reference side is exchanged. This neutral geometry assigns no
  wave label, medium, ray, group velocity, energy flux, outgoing condition, irradiance, or power.
- [ ] Human-check E2e's complex-wavevector convention: the carrier uses
  `exp (I * (ω t - K·x))`, the pairing `K·x` and dispersion square `K·K` are complex-bilinear
  rather than Hermitian, `K = q - I a`, and `a = α n` with `α > 0` gives amplitude decay
  `exp (-α u)` at increasing positive-normal depth. With `q ⊥ n`, confirm that the bilinear
  square is `K·K = ‖q‖² - α²`, and independently check that the exact
  `(waveNumber, 0, -I * decayRate)` regression pins the intended sign.
- [ ] Human-check the neutral complex-wave-vector hyperplane decomposition before using it for
  interface phase matching. Confirm that the normal scalar is the complex-bilinear pairing
  `ofReal(n) dot K`, the tangential projection is `K - (ofReal(n) dot K) ofReal(n)`, and their sum
  recovers `K`. For `K = q - I a`, confirm that projection produces the complexification of the
  real tangential projection of `q` minus `I` times that of `a`. Confirm that equality against
  every real tangent displacement is equivalent to equality of these complex tangential
  projections and therefore carries both tangential phase and attenuation data. Finally verify
  that `K` and `K + c ofReal(n)` have identical tangential projections for arbitrary complex `c`;
  tangent data cannot imply full wave-vector or normal-component equality. Assign no medium,
  interface side, propagation, dispersion, square-root branch, observable, or power meaning here.
- [ ] Human-check the neutral complex hyperplane-reflection API before upstreaming. Confirm that
  its square decomposition uses the complex-bilinear pairing, never the Hermitian norm; reflection
  negates the oriented complex normal component while preserving the complex tangential projection
  and bilinear square; and applying reflection twice recovers the original vector. Under
  `K = q - I a`, confirm that its normal component is `q_normal - I a_normal`, reflection applies
  the real formula `v - 2 v_normal n` separately to `q` and `a`, and therefore negates both real
  normal components. In particular, a positive attenuation normal component becomes negative
  under neutral reflection, so reflection alone does not select a decaying branch.
  Confirm that equal tangential projections and bilinear squares imply exactly the nonexclusive
  alternative of equal vectors or reflected vectors. At zero normal component, including grazing
  real geometry, both alternatives coincide. Do not interpret this algebraic classification as
  selecting an incident, reflected, outgoing, decaying, medium-specific, or positive-power root.
- [ ] Human-check the complex material normal-shell identity before upstreaming. Starting from the
  bilinear dispersion equation and the neutral hyperplane square decomposition, confirm exactly
  `K_normal ^ 2 = epsilon * mu * omega ^ 2 - K_tangent dot K_tangent`. The material coefficient is
  embedded from the reals while the tangential square remains complex-bilinear. This equation
  leaves the two square-root choices unresolved; assign no interface side, incident, transmitted,
  outgoing, evanescent, or power meaning until later hypotheses make that choice.
- [ ] Human-check the neutral real-radicand normal-root alternatives before upstreaming. Confirm
  that a nonnegative radicand gives `K_normal = ±√c`, a zero square forces the unique zero normal
  component, and a nonpositive radicand gives `K_normal = ±I * √(-c)`. The weak inequalities are
  deliberate and both displayed alternatives coincide at zero. This package does not use the
  principal complex square root, prefer either sign, or prove that an interface radicand is real.
  With `K = q - I a`, future positive-side decay must select the negative-imaginary root
  `-I * √(-c)`, not its positive-imaginary partner; this sign is only a future certification gate,
  not a conclusion of the neutral package. Do not call these roots propagating, grazing,
  evanescent, transmitted, outgoing, or power-carrying before their separate hypotheses land.
- [ ] Human-check strict side-relative attenuation direction and directed normal-root selection
  before upstreaming. For the stored normal from the negative side to the positive side, confirm
  that attenuation direction uses the real attenuation vector `a` in `K = q - I a`, so positive-
  side attenuation means `a_normal > 0` and therefore `Im K_normal < 0`. When `K_normal ^ 2 = c`
  is real, strict phase direction must force `c > 0`, zero attenuation normal component, and
  `K_normal = side.sign * √c`; strict attenuation direction must force `c < 0`, zero phase normal
  component, and `K_normal = -I * side.sign * √(-c)`. In particular, positive-side attenuation
  selects `-I * √(-c)` and negative-side attenuation selects `I * √(-c)`. Confirm that this proves
  neither zero tangential attenuation nor an interface role, carrier limit, evanescence, outgoing
  radiation condition, group velocity, Poynting-flux direction, or positive-power statement.
- [ ] Human-check the phase-matched dispersion consequences before upstreaming. Confirm that they
  use `IsElectricPhaseMatched` alone, not the referenced electric amplitude balance. Incident and
  transmitted material shells are direct premises; the reflected shell is required only under
  nonzero reflected electric amplitude so its zero-amplitude wave vector remains dummy data.
  Confirm the transmitted-minus-incident squared normal-component sign and positive-minus-negative
  material contrast. In the active reflected branch, confirm the exhaustive but nonexclusive
  alternative `K_reflected = K_incident` or `K_reflected = reflection K_incident`. Do not remove the
  same-vector continuation root without a separate side or outgoing condition, and do not call the
  complex tangential equality an angular Snell law or infer a transmitted square-root, decay,
  evanescence, irradiance, or power result.
- [ ] Human-check the transmitted real-radicand reduction before upstreaming. Confirm that complex
  tangential phase matching decodes into equality of both real tangential phase and attenuation
  projections. Under the explicit hypothesis that the incident tangential attenuation projection
  is zero, verify
  `K_transmitted,normal ^ 2 = ε₂ μ₂ ω_incident ^ 2 - ‖q_incident,tangential‖ ^ 2`.
  This hypothesis deliberately does not require the incident normal attenuation, or the whole
  incident attenuation vector, to vanish. Confirm also that material dispersion alone does not
  make the tangential bilinear square real: whole-vector phase--attenuation orthogonality can be
  balanced between tangential and normal parts. Do not infer a radicand sign, select a transmitted
  root, or use propagating, critical-angle, evanescent, side-decaying, outgoing, TIR, irradiance, or
  power language until the corresponding later hypotheses and results land.
- [ ] Human-check the transmitted direction-selected normal-root application before upstreaming.
  Confirm that zero incident tangential attenuation is transported by phase matching to the
  transmitted candidate. With a separately supplied transmitted phase direction into the
  geometric positive side, verify that the real radicand is forced positive, the entire
  transmitted attenuation vector is zero, and the normal root is `+√c`. At zero radicand, verify
  the unique zero normal root, zero phase normal component, and zero whole attenuation without a
  strict direction premise. With a separately supplied transmitted attenuation direction into the
  positive side, verify that the radicand is forced negative, the phase normal component is zero,
  and the normal root is `-I * √(-c)` for the convention `K = q - I a`. Neither direction follows
  from the transmitted label, and these results classify only an already supplied candidate. Do
  not infer existence, an angle or critical angle, evanescence, outgoing behavior, TIR,
  irradiance, or power from these root statements. Spatial scaling is supplied only by the
  separately named carrier and field results below.
- [ ] Human-check the neutral hyperplane-normal spatial-scaling laws before upstreaming. For the
  carrier convention `exp (-I * K dot x)` and `K = q - I a`, confirm that displacement by `u` in
  the stored-normal direction multiplies the spatial factor by `exp (-I * u * K_normal)`, that
  `K_normal = -I * α` reduces this to `exp (-α * u)`, and that the general norm factor is
  `exp (-a_normal * u)`. The norm identity deliberately requires neither zero tangential
  attenuation nor zero phase normal component. Confirm that strict attenuation direction into the
  geometric positive side is exactly the positivity needed for convergence to zero as
  `u → +∞`. These are global spatial-factor statements based at an arbitrary point, not a
  half-space support condition. Do not infer a medium, transmitted or evanescent role, outgoing
  behavior, TIR, irradiance, or power.
- [ ] Human-check the hyperplane-normal carrier and transmitted real-field scaling before
  upstreaming. Confirm that the complete carrier inherits the spatial-factor multiplier and that a
  normal root `K_normal = -I * α` gives `exp (-α * u)` under displacement by `u` times the stored
  normal. Because this multiplier is real, verify that taking componentwise real parts gives the
  same exact scalar law for every constructed real field, including the transmitted `E` and `B`
  fields at `α = √(-c)`. The supplied positive-side attenuation direction forces `c < 0`, hence a
  strictly positive rate. The identities hold at an arbitrary base point and for every real `u`;
  negative `u` gives growth. They do not impose one-sided support or prove a nonzero field,
  evanescent/outgoing status, TIR, irradiance, or power decay.
- [ ] Human-check strict phase-directed reflected-root selection before upstreaming. For the stored
  normal from the negative to the positive side, confirm that `IsPhaseDirectedInto .positive`
  means a strictly positive phase-vector normal component and `.negative` means a strictly
  negative one. This predicate concerns the real phase vector only; it does not assert zero
  attenuation, group velocity, Poynting flux, or an outgoing-power role. Confirm that the incident
  positive-side hypothesis is unconditional while reflected negative-side direction and material
  dispersion are guarded by nonzero reflected electric amplitude, preserving arbitrary dummy
  labels at zero amplitude. In the active branch the opposite strict signs exclude equality with
  the incident wave vector, leaving exact neutral hyperplane reflection. Strictness excludes phase
  grazing; do not replace either strict inequality by a non-strict one. This theorem alone is root
  selection; its separately audited angular interpretation is recorded immediately below.
- [ ] Human-check the planar dielectric phase-angle conventions and guarded law of reflection
  before upstreaming. The incident and transmitted phase vectors are measured from the
  positive-side unit normal, while the reflected phase vector is measured from the negative-side
  unit normal. These are total label-relative measurements, not stored propagation roles, and a
  zero phase vector receives the Mathlib value `π / 2`. Confirm that supplied strict phase
  direction is what places each angle in `[0, π / 2)`. In the angular reflection result, incident
  and reflected dispersion and direction hypotheses must match the existing guarded root-selection
  theorem exactly; nonzero reflected electric amplitude selects neutral hyperplane reflection and
  hence equal phase angles. The zero-amplitude branch must remain explicit because its wave vector
  and angle are arbitrary dummy data. Do not interpret this phase-angle equality as a ray,
  group-velocity, energy-flux, outgoing, irradiance, or power theorem.
- [ ] Human-check the phase Snell stack before upstreaming. Confirm first that complex material
  dispersion plus zero whole attenuation gives `‖q‖ * v = omega` on the positive-frequency and
  positive-wave-speed branches; zero tangential attenuation alone is insufficient. Confirm that
  electric phase matching alone gives
  `sin(theta_i) * ‖q_i‖ = sin(theta_t) * ‖q_t‖` through equality of tangential phase-vector norms,
  including the total zero-vector angle convention. For the material laws, check that the
  transmitted frequency is rewritten to the incident frequency before its explicit nonzero
  cancellation, giving `v_2 sin(theta_i) = v_1 sin(theta_t)` and hence
  `n_1 sin(theta_i) = n_2 sin(theta_t)` for both indices relative to the same supplied homogeneous
  isotropic reference medium. The latter is explicitly relative, not an unqualified absolute
  index. Neither zero attenuation nor a phase direction is inferred from phase matching, and the
  identities alone construct or select no transmitted branch and assign no ray, group-velocity,
  outgoing, critical-angle, evanescent, Fresnel, irradiance, or power meaning.
- [ ] Human-check the critical phase-angle geometry before upstreaming. Confirm that medium 1 is
  the negative-side incident medium, medium 2 is the positive-side transmitted medium, and the
  strict contrast `v₁ < v₂` gives the reference-free sine threshold `v₁ / v₂ = n₂ / n₁` in
  `(0, 1)`, with both refractive indices taken relative to one common reference medium. The
  proof-bearing critical phase angle must remain in `(0, π / 2)`; do not use Mathlib's total
  `arcsin` outside the proved contrast domain or silently extend that interior angle to the
  equal-speed endpoint. Separately, confirm that the unconditional sine-critical predicate
  deliberately includes equal-speed grazing and, under strict contrast but without an angle range,
  can represent the supplementary obtuse branch. The three primitive incidence predicates become
  ordinary angle comparisons only under the explicit `[0, π / 2]` incident-angle hypothesis.
  Check that the transmitted normal-radicand factorization and sign equivalences require incident
  negative-medium dispersion and zero whole incident attenuation, but neither phase matching nor
  transmitted dispersion. Finally, the critical connector classifies an already supplied
  electrically phase-matched candidate with negative-medium incident dispersion, positive-medium
  transmitted dispersion, and zero whole incident attenuation: it forces the unique zero normal
  root, zero whole transmitted attenuation, and a nonzero transmitted phase vector tangent to the
  interface. It constructs no candidate and assigns no amplitude activity, outgoing, evanescent,
  TIR, Fresnel, irradiance, or power meaning. For eventual upstream review, split this fork milestone
  into a neutral Space prerequisite, material threshold and radicand-sign geometry, and angle
  interpretation plus the supplied-candidate connector.
- [ ] Human-check the subcritical positive-phase transmitted construction before upstreaming.
  Confirm that the neutral setter changes only the complex normal component and that its real
  specialization is exactly the real tangential-plus-normal decomposition. Under incident
  negative-medium dispersion and zero whole incident attenuation, verify that strict
  sine-subcritical incidence is equivalent to unique existence of a vector with the incident
  complex tangential projection, the positive-medium shell at the incident frequency, zero whole
  attenuation, and strictly positive stored-normal phase component. Check that the total
  `Real.sqrt` construction is certified only after positivity is proved, that the zero-radicand
  critical endpoint remains excluded by strict phase direction, and that full plane-wave
  uniqueness is claimed only after fixing the arbitrary electric amplitude. The supplied-candidate
  bridge must require phase matching, positive-medium transmitted dispersion, zero incident
  tangential attenuation, and supplied positive-side phase direction; it solves no reflected or
  boundary-amplitude data. Do not interpret positive phase direction as a ray, outgoing or group-
  velocity condition, or as positive Poynting flux. For eventual upstream review, split this fork
  milestone into neutral WaveEquation coordinate replacement, vector construction/uniqueness, and
  the arbitrary-amplitude plus supplied-candidate bridge.
- [ ] Human-check the supercritical positive-normal-decay transmitted construction before
  upstreaming. With the carrier convention `K = q - I a`, confirm that setting the stored normal
  component to `-I * √(-c)` gives tangent phase and the purely normal attenuation vector
  `a = √(-c) n`, so negative `c` makes attenuation strictly positive into the geometric positive
  side. Verify that zero incident tangential attenuation plus `c < 0` is exactly equivalent to
  unique existence of the common-complex-tangent, positive-medium-shell, zero-tangential-
  attenuation, positive-side-directed wave vector, and that incident negative-medium dispersion
  plus zero whole incident attenuation are the additional premises needed to replace `c < 0` by
  strict sine-supercritical incidence. Confirm the exact global factor
  `exp (-√(-c) * u)` for the spatial factor, complete carrier, ordinary electric field, and ordinary
  magnetic induction. The nonzero spatial factor and complete carrier grow in magnitude for
  negative `u`; the ordinary fields obey the same scaling but may vanish for the arbitrary stored
  amplitude. None of these identities supplies half-space support. Full carrier uniqueness must
  remain conditional on fixing the otherwise arbitrary electric amplitude. The supplied-candidate
  bridge must require phase matching, positive-medium
  transmitted dispersion, zero incident tangential attenuation, and separately supplied
  positive-side attenuation direction. Do not infer electric transversality, Maxwell satisfaction,
  ray or group velocity, energy-flow direction, outgoing behavior, an evanescent-field role, TIR,
  Fresnel data, irradiance, or power. For eventual upstream review, split the fork milestone into
  the generic negative-imaginary normal setter, the branch-neutral normal-square reduction, the
  vector construction/uniqueness and decay-data bridge, and the arbitrary-amplitude carrier lift.
- [ ] Preserve E2e's current semantic boundary: `PositiveNormalDecayWaveVector` proves local decay
  geometry only. It does not choose an interface half-space or square-root branch, label a field
  transmitted or outgoing, construct real `E`/`D`/`B`/`H` fields, prove the real macroscopic
  Maxwell predicate, or assign power flow. Split a future upstream stack into
  complex-vector/bilinear foundations, phase--attenuation spatial factors, positive-normal decay,
  and coordinate regressions.
- [ ] Human-check the complex-carrier convention and ownership: the carrier is
  `exp (I * omega * t) * exp (-I * K dot x)`, `K = q - I a` therefore decays as
  `exp (-a dot x)`, and `B0 = omega^-1 * (K x E0)` uses `K x E0`, not the reversed cross product.
  The complex amplitude is relative to the selected spatial origin and carrier phase; translating
  an attenuating wave can change its modulus, so its norm is neither an intrinsic Jones intensity
  nor irradiance or power. Physical `E`/`D`/`B`/`H` remain ordinary real fields, and the carrier
  introduces no complex Maxwell-field, potential, or gauge state.
- [ ] Human-check the exact real-wave bridge: `K` is the componentwise complexification of the real
  wave vector, `E0 = electricReal + I * electricImag`, the componentwise-real realization has the
  existing cosine-minus-sine sign, complex-bilinear transversality is equivalent to both existing
  real-quadrature conditions, the complex amplitude is nonzero exactly when at least one real
  quadrature is nonzero, and the derived magnetic amplitude recovers both magnetic quadratures.
  Confirm exact equality of ordinary real `E`/`D`/`B`/`H`, but no equality claim about potentials,
  gauges, power normalization, interface roles, or hidden complex states. Treat the embedded-image
  Maxwell parity as a composition of these primitive bridges, not as evidence that attenuating or
  complex-null-vector modes have been cross-validated against the real carrier.
- [ ] Human-check the complex-carrier calculus signs against the selected convention:
  `partial_t C = I omega C`, `partial_j C = -I K_j C`,
  `div Re(C A) = Re(-I C (K dot A))`, and
  `curl Re(C A) = Re(-I C (K cross A))`. Confirm that the dot product is complex-bilinear, the
  cross-product order is `K cross A`, and the public curl theorem is expressed through the same
  ordinary-real-field realization spine. Joint smoothness and these off-shell identities do not
  by themselves imply transversality, dispersion, any Maxwell equation, an interface or
  evanescent-wave role, or a power normalization.
- [ ] Human-check the complex material shell and all coefficient signs. The definition is the
  complex-bilinear equality `K dot K = epsilon * mu * omega ^ 2`, never the Hermitian norm square.
  For `K = q - I a`, confirm that its real decomposition is exactly `q dot a = 0` and
  `‖q‖ ^ 2 - ‖a‖ ^ 2 = epsilon * mu * omega ^ 2`; the imaginary mixed term is
  `-2 I (q dot a)`. Under electric transversality, confirm
  `K cross (K cross E0) = -(epsilon * mu * omega ^ 2) E0` and, because
  `B0 = omega^-1 (K cross E0)`, `K cross B0 = -(epsilon * mu * omega) E0` with only one remaining
  frequency factor. Matching forces `K` nonzero but permits `E0 = 0`. The exact real-wave bridge
  recovers the existing branch only because that representation already carries positive
  frequency and wave number. No square-root, propagation, interface, evanescent-wave, or power
  role is selected.
- [ ] Human-check the forward complex-carrier Maxwell layer against the selected carrier signs.
  For any realized amplitude `F_A = Re(C A)`, confirm
  `partial_t F_A = F_(I omega A)`,
  `div F_A = Re(-I C (K dot A))`, and
  `curl F_A = F_(-I (K cross A))`. Magnetic Gauss and Faraday must remain off-shell structural
  laws; electric Gauss must use only bilinear electric transversality; Ampere--Maxwell must use
  transversality and material dispersion. Confirm the positive Ampere sign from
  `(-I) * (-epsilon * mu * omega) = I * epsilon * mu * omega`, the real constitutive scalings
  `D = epsilon E` and `H = mu^-1 B`, and all four joint differentiability fields in the bundled
  predicate. Zero electric amplitude is allowed by the forward theorem but in fact solves Maxwell
  even for a mismatched shell, so neither this theorem nor its endpoint is a converse. It assigns
  no interface, outgoing, evanescent-wave, power, potential, or gauge role.
- [ ] Human-check the guarded complex-carrier converse and its degeneracies. Confirm that at every
  fixed spatial point the positive-frequency carrier satisfies
  `C(pi / (2 omega), x) = I C(0, x)` and never vanishes, so the real parts at time zero and one
  quarter-period determine an arbitrary complex scalar. One time sample alone is insufficient.
  Gauss--electric must recover `K dot E0 = 0`; Ampere--Maxwell must recover
  `K cross B0 = -(epsilon * mu * omega) E0`; and, only after assuming `E0 != 0`, vector-scalar
  cancellation may recover `K dot K = epsilon * mu * omega ^ 2`. Confirm that no nonzero `K`,
  propagation, or attenuation hypothesis is used. When `E0 = 0`, all four ordinary real fields
  vanish and solve source-free Maxwell for every positive frequency and complex wave vector, so
  the nonzero guard is necessary for dispersion. The resulting iff characterizes only this
  candidate family; it is not a completeness theorem and makes no interface, outgoing,
  evanescent-wave, power, potential, or gauge claim.
- [ ] Human-check the exact complex-dispersion regression independently of its Lean proofs.
  For `epsilon = mu = 3`, `omega = 1`, and `K = (5, 0, -4 I)`, confirm the bilinear square
  `K dot K = 25 - 16 = 9` while the Hermitian squared norm is `25 + 16 = 41`. Confirm the TE data
  `E0 = (0, 1, 0)`, `B0 = (4 I, 0, 5)` and the TM data
  `E0 = (4, 0, -5 I)`, `B0 = (0, 9 I, 0)`. Both bilinear pairings `K dot E0` must vanish and both
  direct cross products must give `K cross B0 = -9 E0`; the TM Hermitian pairing must instead be
  `40`. This is exact attenuating algebra only: do not assign the fixture an incident,
  transmitted, outgoing, or evanescent-wave role and do not infer Maxwell satisfaction or power.
- [ ] Human-check the exact complex-Maxwell regressions independently of their Lean proofs. With
  `A = exp (-4 x_2)` and `theta = t - 5 x_0`, confirm
  `E_TE = (0, A cos theta, 0)`, `B_TE = (-4 A sin theta, 0, 5 A cos theta)`,
  `E_TM = (4 A cos theta, 0, 5 A sin theta)`, and
  `B_TM = (0, -9 A sin theta, 0)`, and confirm both source-free Maxwell endpoints. At the origin,
  the TM third amplitude `-5 I` must realize as zero at time zero and positive five at time
  `pi / 2`. In the unit medium, confirm that `K = E0 = 0` solves Maxwell but is off shell; that
  `K = E0 = (1, 0, 0)` gives electric-displacement divergence zero at time zero but one at
  `pi / 2` and is not transverse; and that `K = E0 = (1, 0, -I)` has bilinear square zero,
  Hermitian pairing two, `B0 = 0`, satisfies magnetic Gauss, Faraday, and electric Gauss, but at
  the origin has `curl H = 0` and `partial_t D = (0, 0, 1)`, so Ampere--Maxwell fails. The concrete
  real embedding checks only the embedded image of both guarded converses; it does not validate
  the genuinely complex fixtures. Assign none of these data an interface, evanescent-wave,
  irradiance, or power role.
- [ ] Decide during upstream regression review whether to add two optional converse-boundary
  fixtures: `K = 0` with nonzero `E0`, which makes the spatial phase constant while Ampere--Maxwell
  fails, and a purely decaying `q = 0` carrier, which makes temporal rather than spatial sampling
  essential. The present one-phase and complex-null fixtures already cover the required failure
  modes, so neither optional fixture should enlarge the first PR without reviewer demand.
- [ ] Split the fork-side complex-carrier work before an upstream proposal: off-shell carrier,
  algebra, ordinary-real-field realization, transversality, decay, and constitutive results first;
  the exact existing-real-wave bridge second; generic carrier calculus third; bilinear material
  dispersion and its phase/attenuation decomposition fourth; forward Maxwell fifth; the guarded
  converse sixth; and exact algebraic plus ordinary-field TE/TM and converse-boundary regressions
  last. Keep square-root branch choice, interface roles, and power out of these PRs.
- [ ] Correctly layer E4a/E5a/E5b: the primitive time-domain boundary configuration must give
  incident, reflected, and transmitted waves independent positive frequencies and wave vectors,
  then compare ordinary real traces for every boundary point and time. Prove harmonic uniqueness,
  frequency conservation, and tangential-wave-vector conservation under explicit nonzero and
  noncancellation hypotheses before introducing the reduced fixed-frequency complex-amplitude
  problem used for Snell and Fresnel calculations. Never assume common frequency in a premise
  whose conclusion is meant to establish frequency conservation.
- [ ] Human-check E5a's aggregate-collision guard. If the reflected boundary exponent equals the
  incident exponent, harmonic uniqueness sees the combined referenced amplitude `A_i + A_r`, not
  `A_i` alone. A nonzero incident amplitude therefore cannot force the transmitted rate: choosing
  `A_r = -A_i` at the same exponent and zero transmitted amplitude leaves its exponent arbitrary.
  The exact guard is `G_i := A_i + if L_r = L_i then A_r else 0`, the negative-side coefficient at
  the incident exponent. The signed exponent-keyed coefficient identity is unconditional under its
  local-boundary hypothesis; from that identity and `G_i ≠ 0`, label matching derives both
  `L_t = L_i` and `A_r = 0 ∨ L_r = L_i` rather than assuming the latter disjunction. The literal
  guard `A_i + A_r ≠ 0` is unsound when `L_i ≠ L_r = L_t`, `A_i = 0`, and
  `A_r = A_t ≠ 0`: the signed coefficients cancel but the transmitted exponent does not equal the
  incident one.
- [ ] Use finite exponential-character independence for E5a rather than assuming a Fourier
  transform or common period. The neutral layer now proves both uniqueness for finite complex sums
  indexed by complex-valued real-linear functionals and its ordinary-real-sum consequence when all
  supported functionals have strictly positive imaginary rate in one common direction. Its
  `Multiplicative V` source is only the type-level presentation of addition as multiplication
  required by Mathlib's character theorem, not extra structure on `V`. Human-check that the
  physical specialization evaluates the project carrier convention on a unit time translation to
  obtain exactly the positive angular frequency. Strict positivity is essential: a zero functional
  with imaginary coefficient has zero real realization, while conjugate positive/negative-rate
  terms can cancel. Repeated functionals are deliberately aggregated by the `Finsupp` key; the
  theorem does not claim labelwise uniqueness. Before upstream, also confirm whether these
  Mathlib-candidate declarations should continue to extend the `Complex` namespace or move under
  `Physlib` to avoid possible future name collisions. A nonzero electromagnetic boundary amplitude
  should bundle tangential `E` with normal `D` (or an equivalently injective joint trace), because
  tangential `E` alone can vanish for a nonzero field. State
  incident/transmitted conservation under the primitive time-domain noncancellation condition.
  State reflected conservation conditionally as zero reflected amplitude or common frequency and
  tangential wave vector, so Brewster and other zero-reflection cases retain unconstrained dummy
  labels. After conservation, reference reduced complex amplitudes at the interface point using
  the spatial factor; do not compare raw origin-referenced amplitudes across the interface.
- [ ] Human-check E5a's single-wave boundary-exponent convention before upstreaming. For the
  carrier `exp (I * omega * t) * exp (-I * K dot x)` and a real tangent displacement `v`, confirm
  that the exponent is `((omega * t : ℝ) : ℂ) * I - I * (K dot ofReal v)`, that `(1, 0)` has
  imaginary rate exactly the positive angular frequency, and that the carrier at
  `v +ᵥ plane.point` factors as `exp (boundaryExponent (t, v))` times the spatial factor at
  `plane.point`. The affine-point term must remain in the coefficient rather than the real-linear
  exponent, and the pairing must be complex-bilinear rather than Hermitian. Exponent equality gives
  only frequency equality and pairing equality against every real tangent displacement; it does not
  yet give full wave-vector equality, tangential projection equality, phase matching, Snell, or
  conservation. The wave remains off shell and the hyperplane receives no medium, interface-side,
  propagation-role, branch, or power semantics.
- [ ] Human-check E5a's electric-only boundary projection before upstreaming. Confirm that
  `IsPlanarElectricBoundary` contains exactly tangential-`E` continuity and the signed normal-`D`
  jump with supplied free surface charge, and contains neither magnetic law nor free surface
  current. Confirm that every full `IsPlanarMacroscopicBoundary` projects to it, but not conversely.
  For the three-wave dielectric traces at zero free charge, check both directions of the exact
  equivalence with pointwise equality of the actual ordinary-real joint tangential-`E`/normal-`D`
  field data on the plane carrier. The reverse direction must reconstruct only those two electric
  laws. The boundary-character consequence remains confined to the affine plane and proves no
  off-plane field equality, magnetic boundary law, noncancellation, phase matching, or conservation.
- [ ] Human-check E5a's joint electric calculation-amplitude convention before upstreaming. For a
  real unit normal `n`, confirm that the complex coefficient is
  `(E0 - (n dot E0) n, ε * (n dot E0))`, with the first entry stored in ambient complex
  three-space but proved normal-free, and that unit-normal decomposition plus `ε ≠ 0` makes it zero
  exactly when `E0 = 0`. Confirm that stored-point referencing multiplies by
  `spatialFactor K plane.point` and preserves zero because this factor never vanishes. For complex
  `K` this multiplier can change modulus, so it is not pure phase and the referenced coefficient
  is neither canonical nor reference-point independent. Confirm that the ordinary-real plane data
  is componentwise `Re (exp (boundaryExponent) • referencedAmplitude)`. This complex coefficient
  is calculation data, not a physical complex field, full `PlanarMacroscopicTrace`, or observable;
  a nonzero coefficient need not give a nonzero single real sample and does not prevent
  cancellation among equal exponents. The medium supplies `D = ε E` only and assigns no interface
  side or on-shell/Maxwell semantics. Later all-parameter harmonic uniqueness and the exact
  aggregate guard must establish multiwave noncancellation.
- [ ] Human-check E5a's joint-amplitude uniqueness lift before upstreaming. Confirm that it tests
  all three coordinates of the ambient complex vector slot used to store tangential electric
  amplitudes and the scalar normal-`D` coordinate, applies the scalar theorem only after
  componentwise ordinary-real equality for every parameter, and transports the common
  positive-imaginary-rate hypothesis from the original `Finsupp` support to each coordinate
  projection. The generic theorem has no plane and therefore proves no tangency. A nonzero complex
  coefficient may vanish at one real sample; exact repeated exponent functionals are already
  aggregated, and no labelwise, interface, or conservation claim follows.
- [ ] Human-check E5a's planar joint-electric coefficient collision before upstreaming. Confirm
  that incident and reflected referenced amplitudes use the negative-side medium, the transmitted
  referenced amplitude uses the positive-side medium with a negative sign, and exact equal
  boundary exponents aggregate in the `Finsupp`. Confirm both directions between the zero-charge
  two-law electric boundary and the zero coefficient map: the forward direction uses the
  all-parameter boundary-character identity plus positive-rate uniqueness, while the reverse uses
  zero harmonic data plus the exact character-to-electric-trace bridge. A full local boundary
  supplies only the forward implication through its electric projection; its arbitrary surface
  current and magnetic laws are not reconstructed. The zero-map equivalence has no nonzero guard
  and proves no labelwise exponent or amplitude equality: zero labeled contributions impose no
  constraint on their labels, while coincident exponent contributions may cancel. Guarded label
  matching, propagation roles, Fresnel data, and the fixed-frequency reduction remain separate.
- [ ] Human-check E5a's guarded electric label matching before upstreaming. Confirm that its weakest
  boundary premise is the zero-charge two-law electric predicate and its only noncancellation
  premise is the exact conditional incident-key aggregate `G_i ≠ 0`; the reflected
  zero-or-equal-exponent alternative is derived. Confirm the full five-case exponent partition:
  the guard permits only `L_i = L_t ≠ L_r`, forcing `A_r = 0` and `A_t = A_i`, or
  `L_i = L_r = L_t`, forcing `A_t = A_i + A_r`. In particular, a zero reflected electric
  amplitude leaves its dummy exponent unconstrained. The final equality concerns stored-point-
  referenced, medium-dependent joint tangential-`E`/normal-`D` coefficients, not raw electric
  phasors or full electromagnetic amplitudes. A full local boundary inherits the result only
  through its electric projection. Decode matched exponents only into frequency and
  tangent-pairing equality; full wave-vector equality, propagation roles, Maxwell/on-shellness,
  Fresnel data, and power remain absent.
- [ ] Human-check E5a's electric boundary conservation corollaries before upstreaming. Under the
  same zero-charge electric predicate and exact aggregate guard, confirm in both reflected
  branches that the aggregate equals the transmitted stored-point-referenced joint electric
  coefficient; its nonvanishing therefore forces the transmitted electric amplitude to be
  nonzero. This establishes only electric activity, not outward propagation, on-shellness, or
  positive power. Confirm that a full local boundary supplies only wrapper corollaries through its
  electric projection and that no common frequency appears among the premises. Decode transmitted
  exponent equality into incident/transmitted angular-frequency equality and equality of the
  complex-bilinear wave-vector pairing against every real tangent displacement. Preserve the
  reflected conclusion as zero electric amplitude or the analogous two equalities, since its zero
  branch retains arbitrary dummy frequency and wave-vector data. The complex pairing equality
  captures both tangential phase and attenuation data. Confirm that the neutral hyperplane
  characterization packages it exactly as complex tangential-projection equality in the same
  transmitted and reflected branches. The reflected disjunction ranges over the entire frequency-
  and-projection conjunction, needs no separate activity hypothesis, and is not exclusive. Because
  arbitrary complex normal shifts leave the projection unchanged, do not call it full wave-vector
  equality or claim Snell, propagation-root selection, Fresnel, irradiance, or power.
- [ ] Human-check E5a's fixed-frequency electric reduction before upstreaming. Confirm that
  `IsElectricPhaseMatched` requires incident/transmitted equality of angular frequency and the
  full complex hyperplane-tangential wave-vector projection, while the reflected clause remains
  the nonexclusive alternative of zero electric amplitude or those same equalities. The zero
  branch must retain arbitrary dummy frequency and wave-vector labels. Confirm that
  `HasReferencedJointElectricBalance` is exactly `A_t = A_i + A_r`, with `A_t` formed in the
  positive-side medium and `A_i`, `A_r` in the negative-side medium, all referenced at the stored
  plane point; it is not raw electric-phasor equality. Confirm that the exact incident-key
  aggregate guard remains outside `IsFixedFrequencyElectricBoundary` and is spent only when
  deriving the reduced predicates from `IsElectricBoundary 0`. The reverse implication must be
  guard-free through the zero aggregated coefficient map and must reconstruct only tangential-`E`
  and normal-`D` laws. A full local boundary may inherit the forward reduction through its electric
  projection, but there must be no reduced-to-full implication or full-boundary equivalence:
  normal-`B` and tangential-`H` data are absent.
- [ ] Human-check E5a's referenced tangential-magnetic reduction before upstreaming. Confirm the
  project phasor convention `B₀ = ω⁻¹ (K cross E₀)` and the homogeneous-medium constitutive
  convention `H₀ = μ⁻¹ B₀`, including the absence of complex conjugation in both formulas. The
  calculation amplitude must be the complex hyperplane-tangential projection of `H₀`, multiplied
  by the wave's spatial factor at the plane's stored point; for complex `K` this reference factor
  can change modulus. Confirm that zero electric amplitude implies zero tangential `H₀`, while the
  converse is intentionally absent. The primitive premise is a full local boundary with arbitrary
  free surface charge and exactly zero free surface current. Its stored-point reduction needs only
  transmitted frequency equality and the reflected alternative of zero referenced tangential
  `H₀` amplitude or reflected frequency equality. The electric phase-matching wrapper maps its
  `E₀ᵣ = 0` branch to that magnetic-zero branch; its tangential-wave-vector conditions are unused.
  Check that the proof recovers the complex vector from the actual real field at time zero and at
  `π / (2 * ω)`, rather than assuming a complex boundary equation. The exact
  regression uses `K = (5, 0, -4 I)`, `E₀ = (0, 1, 0)`, `B₀ = (4 I, 0, 5)`, and `μ = 3`, giving
  unreferenced tangential `H₀ = (4 I / 3, 0, 0)`. At stored point `(0, 0, 1)`, confirm that
  `K dot p = -4 I`, the spatial factor is `exp (-4)`, the referenced amplitude is
  `(4 exp (-4) I / 3, 0, 0)`, the actual data is zero at time zero, and its value at time
  `π / 2` is `(-4 exp (-4) / 3, 0, 0)`. The zero-reflection branch must keep arbitrary dummy
  frequency and wave-vector labels. This is only a one-way reduction of tangential `H`; it
  neither reconstructs the full boundary nor proves normal-`B` continuity.
- [ ] Human-check the common planar-frame Jones projection before upstreaming. Confirm that the
  plane frame uses `u1 = n cross u0`, every propagation frame is aligned by exact equality of its
  first axis with `u0`, and `chi = n dot k-hat` is the signed normal component of the unit
  propagation direction. With full-vector Jones electric coordinates, tangential projection must
  give `(J0, chi J1)` and the propagation quarter-turn must give `(-J1, chi J0)`. A direction into
  the geometric negative side has negative `chi`, but no incident/reflected/transmitted label
  proves that sign. Grazing `chi = 0` remains valid and no division is allowed.
- [ ] Human-check the plane-referenced material Jones connector before upstreaming. Confirm that it
  fixes `K = ofReal ((omega / v) k-hat)` and the complete stored-point-referenced electric phasor
  `spatialFactor K plane.point` times `E0`, not the raw amplitude at the origin. Verify that its
  derived magnetic-induction phasor is `v inverse` times the propagation quarter-turn, while the
  referenced tangential magnetic-field-strength phasor is `Z inverse` times its tangential
  projection. Here `Z inverse` is the intrinsic material admittance; neither formula uses
  conjugation or a time-average factor. The role-neutral zero guard must constrain only the
  electric amplitude and Jones coordinates to zero; its dummy frequency and wave vector remain
  arbitrary.
- [ ] Human-check the four aligned Jones boundary equations before upstreaming. The transmitted
  connector uses the positive-side medium while incident and reflected connectors use the
  negative-side medium. Confirm exactly
  `T0 = I0 + R0`, `chi_t T1 = chi_i I1 + chi_r R1`,
  `Y2 chi_t T0 = Y1 chi_i I0 + Y1 chi_r R0`, and
  `Y2 T1 = Y1 I1 + Y1 R1`, with `Y = Z inverse`. These lemmas assume only the two referenced
  amplitude balances plus connectors and frame alignments; common frequency and phase matching
  are not hidden premises. They do not divide by signed cosines or amplitudes, scalarize normal
  `D`, reconstruct normal `B`, or yet prove a general Fresnel formula.
- [ ] Human-check the exact Jones-boundary regression before upstreaming. Its nonzero stored plane
  point must make all three canonical real material waves acquire a nontrivial carrier phase that
  multiplication of the origin Jones data by `I` cancels. Verify the signed axes and normal
  components for the incident
  `(3/5, 0, 4/5)`, reflected `(3/5, 0, -4/5)`, and transmitted `(4/5, 0, 3/5)` directions, the
  medium admittances `5/2` and `5/4`, and the simultaneous `s`/`p` solution
  `r_s = 5/11`, `t_s = 16/11`, `r_p = -1/5`, and `t_p = 8/5`. Treat this as an exact regression of
  the scalar equations, not as the general Fresnel theorem. Independently verify that the stated
  tuple satisfies both complete reduced vector balances, including the normal-`D` entry, so the
  uniqueness result is not only conditional.
- [ ] Human-check the propagating Fresnel amplitude solver before upstreaming. With
  `Y_j = Z_j inverse`, `chi_r = -chi_i`, and full-vector electric Jones coordinates, confirm
  `r_s = (Y1 chi_i - Y2 chi_t) / (Y1 chi_i + Y2 chi_t)`,
  `t_s = 2 Y1 chi_i / (Y1 chi_i + Y2 chi_t)`,
  `r_p = (Y2 chi_i - Y1 chi_t) / (Y2 chi_i + Y1 chi_t)`, and
  `t_p = 2 Y1 chi_i / (Y2 chi_i + Y1 chi_t)`. The `p` reflection sign is tied to the
  propagation-oriented full-vector basis, so normal incidence gives `r_p = -r_s`, not equality.
  Verify that `chi_i > 0` and `chi_t >= 0` make both denominators positive, that the solver never
  divides by `chi_t`, and that a zero reflected field keeps arbitrary dummy carrier data. The
  core connected theorem assumes the reflected normal alternative. Confirm that the canonical
  wrapper instead derives it from phase matching, referenced material dispersion, canonical
  non-normal frames, and explicit positive-incident plus active-negative-reflected normal
  selection rather than treating a wave label as a direction law. Keep the manual rational
  fixture solve independent of the general coefficient theorem.
- [ ] Human-check the selected-tangent normal-incidence relation before upstreaming. A caller must
  independently supply a plane-normal polarization frame; a propagation frame qualifies on a
  selected geometric side only when its first axis is exactly equal to the selected first axis and
  its propagation vector is exactly that side-normal vector. Confirm that its signed normal is the
  side sign, its second full-vector axis is the side sign times the plane frame's second axis, and
  its fixed-plane `p` component is `side.sign * J1`. This is a gauge choice, not a canonical `s`
  axis or an incident/reflected/transmitted direction inferred from a label.
- [ ] Human-check the fixed-plane tangential-`p` Fresnel convention before upstreaming. With the
  existing full-vector denominator `D_p = Y2 chi_i + Y1 chi_t`, confirm
  `r_p_tangent = (Y1 chi_t - Y2 chi_i) / D_p = -r_p_full` and
  `t_p_tangent = 2 Y1 chi_t / D_p`, together with the division-free law
  `chi_i * t_p_tangent = chi_t * t_p_full`. The quotient normal-ratio form requires
  `chi_i != 0`; at transmitted grazing the tangential transmitted multiplier is zero even when the
  full-vector field coefficient is finite. At selected-tangent normal incidence, verify
  `r_p_tangent = r_s` and `t_p_tangent = t_s` while the moving reflected full-vector coordinate
  still has `r_p_full = -r_s`.
- [ ] Human-check the supercritical complex Fresnel convention before upstreaming. The transmitted
  argument is the dimensionless normalized normal factor
  `zeta = (n dot K_t) / beta_2 = -I * alpha / beta_2`, never the dimensional value `-I * alpha`.
  With `Y_j = Z_j inverse`, `chi_i > 0`, and `delta = alpha / beta_2 > 0`, independently verify
  `r_s = (Y1 chi_i + I Y2 delta) / (Y1 chi_i - I Y2 delta)` and
  `r_p = (Y2 chi_i + I Y1 delta) / (Y2 chi_i - I Y1 delta)`. Under the repository convention
  `exp (I omega t - I K dot x)`, their phases are the positive `Real.Angle` values
  `2 arctan (Y2 delta / (Y1 chi_i))` and
  `2 arctan (Y1 delta / (Y2 chi_i))`; a source using negative-time phasors generally gives the
  conjugate signs. Confirm `norm r_s = norm r_p = 1`. Keep the moving full-vector `p` coefficient
  distinct from the fixed-plane tangential coefficient `-r_p`, whose extra minus sign is a basis
  change and hence a `pi` phase shift rather than a physical disagreement.
- [ ] Human-check the connected supercritical boundary theorem and exact regressions. The raw
  canonical decay constructor stores its Jones amplitude at the coordinate origin, whereas every
  boundary balance uses the affine plane's stored point; therefore the transmitted referenced
  Jones data must be `spatialFactor K plane.point` times the raw data. Recheck the shifted fixture
  where that multiplier is `-I`, since an origin-only test cannot detect omitted, conjugated, or
  reversed referencing. In the reflected zero-field branch, proved-zero Jones data may be locally
  reframed, but the original dummy carrier, frequency, wave vector, and frame labels must remain
  unrestricted. Independently recheck the unequal-admittance fixture
  `Y1 = 2/3`, `Y2 = 1`, `chi_i = 4/5`, `zeta = -4 I/3`, including
  `r_s = (-21 + 20 I)/29`, `t_s = (8 + 20 I)/29`,
  `r_p = (-19 + 180 I)/181`, and `t_p = (108 + 120 I)/181`. The proved Jones-intensity equality
  concerns only the incident and reflected ordinary propagating waves; it does not assign raw
  transmitted decay-frame Jones norm the meaning of power. Its use in the separate actual-flux
  module must pass through the propagating material-wave connector instead.
- [ ] Keep positive-side decay, zero transmitted normal mean flux, and outgoing or causal
  semantics as three distinct claims. This complex Fresnel slice selects the algebraic
  positive-normal-decay boundary amplitude and proves unit reflected modulus and phase, but it
  does not establish a radiation condition, limiting-absorption prescription, half-space support,
  or an evanescent positive-power port. The subsequent actual-flux module establishes only the
  stored-normal mean-flux endpoint and still supplies no outgoing or causal semantics. For upstream
  review, split affine referenced-transmitted data, branch-neutral complex coefficient algebra and
  real compatibility, TIR denominator/modulus/phase, connected boundary elimination, exact
  regressions, actual flux, and any outgoing semantics into separately reviewable concepts.
- [ ] Human-check the connected complex-TIR actual-flux endpoint before upstreaming. Equal complex
  Fresnel reflected Jones intensity must be converted to equal incident/reflected propagating
  irradiance only because both carriers use the same negative-side material. In the active branch,
  independently verify that the stored-normal factors `chi_r = -chi_i` make the reflected
  own-period signed flux the negative of the incident flux. In the zero-reflected branch, verify
  that proved-zero reflected Jones data plus the boundary-selected intensity equality also forces
  zero incident flux while leaving the dummy reflected normal and frequency unrestricted. The
  transmitted side must use the Maxwell-qualified positive-normal-decay zero-mean-flux theorem,
  never propagating transmittance or raw decay-frame Jones intensity. Confirm that actual
  incident-plus-reflected superposition uses pointwise normal-interference cancellation and
  guarded reflected period reconciliation; it must not use Poynting-vector linearity or silently
  require a frequency for the zero-field dummy. Recheck the unequal-admittance exact values
  `F_i = 8/15`, `F_r = -8/15`, `F_t = 0`, and superposed normal mean flux zero. These are local
  stored-normal statements at the affine interface point, except that the transmitted zero result
  holds at every point; they do not imply pointwise zero normal flux, zero tangential flux,
  aperture power, an evanescent port, whole-plane conservation, outgoing behavior, or causality.
- [ ] Human-check the total-internal-reflection retarder bridge before upstreaming. Confirm that
  unit norm plus the named `Real.Angle` reconstructs each complex reflection coefficient in the
  positive-time convention; the physical relative coefficient phase is `phi_p - phi_s`, while the
  existing linear retarder must use `rho = phi_s - phi_p` because its second eigenvalue is
  `exp (-I * rho)`. Confirm that the diagonal numerical transform orders abstract coordinates as
  `(s,p)` and that the connected wrapper interprets them in the separately declared incident and
  reflected frames only under its explicit alignments and full referenced electric and magnetic
  boundary balances; the zero-reflection branch may retain a dummy reflected frame. Recheck the
  exact design's incident normal factor `sqrt 2 / 2`, positive normalized decay, negative-radicand
  shell identity, admittances, phase ratios `sqrt 2 - 1` and one, phases `pi/4` and `pi/2`, physical
  relative phase `pi/4`, and retarder parameter `-pi/4`. Check that matrix self-composition gives
  the negative-quarter-wave, diagonal-to-positive-quadrature, and Mueller results, but does not
  itself prove the frame identification required to interpret two physical bounces. The common
  `s` coefficient and its square are raw unit Jones phases, not modal power. Do not publish this
  self-composition kernel as a `FresnelRhomb` component until two-face geometry, intermediate
  frame transport, affine inter-bounce propagation phase, and entrance/exit faces are formalized
  and a page-verified optics source is recorded by the human author. For upstream review, split
  this work into a small phase-reconstruction support PR, a one-reflection Jones/connected-wrapper
  PR, and a self-composition/physical-regression PR if maintainers prefer the usual sub-200-line
  review units.
- [ ] Human-check the selected-tangent connected wrapper and regressions. The incident and
  transmitted relations use the positive side; only a nonzero reflected field requires the
  negative-side relation. In the zero branch the original reflected direction, frame, frequency,
  and wave vector remain arbitrary while proved-zero Jones data is locally reframed. Independently
  recheck the exact normal electric vectors `(-1,1,0)`, `(-1/3,1/3,0)`, `(-4/3,4/3,0)` and
  magnetic-field-strength (`H`) vectors `(-5/2,-5/2,0)`, `(5/6,5/6,0)`, `(-5/3,-5/3,0)`, plus the
  oblique conversion from full coefficients `(-1/5,8/5)` to fixed-plane coefficients `(1/5,6/5)`.
  The connected zero-field regression deliberately uses wave vector zero, angular frequency two
  against the active frequency one, and the positive-side frame in the reflected slot; confirm
  that the conditional reflected-frame premise is unreachable rather than silently imposed.
- [ ] Human-check the canonical incidence wrapper before upstreaming. Confirm that positive scalar
  rescaling of equal tangential phase directions preserves the oriented `s = normalize (n cross
  k-hat)` axis; complex hyperplane reflection descends to the exact real propagation-vector
  reflection only after equal frequency and both referenced material connectors are supplied; and
  equality of the supplied active reflected frame with the direction-determined canonical frame
  is an explicit conditional premise. In the zero reflected branch, verify that the proof locally
  uses the common plane frame only with proved-zero Jones data, so the original reflected wave
  vector, frequency, propagation-frame direction, and frame remain entirely arbitrary. Recheck
  that the exact `3-4-5` manual frames equal the canonical incident, reflected, and transmitted
  frames and that both the old explicit-alignment endpoint and the canonical wrapper prove the
  same actual superposed-field normal-flux balance. Normal incidence still requires a selected
  tangent frame.
- [ ] Human-check the role-specific canonical non-normal frame bundle before upstreaming. Confirm
  that `IsCanonicalNonNormalIncidenceFrame` hides only the proof of non-normality and still means
  exact equality with `incidencePolarizationFrame`; it must not manufacture a tangent at parallel
  or antiparallel normal incidence. Confirm that
  `HasCanonicalNonNormalIncidenceFrames` requires canonical incident and transmitted frames
  unconditionally, requires the reflected frame only when its electric amplitude is nonzero, and
  contains no phase-matching, material-connector, propagation-sign, reflection, boundary, flux, or
  outgoing assertion. Recheck the exact bundled `3-4-5` axes `s_i = s_r = s_t = (0,1,0)`,
  `p_i = (-4/5,0,3/5)`, `p_r = (4/5,0,3/5)`, and `p_t = (-3/5,0,4/5)`. In the zero-reflection
  regression, confirm that the reflected wave vector remains zero, its frequency remains two
  against the active frequency one, and its plane-normal dummy frame remains noncanonical while
  the canonical superposed-flux endpoint succeeds.
- [ ] Human-check the propagating Fresnel flux layer before upstreaming. Confirm that peak electric
  amplitudes give signed normal flux `(1 / 2) Y chi (abs Js squared + abs Jp squared)` and that the
  full-vector `p` coefficient uses the same transmitted-to-incident normal-admittance factor
  `(Y2 chi_t) / (Y1 chi_i)` as `s`, not the tangential-`p` factor `Y / chi`. Verify the
  denominator-free numerator certificates and the denominator-local unnormalized balances.
  Reflectance is unconditionally nonnegative; verify the physical hypotheses `0 < chi_i` and
  `0 <= chi_t` for the nonnegative transmission factor and `T`, and for `R + T = 1`.
  Recheck the exact oblique values `3/8`, `(25/121, 96/121)`, and `(1/25, 24/25)`; normal values
  `(1/9, 8/9)`; grazing values `(1, 0)` despite finite transmitted field amplitude; and matched
  values `(0, 1)`. Certify that the quadrature regression exercises a nontrivial relative phase,
  while the general arbitrary-Jones theorem proves phase independence. In the matched zero-field
  regression, confirm that the deliberately arbitrary reflected normal is `chi_r = chi_i = 1`, so
  `chi_r ≠ -chi_i`, while zero reflected Jones data still makes the signed balance hold. Confirm
  that the final connected result in this layer balances the three waves' separate actual
  one-period normal fluxes at the stored point. Keep its claim distinct from the later
  superposed-field theorem even though that theorem now supplies the required bridge.
- [ ] Human-check the Fresnel interference layer before upstreaming. Confirm directly that the two
  ordered actual-field cross terms have stored-normal sum
  `Y (chi_i + chi_r) (S_i S_r + P_i P_r)`, so opposite signed normals cancel pointwise with
  independent phases and frequencies. Verify that only the normal component is additive, that the
  active reflected branch uses the negative-side impedance, and that common frequency enters only
  when replacing carrier-period labels. In the zero branch, confirm that both actual reflected
  fields vanish, dummy reflected normal and frequency remain unrestricted, and the uniform
  common-axis hypothesis is stated honestly. Recheck the independent harmonic values
  `(-36/55, 36/55)`, their nonzero tangential vector sum `(21/55, 0, 0)`, instantaneous values
  `(-10/11, 10/11)` and `(-2/5, 2/5)`, connected total `5304/3025`, and the unequal-frequency
  zero-wave fixture `omega_r = 2`, `omega_i = 1`. Keep the actual superposed-field endpoint separate
  from whole-plane, aperture/modal-power, TIR, lossy, and scattering-unitarity claims.
- [ ] Before claiming a complete fixed-frequency reduction of the four macroscopic boundary laws,
  prove that normal-`B` continuity is redundant for fixed-frequency phase-matched Faraday waves:
  `n dot B₀ = ω⁻¹ (n cross K) dot E₀`, so only tangential `K` and tangential `E₀` enter. Keep
  normal-`D` distinct: without the required Ampere--Maxwell/on-shell hypotheses it is not redundant
  in the same structural way. Split any upstream proposal into the Electromagnetism-owned magnetic
  amplitude/realization connector and the Optics-owned three-wave boundary reduction before adding
  incidence-frame equations or Fresnel coefficients.
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
- [x] Prove the local common-frequency bridge from ordinary real fields and peak phasors to the
  one-period average of the actual instantaneous Poynting vector. This first slice deliberately
  stops before Maxwell, propagation, impedance, normal flux, irradiance, and modal power.
- [ ] Complete the bridge from propagating field modes and complex amplitudes to time-averaged
  normal Poynting flux. Until then, modal power and losslessness are terms internal to the stated
  power-normalization convention, not field-level energy theorems.

## Harmonic-flux conventions

- [ ] Human-check the E3b-0 peak-phasor identity against a page-verified optics reference and the
  repository carrier convention: `Phasor.realize z phase = Re (z * exp (I * phase))` must yield
  `(1 / 2) Re (Ephasor cross conj Hphasor)`, conjugating the second phasor and using magnetic field
  strength `H`, not magnetic induction `B`. Check also that the exact linear regression gives
  third-coordinate flux `1 / 2` and the quadrature regression gives `1`, rather than zero.
- [ ] Human-check that the Mathlib interval average is taken over exactly one positive-frequency
  period, may start at an arbitrary real time, and introduces neither an RMS convention nor an
  extra factor of two.
- [ ] Preserve the local-phasor fence in every complex-plane-wave connector. At spatial point `x`,
  the electric and magnetic phasors must contain the carrier's spatial factor there; a theorem in
  terms of stored reference amplitudes must instead expose the resulting squared spatial modulus.
- [ ] Before proposing E3b-0 upstream, decide whether the generic Euclidean phasor realization and
  conjugation additions should be reviewed separately from `HarmonicFlux.Basic`. Keep the public
  concept local harmonic averaging either way; do not bundle material irradiance, normal flux,
  aperture integration, modal normalization, outgoing-wave, or evanescence claims into it.
- [ ] Human-check E3b-1's propagating material-wave normalization against a page-verified optics
  reference: peak electric phasors must give irradiance `JonesVector.intensity / (2 * impedance)`,
  with magnetic field strength `H = impedance⁻¹ (n × E)` and no RMS reinterpretation.
- [ ] Human-check that E3b-1's local phase offset is the complete negative spatial carrier term
  `-waveNumber * inner x direction`, is shared by both electric and magnetic phasors, and disappears
  only through common-phase invariance after the actual-field averaging theorem is applied.
- [ ] Before proposing E3b-1 upstream, keep signed interface-normal flux in its own coherent
  follow-up and decide whether the two pure frame-quadrature lemmas should travel with the
  polarization-frame prerequisite or with the material irradiance PR.
- [ ] Human-check E3b-2's sign convention: the stored plane normal points from the geometric
  negative side toward the positive side, so its signed mean flux is irradiance times the
  propagation direction's stored-normal component. Against either side normal it must instead be
  irradiance times the signed cosine of that direction's side-relative angle, including negative
  obtuse flux and zero grazing flux.
- [ ] Before proposing E3b-2 upstream, preserve `NormalFlux.lean` as a role-neutral follow-up to
  propagating material irradiance. Do not infer incident, reflected, transmitted, outward, or
  outgoing roles from a geometric side, and do not apply its ordinary-real propagating-wave result
  to the future Maxwell-qualified complex evanescent carrier.
- [x] Before the complex attenuating/evanescent-wave harmonic-flux connector, add the general
  identity expressing `Phasor.realizeEuclidean` as the componentwise real part of a positive-
  exponential carrier times an amplitude. It lives in the narrow cross-layer
  `Polarization.ComplexRealization` module, remains a deliberate named rewrite rather than a simp
  rule, and does not broaden the Jones foundations with WaveEquation imports. The real-scalar
  realization law became public only when both propagating material and complex-carrier field
  connectors consumed it; the real/imaginary-part helpers remain private without that independent
  demand.
- [ ] Human-check the complex-carrier harmonic-flux connector pointwise: both local `E` and `H`
  phasors must contain the complete common `spatialFactor x`, the `H` reference amplitude must be
  `mu⁻¹ B₀`, and realization at `angularFrequency * time` must reconstruct the existing actual
  ordinary-real fields with the repository's positive-time, negative-space carrier convention.
- [ ] Human-check the stored-reference form of the complex-carrier connector: mean flux must carry
  `Complex.normSq (spatialFactor x)`, not one copy of the envelope and not an implicit unit-modulus
  assumption.
- [ ] Confirm the exact complex-decay regression before upstreaming: for `K = (5, 0, -4 I)` the
  transverse TE and TM fixtures must have origin mean vectors `(5 / 6, 0, 0)` and
  `(15 / 2, 0, 0)`, while positive-depth displacement must scale TE mean flux by
  `exp (-8 * depth)`, not the carrier-amplitude factor `exp (-4 * depth)`.
- [ ] Keep the complex-carrier connector off shell when upstreaming: it permits zero amplitude and
  assumes no transversality, dispersion, Maxwell, passivity, conservation, interface role,
  outgoing condition, or evanescent-field meaning. Preserve the Maxwell-qualified zero-normal-
  flux theorem and its interface specialization as a separate follow-up.
- [ ] Human-check the positive-normal-decay harmonic-flux cancellation before upstreaming. For
  `K = q - I * alpha * n`, confirm that `q` is tangent, attenuation is exactly `alpha * n`, and
  complex-bilinear `K dot E₀ = 0` makes the real part of the `n` component of
  `E₀ cross conj (K cross E₀)` vanish. The magnetic coefficient must be real and may be zero or
  have either sign. Material dispersion, Maxwell, nonzero amplitude, and strict positivity of the
  coefficient are not used by this algebra.
- [ ] Decide whether an upstream follow-up needs the critical `alpha = 0` endpoint. The current
  public theorem receives `PositiveNormalDecayWaveVector`, whose decay rate is strictly positive,
  even though the cancellation algebra also covers zero decay. Do not weaken the proof-bearing
  carrier structure merely to enlarge this one theorem without a genuine critical-wave consumer.
- [ ] Confirm the namespace placement with maintainers before upstreaming. The fork follows
  Physlib's receiver-extension convention by placing the role-neutral theorem in
  `ClassicalMechanics.ComplexWaveVector.PositiveNormalDecayWaveVector`, while the file/import graph
  keeps the ClassicalMechanics base independent of Optics. If maintainers instead want every
  Poynting-vector declaration named under `Optics`, move the public wrapper then; keep the generic
  conjugation helpers private until a second consumer establishes their proper owner.
- [ ] Human-check the planar positive-normal-decay flux specialization. The transmitted-candidate
  predicate supplies the positive-medium material shell but deliberately not electric
  transversality. Adding explicit bilinear transversality must both yield the source-free
  positive-medium macroscopic Maxwell solution and give zero actual one-period flux through the
  stored interface normal at every point and arbitrary period start. Do not strengthen this to
  pointwise zero normal flux, zero tangential flux, boundary satisfaction, TIR, or outgoing power.
- [ ] Confirm the sharp positive-normal-decay flux regressions before upstreaming. The transverse
  TM fixture must have instantaneous vector `(15 / 2, 0, -6)` at `time = pi / 4` and the origin,
  despite mean `(15 / 2, 0, 0)`. The on-shell fixture with the same `K = (5, 0, -4 I)` and
  `E₀ = (1, 0, 1)` must have bilinear pairing `5 - 4 I` and mean vector
  `(5 / 6, 0, -5 / 6)`, proving transversality cannot be dropped.
- [ ] Human-check the named half-space evanescence semantics before upstreaming. Confirm that the
  five defining facts are nonzero electric amplitude, complex-bilinear transversality, the
  lossless homogeneous-isotropic material shell, zero tangential attenuation, and strict
  attenuation direction into the selected side. Phase tangency, positivity of the side-relative
  rate, the positive-normal-decay representation, source-free Maxwell satisfaction, exact
  carrier/local-phasor/ordinary-field scaling, and zero side-normal one-period mean flux must all
  remain derived consequences. The carrier is global and grows into the opposite side; do not
  reinterpret the predicate as half-space support, a medium-domain restriction, an outgoing or
  causal condition, TIR, pointwise zero normal flux, zero tangential flux, or an evanescent
  positive-power port. Recheck that the canonical negative-radicand Jones carrier satisfies the
  predicate exactly when `J.components ≠ 0`, that the `(5, 0, -4 I)` regression has positive-side
  rate four and fails on the negative side, and that its on-shell zero-amplitude copy satisfies the
  other four conditions but is rejected solely by the active-field guard.
- [ ] Split a future upstream proposal into the role-neutral positive-normal-decay harmonic-flux
  algebra and actual-field bridge, the planar Maxwell/normal-flux specialization, and the exact
  falsification regressions. Keep `NormalFlux.lean` restricted to its propagating material-wave
  concept.

## Polarization conventions

- [ ] Human-check the positive-normal-decay polarization-frame convention before upstreaming.
  With `exp (I * omega * t - I * K dot x)`, verify `K = q - I * alpha * n`,
  `s = normalize (n cross q)`, and `p = (K cross s) / beta` for positive real shell
  wavenumber `beta`; the planar medium connector then identifies `beta` with `omega / v_2`.
  Confirm the complex-bilinear identities `p dot p = 1`,
  `K cross s = beta p`, and `K cross p = -beta s`; do not replace them by Hermitian
  orthonormality or normalize `p` by its Hermitian norm.
- [ ] Human-check the full-vector/fixed-plane `p` sign. The retained real plane axis is
  `n cross s = -normalize q`, so the tangential multiplier of full-vector `p` is
  `-I * alpha / beta`, while its normal coefficient is `norm q / beta`. In the exact fixture
  `K = (5, 0, -4 I)` and `beta = 3`, this gives `p = (4 I / 3, 0, 5 / 3)`, fixed-plane
  multiplier `-4 I / 3`, and Hermitian squared norm `41 / 9`, not one.
- [ ] Keep `PositiveNormalDecayPolarizationFrame.embedJones` documented as raw TE/TM amplitude
  coordinates. Standard `JonesVector.intensity` is not the Hermitian norm or physical power of
  the embedded electric amplitude. Do not place an evanescent transmitted channel in the ordinary
  positive-admittance port/unitarity API.
- [ ] Decide with maintainers whether the dedicated proof-bearing
  `PositiveNormalDecayPolarizationFrame` is the preferred upstream abstraction. If so, split the
  fork milestone into neutral complex cross-product and hyperplane geometry, the bilinear frame
  and fixed-plane conversion, and the planar negative-radicand constructor/Maxwell connector.
  Keep each exact regression beside the concept it tests rather than proposing a standalone
  regression PR. Do not fold the complex frame into the existing real `PolarizationFrame` API.
- [ ] Human-check that the connected negative-radicand positive-normal-decay Jones carrier uses
  zero incident tangential attenuation only to obtain the existing candidate specification. Its
  embedded amplitude supplies bilinear transversality automatically, which yields the source-free
  positive-medium Maxwell solution and zero stored-normal one-period mean flux. These statements
  do not prove boundary satisfaction, a Fresnel coefficient, pointwise zero normal flux, TIR, or
  outgoing/limiting-absorption semantics.
- [ ] Human-check the exact planar connector regression. For stored normal `+z`, negative-side
  `epsilon_1 = mu_1 = 13`, positive-side `epsilon_2 = mu_2 = 3`, `omega = 1`, and incident
  `K_i = (5, 0, 12)`, verify the incident `5^2 + 12^2 = 13^2` material shell, radicand `-16`,
  transmitted `K_t = (5, 0, -4 I)`, normalized normal factor `-4 I / 3`, raw TM data
  `(0, -3 I)`, `B_0 = (0, 9 I, 0)`,
  `E_tan = (4, 0, 0)`, and `H_tan = (0, 3 I, 0)`. Confirm that the regression consumes the
  canonical constructor from an unrelated zero transmitted slot and reaches the configuration-level
  Maxwell and zero-normal-mean-flux endpoints without asserting a boundary equation or TIR.
- [ ] Human-confirm that no external implementation was copied or translated into the
  positive-normal-decay frame, connector, or regressions. Separately, if the roadmap, API map, or
  a future PR description relies on listed optics literature, independently verify every
  bibliographic fact and physics claim under `AI-POLICY.md`.
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
- [x] Define restriction and zero extension along finite mode embeddings. Prove exact selected and
  omitted-coordinate action, `R * E = 1`, the ambient star projector `E * R`, zero-extension
  isometry and power preservation, restriction/projector passivity, arbitrary-input action and
  exact output power, passive zero extension of rectangular transforms, and that restriction
  preserves ambient modal power precisely when every omitted coordinate has zero amplitude.
- [x] Define dependent port/channel families, nominally distinct incident and outgoing endpoint
  types, a local connection with compatible mode fibers, endpoint-presentation exchange, the
  fixed-point-free mate involution, the oriented scattering adapter, and unit-gain routing with
  relabeling covariance, normalized-power preservation, and the local `C * S` action order.
- [x] Extend the local connection API to proof-carrying indexed families with physical-port
  endpoint uniqueness, dependent connected-channel embedding, blockwise fixed-point-free mating,
  and exact total routing on connected channels. Keep family cardinality unrestricted in the data
  and require finiteness only for finite-dimensional action and power results.
- [x] Define the total ambient internal-wiring transform by zero-extending connected routing.
  Prove exact connected, omitted-row, omitted-column, arbitrary-input, and selected-input action;
  both connected range-projector Gram laws; exact output power; global normalized-modal passivity;
  and power equality precisely on inputs supported on connected outgoing channels.
- [x] Define the explicit external-channel complement, typed incident injection `E_in`, outgoing
  exposure `E_out`, and restriction readout `E_outᴴ`. Prove complete connected/external endpoint
  partitions, identify external channels with the dependent sum of modes over unconnected ports,
  and prove exact action, Gram, isometry, cross-zero, projector-completeness, `C b + E_in u`, and
  additive normalized-power laws. Preserve the empty-mode channel-versus-port distinction. The
  later `FlatNetlist` construction now closes the broad structural API-map requirement; executable
  well-formedness checking and semantic compilation remain separate N4C work.
- [ ] Before upstreaming the external-output completion, prepare a stack in this order: the neutral
  complementary-range-projector lemma in `Mode/Embedding`; outgoing endpoint partition, exposure,
  and readout; routing/exposure orthogonality and projector completeness; then the focused mixed
  complex-amplitude regressions. The connected fork milestone may remain integrated while the
  human review and maintainer-facing split are pending.
- [x] Begin N4 with dependent component-owned physical-port and channel sums, an explicit
  reassociation equivalence, and dependent block-diagonal scattering. Prove the cast-free indexed
  versus aggregate entry bridge, exact same-component and cross-component-zero entries, and the
  arbitrary-input component restriction law. Keep component-family data nonfinite and require
  finite-dimensional instances only where matrix action needs them.
- [x] Add a heterogeneous component-family regression with one scalar channel and one two-mode
  component. Reuse the same local port label under different component tags, retain a nonsymmetric
  nonreal two-mode block, test all four cross-component entries, and pin the mixed aggregate
  output as `(4 + 3 I, 12 + 16 I, 18 + 26 I)`.
- [x] Add the source-neutral `LinearBehavior.feedbackSolutions` construction and singular-safe
  `FlatNetlist` relational semantics. Derive `S`, `C`, `E_in`, `E_out`, and `E_outᴴ` from the owned
  component/connection data, retain complete incident/outgoing states, project the external
  relation, and prove the exact shaped and implicit feedback equations without an inverse.
- [x] Add the hostile N-11 shared-link regression: both local component matrices have explicit
  two-sided inverses, while zero input has distinct complete states and external outputs, the
  feedback operator has a nonzero kernel witness, and a separate external input has no solution.
- [ ] Before upstreaming flat-netlist semantics, prepare a focused stack for the source-neutral
  feedback relation, netlist data and derived maps, compositional external semantics, and hostile
  singular regression. Human-check state order, `C * S`, `E_outᴴ`, partial/multivalued behavior,
  and the absence of inverse or physical conservation claims.
- [ ] Human-certify every flat-netlist declaration and proof under `AI-POLICY.md`. This milestone
  introduces no new bibliographic claim; the DATE/SysCon convention and source-formula gates stay
  separate and open where already recorded.
- [ ] Before upstreaming component-family assembly, prepare a stack in this order: the generic
  dependent block-diagonal action lemma in `Mode/Embedding`; aggregate component/port/channel types
  and reassociation; assembled scattering and exact laws; then the hostile heterogeneous
  regression. Human-check that cross-component zeros mean only absence of direct pre-wiring
  scattering, not termination, absorption, passivity, losslessness, or solved feedback.
- [x] Define implicit complex-linear component behavior independently of invertibility, embed
  arbitrary complex-linear maps and finite mode transforms as graph behaviors, and prove identity,
  relational series, independent parallel, graph-composition, matrix-cascade, and block-diagonal
  direct-sum laws. Preserve `(input, output)` pair order and `first.series second = second * first`
  for transform graphs.
- [x] Define rectangular copy, coherent-sum, heterogeneous selection, and direct-coefficient
  weighted split/combine graph behaviors. Prove exact membership, one-sided identity,
  reverse-order idempotence and kernel, copy-selection, and weighted-split modal-power laws. Keep
  these algebraic junctions distinct from physical square beam splitters, termination, absorption,
  passive wiring, and quantum cloning.
- [x] Add proof-gated extraction and round trips for total single-valued behaviors, including
  identity, series, and independent parallel closure plus exact complex gain and cascade-order
  regressions. N3 is complete. Provisional convention-explicit N3T work may proceed on the fork,
  while source-parity aliases, citations, and upstreaming remain human-gated.
- [x] Add the convention-explicit N3T foundation with backward-first travelling-wave states,
  relational two-port behavior, reversible scattering regrouping
  `(aL, aR; bL, bR) ↔ ((bL, aL), (aR, bR))`, proof-gated chain-transform extraction, graph
  uniqueness, and later-times-earlier matrix multiplication derived from relational series. The
  zero-scattering regression must remain: it is functional as a scattering graph but multivalued
  as a chain relation.
- [x] Keep the convention-explicit `BackwardFirst` prefix in the fork API: it records the direct-sum
  and matrix presentation order, while nominal wave wrappers separately record direction. Revisit
  this public name during the human convention review before upstreaming.
- [x] Add an orientation-sensitive end-to-end scattering regression: unequal through gains two and
  three regroup and extract as backward-first gains one half and three. This prevents the symmetric
  perfect-through identity from hiding a left/right, row/column, or inverted-block swap.
- [x] Conceptually separate the N3T foundation into focused modules: reversible two-port/scattering
  regrouping first, then proof-gated chain extraction and series, with each concept's regression
  fixtures kept beside its public layer and the connected files retained for end-to-end validation.
- [ ] Prepare those two N3T concepts as stacked upstream proposals after the convention and source
  ledger are independently verified, unless maintainers explicitly request one connected proposal;
  obtain maintainer agreement or split further if either proposal remains too large for review.
- [ ] Human-check the fork's DATE-compatible convention before upstreaming, with SysCon used only
  to corroborate the four-wave arrows and behavior: backward means toward the declared left port;
  forward means toward the declared right port; the state order is backward then forward;
  `(aL, aR)` are incident and `(bL, bR)` outgoing; and the regrouping is exactly left `(bL, aL)`,
  right `(aR, bR)`. Confirm that an adjacent physical cascade identifies the entire middle
  reference-plane state or inserts an explicit propagation behavior.
- [x] Implement the one-way N3T scattering-to-chain slice without a total scattering-matrix
  inverse: chain functionality is exactly bijectivity of the right-incident to left-outgoing block,
  and the behavior-derived transform has the proved block formula and exact graph equality. Its
  regressions include a singular full scattering transform with bijective pivot, noncommuting
  reflection blocks, and a zero-pivot negative case.
- [x] Derive the inverse chain-to-scattering block formula under bijectivity of the exact leading
  chain block and prove behavioral and matrix round trips in both directions. The proved formula
  distinguishes right-to-left transmission `K₁₁⁻¹` from left-to-right transmission
  `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`. For scalar blocks with `K₁₁ ≠ 0`, the latter is
  `det K / K₁₁`, hence equals `1 / K₁₁` when `det K = 1`. Keep the opposite convention behind an
  explicit permutation.
- [ ] Before upstreaming chain-to-scattering conversion, use maintainer-agreed stacked proposals in
  this order: neutral chain blocks and generic inverse support; scattering behavior and its exact
  pivot criterion; the block formula and graph equality; behavior-derived extraction with both
  round trips; then focused adversarial regressions. Move the generic chain block decomposition
  from `TwoPortChainScattering.lean` to `TwoPortChain.lean` in the neutral first stack. The
  connected fork milestone and its deliberately independent formula regressions remain larger than
  the usual 200-line review guide.
- [ ] Human-verify whether and how DATE14 Theorem 5's terminated `transm = 1 / M11` statement uses
  determinant one and maps onto this backward-first convention. Until then, describe the Lean
  result as independent block algebra rather than DATE/HOL source parity.
- [x] Connect the two-port scattering type to the N2a component boundary with canonical
  `Incident`/`Outgoing` sum-label equivalences and a typed two-port adapter from the existing
  oriented scattering transform. Exact four-block entries, amplitude covariance, losslessness,
  behavior membership, label round trip, and a four-distinct-nonreal-entry regression now agree.
- [x] Derive source-neutral right-load termination from the relational constraint. The generic
  behavior retains the complete solution `(bL, (aR, bR))`; for a graph load `aR = Γ bR`, exact
  well-posedness is injectivity of `P = K₁₁ - Γ K₂₁` together with solvability of every incident
  forcing `Q aL`, where `Q = Γ K₂₂ - K₁₂`. Under the stronger bijective-pivot gate, the extracted
  responses are `RΓ = P⁻¹ Q` and `FΓ = K₂₁ RΓ + K₂₂`. Zero return agrees with the existing
  left-reflection and left-to-right scattering blocks. Scalar, asymmetric tuple-order,
  noncommutative, rectangular non-surjective, and singular-pivot regressions guard the result.
- [ ] Before upstreaming right termination, split the connected fork milestone into stacked
  proposals for relational semantics, exact chain well-posedness, bijective-pivot formulas, and
  zero-return/scattering agreement. Keep the core chain-termination layer independent of
  chain-to-scattering conversion, and place zero-return/scattering agreement in a small bridge.
  Its connected regression suite intentionally exceeds the usual 200-line review guideline.
- [x] Validate the merged fork right-termination milestone on 2026-08-24 with a cache check, the
  4,704-job Physlib build, Physlib and QuantumInfo declaration linters, the commit-sensitive style
  linter, the API-map linter, and `lint_all`. The full linter reported only pre-existing repository
  backlogs in unrelated files; no termination file was flagged.
- [ ] Human-check every right-termination definition, statement, and proof before upstreaming, and
  do not call zero return a matched, absorbing, passive, or physically realized load without
  separate electromagnetic hypotheses. Do not identify the generic Schur complement with DATE's
  terminated `1 / M11` statement until the source/convention audit establishes its hypotheses and
  coordinate correspondence.
- [ ] Factor the repeated proof-dependent inverse construction for a bijective `ModeTransform`
  into a generic mode API before a third upstream inverse block is proposed; leading-block,
  transmission-block, and termination-pivot inverses currently repeat the same equivalence pattern.
- [ ] Before an upstream functional-behavior proposal, decide whether its core extraction API and
  adversarial regression suite should be reviewed as one coherent PR or as two stacked PRs. The
  fork milestone keeps atomic core and regression commits while preserving end-to-end validation.
- [ ] Before an upstream rectangular-behavior proposal, decide with maintainers whether the core
  and its extensive regression suite should be reviewed as one coherent PR or split into two
  sequential PRs. The current fork milestone intentionally keeps them together for end-to-end
  validation, but it exceeds the usual 200-line review guideline.
- [ ] Human-check every rectangular-junction definition, theorem statement, and proof before any
  upstream proposal as required by `AI-POLICY.md`; a successful Lean build is not certification of
  the intended semantics.
- [ ] Define time-reversed channel pairing and port reference planes before defining reciprocity;
  typed endpoints and coordinate rephasing alone do not supply these physical conventions.
- [ ] Human-check the local typed-routing semantics before upstreaming. Confirm that component
  scattering has type `Incident → Outgoing`, connection routing has type `Outgoing → Incident`,
  and the incident-space round-trip order is `C * S`. Confirm that exchanging left/right endpoint
  presentation only relabels the local sum, and that a wire has unit gain with no nontrivial
  coupling coefficient, attenuation, phase, delay, fan-out, termination, time-reversal,
  reciprocity, feedback-solvability, or electromagnetic-flux claim. Recheck the dependent
  `Fin 2`/`Bool` fiber fixture, both routing directions, the fixed-point-free and
  swapped-presentation regressions, and the nonsymmetric scattering entries `3` and `2` that catch
  row/column reversal.
- [ ] Human-check the connection-family invariant before upstreaming. Confirm that uniqueness is
  enforced on indexed physical-port ends, not inferred from aggregate channel injectivity; each
  whole port therefore belongs to at most one wire. Recheck the opposite-order second mode
  equivalence, composed embedding-after-mate result, cross-block zero, and both endpoint-reuse
  counterexamples. In particular, the all-`Empty` channel map is vacuously injective while its
  physical endpoint map is not. Treat connected-channel power preservation only as normalized
  modal power; external complements, electromagnetic losslessness, presentation covariance, and
  netlists remain absent from this layer.
- [ ] Human-check ambient partial-routing semantics before upstreaming. Confirm the factorization
  `C = E_inc * U * R_out`, `Cᴴ * C = P_out`, and `C * Cᴴ = P_inc`; neither projector is generally
  the ambient identity. In the three-port fixture recheck the two matched entries, unmatched zero,
  omitted incident row and outgoing column, unit-power omitted pulse, strict modal-power decrease,
  complex connected pulse of power five, and asymmetric `C * probe` regression. A zero outgoing
  column means no internal feedback, while a zero incident row means no internal-wiring
  contribution; neither means a matched load, absorption, termination, zero total incident
  amplitude, or electromagnetic power loss. Confirm that `partialRouting` is a total transform;
  “partial” refers to its connected-subspace action. Check `partialRouting_isPassive` only in
  normalized modal coordinates and `partialRouting_power_eq_iff` exactly: full input power is
  preserved iff every complement outgoing amplitude vanishes. The strict-decrease witness and
  connected equality witness must not be summarized as a strict contraction. Confirm that an empty
  exposed port need not create a complement channel.
- [ ] Human-check the external-channel complement and both endpoint exposures before upstreaming.
  Confirm that `ExternalChannel` means external only to the selected connection-family range, not
  spatial exterior, radiation, physical accessibility, or completeness of an electromagnetic mode
  basis. Recheck the connected/external partition equivalence, the equivalence with the dependent
  sum of modes over unconnected ports, and the nonempty fixture's unique exposed channel. Verify
  the incident coefficient `2 + I`, its power five before and after injection, the connected zero,
  the outgoing coefficient `3 - 2I`, its exact unconjugated adjoint readout, both cross-zero laws,
  both connected/external projector sums, the `C b + E_in u` connected value `2 + I`, external
  value one, and total normalized modal power six. In the empty-fiber fixture confirm
  simultaneously that the third physical port is
  unconnected, the connected-channel embedding is surjective, and the external-channel type is
  empty. Treat `E_in` and `E_out` as coordinate zero extensions, and `E_outᴴ` as coordinate
  restriction—not as a source, termination, detector, boundary condition, or feedback solution.
  Confirm `E_outᴴ * E_out = 1` while `E_out * E_outᴴ` is the external outgoing range projector;
  the analogous incident laws hold for `E_in`. Do not call either exposure unitary, surjective, or
  a lossless device. Complement outgoing power omitted by `C b` is not absorption. The broad
  netlist and elimination requirements remain open.
- [ ] Human-check the implicit linear-behavior layer before upstreaming. Confirm that membership
  orders amplitudes as `(input, output)`, `first.series second` hides one exact intermediate
  amplitude, and its transform graph and extracted functional map compose as `second * first` and
  `second.comp first`, respectively. Check that totality means existence for every input and
  single-valuedness means uniqueness at fixed input: the top and bottom relations separate the two
  predicates, while the free-output relation is neither. Recheck the exact gain `(2 + I) *
  (3 - I) = 7 + I`, concrete forward output `(1 + 2I, 3 + 7I)`, reverse output
  `(7 + 2I, 3 + I)`, the free-output pairs `(0, 0)` and `(0, unitPulse)`, the singular zero
  transform mapping a nonzero pulse to zero while still inducing a functional noninjective graph,
  and the independent gain-two/gain-three parallel output `(2, 3I)` together with rejection of the
  wrong right-branch value `2I`. An arbitrary `LinearBehavior` is only a homogeneous
  fixed-frequency complex-linear constraint; a linear input-output map exists only behind explicit
  totality and single-valuedness proofs, which imply neither invertibility, causality, passivity,
  electromagnetic normalization, nor physical realizability. Parallel composition takes two
  independent inputs; it is not fan-out, summation, or a physical splitter.
- [ ] Human-check the mode-embedding semantics before upstreaming. Recheck the non-prefix
  `Bool ↪ Fin 3` fixture, the omitted coordinate-one amplitude of power five, strict restriction
  loss, zero-extension isometry, the passive nonidentity ambient projector, and the genuinely
  complex nonsymmetric zero-extended action `[3 - I, 0, 11 - I]`. Confirm that restriction is not
  described as physical absorption, zero extension is not described as surjective or unitary,
  `E * R` is not collapsed to the ambient identity, and the exact power-equality iff has no hidden
  surjectivity or nonempty-family premise. For
  `rangeProjector_add_rangeProjector_eq_one`, confirm that the supplied sum equivalence identifies
  the two embeddings on both summands and therefore proves both disjointness and exhaustive
  coverage; the theorem makes no claim for embeddings that are merely disjoint.
- [ ] Add the electromagnetic normalization theorem before equating modal unitary or passive
  predicates with physical losslessness or passivity.
- [ ] Keep P5a's contraction and Malus results explicitly about squared raw Jones intensity and
  raw Stokes coordinates. The separate P5b/E3b follow-up now supplies propagating plane-wave
  irradiance and actual mean-flux corollaries, but no aperture power, normalized modal power, or
  electromagnetic-passivity conclusion exists until the flux-normalized mode family is proved.
- [ ] Human-check P5b-1's ideal-analyzer boundary: its actual-field Malus theorem constructs input
  and output plane waves in the same medium, propagation frame, frequency, and phase convention.
  It models no reflection, refraction, internal component field, absorption, heating, or fate of
  the discarded orthogonal polarization, so irradiance contraction must not be presented as a
  complete component energy balance.
- [ ] Supply an induced operator-norm bridge before expressing passivity as a matrix norm bound;
  the ambient norm inherited by the raw matrix alias is not that operator norm.
- [x] Represent component behavior independently of invertibility, with graph behaviors only as a
  proved functional specialization.
- [ ] For network equations `b = S a`, `a = C b + E_in u`, and `y = E_outᴴ b`, define
  well-posedness by unique internal solvability of `(1 - C * S) a = E_in u`; a contraction estimate
  may be sufficient but must not be necessary.
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
- [ ] Human-verify the N3T source ledger before citing it upstream. DATE 2014 fixes the four-wave
  chain state as `[d; b] = K [c; a]`, hence backward-first, while its separately named two-port MRR
  matrix uses internal ring fields and is not the generic two-sided scattering conversion. The
  DATE termination notation appears endpoint-ambiguous, and the heterogeneous product notation
  does not by itself fix fold direction. SysCon 2015 repeats the four-wave behavior. Treat these as
  mathematical architecture references only; the inspected IEEE, EDAA, Springer, and Concordia
  materials do not supply a license for adapting HOL implementation text.
- [ ] Record every source hypothesis strengthened, corrected, or rejected by a Lean theorem.
- [ ] Repair or independently reverify the vector-calculus Zulip reference in
  `Physlib/Optics/API-map.yaml`: its current `Physlib` archive path is stale and the cited message
  range was not recovered from the older `PhysLean` archive during the E1 audit.
- [ ] Replace source decimal examples by exact values or certified intervals before using them as
  regression evidence.

## Validation before an upstream proposal

- [ ] Run `lake-lock exe cache get` and `lake-lock build` from a clean checkout of the proposed
  branch; the machine-wide wrapper serializes Lean jobs, caps worker threads, and enforces the
  free-disk guard.
- [ ] Run `lake-lock exe lint_all` and distinguish new failures from failures reproducible on the
  exact upstream base commit.
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
  `attenuationvector`, `decayrate`, `envelope`, `kappa`, `omega`, `phasevector`, and `wavenumber`;
  the complex-carrier and exact-bridge differential added `attenuating`, `bilinearly`, `hidden`,
  `normalizations`, `spine`, and `theta`. The complex-calculus differential initially reported
  only `requested`; rewording the two affected docstrings leaves that slice with no dictionary
  delta. The complex-dispersion differential reported `epsilon` and `imposes`; the ordinary verb
  was reworded and only the physics term `epsilon` was added. The forward complex-Maxwell
  differential reported no new vocabulary. The guarded-converse differential initially reported
  only `nonvanishing`; rewording that sentence with existing dictionary words leaves no delta. The
  complex-dispersion regression reported `despite`, `exercise`, `guards`, and `te`; the ordinary
  words were reworded and only the transverse-electric abbreviation `te` was added to both the
  Lean spelling dictionary and the separate CI codespell ignore list. The exact real-wave
  nonzero-amplitude bridge and complex-Maxwell regression introduced no new spelling vocabulary.
  The selected-tangent normal-incidence differential added the correct new prose vocabulary
  `alignment`, `apart`, `assertion`, `balance`, `balanced`, `balances`, `chi`, `conclusions`,
  `converting`, `crosses`, `intentionally`, `multiplier`, `passes`, `performs`, `propagate`,
  `reconciles`, `records`, `solved`, `solver`, `specialize`, and `unavailable`.
  The guarded canonical-role-frame differential added `accepted`, `assigning`, `canonicality`,
  `conditionally`, `connectivity`, `existential`, `flow`, `hides`, `literal`, `manual`, `packages`,
  `recognition`, `role`, `roles`, and `unconditional`. The complex Fresnel/TIR differential added
  `acquires`, `arctangent`, `denominators`, `hybrid`, and `quadrant`. The connected complex-TIR
  actual-flux differential introduced no new spelling vocabulary. The total-reflection retarder
  differential added `accumulates`, `bounces`, `catches`, `diagonally`, `disappears`, `entrance`,
  `errors`, `exit`, `omit`, `prism`, `reflecting`, and `unobservable`. The named half-space
  evanescence differential introduced no new spelling vocabulary after ordinary prose was
  reworded. The typed local-routing differential added `adapter`, `bidirectional`, `combiners`,
  `east`, `elimination`, `fibers`, `flattening`, `gain`, `mate`, `mates`, `mating`, `nonsymmetric`,
  `routing`, `secondary`, `solvability`, `splitter`, `splitters`, `termination`, and `west`.
  The indexed connection-family differential added `blockwise`, `netlists`, `south`, and
  `vacuous`. The finite mode-embedding differential added `absorption`, `ambient`, `rectangular`,
  and `restriction`; all other initially reported ordinary prose was reworded using the existing
  dictionary. The ambient partial-routing differential introduced no new spelling vocabulary
  after ordinary prose was reworded using the existing dictionary and repository baseline. The
  implicit linear-behavior differential reworded ordinary prose and added `behavior`, `behaviors`,
  `directsum`, `graphs`, `linearbehavior`, `modetransform`, `multivalued`, `oflinearmap`,
  `relational`, `singular`, and `tobehavior`. The rectangular-behavior differential added the 51
  exact reported words `admitting`, `annihilates`, `assembly`, `asserted`, `changed`, `cloning`,
  `coherent`, `conjugated`, `conjugating`, `copy`, `device`, `differs`, `displayed`, `doubles`,
  `elementary`, `embedded`, `enhancement`, `establish`, `fifty`, `five`, `fixtures`, `followed`,
  `identification`, `incorrect`, `interpret`, `invoking`, `joins`, `mechanism`, `missing`,
  `mistakes`, `nonidentity`, `nontrivial`, `omitted`, `placing`, `plausible`, `produced`,
  `producing`, `realizability`, `reject`, `rejects`, `requiring`, `reversed`, `selecting`,
  `selection`, `selector`, `sentinels`, `shapes`, `ten`, `unconjugated`, `wire`, and `wrong`.
- [x] Reproduce and document any repository-wide baseline lint failures instead of presenting them
  as failures introduced by Optics or claiming a completely clean gate. The 2026-08-24 typed
  local-routing run reproduced pre-existing style and transitive-import diagnostics only in
  unrelated files. Its build, file-import, illegal-import, alpha-import, duplicate-tag,
  sorry/pseudo-attribution, and declaration-linter stages passed, and neither new Network file
  appeared in a failure list.
- [x] The 2026-08-24 implicit linear-behavior run passed the build, file-import, illegal-import,
  alpha-import, duplicate-tag, sorry/pseudo-attribution, declaration-linter, API-map, and
  changed-file style gates. The full linter reproduced only the known unrelated repository style
  and transitive-import baseline after the new behavior module's initially redundant direct
  Mathlib import was removed; a targeted transitive-import rerun then reported no changed Optics
  module.
- [x] The 2026-08-24 rectangular-behavior run passed cache retrieval, the 4,689-job `Physlib`
  build, warnings-as-errors elaboration for all three changed Lean modules, both Physlib and
  QuantumInfo declaration linters, public-file import checks, illegal- and alpha-import checks,
  duplicate-tag and sorry/pseudo-attribution checks, the API-map linter with 3,571 resolved names,
  committed-state style lint, forbidden-term and whitespace checks, and the exact differential
  spelling emulation. The full linter reproduced only the known unrelated repository style and
  transitive-import baseline; neither rectangular Optics module appeared in either list.
- [x] The 2026-08-24 functional-behavior run passed cache retrieval, the 4,690-job `Physlib`
  build, warnings-as-errors elaboration for the core and functional regression modules, both
  Physlib and QuantumInfo declaration linters, public-file import, illegal-import, alpha-import,
  duplicate-tag, sorry/pseudo-attribution, API-map, whitespace, forbidden-term, and line-length
  gates. The API map resolved 3,614 names with no missing file or declaration. The official
  spelling executable still fails at the documented Lean 4.33 string-API incompatibility; exact
  docstring-token emulation found no new missing word after prose rewording. The full linter
  reproduced only the known unrelated repository style and transitive-import baselines; neither
  functional-behavior Optics module appeared in either failure list.

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
