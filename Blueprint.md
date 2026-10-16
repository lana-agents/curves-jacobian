# Blueprint: curves-jacobian

Status keys: **done** (proved, no `sorry`), **wip**, **planned**.

| # | content | status |
|---|---|---|
| CJ0 | skeleton | done |
| CJ1 | Serre's criterion for Noetherian domains (Stacks 031S, 031T), associated-primes form | **done** |

### CJ1 (done) — `CurvesJacobian/CommAlg/SerreCriterion.lean`

* `AssPrimesHeightOne A` ((S₂): associated primes of `A ⧸ (a)`, `a ≠ 0`, have height 1);
  `RegularInCodimOne A` ((R₁): `A_𝔭` DVR for `ht 𝔭 = 1`).
* `isIntegrallyClosed_iff_regularInCodimOne_and_assPrimesHeightOne` (Stacks 031S for domains).
* `mem_range_of_forall_height_eq_one`: (S₂) ⇒ `A = ⋂_{ht 𝔭 = 1} A_𝔭`; normal case
  `mem_range_of_forall_height_eq_one_of_isIntegrallyClosed` (Stacks 031T (2)).
* `isIntegrallyClosed_of_assPrimesHeightOne`: (S₂) + height-one localisations integrally closed ⇒ normal.
* Divergence: (S₂) is in associated-primes form, not depth form (no depth in Mathlib); CJ2 links them.

| CJ2 | depth of Noetherian local rings, (R_k)/(S_k) (Stacks 031P), regular ⇒ normal | **done** (for domains) |

### CJ2a (done) — `CurvesJacobian/CommAlg/SerreS2.lean`

* `DepthGeTwo B` (maximal ideal contains a `B`-regular sequence of length 2, i.e. depth ≥ 2 in
  the sense of Stacks 00LI with Mathlib's `IsRegular` = Stacks 00LF); `SerreS2 A` (depth `A_𝔭 ≥ 2`
  for `ht 𝔭 ≥ 2`; for a domain this is Stacks 031P (S₂)).
* `serreS2_iff_assPrimesHeightOne` (Noetherian domains), elementary (no `Ext`); key lemma
  `mem_span_of_isWeaklyRegular_pair`.
* `isIntegrallyClosed_iff_regularInCodimOne_and_serreS2`: **Serre's criterion** for Noetherian
  domains in the depth form of Stacks 031S.
* `SerreR1 A` (Stacks 031P (R₁): `A_𝔭` regular for `ht 𝔭 ≤ 1`, Mathlib `IsRegularLocalRing`),
  `serreR1_iff_regularInCodimOne`, and `isIntegrallyClosed_iff_serreR1_and_serreS2`: Stacks 031S
  verbatim for Noetherian domains.

### CJ2b (done) — `CurvesJacobian/CommAlg/RegularLocal.lean`

* `isRegularLocalRing_quotient_span_singleton`: `x ∈ 𝔪 \ 𝔪²` ⇒ `R ⧸ (x)` regular local,
  `dim R ⧸ (x) + 1 = dim R`.
* `IsRegularLocalRing.isDomain` (Stacks 00NP).
* `depthGeTwo_of_isRegularLocalRing` (dim ≥ 2 ⇒ depth ≥ 2; part of Stacks 00NQ).
* `isIntegrallyClosed_of_isRegularRing`: a regular domain is normal (Stacks 0567).

### CJ2c (done) — `CurvesJacobian/CommAlg/Depth.lean`

* `depth I M : ℕ∞` (Stacks 00LI), `SerreS k A` (Stacks 031P (S_k)).
* `depthGeTwo_iff`, `one_le_depth_of_isDomain`, `serreS_two_iff_serreS2`.
* `isIntegrallyClosed_iff_serreR1_and_serreS_two`: Stacks 031S with the definitions of Stacks
  031P, for Noetherian domains. (Non-domain Noetherian rings: not done.)


| CJ3 | normal Noetherian 1-dimensional schemes, closed points of curves ↔ places | **done** (points ↔ places) |

### CJ3a (done) — `CurvesJacobian/Scheme/ValuationPoints.lean`

For `X` integral with all stalks valuation rings, `K = K(X)`:
* `stalkValuationSubring hX x : ValuationSubring K` (the stalk `𝒪_{X,x}`);
* `stalkValuationSubring_injective` (`X` separated; valuative criterion, Stacks 01KZ);
* `exists_stalkValuationSubring_eq` (`π : X ⟶ Y` universally closed; Stacks 01KF + domination);
* `pointEquivValuationSubring : X ≃ {O // ExtendsOver π O}`.

### CJ3b (done) — `CurvesJacobian/Scheme/CurvePlaces.lean` (depends on belyi, weil-curves)

* `extendsOver_iff`: over `Spec k`, `ExtendsOver ↔ k ⊆ O` (belyi's `Algebra k K(X)`).
* `pointEquivValuationSubringOver`: `X ≃ {O : ValuationSubring K(X) // k ⊆ O}`.
* `stalkValuationSubring_eq_top_iff`: `𝒪_{X,x} = K(X) ↔ x` generic.
* `curvePlaceEquiv`: for `IsCurveOver k X`, `k` perfect: non-generic points of `X` ≃
  `WeilCurves.FunctionField.Place k K(X)`, `x ↦ 𝒪_{X,x}`.

### CJ4a (done) — `CurvesJacobian/FunctionField/OfSmooth.lean`, `Scheme/CurveFunctionField.lean`

* Algebra: for `A` a standard smooth domain of relative dimension 1 over a perfect field:
  `krullDimLE_one_of_smooth`, `exists_transcendental_of_smooth` (Kähler rank 1 vs. Ω = 0 for
  finite separable fields), `exists_finite_injective_mvPolynomial_fin_one` (Noether
  normalisation + going-up), `isFunctionField_of_smooth`.
* Schemes: instance `isFunctionField_functionField` (`IsCurveOver k X`, `k` perfect ⇒
  `IsFunctionField k K(X)`), `curveGenus`, `curve_riemannRoch`, `curve_deg_canonical`
  (weil-curves Riemann–Roch transported to curves).

### CJ4b (part 1, done) — `CurvesJacobian/Scheme/ConstantField.lean`

* `mem_range_algebraMap_of_isAlgebraic`: for `X` geometrically integral over a field `k`, `k` is
  algebraically closed in `K(X)` (via belyi's `isDomain_tensorProduct_of_geometricallyIntegral`:
  `L ⊗_k L` is a finite-dimensional domain, hence `L = k`). So `curveGenus` is the usual genus.
* Open: `curveGenus = dim H¹(X, 𝒪_X)` (needs coherent cohomology on curves); divisors on `X`
  vs. Mathlib's `AlgebraicCycle`.
| CJ4 | comparison with weil-curves (places, divisors, ℓ(D)); genus = h¹(O) | **wip** (CJ4a done) |
| CJ5 | canonical embedding, hyperelliptic curves, Hurwitz bound, Bertini | planned |
| CJ6 | Kummer sequence, Pic = H¹(G_m), H²(X_k̄, μ_n) ≅ Z/n via degree | **wip** |

### CJ6a (done) — `CurvesJacobian/Etale/KummerCover.lean`

* `kummerPair`, `kummerPresentation`, `etale_kummer`: `R[T]/(Tⁿ - u)` is standard étale for
  `n, u` units; `faithfullyFlat_kummer` (free of rank `n`); `root_pow_kummer`. The local input of
  the Kummer sequence (Stacks 03PK).

### CJ6b (done) — `CurvesJacobian/Etale/Gm.lean`, `Etale/Kummer.lean`

* `isSheaf_gammaType` (`Γ` represented by `Spec ℤ[T]`, étale topology subcanonical),
  `isSheaf_units`, `gmBig` + `isSheaf_gmBig`, continuity of `etaleForget X : X.Etale ⥤ Scheme`,
  `Gm X : Sheaf X.smallEtaleTopology Ab`.
* `kummerMap X n = n • 𝟙`, `isLocallySurjective_kummerMap`, `epi_kummerMap`, `mu X n`,
  `kummer_shortExact`: `0 → μₙ → 𝔾ₘ → 𝔾ₘ → 0` short exact for `n` invertible on `X`
  (Stacks 03PK).

### CJ6c (done) — `CurvesJacobian/Etale/KummerCohomology.lean`

* `isTerminal_etaleTerminal`, `H0GmEquiv : H⁰(X, 𝔾ₘ) ≃+ Γ(X, 𝒪)ˣ`, `kummerδ`, and the exactness
  of the Kummer long exact sequence `kummer_exact_Gm`, `kummer_exact_δ`, `kummer_exact_mu`.
* Next (large): Hilbert 90 `H¹(X_et, 𝔾ₘ) = Pic X`; `H²(X_k̄, 𝔾ₘ) = 0` for curves (Tsen);
  then `H²(X_k̄, μₙ) ≅ Pic(X_k̄)/n ≅ ℤ/n` via degree; `H¹(X_et, 𝔾ₘ) = Pic X` needs invertible sheaves (tensor product of sheaves of modules
  is not in Mathlib: presheaf-level only) — large.
| CJ7 | Picard group of schemes, Picard functor, representability | **wip** (divisor-level Pic of curves done) |

### CJ7a (done) — `CurvesJacobian/Scheme/CurvePic.lean` (weil-curves pinned 58b577b)

* `ClosedPoint X`, `isClosed_singleton_iff` (closed ⇔ non-generic), `CurveDivisor X`,
  `divisorEquiv : CurveDivisor X ≃+ Divisor k K(X)`, `pointDegree`, `CurveDivisor.deg`.
* `curveDiv f` with `curveDiv_apply` (ord at the place of `x`), `curveDiv_mul`, `deg_curveDiv`,
  `mem_stalk_iff` (`f ∈ 𝒪_{X,x} ↔ ord_x f ≥ 0`).
* `CurvePic X := CurveDivisor X ⧸ curvePrincipal`, `curvePicEquiv : CurvePic X ≃+ Pic k K(X)`,
  `CurvePic.deg`, `CurvePic0 := ker deg`.
* `Scheme/PointDegree.lean`: `pointDegree_eq_finrank` — `deg x = [κ(x) : k]` for the scheme residue
  field (`stalkRingEquiv`: stalk ≅ valuation ring of the place, compatibly with `k`).
* Not done: invertible sheaves / `H¹(X_et, 𝔾ₘ)` comparison, Picard functor (large).
| CJ8 | Jacobian as abelian variety, J[n], theta divisor | **wip** (Pic[n] ≅ unramified μₙ-characters done; CJ-plan §10–11) |

### CJ8a (done) — `CurvesJacobian/FunctionField/KummerPic.lean`

* `kummerClasses k K n` (`f` with `div f ∈ n • Div`), `kummerToPic` (`f ↦ [D]`, `n • D = div f`),
  `kummerToPic_surjective`, `ker_kummerToPic` (constants · `n`-th powers), `picTorsionEquiv`:
  `kummerClasses ⧸ (constants + n-th powers) ≃+ Pic(K)[n]`; `deg_eq_zero_of_mem_picTorsion`.
  Divisor-level half of Milne AV III.9.2. Next: Kummer extensions `K(f^{1/n})` unramified ⇔
  `div f ∈ n • Div`, and the link to `π₁` (pi1). The count `n^{2g}` is open (§10).

### CJ8b (wip) — Kummer covers and inertia

* `FunctionField/KummerInertia.lean` (done): `IsInertial`, `LiesOverPlace`,
  `inertial_fixes_kummerRoot` — for `k` algebraically closed, `n` invertible, `yⁿ = f`,
  `n ∣ ord_P f`: every automorphism inertial at a valuation ring `W | P` fixes `y`.
* `Galois/FunctionFieldF.lean` (deps pi1 8e0239a, continuous-kummer-theory e3fc64c):
  `isFunctionField_F` (the function field `F = Ω^H` of the Galois model is a weil-curves function
  field over `k`), `exists_valuationSubring_liesOver` (places of `F` extend to `Ω`).
* `Galois/UnramifiedKummer.lean`: `IsUnramifiedKummer D n v` (Kummer class trivial on all inertia
  groups of places `W ⊇ k`) and `isUnramifiedKummer_iff`: `↔ ∀ P, n ∣ ord_P v` — via
  continuous-kummer-theory's `evalTriv_res_kummer_eq_zpow` and `evalTriv_kummer_surjective`.
* `Galois/PicTorsion.lean` (done): `unramifiedChars D n ≤ H¹(Gal(Ω/F), μₙ)` (classes trivial on
  the inertia of every place `W ⊇ k` — characters of `Π_X = H ⧸ ⟨⟨all inertia⟩⟩`), and for `k`
  algebraically closed `picTorsionEquivUnramified : Pic(F)[n] ≃+ Additive (unramifiedChars D n)`
  — Milne AV III.9.2 for curves in the Galois model.
* Open: identifying `unramifiedChars` with `Hom_cont(π₁ᵉᵗ(X), μₙ)` for the proper scheme `X`
  (pi1 has the comparison for affine curves); the count `n^{2g}` (lead/π₁ track).
| CJ9 | stable curves over DVRs, log structures | planned |
| CJ10 | Néron models, Raynaud extension | planned |
| CJ11 | fppf Kummer map for formal groups | planned |

Literature looked up: Stacks Project Tags 031P, 031Q, 031R, 031S, 031T, 0567 (2026-10-16).
[LocAn] cites Serre's criterion as "[Mats], Chapter 7, §17.I, Theorem 39" (Lemma 13.3); Matsumura
is not available locally.
