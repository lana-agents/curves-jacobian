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


| CJ3 | normal Noetherian 1-dimensional schemes, closed points of curves ↔ places | **wip** |

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
* Open: `IsFunctionField k K(X)` for curves (from belyi's finite map to ℙ¹), so that weil-curves'
  divisors, `ℓ(D)`, genus apply to `K(X)` (CJ4).
| CJ4 | comparison with weil-curves (places, divisors, ℓ(D)); genus = h¹(O) | planned (needs weil-curves) |
| CJ5 | canonical embedding, hyperelliptic curves, Hurwitz bound, Bertini | planned |
| CJ6 | Kummer sequence, Pic = H¹(G_m), H²(X_k̄, μ_n) ≅ Z/n via degree | planned |
| CJ7 | Picard group of schemes, Picard functor, representability | planned |
| CJ8 | Jacobian as abelian variety, J[n], theta divisor | planned |
| CJ9 | stable curves over DVRs, log structures | planned |
| CJ10 | Néron models, Raynaud extension | planned |
| CJ11 | fppf Kummer map for formal groups | planned |

Literature looked up: Stacks Project Tags 031P, 031Q, 031R, 031S, 031T, 0567 (2026-10-16).
[LocAn] cites Serre's criterion as "[Mats], Chapter 7, §17.I, Theorem 39" (Lemma 13.3); Matsumura
is not available locally.
