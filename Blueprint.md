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

| CJ2 | depth of Noetherian local rings, (R_k)/(S_k) (Stacks 031P), regular ⇒ normal | **wip** (S₂ for domains done) |

### CJ2a (done) — `CurvesJacobian/CommAlg/SerreS2.lean`

* `DepthGeTwo B` (maximal ideal contains a `B`-regular sequence of length 2, i.e. depth ≥ 2 in
  the sense of Stacks 00LI with Mathlib's `IsRegular` = Stacks 00LF); `SerreS2 A` (depth `A_𝔭 ≥ 2`
  for `ht 𝔭 ≥ 2`; for a domain this is Stacks 031P (S₂)).
* `serreS2_iff_assPrimesHeightOne` (Noetherian domains), elementary (no `Ext`); key lemma
  `mem_span_of_isWeaklyRegular_pair`.
* `isIntegrallyClosed_iff_regularInCodimOne_and_serreS2`: **Serre's criterion** for Noetherian
  domains in the depth form of Stacks 031S.
* Open in CJ2: `depth` as an `ℕ∞`-valued invariant, general (S_k) for modules, regular ⇒ normal.

| CJ3 | normal Noetherian 1-dimensional schemes, closed points of curves ↔ places | planned |
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
