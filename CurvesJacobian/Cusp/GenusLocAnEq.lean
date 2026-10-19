/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverGenus

/-!
# `dim H⁰(X, Ω¹) = g` for a curve over a field of characteristic zero

For a curve `X` over a field `k` of characteristic zero (belyi's `IsCurveOver`), the genus
`Belyi.Anabelian.curveGenus k X = dim_k H⁰(X, Ω¹_{X/k})` (regular differentials of the function
field) equals the Riemann–Roch genus `CurvesJacobian.curveGenus k X`
(`CurvesJacobian.Cusp.locAn_curveGenus_eq`). The inequality `≤` is
`CurvesJacobian.Cusp.locAn_curveGenus_le`; here we prove `≥`
(`CurvesJacobian.Cusp.curveGenus_le_locAn`).

Proof. As in `CurvesJacobian.Cusp.finrank_le_genus`, fix `t ∈ F = K(X)` with `F / k(t)` finite
and put `E = Diff(F/k(t)) - 2 (t)_∞`. At every place `Q` the local relation
`c ds = π^{e-1} v dπ` (`s = t` or `t⁻¹`) holds with `c = p'(s)` a *unit* (`p` is separable,
`CurvesJacobian.Cusp.ord_aeval_derivative_minpoly`), so `dt = h_Q dπ_Q` with
`ord_Q h_Q = E(Q)` exactly. Hence `f ↦ f dt` maps `L(E)` injectively into the regular
differentials (`CurvesJacobian.Cusp.genus_le_finrank`). Finally `ℓ(E) ≥ g`: `E` is a canonical
divisor, since `Con W_{k(t)} + Diff = W_F + (x)` (weil-curves, `canonical_linearEquiv`) and on
`k(t)` the degree-zero divisor `W_{k(t)} + 2 (t)_∞` has `ℓ ≥ 1` by Riemann–Roch; so
`ℓ(W_F - E) ≥ 1` and Riemann–Roch gives `ℓ(E) ≥ g`.
-/

open CategoryTheory AlgebraicGeometry Belyi WeilCurves.FunctionField Polynomial Module
  KaehlerDifferential
open scoped IntermediateField

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section FunctionField

variable {k : Type*} [Field k] [CharZero k]

/-- **`p'(s)` is a unit at `P`** for `p` the minimal polynomial of the residue of `s ∈ 𝒪_P`
(characteristic zero: `p` is separable). -/
lemma ord_aeval_derivative_minpoly {K : Type*} [Field K] [Algebra k K] [IsFunctionField k K]
    (P : Place k K) {s : K} (hsP : s ∈ P.1) :
    aeval s (derivative (minpoly k (P.residue ⟨s, hsP⟩))) ≠ 0 ∧
      P.ord (aeval s (derivative (minpoly k (P.residue ⟨s, hsP⟩)))) = 0 := by
  set r := P.residue ⟨s, hsP⟩
  have hint : IsIntegral k r := Algebra.IsIntegral.isIntegral r
  set p := minpoly k r
  set e : P.1 := (derivative p).eval₂ P.baseHom ⟨s, hsP⟩
  have hcomp : P.1.subtype.comp P.baseHom = algebraMap k K := by
    ext q; rfl
  have he : (e : K) = aeval s (derivative p) := by
    have := Polynomial.hom_eval₂ (derivative p) P.baseHom P.1.subtype ⟨s, hsP⟩
    rw [hcomp] at this
    rw [aeval_def]
    exact this
  have hcomp' : P.residue.comp P.baseHom = algebraMap k P.ResidueField := by
    ext q; rfl
  have hres : P.residue e ≠ 0 := by
    rw [Polynomial.hom_eval₂, hcomp', ← aeval_def]
    exact (minpoly.irreducible hint).separable.aeval_derivative_ne_zero (minpoly.aeval k r)
  have he0 : (e : K) ≠ 0 := fun h ↦ hres (by rw [show e = 0 from Subtype.ext h, map_zero])
  rw [← he]
  refine ⟨he0, ?_⟩
  have h1 := P.ord_nonneg_of_mem e.2
  have h2 : ¬ 0 < P.ord e := fun h ↦
    hres (P.residue_eq_zero_iff.mpr ((P.ord_pos_iff_mem_maximalIdeal he0).mp h))
  omega

variable {F : Type*} [Field F] [Algebra k F] [IsFunctionField k F]

/-- **The exact local relation `c ds = π^{e-1} v dπ`** with `c` and `v` units at `Q` and
`e = e(Q | Q ∩ K)`, for `K = k(s)` and `s ∈ 𝒪_Q`. -/
lemma exists_unit_smul_D_eq (K : IntermediateField k F) [IsFunctionField k K]
    [FiniteDimensional K F] (s : K) (hs : Transcendental k s) (h1 : k⟮s⟯ = ⊤) (Q : Place k F)
    (hsQ : (s : F) ∈ Q.1) {π : F} (hπ : Q.ord π = 1)
    (hgen : ∀ u ∈ Q.1, ∃ g ∈ Q.1, D k F u = g • D k F π) :
    ∃ c : F, c ≠ 0 ∧ Q.ord c = 0 ∧ ∃ v : F, v ≠ 0 ∧ Q.ord v = 0 ∧
      c • D k F (s : F) = (π ^ ((ramIndex K Q).toNat - 1) * v) • D k F π := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  set P := Q.restrict (K := K)
  have hsP : s ∈ P.1 := Place.mem_restrict.mpr hsQ
  set p := minpoly k (P.residue ⟨s, hsP⟩)
  have hw := ord_aeval_minpoly_residue_eq_one hs h1 P hsP
  obtain ⟨hc0, hcP⟩ := ord_aeval_derivative_minpoly P hsP
  set e := ramIndex K Q
  have he := ramIndex_pos (K := K) Q
  set n := e.toNat
  have hn : (n : ℤ) = e := Int.toNat_of_nonneg he.le
  have hn1 : 1 ≤ n := by omega
  set w : F := aeval (s : F) p
  have hwK : algebraMap K F (aeval s p) = w := by
    change algebraMap K F (aeval s p) = aeval (algebraMap K F s) p
    rw [aeval_algebraMap_apply]
  have hcK : algebraMap K F (aeval s (derivative p)) = aeval (s : F) (derivative p) := by
    change algebraMap K F (aeval s (derivative p)) = aeval (algebraMap K F s) (derivative p)
    rw [aeval_algebraMap_apply]
  have hQw : Q.ord w = n := by
    rw [← hwK, ord_algebraMap_eq_ramIndex_mul, hw, mul_one, hn]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hQw; omega
  set u := w / π ^ n
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ0
  have hu0 : u ≠ 0 := div_ne_zero hw0 hπn
  have hQu : Q.ord u = 0 := by
    rw [Q.ord_div hw0 hπn, Place.ord_pow, hQw, hπ]; ring
  have huQ : u ∈ Q.1 := Q.mem_of_ord_nonneg hQu.ge
  have hwu : w = u * π ^ n := by rw [div_mul_cancel₀ _ hπn]
  obtain ⟨u', hu'Q, hu'⟩ := hgen u huQ
  set v : F := n * u + π * u'
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnu0 : (n : F) * u ≠ 0 := mul_ne_zero hnF hu0
  have hQnu : Q.ord ((n : F) * u) = 0 := by rw [Q.ord_mul hnF hu0, Q.ord_natCast, hQu, add_zero]
  have hv : v ≠ 0 ∧ Q.ord v = 0 := by
    by_cases hu'0 : u' = 0
    · simp only [v, hu'0, mul_zero, add_zero]; exact ⟨hnu0, hQnu⟩
    · have hπu' : π * u' ≠ 0 := mul_ne_zero hπ0 hu'0
      have hlt : Q.ord ((n : F) * u) < Q.ord (π * u') := by
        rw [hQnu, Q.ord_mul hπ0 hu'0, hπ]
        have := Q.ord_nonneg_of_mem hu'Q
        omega
      have h := Q.ord_add_eq_of_lt hnu0 hπu' hlt
      refine ⟨fun h0 ↦ ?_, h.trans hQnu⟩
      have h1 : (n : F) * u = -(π * u') :=
        eq_neg_of_add_eq_zero_left (h0 : (n : F) * u + π * u' = 0)
      have h2 := congrArg Q.ord h1
      rw [Place.ord_neg] at h2
      omega
  refine ⟨aeval (s : F) (derivative p), ?_, ?_, v, hv.1, hv.2, ?_⟩
  · rw [← hcK]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc0
  · rw [← hcK, ord_algebraMap_eq_ramIndex_mul, hcP, mul_zero]
  have hDw : D k F w = aeval (s : F) (derivative p) • D k F (s : F) :=
    (D k F).map_aeval p (s : F)
  rw [← hDw, hwu, Derivation.leibniz, Derivation.leibniz_pow, hu', ← Nat.cast_smul_eq_nsmul F]
  simp only [smul_smul, ← add_smul]
  congr 1
  simp only [v]
  have hpow : π ^ n = π ^ (n - 1) * π := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  rw [hpow]
  ring

/-- `e · max 0 (-o) = max 0 (-(e · o))` for `e > 0`. -/
lemma mul_max_zero_neg {e o : ℤ} (he : 0 < e) : max 0 (-(e * o)) = e * max 0 (-o) := by
  rcases le_total 0 o with h | h
  · rw [max_eq_left (by nlinarith), max_eq_left (by linarith), mul_zero]
  · rw [max_eq_right (by nlinarith), max_eq_right (by linarith), mul_neg]

/-- **Regular differentials have dimension `≥ g`.** If `H` contains every differential that is
regular everywhere (`ω ∈ 𝒪_Q dπ_Q` for all `Q`), then `g ≤ dim_k H`. -/
theorem genus_le_finrank (π : Place k F → F) (hπ : ∀ Q : Place k F, Q.ord (π Q) = 1)
    (hgen : ∀ Q : Place k F, ∀ u ∈ Q.1, ∃ g ∈ Q.1, D k F u = g • D k F (π Q))
    (hell : Divisor.ell (0 : Divisor k F) = 1) [Nontrivial Ω[F⁄k]]
    (H : Submodule k Ω[F⁄k]) [FiniteDimensional k H]
    (hH : ∀ ω : Ω[F⁄k], (∀ Q : Place k F, ∃ g ∈ Q.1, ω = g • D k F (π Q)) → ω ∈ H) :
    genus k F ≤ finrank k H := by
  classical
  obtain ⟨t, ht, hfin⟩ := IsFunctionField.exists_finite (k := k) (K := F)
  set K := k⟮t⟯
  set tK : K := IntermediateField.AdjoinSimple.gen k t
  have htK : Transcendental k tK := by
    rw [← transcendental_algebraMap_iff (algebraMap K F).injective]; exact ht
  have htop : k⟮tK⟯ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have htop' : k⟮tK⁻¹⟯ = ⊤ := by rw [adjoin_inv_eq]; exact htop
  have hK1' : finrank k⟮tK⟯ K = 1 := by
    rw [IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  haveI : FiniteDimensional k⟮tK⟯ K := Module.finite_of_finrank_eq_succ hK1'
  haveI : IsFunctionField k K := ⟨⟨tK, htK, inferInstance⟩⟩
  have hgK : genus k K = 0 :=
    genus_eq_zero_of_finrank_eq_one (ell_zero_eq_one_of_le K hell) htK hK1'
  -- the divisor `E = Diff(F/K) - 2 (t)_∞`
  set E : Divisor k F := different k K F - 2 • Divisor.polarDivisor k t
  have hdegE : E.deg = 2 * genus k F - 2 := by
    have hRH := riemannHurwitz (k := k) (K := K) (L := F)
    rw [hgK] at hRH
    have hpol : (Divisor.polarDivisor k t).deg = finrank K F := Divisor.deg_polarDivisor ht
    simp only [E, Divisor.deg_sub, Divisor.deg_nsmul]
    rw [hpol]
    push_cast
    linarith
  -- the exact local relation `dt = h dπ_Q` with `ord_Q h = E(Q)`
  have hloc : ∀ Q : Place k F, ∃ h : F, h ≠ 0 ∧ D k F t = h • D k F (π Q) ∧
      Q.ord h = E Q := by
    intro Q
    have hπ0 : π Q ≠ 0 := by intro h0; have := hπ Q; rw [h0, Place.ord_zero] at this; omega
    have hdiff : different k K F Q = ramIndex K Q - 1 := different_apply_of_charZero Q
    have he := ramIndex_pos (K := K) Q
    by_cases htQ : t ∈ Q.1
    · obtain ⟨c, hc0, hcQ, v, hv0, hvQ, hrel⟩ :=
        exists_unit_smul_D_eq K tK htK htop Q htQ (hπ Q) (hgen Q)
      have hrel' : c • D k F t =
          (π Q ^ ((ramIndex K Q).toNat - 1) * v) • D k F (π Q) := hrel
      have hpv : π Q ^ ((ramIndex K Q).toNat - 1) * v ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ0) hv0
      refine ⟨(π Q ^ ((ramIndex K Q).toNat - 1) * v) / c, div_ne_zero hpv hc0, ?_, ?_⟩
      · rw [div_eq_mul_inv, mul_comm _ c⁻¹, mul_smul, ← hrel', smul_smul, inv_mul_cancel₀ hc0,
          one_smul]
      · rw [Q.ord_div hpv hc0, Q.ord_mul (pow_ne_zero _ hπ0) hv0, Place.ord_pow, hπ Q, hvQ, hcQ]
        have htQ' := Q.ord_nonneg_of_mem htQ
        simp only [E, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
          Divisor.polarDivisor_apply, hdiff, nsmul_eq_mul, Nat.cast_ofNat]
        rw [max_eq_left (by omega)]
        omega
    · have hti : t⁻¹ ∈ Q.1 := (Q.mem_or_inv_mem t).resolve_left htQ
      have htQ' : Q.ord t < 0 := (Q.ord_neg_iff).mpr htQ
      have ht0 : t ≠ 0 := by rintro rfl; exact htQ (Subring.zero_mem _)
      have htiK : ((tK⁻¹ : K) : F) = t⁻¹ := by simp [tK]
      obtain ⟨c, hc0, hcQ, v, hv0, hvQ, hrel⟩ :=
        exists_unit_smul_D_eq K tK⁻¹ (transcendental_inv htK) htop' Q (htiK ▸ hti) (hπ Q)
          (hgen Q)
      rw [htiK, Derivation.leibniz_inv, smul_smul] at hrel
      have hpv : π Q ^ ((ramIndex K Q).toNat - 1) * v ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ0) hv0
      have ht2 : -t⁻¹ ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero ht0))
      have hct : c * -t⁻¹ ^ 2 ≠ 0 := mul_ne_zero hc0 ht2
      refine ⟨(π Q ^ ((ramIndex K Q).toNat - 1) * v) / (c * -t⁻¹ ^ 2), div_ne_zero hpv hct,
        ?_, ?_⟩
      · rw [div_eq_mul_inv, mul_comm _ (c * -t⁻¹ ^ 2)⁻¹, mul_smul, ← hrel, smul_smul,
          inv_mul_cancel₀ hct, one_smul]
      · rw [Q.ord_div hpv hct, Q.ord_mul (pow_ne_zero _ hπ0) hv0, Place.ord_pow, hπ Q, hvQ,
          Q.ord_mul hc0 ht2, Place.ord_neg, Place.ord_pow, Place.ord_inv, hcQ]
        simp only [E, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
          Divisor.polarDivisor_apply, hdiff, nsmul_eq_mul, Nat.cast_ofNat]
        rw [max_eq_right (by omega)]
        omega
  -- `dt ≠ 0`
  have hDt : D k F t ≠ 0 := kaehler_D_ne_zero
  -- the injective map `L(E) → H`, `f ↦ f dt`
  let Ψ₀ : Divisor.L E →ₗ[k] Ω[F⁄k] :=
    ((LinearMap.toSpanSingleton F Ω[F⁄k] (D k F t)).restrictScalars k) ∘ₗ (Divisor.L E).subtype
  have hΨ₀ : ∀ f : Divisor.L E, Ψ₀ f ∈ H := by
    intro f
    refine hH _ fun Q ↦ ?_
    obtain ⟨h, hh0, hh, hord⟩ := hloc Q
    refine ⟨(f : F) * h, ?_, ?_⟩
    · by_cases hf0 : (f : F) = 0
      · rw [hf0, zero_mul]; exact Subring.zero_mem _
      refine Q.mem_of_ord_nonneg ?_
      have := ((Divisor.mem_L.mp f.2).resolve_left hf0) Q
      rw [Q.ord_mul hf0 hh0]
      omega
    · change (f : F) • D k F t = _
      rw [hh, smul_smul]
  let Ψ : Divisor.L E →ₗ[k] H := LinearMap.codRestrict H Ψ₀ hΨ₀
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker] at hf
    have : (f : F) • D k F t = 0 := congrArg Subtype.val hf
    rw [smul_eq_zero] at this
    rcases this with h | h
    · exact (Submodule.mem_bot k).mpr (Subtype.ext h)
    · exact absurd h hDt
  have h1 : Divisor.ell E ≤ finrank k H := LinearMap.finrank_le_finrank_of_injective hΨ
  -- `ℓ(D_K) ≥ 1` for the degree-zero divisor `D_K = W_K + 2 (t)_∞` of `K`
  set DK : Divisor k K := canonical k K + 2 • Divisor.polarDivisor k tK
  have hdegDK : DK.deg = 0 := by
    have hpol : (Divisor.polarDivisor k tK).deg = finrank k⟮tK⟯ K := Divisor.deg_polarDivisor htK
    have hW := deg_canonical (k := k) (K := K)
    simp only [DK, Divisor.deg_add, Divisor.deg_nsmul]
    rw [hpol, hK1', hW, hgK]
    norm_num
  have hDK : 0 < Divisor.ell DK := by
    have hRR := riemannRoch DK
    rw [hdegDK, hgK] at hRR
    have : (0 : ℤ) < Divisor.ell DK := by
      have := Int.natCast_nonneg (Divisor.ell (canonical k K - DK))
      linarith
    exact_mod_cast this
  rw [Divisor.ell] at hDK
  obtain ⟨⟨y, hy⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hDK
  have hy0' : y ≠ 0 := fun h ↦ hy0 (Subtype.ext h)
  have hyP := (Divisor.mem_L.mp hy).resolve_left hy0'
  -- `ℓ(W_F - E) ≥ 1`
  obtain ⟨x, hx0, hxeq⟩ := canonical_linearEquiv (k := k) (K := K) (L := F)
  set z : F := x * algebraMap K F y
  have hyF : algebraMap K F y ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hy0'
  have hz0 : z ≠ 0 := mul_ne_zero hx0 hyF
  have hz : z ∈ Divisor.L (canonical k F - E) := by
    refine Divisor.mem_L.mpr (Or.inr fun Q ↦ ?_)
    have hQ := DFunLike.congr_fun hxeq Q
    simp only [Finsupp.coe_add, Pi.add_apply, conormOf_apply, Divisor.div_apply] at hQ
    have hyQ := hyP (Q.restrict (K := K))
    simp only [DK, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply,
      Divisor.polarDivisor_apply, nsmul_eq_mul, Nat.cast_ofNat] at hyQ
    have he := ramIndex_pos (K := K) Q
    have hmul := mul_le_mul_of_nonneg_left hyQ he.le
    have htQ : Q.ord t = ramIndex K Q * (Q.restrict (K := K)).ord tK :=
      ord_algebraMap_eq_ramIndex_mul Q tK
    have hmax := mul_max_zero_neg (o := (Q.restrict (K := K)).ord tK) he
    simp only [z, E, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
      Divisor.polarDivisor_apply, nsmul_eq_mul, Nat.cast_ofNat]
    rw [Q.ord_mul hx0 hyF, ord_algebraMap_eq_ramIndex_mul, htQ, hmax]
    linarith
  have hWE : 0 < Divisor.ell (canonical k F - E) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨z, hz⟩, fun h ↦ hz0 (congrArg Subtype.val h)⟩
  -- Riemann–Roch: `ℓ(E) = g - 1 + ℓ(W_F - E) ≥ g`
  have hRR := riemannRoch E
  rw [hdegE] at hRR
  have hWE' : (1 : ℤ) ≤ Divisor.ell (canonical k F - E) := by exact_mod_cast hWE
  have h1' : (Divisor.ell E : ℤ) ≤ finrank k H := by exact_mod_cast h1
  linarith

end FunctionField

section Curve

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsCurveOver k X]

section Integral

variable [IsIntegral X]

/-- **`g ≤ dim_k H⁰(X, Ω¹)`** for a curve over a field of characteristic zero. -/
theorem curveGenus_le_locAn [CharZero k] :
    curveGenus k X ≤ (Anabelian.curveGenus k X : ℤ) := by
  set F := X.functionField
  choose π hπ using fun Q : Place k F ↦ Q.exists_ord_eq_one
  have hπQ : ∀ Q : Place k F, π Q ∈ Q.1 := fun Q ↦ Q.mem_of_ord_nonneg (by rw [hπ Q]; omega)
  choose π' hπ' using fun Q : Place k F ↦ exists_stalk_eq k X Q (hπQ Q)
  have hmax : ∀ Q : Place k F, IsLocalRing.maximalIdeal
      (X.presheaf.stalk (pointOfPlace k X Q)) = Ideal.span {π' Q} := fun Q ↦
    maximalIdeal_stalk_eq_span k X Q (by rw [hπ' Q, hπ Q])
  have hfin : ∀ Q : Place k F,
      letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
      Module.Finite (X.presheaf.stalk (pointOfPlace k X Q))
        Ω[X.presheaf.stalk (pointOfPlace k X Q)⁄k] := fun Q ↦ by
    letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
    haveI := essFiniteType_stalk k X (pointOfPlace k X Q)
    infer_instance
  haveI : Nontrivial Ω[F⁄k] :=
    Module.nontrivial_of_finrank_eq_succ
      (Module.finrank_eq_of_rank_eq (by rw [rank_kaehler_functionField k X]; rfl) :
        finrank F Ω[F⁄k] = 0 + 1)
  haveI := finiteDimensional_globalDifferentials k X
  refine genus_le_finrank π hπ (fun Q u hu ↦ ?_) (ell_zero_eq_one k X)
    (Anabelian.globalDifferentials k X) (fun ω hω ↦ ?_)
  · letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
    haveI := Anabelian.stalkAlgebra_isScalarTower k X (pointOfPlace k X Q)
    haveI := hfin Q
    obtain ⟨a, rfl⟩ := exists_stalk_eq k X Q hu
    obtain ⟨g, hg⟩ := exists_D_eq_smul_D (exists_aeval_stalk k X Q) (hmax Q) (F := F) a
    refine ⟨algebraMap _ F g, (stalkPlaceEquiv k X Q g).2, ?_⟩
    rw [hg, hπ' Q]
  · rw [Anabelian.globalDifferentials, Submodule.mem_iInf]
    intro x
    letI := Anabelian.stalkAlgebra k X x
    haveI := Anabelian.stalkAlgebra_isScalarTower k X x
    by_cases hx : x = genericPoint X
    · obtain ⟨a, ha⟩ := KaehlerDifferential.map_surjective_of_surjective k k
        (X.presheaf.stalk x) F
        (fun f ↦ mem_range_algebraMap_of_eq_genericPoint hx f) ω
      exact ⟨a, ha⟩
    · obtain ⟨Q, rfl⟩ : ∃ Q : Place k F, pointOfPlace k X Q = x :=
        ⟨curvePlaceEquiv k X ⟨x, hx⟩, by simp [pointOfPlace]⟩
      obtain ⟨g, hgQ, rfl⟩ := hω Q
      obtain ⟨a, rfl⟩ := exists_stalk_eq k X Q hgQ
      refine ⟨a • D k _ (π' Q), ?_⟩
      change KaehlerDifferential.map k k _ F (a • D k _ (π' Q)) = _
      rw [LinearMap.map_smul, KaehlerDifferential.map_D, hπ' Q, algebraMap_smul]

/-- **`dim_k H⁰(X, Ω¹) = g`** for a curve over a field of characteristic zero. -/
theorem locAn_curveGenus_eq [CharZero k] :
    (Anabelian.curveGenus k X : ℤ) = curveGenus k X :=
  le_antisymm (locAn_curveGenus_le k X) (curveGenus_le_locAn k X)

/-- `g = dim_k H⁰(X, Ω¹)` as natural numbers. -/
theorem curveGenus_toNat_eq_locAn [CharZero k] :
    (curveGenus k X).toNat = Anabelian.curveGenus k X := by
  rw [← locAn_curveGenus_eq k X, Int.toNat_natCast]

/-- `g ≤ dim_k H⁰(X, Ω¹)` as natural numbers. -/
theorem curveGenus_toNat_le_locAn [CharZero k] :
    (curveGenus k X).toNat ≤ Anabelian.curveGenus k X :=
  (curveGenus_toNat_eq_locAn k X).le

end Integral

/-- **A curve of positive genus has a nonzero regular differential** (characteristic zero):
the hypothesis `hg` of `CurvesJacobian.Cusp.two_lt_locAn_of_not_commute_baseChange`. -/
theorem locAn_curveGenus_pos [CharZero k] :
    haveI := IsCurveOver.isIntegral k X
    0 < (curveGenus k X).toNat → 0 < Anabelian.curveGenus k X := by
  haveI := IsCurveOver.isIntegral k X
  intro h
  exact h.trans_le (curveGenus_toNat_le_locAn k X)

end Curve

end CurvesJacobian.Cusp
