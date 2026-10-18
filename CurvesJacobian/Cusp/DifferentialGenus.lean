/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.RationalPlace
import WeilCurves.Hurwitz.Tame

/-!
# Regular Kähler differentials of a function field: `dim ≤ g`

Let `F` be a function field of one variable over a field `k` of characteristic zero with `k`
algebraically closed in `F` (`ℓ(0) = 1`). Suppose that for every place `Q` we are given a
uniformiser `π_Q` such that `du ∈ 𝒪_Q dπ_Q` for all `u ∈ 𝒪_Q` (this holds for the local rings
of a smooth curve, `CurvesJacobian.Cusp.kaehler_eq_smul_D`). Then every `k`-subspace `H` of
`Ω_{F/k}` consisting of differentials that are regular everywhere (`ω ∈ 𝒪_Q dπ_Q` for all `Q`)
has `dim_k H ≤ g` (`CurvesJacobian.Cusp.finrank_le_genus`), where `g` is the genus of `F`
(weil-curves, Riemann–Roch).

Proof. Fix `t ∈ F` transcendental with `F / k(t)` finite and put `K = k(t)`. At a place `Q`, let
`s = t` if `t ∈ 𝒪_Q` and `s = t⁻¹` otherwise, `P = Q ∩ K`, `p` the minimal polynomial of the
residue of `s` at `P`, `w = p(s)` (a uniformiser at `P`, `CurvesJacobian.Cusp.ord_aeval_minpoly_
residue_eq_one`) and `e = e(Q|P) = ord_Q w`. Writing `w = u π^e`, `dw = π^{e-1}(e u + π u') dπ`
with `e u + π u'` a unit, and `dw = p'(s) ds`; hence `dπ = h_Q dt` with
`ord_Q h_Q ≥ -E(Q)`, `E = Diff(F/K) - 2 (t)_∞` (`CurvesJacobian.Cusp.exists_D_uniformizer_eq`).
So every regular `ω` is `f dt` with `f ∈ L(E)`, and `deg E = 2g - 2` by the Riemann–Hurwitz
formula (`g(K) = 0`), so `ℓ(E) ≤ g` by Riemann–Roch.
-/

open WeilCurves.FunctionField Polynomial Module KaehlerDifferential
open scoped IntermediateField

namespace CurvesJacobian.Cusp

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [IsFunctionField k F]

omit [CharZero k] [IsFunctionField k F] in
/-- Polynomials in an element of `𝒪_Q` lie in `𝒪_Q`. -/
lemma aeval_mem_place (Q : Place k F) {s : F} (hs : s ∈ Q.1) (p : k[X]) : aeval s p ∈ Q.1 := by
  rw [aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (Q.algebraMap_mem _) (Subring.pow_mem _ hs _)

section Local

variable (K : IntermediateField k F) [IsFunctionField k K] [FiniteDimensional K F]

/-- **The local relation `c ds = π^{e-1} v dπ`** with `c ∈ 𝒪_Q`, `v` a unit at `Q` and
`e = e(Q | Q ∩ K)`, for `K = k(s)` and `s ∈ 𝒪_Q`. -/
lemma exists_smul_D_eq (s : K) (hs : Transcendental k s) (h1 : k⟮s⟯ = ⊤) (Q : Place k F)
    (hsQ : (s : F) ∈ Q.1) {π : F} (hπ : Q.ord π = 1)
    (hgen : ∀ u ∈ Q.1, ∃ g ∈ Q.1, D k F u = g • D k F π) :
    ∃ c ∈ Q.1, ∃ v : F, v ≠ 0 ∧ Q.ord v = 0 ∧
      c • D k F (s : F) = (π ^ ((ramIndex K Q).toNat - 1) * v) • D k F π := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  set P := Q.restrict (K := K)
  have hsP : s ∈ P.1 := Place.mem_restrict.mpr hsQ
  set p := minpoly k (P.residue ⟨s, hsP⟩)
  have hw := ord_aeval_minpoly_residue_eq_one hs h1 P hsP
  set e := ramIndex K Q
  have he := ramIndex_pos (K := K) Q
  set n := e.toNat
  have hn : (n : ℤ) = e := Int.toNat_of_nonneg he.le
  have hn1 : 1 ≤ n := by omega
  set w : F := aeval (s : F) p
  have hwK : algebraMap K F (aeval s p) = w := by
    change algebraMap K F (aeval s p) = aeval (algebraMap K F s) p
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
  refine ⟨aeval (s : F) (derivative p), aeval_mem_place Q hsQ _, v, hv.1, hv.2, ?_⟩
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

end Local

/-- `ℓ(0) = 1` for a subfield `K ⊆ F` (a function field over `k`) if `ℓ(0) = 1` for `F`. -/
lemma ell_zero_eq_one_of_le (K : IntermediateField k F) [IsFunctionField k K]
    (hell : Divisor.ell (0 : Divisor k F) = 1) : Divisor.ell (0 : Divisor k K) = 1 := by
  have hle : Divisor.ell (0 : Divisor k K) ≤ 1 := by
    rw [← hell, Divisor.ell, Divisor.ell]
    let φ : Divisor.L (0 : Divisor k K) →ₗ[k] Divisor.L (0 : Divisor k F) :=
      { toFun := fun f ↦ ⟨algebraMap K F f, Divisor.mem_L_zero.mpr
          ((Divisor.mem_L_zero.mp f.2).algebraMap)⟩
        map_add' := fun a b ↦ Subtype.ext (map_add _ _ _)
        map_smul' := fun c a ↦ Subtype.ext (by
          simp only [SetLike.val_smul, RingHom.id_apply, Algebra.smul_def, map_mul]
          rfl) }
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) fun a b h ↦ ?_
    apply Subtype.ext
    apply (algebraMap K F).injective
    have h' : ((φ a : Divisor.L (0 : Divisor k F)) : F) = (φ b : F) := by rw [h]
    exact h'
  have hpos : 0 < Divisor.ell (0 : Divisor k K) := by
    rw [Divisor.ell]
    refine Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨1, Divisor.mem_L_zero.mpr isAlgebraic_one⟩, fun h ↦ one_ne_zero (congrArg Subtype.val h)⟩
  omega

/-- **Regular differentials have dimension `≤ g`.** -/
theorem finrank_le_genus (π : Place k F → F) (hπ : ∀ Q : Place k F, Q.ord (π Q) = 1)
    (hgen : ∀ Q : Place k F, ∀ u ∈ Q.1, ∃ g ∈ Q.1, D k F u = g • D k F (π Q))
    (hell : Divisor.ell (0 : Divisor k F) = 1)
    (H : Submodule k Ω[F⁄k]) (hH : ∀ ω ∈ H, ∀ Q : Place k F, ∃ g ∈ Q.1, ω = g • D k F (π Q)) :
    (finrank k H : ℤ) ≤ genus k F := by
  classical
  obtain ⟨t, ht, hfin⟩ := IsFunctionField.exists_finite (k := k) (K := F)
  set K := k⟮t⟯
  set tK : K := IntermediateField.AdjoinSimple.gen k t
  have htx : algebraMap K F tK = t := rfl
  have htK : Transcendental k tK := by
    rw [← transcendental_algebraMap_iff (algebraMap K F).injective, htx]; exact ht
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
  -- the local relation at every place
  have hloc : ∀ Q : Place k F, ∃ h : F, D k F (π Q) = h • D k F t ∧
      (h = 0 ∨ -E Q ≤ Q.ord h) := by
    intro Q
    have hπ0 : π Q ≠ 0 := by intro h0; have := hπ Q; rw [h0, Place.ord_zero] at this; omega
    have hdiff : different k K F Q = ramIndex K Q - 1 := different_apply_of_charZero Q
    have he := ramIndex_pos (K := K) Q
    by_cases htQ : t ∈ Q.1
    · obtain ⟨c, hcQ, v, hv0, hvQ, hrel⟩ :=
        exists_smul_D_eq K tK htK htop Q htQ (hπ Q) (hgen Q)
      have hpv : π Q ^ ((ramIndex K Q).toNat - 1) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ0) hv0
      refine ⟨c / (π Q ^ ((ramIndex K Q).toNat - 1) * v), ?_, ?_⟩
      · have hrel' : c • D k F t =
            (π Q ^ ((ramIndex K Q).toNat - 1) * v) • D k F (π Q) := hrel
        rw [div_eq_inv_mul, mul_smul, hrel', smul_smul, inv_mul_cancel₀ hpv, one_smul]
      · by_cases hc : c = 0
        · left; rw [hc, zero_div]
        right
        rw [Q.ord_div hc hpv, Q.ord_mul (pow_ne_zero _ hπ0) hv0, Place.ord_pow, hπ Q, hvQ]
        have hc' := Q.ord_nonneg_of_mem hcQ
        have htQ' := Q.ord_nonneg_of_mem htQ
        simp only [E, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
          Divisor.polarDivisor_apply, hdiff, nsmul_eq_mul, Nat.cast_ofNat]
        rw [max_eq_left (by omega)]
        omega
    · have hti : t⁻¹ ∈ Q.1 := (Q.mem_or_inv_mem t).resolve_left htQ
      have htQ' : Q.ord t < 0 := (Q.ord_neg_iff).mpr htQ
      have ht0 : t ≠ 0 := by rintro rfl; exact htQ (Subring.zero_mem _)
      have htiK : ((tK⁻¹ : K) : F) = t⁻¹ := by simp [tK]
      obtain ⟨c, hcQ, v, hv0, hvQ, hrel⟩ :=
        exists_smul_D_eq K tK⁻¹ (transcendental_inv htK) htop' Q (htiK ▸ hti) (hπ Q) (hgen Q)
      rw [htiK, Derivation.leibniz_inv, smul_smul] at hrel
      have hpv : π Q ^ ((ramIndex K Q).toNat - 1) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ0) hv0
      refine ⟨c * -t⁻¹ ^ 2 / (π Q ^ ((ramIndex K Q).toNat - 1) * v), ?_, ?_⟩
      · rw [div_eq_inv_mul, mul_smul, hrel, smul_smul, inv_mul_cancel₀ hpv, one_smul]
      · by_cases hc : c = 0
        · left; rw [hc, zero_mul, zero_div]
        right
        have hct : c * -t⁻¹ ^ 2 ≠ 0 := mul_ne_zero hc (neg_ne_zero.mpr (pow_ne_zero _
          (inv_ne_zero ht0)))
        rw [Q.ord_div hct hpv, Q.ord_mul (pow_ne_zero _ hπ0) hv0, Place.ord_pow, hπ Q, hvQ,
          Q.ord_mul hc (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero ht0))), Place.ord_neg,
          Place.ord_pow, Place.ord_inv]
        have hc' := Q.ord_nonneg_of_mem hcQ
        simp only [E, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
          Divisor.polarDivisor_apply, hdiff, nsmul_eq_mul, Nat.cast_ofNat]
        rw [max_eq_right (by omega)]
        omega
  -- `g ≥ 0`
  have hg0 : 0 ≤ genus k F := by
    have := ell_canonical (k := k) (K := F)
    rw [hell] at this
    omega
  by_cases hDt : D k F t = 0
  · -- then every `dπ_Q` vanishes, so `H = 0`
    have hH0 : H = ⊥ := by
      rw [eq_bot_iff]
      intro ω hω
      obtain ⟨Q₀, -⟩ := Place.exists_ord_neg (k := k) ht
      obtain ⟨g, -, rfl⟩ := hH ω hω Q₀
      obtain ⟨h, hh, -⟩ := hloc Q₀
      rw [hh, hDt, smul_zero, smul_zero]
      exact Submodule.zero_mem _
    rw [hH0, finrank_bot, Nat.cast_zero]
    exact hg0
  -- the injective map `L(E) → Ω`, `f ↦ f dt`
  let Ψ : Divisor.L E →ₗ[k] Ω[F⁄k] :=
    ((LinearMap.toSpanSingleton F Ω[F⁄k] (D k F t)).restrictScalars k) ∘ₗ (Divisor.L E).subtype
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker] at hf
    have : (f : F) • D k F t = 0 := hf
    rw [smul_eq_zero] at this
    rcases this with h | h
    · exact (Submodule.mem_bot k).mpr (Subtype.ext h)
    · exact absurd h hDt
  have hHle : H ≤ LinearMap.range Ψ := by
    intro ω hω
    obtain ⟨Q₀, -⟩ := Place.exists_ord_neg (k := k) ht
    obtain ⟨g₀, -, hg₀⟩ := hH ω hω Q₀
    obtain ⟨h₀, hh₀, -⟩ := hloc Q₀
    set f := g₀ * h₀
    have hωf : ω = f • D k F t := by rw [hg₀, hh₀, smul_smul]
    have hfL : f ∈ Divisor.L E := by
      refine Divisor.mem_L.mpr ?_
      by_cases hf0 : f = 0
      · exact Or.inl hf0
      refine Or.inr fun Q ↦ ?_
      obtain ⟨g, hgQ, hg⟩ := hH ω hω Q
      obtain ⟨h, hh, hord⟩ := hloc Q
      have hfeq : f = g * h := by
        have h1 : f • D k F t = (g * h) • D k F t := by rw [← hωf, hg, hh, smul_smul]
        have h2 : (f - g * h) • D k F t = 0 := by rw [sub_smul, h1, sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hDt
      rw [hfeq] at hf0 ⊢
      have hg0 : g ≠ 0 := left_ne_zero_of_mul hf0
      have hh0 : h ≠ 0 := right_ne_zero_of_mul hf0
      rw [Q.ord_mul hg0 hh0]
      have := Q.ord_nonneg_of_mem hgQ
      rcases hord with h' | h'
      · exact absurd h' hh0
      · omega
    exact ⟨⟨f, hfL⟩, hωf.symm⟩
  haveI : FiniteDimensional k (LinearMap.range Ψ) := LinearMap.finiteDimensional_range Ψ
  have h1 : finrank k H ≤ Divisor.ell E := by
    calc finrank k H ≤ finrank k (LinearMap.range Ψ) := Submodule.finrank_mono hHle
      _ = Divisor.ell E := LinearMap.finrank_range_of_inj hΨ
  -- `ℓ(E) ≤ g` by Riemann–Roch
  have hRR := riemannRoch E
  have hle := Divisor.ell_le_max (canonical k F - E)
  rw [Divisor.deg_sub, deg_canonical, hdegE, sub_self, zero_add, hell] at hle
  have : (Divisor.ell (canonical k F - E) : ℤ) ≤ 1 := hle.trans (by simp)
  have h1' : (finrank k H : ℤ) ≤ Divisor.ell E := by exact_mod_cast h1
  rw [hdegE] at hRR
  linarith

end CurvesJacobian.Cusp
