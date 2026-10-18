/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.MatSheaf
import CurvesJacobian.Picard.PicLocTriv
import CurvesJacobian.Picard.LocIso

/-!
# Invertible sheaves glued from two charts by a transition function

This file is generic. Let `Y` be a scheme covered by two opens `U`, `V` and let
`t ∈ Γ(Y, U ∩ V)ˣ`. The invertible sheaf `𝒪(t) = TwoChart.tw U V t` (the `1 × 1` case of
`CurvesJacobian.MatSheaf.Data`) has a basis `bU` on `U` and a basis `bV` on `V` with
`bV = t · bU` on `U ∩ V` (`TwoChart.bV_res`).

* `TwoChart.nonempty_iso_pullback_tw`: if a sheaf `N` on `T` has bases `ε` on `s⁻¹U`, `δ` on
  `s⁻¹V` with `δ = s^♯ t · ε` on the overlap, then `s^* 𝒪(t) ≅ N`. In particular
  (`s = 𝟙`) every invertible sheaf with bases on `U` and `V` is some `𝒪(t)`
  (`TwoChart.exists_nonempty_iso_tw`), and `s^* 𝒪(t) ≅ 𝒪(s^♯ t)` (`TwoChart.map_mk_tw`).
* `TwoChart.mk_tw_eq_mk_tw_iff`: `𝒪(t) ≅ 𝒪(t')` iff `v t' = t u` on `U ∩ V` for units
  `u ∈ Γ(U)ˣ`, `v ∈ Γ(V)ˣ` (the transition functions differ by a Čech coboundary of units);
  `TwoChart.mk_tw_one`: `𝒪(1)` is trivial.

This is the Čech description of `Pic` for a covering by two opens (Stacks, Tag 01CX/0B8M for
invertible modules on locally ringed spaces), used to compute the tangent space of the Picard
scheme.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Matrix

universe u

noncomputable section

namespace CurvesJacobian.TwoChart

open Scheme ModulesGlue MatSheaf

variable {Y : Scheme.{u}} (U V : Y.Opens)

/-- The `1 × 1` matrix data with transition function `t` from `V` to `U`. -/
def twData (t : Γ(Y, U ⊓ V)ˣ) : Data U V where
  n := 1
  m := 1
  eU := 1
  eV := 1
  Φ := Matrix.of fun _ _ ↦ (t : Γ(Y, U ⊓ V))
  Ψ := Matrix.of fun _ _ ↦ ((t⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V))
  eU_mul := mul_one 1
  eV_mul := mul_one 1
  Φ_Ψ := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
  Ψ_Φ := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
  eU_Φ := by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  Φ_eV := by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

instance (t : Γ(Y, U ⊓ V)ˣ) : Unique (Fin (twData U V t).n) := inferInstanceAs (Unique (Fin 1))

instance (t : Γ(Y, U ⊓ V)ˣ) : Unique (Fin (twData U V t).m) := inferInstanceAs (Unique (Fin 1))

/-- The invertible sheaf `𝒪(t)` glued from `𝒪_U` and `𝒪_V` along `t`. -/
def tw (t : Γ(Y, U ⊓ V)ˣ) : Y.Modules := (twData U V t).sheaf

variable {U V} (t : Γ(Y, U ⊓ V)ˣ)

/-- Rank-one data on `U`. -/
def rankOneU : (twData U V t).RankOneU U where
  le := le_refl U
  p := fun _ ↦ 1
  l := fun _ ↦ 1
  eU_eq := by
    ext i j
    fin_cases i; fin_cases j
    simp [twData, vecMulVec_apply]
  dot := by
    change ∑ _ : Fin 1, (1 : Γ(Y, _)) * 1 = 1
    simp

/-- Rank-one data on `V`. -/
def rankOneV : (twData U V t).RankOneV V where
  le := le_refl V
  p := fun _ ↦ 1
  l := fun _ ↦ 1
  eV_eq := by
    ext i j
    fin_cases i; fin_cases j
    simp [twData, vecMulVec_apply]
  dot := by
    change ∑ _ : Fin 1, (1 : Γ(Y, _)) * 1 = 1
    simp

/-- The basis of `𝒪(t)` on `U`. -/
def bU : Γ(tw U V t, U) := (rankOneU t).sec

/-- The basis of `𝒪(t)` on `V`. -/
def bV : Γ(tw U V t, V) := (rankOneV t).sec

lemma isBasisOn_bU : (tw U V t).IsBasisOn U (bU t) := (rankOneU t).isBasisOn

lemma isBasisOn_bV : (tw U V t).IsBasisOn V (bV t) := (rankOneV t).isBasisOn

lemma isInvertible_tw (hUV : U ⊔ V = ⊤) : (tw U V t).IsInvertible where
  exists_basis y := by
    have : y ∈ U ⊔ V := hUV ▸ trivial
    rcases Opens.mem_sup.mp this with h | h
    · exact ⟨U, bU t, h, isBasisOn_bU t⟩
    · exact ⟨V, bV t, h, isBasisOn_bV t⟩

lemma rs_tw {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(tw U V t, W)) :
    rs (tw U V t) h x = (twData U V t).restrictSec h x := rfl

/-- **The transition function of `𝒪(t)`**: `bV = t · bU` on `U ∩ V`. -/
lemma bV_res : rs (tw U V t) (inf_le_right : U ⊓ V ≤ V) (bV t) =
    (t : Γ(Y, U ⊓ V)) • rs (tw U V t) (inf_le_left : U ⊓ V ≤ U) (bU t) := by
  refine Subtype.ext (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
  · change ρ _ (((twData U V t).Φ.map (ρ _) *ᵥ rv _ (fun _ ↦ (1 : Γ(Y, V)))) i) =
      ρ _ (t : Γ(Y, U ⊓ V)) * ρ _ (rv _ (fun _ ↦ (1 : Γ(Y, U))) i)
    simp [twData, mulVec, dotProduct, ρ_ρ]
  · change ρ _ (rv _ (fun _ ↦ (1 : Γ(Y, V))) i) =
      ρ _ (t : Γ(Y, U ⊓ V)) * ρ _ (((twData U V t).Ψ.map (ρ _) *ᵥ
        rv _ (fun _ ↦ (1 : Γ(Y, U)))) i)
    simp only [mulVec, dotProduct, Fintype.sum_unique]
    simp only [twData, Matrix.map_apply, Matrix.of_apply, map_one, mul_one, ρ_ρ]
    rw [← map_mul, Units.mul_inv, map_one]

/-! ### Pullbacks -/

section Pullback

variable {T : Scheme.{u}}

/-- **Pullback criterion.** If `N` on `T` has bases `ε` on `s⁻¹U` and `δ` on `s⁻¹V` with
`δ = s^♯ t · ε` on the overlap, then `s^* 𝒪(t) ≅ N`. -/
theorem nonempty_iso_pullback_tw (hUV : U ⊔ V = ⊤) (s : T ⟶ Y) {N : T.Modules}
    (ε : Γ(N, s ⁻¹ᵁ U)) (δ : Γ(N, s ⁻¹ᵁ V)) (hε : N.IsBasisOn (s ⁻¹ᵁ U) ε)
    (hδ : N.IsBasisOn (s ⁻¹ᵁ V) δ)
    (hc : rs N (s.preimage_mono (inf_le_right : U ⊓ V ≤ V)) δ =
      s.app (U ⊓ V) (t : Γ(Y, U ⊓ V)) • rs N (s.preimage_mono (inf_le_left : U ⊓ V ≤ U)) ε) :
    Nonempty ((Scheme.Modules.pullback s).obj (tw U V t) ≅ N) := by
  have hc' : (twData U V t).Compat (s := s) (N := N) (fun _ ↦ ε) (fun _ ↦ δ) := by
    intro j
    rw [Data.lc, Fintype.sum_unique]
    exact hc
  refine (twData U V t).nonempty_iso_pullback_sheaf hUV hc' fun y ↦ ?_
  have : s.base y ∈ U ⊔ V := hUV ▸ trivial
  rcases Opens.mem_sup.mp this with h | h
  · refine Or.inl ⟨U, rankOneU t, h, ?_⟩
    have e : Data.lc s N (fun _ ↦ ε) (rankOneU t).le (rankOneU t).p = ε := by
      rw [Data.lc, Fintype.sum_unique]
      simp only [rankOneU, map_one, one_smul, rs_self]
    rw [e]
    exact hε
  · refine Or.inr ⟨V, rankOneV t, h, ?_⟩
    have e : Data.lc s N (fun _ ↦ δ) (rankOneV t).le (rankOneV t).p = δ := by
      rw [Data.lc, Fintype.sum_unique]
      simp only [rankOneV, map_one, one_smul, rs_self]
    rw [e]
    exact hδ

/-- **Every sheaf with bases on `U` and `V` is a twist.** -/
theorem nonempty_iso_tw (hUV : U ⊔ V = ⊤) {L : Y.Modules} (ε : Γ(L, U)) (δ : Γ(L, V))
    (hε : L.IsBasisOn U ε) (hδ : L.IsBasisOn V δ)
    (hc : rs L (inf_le_right : U ⊓ V ≤ V) δ =
      (t : Γ(Y, U ⊓ V)) • rs L (inf_le_left : U ⊓ V ≤ U) ε) :
    Nonempty (tw U V t ≅ L) := by
  obtain ⟨e⟩ := nonempty_iso_pullback_tw t hUV (𝟙 Y) (N := L) ε δ hε hδ hc
  exact ⟨((Scheme.Modules.pullbackId Y).app (tw U V t)).symm ≪≫ e⟩

/-- The transition function between two bases. -/
lemma exists_trans {L : Y.Modules} {ε : Γ(L, U)} {δ : Γ(L, V)}
    (hε : L.IsBasisOn U ε) (hδ : L.IsBasisOn V δ) :
    ∃ t : Γ(Y, U ⊓ V)ˣ, rs L (inf_le_right : U ⊓ V ≤ V) δ =
      (t : Γ(Y, U ⊓ V)) • rs L (inf_le_left : U ⊓ V ≤ U) ε := by
  have hε' := isBasisOn_rs hε (inf_le_left : U ⊓ V ≤ U)
  have hδ' := isBasisOn_rs hδ (inf_le_right : U ⊓ V ≤ V)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_isBasisOn hε' (rs L inf_le_right δ)
  obtain ⟨b, hb⟩ := exists_smul_eq_of_isBasisOn hδ' (rs L inf_le_left ε)
  have hab : b * a = 1 := by
    refine smul_left_injective_of_isBasisOn hε' ?_
    rw [mul_smul, ha, hb, one_smul]
  exact ⟨⟨a, b, by rw [mul_comm, hab], hab⟩, ha.symm⟩

theorem exists_nonempty_iso_tw (hUV : U ⊔ V = ⊤) {L : Y.Modules} {ε : Γ(L, U)} {δ : Γ(L, V)}
    (hε : L.IsBasisOn U ε) (hδ : L.IsBasisOn V δ) :
    ∃ t : Γ(Y, U ⊓ V)ˣ, Nonempty (tw U V t ≅ L) := by
  obtain ⟨t, ht⟩ := exists_trans hε hδ
  exact ⟨t, nonempty_iso_tw t hUV ε δ hε hδ ht⟩

/-- The twist pulled back. -/
abbrev twPull (s : T ⟶ Y) : Γ(T, s ⁻¹ᵁ U ⊓ s ⁻¹ᵁ V)ˣ := Units.map (s.app (U ⊓ V)).hom.toMonoidHom t

theorem nonempty_iso_pullback_tw_tw (hUV : U ⊔ V = ⊤) (s : T ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback s).obj (tw U V t) ≅
      tw (s ⁻¹ᵁ U) (s ⁻¹ᵁ V) (twPull t s)) :=
  nonempty_iso_pullback_tw t hUV s _ _ (isBasisOn_bU _) (isBasisOn_bV _) (bV_res _)

/-- The class of `𝒪(t)` in `Pic Y`. -/
def twPic (hUV : U ⊔ V = ⊤) (t : Γ(Y, U ⊓ V)ˣ) : Y.Pic :=
  @Pic.mk _ (tw U V t) (isInvertible_tw t hUV)

/-- **Pullback of a twist**, for opens `U' = s⁻¹ U`, `V' = s⁻¹ V` and `t' = s^♯ t`. -/
theorem map_twPic (hUV : U ⊔ V = ⊤) (s : T ⟶ Y) {U' V' : T.Opens} (hU : s ⁻¹ᵁ U = U')
    (hV : s ⁻¹ᵁ V = V') (hUV' : U' ⊔ V' = ⊤) (t' : Γ(T, U' ⊓ V')ˣ)
    (ht : (t' : Γ(T, U' ⊓ V')) =
      s.appLE (U ⊓ V) (U' ⊓ V') (by subst hU hV; exact le_rfl) (t : Γ(Y, U ⊓ V))) :
    Pic.map s (twPic hUV t) = twPic hUV' t' := by
  subst hU hV
  haveI := isInvertible_tw t hUV
  haveI := isInvertible_tw t' hUV'
  have e : t' = twPull t s := Units.ext (ht.trans (congrArg (fun φ ↦ φ (t : Γ(Y, U ⊓ V)))
    (Scheme.Hom.appLE_eq_app (f := s) (U := U ⊓ V))))
  subst e
  change Pic.map s (Pic.mk (tw U V t)) = Pic.mk _
  rw [Pic.map_mk]
  exact Pic.mk_eq_of_iso (nonempty_iso_pullback_tw_tw t hUV s).some

end Pullback

/-! ### Isomorphic twists -/

lemma isUnit_of_isBasisOn_smul {L : Y.Modules} {O : Y.Opens} {e : Γ(L, O)} {c : Γ(Y, O)}
    (he : L.IsBasisOn O e) (hce : L.IsBasisOn O (c • e)) : IsUnit c := by
  obtain ⟨r, hr⟩ := exists_smul_eq_of_isBasisOn hce e
  refine IsUnit.of_mul_eq_one_right r (smul_left_injective_of_isBasisOn he ?_)
  rw [mul_smul, hr, one_smul]

lemma exists_unit_smul_eq {L : Y.Modules} {O : Y.Opens} {e e' : Γ(L, O)}
    (he : L.IsBasisOn O e) (he' : L.IsBasisOn O e') : ∃ u : Γ(Y, O)ˣ, (u : Γ(Y, O)) • e = e' := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_isBasisOn he e'
  exact ⟨(isUnit_of_isBasisOn_smul he (hc ▸ he')).unit, hc⟩

variable (hUV : U ⊔ V = ⊤)

include hUV in
/-- **Isomorphic twists**: `𝒪(t) ≅ 𝒪(t')` iff `v t' = t u` on `U ∩ V` for units `u` on `U`,
`v` on `V`. -/
theorem twPic_eq_twPic_iff (t t' : Γ(Y, U ⊓ V)ˣ) :
    twPic hUV t = twPic hUV t' ↔ ∃ (u : Γ(Y, U)ˣ) (v : Γ(Y, V)ˣ),
      ρ (inf_le_right : U ⊓ V ≤ V) (v : Γ(Y, V)) * t' =
        t * ρ (inf_le_left : U ⊓ V ≤ U) (u : Γ(Y, U)) := by
  haveI := isInvertible_tw t hUV
  haveI := isInvertible_tw t' hUV
  change Pic.mk (tw U V t) = Pic.mk (tw U V t') ↔ _
  rw [Pic.mk_eq_mk_iff]
  constructor
  · rintro ⟨e⟩
    have h1 := (isBasisOn_bU t).of_iso e
    have h2 := (isBasisOn_bV t).of_iso e
    obtain ⟨u, hu⟩ := exists_unit_smul_eq (isBasisOn_bU t') h1
    obtain ⟨v, hv⟩ := exists_unit_smul_eq (isBasisOn_bV t') h2
    refine ⟨u, v, ?_⟩
    have key := congrArg (e.hom.app (U ⊓ V)) (bV_res t)
    rw [app_rs, Scheme.Modules.Hom.app_smul, app_rs, ← hu, ← hv,
      rs_smul, rs_smul, bV_res, smul_smul, smul_smul] at key
    exact smul_left_injective_of_isBasisOn (isBasisOn_rs (isBasisOn_bU t') inf_le_left) key
  · rintro ⟨u, v, h⟩
    refine ⟨(nonempty_iso_tw t hUV ((u : Γ(Y, U)) • bU t') ((v : Γ(Y, V)) • bV t')
      (isBasisOn_smul_of_isUnit (isBasisOn_bU t') u.isUnit)
      (isBasisOn_smul_of_isUnit (isBasisOn_bV t') v.isUnit) ?_).some⟩
    rw [rs_smul, rs_smul, bV_res, smul_smul, smul_smul, h]

include hUV in
/-- `𝒪(1)` is trivial. -/
theorem twPic_one : twPic hUV (1 : Γ(Y, U ⊓ V)ˣ) = 0 := by
  haveI := isInvertible_tw (1 : Γ(Y, U ⊓ V)ˣ) hUV
  let s : Γ((𝟙_ Y.Modules), ⊤) := (Scheme.Modules.toSheafify (𝟙_ Y.PresheafOfModules)).app (op ⊤)
    (1 : Y.ringCatSheaf.obj.obj (op ⊤))
  have hs : (𝟙_ Y.Modules).IsBasisOn ⊤ s := Scheme.Modules.isBasisOn_sheafify
    (𝟙_ Y.PresheafOfModules) (Scheme.PresheafOfModules.isBasisOn_unit ⊤)
  change Pic.mk (tw U V 1) = 0
  rw [Pic.mk_eq_zero_iff]
  refine nonempty_iso_tw 1 hUV (rs _ le_top s) (rs _ le_top s) (isBasisOn_rs hs le_top)
    (isBasisOn_rs hs le_top) ?_
  rw [rs_rs, rs_rs, Units.val_one, one_smul]

include hUV in
/-- **An invertible sheaf with bases on `U` and `V` is a twist.** -/
theorem exists_twPic_eq {L : Y.Modules} [L.IsInvertible] {ε : Γ(L, U)} {δ : Γ(L, V)}
    (hε : L.IsBasisOn U ε) (hδ : L.IsBasisOn V δ) :
    ∃ t : Γ(Y, U ⊓ V)ˣ, rs L (inf_le_right : U ⊓ V ≤ V) δ =
      (t : Γ(Y, U ⊓ V)) • rs L (inf_le_left : U ⊓ V ≤ U) ε ∧ twPic hUV t = Pic.mk L := by
  obtain ⟨t, ht⟩ := exists_trans hε hδ
  haveI := isInvertible_tw t hUV
  exact ⟨t, ht, Pic.mk_eq_of_iso (nonempty_iso_tw t hUV ε δ hε hδ ht).some⟩

end CurvesJacobian.TwoChart
