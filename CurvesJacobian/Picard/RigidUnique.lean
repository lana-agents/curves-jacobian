/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.LocIso

/-!
# Rigidified section-wise isomorphisms: existence and uniqueness

This file is generic. Let `r : Y ⟶ T` have a section `s : T ⟶ Y` such that
`r^♯ : Γ(T, U) ⟶ Γ(Y, r⁻¹U)` is surjective for every open `U` of `T` (e.g. `Y = X_T` for a
curve `X`, Stacks, Lemma 44.6.1, Tag 0B9U). Let `V` be an open of `Y` which is saturated,
`V = r⁻¹(s⁻¹ V)`, and let `M`, `N` be sheaves of modules, `M` invertible on `V`, with evaluations
`χM`, `χN` along `s` (`Rig`). Then:

* every section-wise isomorphism `M|_V ≅ N|_V` can be rescaled by a unit pulled back from `T` to
  a rigid one, i.e. compatible with `χM`, `χN` (`LocIso.exists_isRigid`);
* rigid section-wise isomorphisms are unique (`LocIso.ext_of_isRigid`).

This is the section-wise form of `exists_iso_pullback_map_eq` and `iso_ext_of_pullback_map_eq`
(the choices in the proof of Stacks, Lemma 44.4.3, Tag 0B9N), suited to gluing.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}} {r : Y ⟶ T} {s : T ⟶ Y}

/-- `s^♯ r^♯ v = v` for a section `s` of `r` (up to the equality `s⁻¹ r⁻¹ U = U`). -/
lemma app_app_eq_rr (hsr : s ≫ r = 𝟙 T) (U : T.Opens) (h : s ⁻¹ᵁ (r ⁻¹ᵁ U) ≤ U)
    (v : Γ(T, U)) : s.app (r ⁻¹ᵁ U) (r.app U v) = rr h v := by
  change (s ≫ r).app U v = _
  rw [Scheme.Hom.congr_app hsr U]
  rfl

lemma rr_one {Z : Scheme.{u}} {U W : Z.Opens} (h : W ≤ U) : rr h (1 : Γ(Z, U)) = 1 :=
  map_one _

section Scalar

variable {M N : Y.Modules} {V : Y.Opens}

/-- Two section-wise isomorphisms differ by a scalar on a basis open. -/
lemma LocIso.exists_local_scalar (Φ Φ' : LocIso M N V) {U : Y.Opens} (hU : U ≤ V)
    {e : Γ(M, U)} (he : M.IsBasisOn U e) : ∃ c : Γ(Y, U), ∀ (W : Y.Opens) (h : W ≤ U)
      (m : Γ(M, W)), Φ'.φ W (h.trans hU) m = rr h c • Φ.φ W (h.trans hU) m := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_isBasisOn (Φ.isBasisOn_φ hU he) (Φ'.φ U hU e)
  refine ⟨c, fun W h m ↦ ?_⟩
  obtain ⟨k, rfl⟩ := exists_smul_eq_of_isBasisOn (isBasisOn_rs he h) m
  rw [Φ'.φ_smul, Φ.φ_smul, Φ'.φ_rs U W hU h, Φ.φ_rs U W hU h, ← hc, rs_smul]
  exact smul_comm' _ _ _

/-- Two section-wise isomorphisms between sheaves invertible on `V` differ by a function on
`V`. -/
lemma LocIso.exists_scalar (hMV : IsInvOn M V) (Φ Φ' : LocIso M N V) :
    ∃ c : Γ(Y, V), ∀ (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)),
      Φ'.φ W hW m = rr hW c • Φ.φ W hW m := by
  choose U e hUV hyU he using fun y : V ↦ hMV y.1 y.2
  choose c hc using fun y : V ↦ Φ.exists_local_scalar Φ' (hUV y) (he y)
  have hcomp : ∀ y z : V, rr (inf_le_left : U y ⊓ U z ≤ U y) (c y) =
      rr (inf_le_right : U y ⊓ U z ≤ U z) (c z) := by
    intro y z
    have hb := Φ.isBasisOn_φ (inf_le_left.trans (hUV y))
      (isBasisOn_rs (he y) (inf_le_left : U y ⊓ U z ≤ U y))
    have h₁ := hc y (U y ⊓ U z) inf_le_left (rs M (inf_le_left : U y ⊓ U z ≤ U y) (e y))
    have h₂ := hc z (U y ⊓ U z) inf_le_right (rs M (inf_le_left : U y ⊓ U z ≤ U y) (e y))
    exact smul_left_injective_of_isBasisOn hb (h₁.symm.trans h₂)
  obtain ⟨g, hg⟩ := CurvesJacobian.sheaf_exists_glue Y.sheaf (V := V) U hUV hyU c hcomp
  refine ⟨g, fun W hW m ↦ ?_⟩
  refine CurvesJacobian.sheaf_eq_of_locally_eq ⟨N.presheaf, N.isSheaf⟩ _ _ fun y hy ↦
    ⟨W ⊓ U ⟨y, hW hy⟩, inf_le_left, ⟨hy, hyU _⟩, ?_⟩
  change rs N inf_le_left (Φ'.φ W hW m) = rs N inf_le_left (rr hW g • Φ.φ W hW m)
  rw [← Φ'.φ_rs, rs_smul, ← Φ.φ_rs, hc _ _ inf_le_right, rr_rr]
  congr 1
  have hg' : rr (hUV ⟨y, hW hy⟩) g = c ⟨y, hW hy⟩ := hg _
  rw [← hg', rr_rr]

end Scalar

section Ratio

variable {M N : Y.Modules} {V VN : Y.Opens}

/-- The evaluation `χN ∘ Φ` of `M` along `s`. -/
def Rig.comp (Φ : LocIso M N V) (χ : Rig s N VN) (h : V ≤ VN) : Rig s M V where
  χ W hW := (χ.χ W (hW.trans h)).comp (Φ.φ W hW)
  χ_smul W hW c m := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Φ.φ_smul, χ.χ_smul]
  χ_rs W W' hW h' m := by
    change χ.χ W' _ (Φ.φ W' _ (rs M h' m)) = _
    rw [Φ.φ_rs W W' hW h' m]
    exact χ.χ_rs W W' (hW.trans h) h' _
  isUnit_χ W hW e he := χ.isUnit_χ W (hW.trans h) _ (Φ.isBasisOn_φ hW he)

lemma Rig.comp_χ (Φ : LocIso M N V) (χ : Rig s N VN) (h : V ≤ VN) (W : Y.Opens) (hW : W ≤ V)
    (m : Γ(M, W)) : (Rig.comp Φ χ h).χ W hW m = χ.χ W (hW.trans h) (Φ.φ W hW m) :=
  rfl

/-- Two evaluations differ by a function on a basis open. -/
lemma Rig.exists_local_ratio (α β : Rig s M V) {U : Y.Opens} (hU : U ≤ V) {e : Γ(M, U)}
    (he : M.IsBasisOn U e) : ∃ w : Γ(T, s ⁻¹ᵁ U), ∀ (W : Y.Opens) (h : W ≤ U) (m : Γ(M, W)),
      rr (s.preimage_mono h) w * α.χ W (h.trans hU) m = β.χ W (h.trans hU) m := by
  set u := (α.isUnit_χ U hU e he).unit
  refine ⟨β.χ U hU e * ↑u⁻¹, fun W h m ↦ ?_⟩
  obtain ⟨k, rfl⟩ := exists_smul_eq_of_isBasisOn (isBasisOn_rs he h) m
  rw [α.χ_smul, β.χ_smul, α.χ_rs U W hU h, β.χ_rs U W hU h]
  have hu : α.χ U hU e = ↑u := (IsUnit.unit_spec _).symm
  rw [hu, mul_left_comm, ← rr_mul, Units.inv_mul_cancel_right]

/-- Two evaluations of a sheaf invertible on `V` differ by a function on `s⁻¹ V`. -/
lemma Rig.exists_ratio (hMV : IsInvOn M V) (α β : Rig s M V) :
    ∃ w : Γ(T, s ⁻¹ᵁ V), ∀ (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)),
      rr (s.preimage_mono hW) w * α.χ W hW m = β.χ W hW m := by
  choose U e hUV hyU he using fun t : s ⁻¹ᵁ V ↦ hMV (s.base t.1) t.2
  choose w hw using fun t : s ⁻¹ᵁ V ↦ α.exists_local_ratio β (hUV t) (he t)
  have hcomp : ∀ t t' : s ⁻¹ᵁ V,
      rr (inf_le_left : s ⁻¹ᵁ U t ⊓ s ⁻¹ᵁ U t' ≤ s ⁻¹ᵁ U t) (w t) =
      rr (inf_le_right : s ⁻¹ᵁ U t ⊓ s ⁻¹ᵁ U t' ≤ s ⁻¹ᵁ U t') (w t') := by
    intro t t'
    have heq : s ⁻¹ᵁ (U t ⊓ U t') = s ⁻¹ᵁ U t ⊓ s ⁻¹ᵁ U t' := rfl
    apply (rr_bijective_of_eq heq).1
    rw [rr_rr, rr_rr]
    have hb := isBasisOn_rs (he t) (inf_le_left : U t ⊓ U t' ≤ U t)
    have h₁ := hw t (U t ⊓ U t') inf_le_left (rs M inf_le_left (e t))
    have h₂ := hw t' (U t ⊓ U t') inf_le_right (rs M inf_le_left (e t))
    have hunit := α.isUnit_χ _ (inf_le_left.trans (hUV t)) _ hb
    exact hunit.mul_left_inj.1 (h₁.trans h₂.symm)
  obtain ⟨g, hg⟩ := CurvesJacobian.sheaf_exists_glue T.sheaf (V := s ⁻¹ᵁ V)
    (fun t ↦ s ⁻¹ᵁ U t) (fun t ↦ s.preimage_mono (hUV t)) hyU w hcomp
  refine ⟨g, fun W hW m ↦ ?_⟩
  refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun t ht ↦
    ⟨s ⁻¹ᵁ (W ⊓ U ⟨t, hW ht⟩), s.preimage_mono inf_le_left, ⟨ht, hyU _⟩, ?_⟩
  change rr _ (rr (s.preimage_mono hW) g * α.χ W hW m) = rr _ (β.χ W hW m)
  rw [rr_mul, rr_rr, ← α.χ_rs W (W ⊓ U ⟨t, hW ht⟩) hW inf_le_left m,
    ← β.χ_rs W (W ⊓ U ⟨t, hW ht⟩) hW inf_le_left m]
  have hgt : rr (s.preimage_mono (inf_le_left.trans hW)) g =
      rr (s.preimage_mono (inf_le_right : W ⊓ U ⟨t, hW ht⟩ ≤ U ⟨t, hW ht⟩)) (w ⟨t, hW ht⟩) := by
    have hg' : rr (s.preimage_mono (hUV ⟨t, hW ht⟩)) g = w ⟨t, hW ht⟩ := hg _
    rw [← hg', rr_rr]
  rw [hgt]
  exact hw _ _ inf_le_right _

/-- Two evaluations of a sheaf invertible on `V` differ by a unit on `s⁻¹ V`. -/
lemma Rig.exists_unit_ratio (hMV : IsInvOn M V) (α β : Rig s M V) :
    ∃ w : Γ(T, s ⁻¹ᵁ V), IsUnit w ∧ ∀ (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)),
      rr (s.preimage_mono hW) w * α.χ W hW m = β.χ W hW m := by
  obtain ⟨w, hw⟩ := α.exists_ratio hMV β
  obtain ⟨w', hw'⟩ := β.exists_ratio hMV α
  refine ⟨w, isUnit_iff_exists_inv.2 ⟨w', ?_⟩, hw⟩
  refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun t ht ↦ ?_
  obtain ⟨U, e, hUV, hU, he⟩ := hMV (s.base t) ht
  refine ⟨s ⁻¹ᵁ U, s.preimage_mono hUV, hU, ?_⟩
  change rr _ (w * w') = rr _ 1
  rw [rr_mul, rr_one]
  have h₁ := hw U hUV e
  have h₂ := hw' U hUV e
  have hunit := β.isUnit_χ U hUV e he
  refine hunit.mul_left_inj.1 ?_
  rw [one_mul, mul_assoc, h₂, h₁]

end Ratio

/-- **Rigid section-wise isomorphisms are unique.** -/
theorem LocIso.ext_of_isRigid (hsr : s ≫ r = 𝟙 T)
    (hΓ : ∀ U : T.Opens, Function.Surjective (r.app U)) {M N : Y.Modules} {V VM VN : Y.Opens}
    (hV : r ⁻¹ᵁ (s ⁻¹ᵁ V) = V) (hMV : IsInvOn M V) {χM : Rig s M VM} {χN : Rig s N VN}
    {hM : V ≤ VM} {hN : V ≤ VN} {Φ Φ' : LocIso M N V} (h : Φ.IsRigid χM χN hM hN)
    (h' : Φ'.IsRigid χM χN hM hN) (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)) :
    Φ.φ W hW m = Φ'.φ W hW m := by
  obtain ⟨c, hc⟩ := Φ.exists_scalar hMV Φ'
  -- `s^♯ c = 1`
  have hs1 : s.app V c = 1 := by
    refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun t ht ↦ ?_
    obtain ⟨U, e, hUV, hU, he⟩ := hMV (s.base t) ht
    refine ⟨s ⁻¹ᵁ U, s.preimage_mono hUV, hU, ?_⟩
    change rr _ (s.app V c) = rr _ 1
    have h₁ := h' U hUV e
    rw [hc, χN.χ_smul, h U hUV e] at h₁
    have hunit := χM.isUnit_χ U (hUV.trans hM) e he
    rw [rr_one, ← app_rr s hUV c]
    exact hunit.mul_eq_right.1 h₁
  -- `c = 1` since `c` is pulled back from `T`
  have hc1 : c = 1 := by
    obtain ⟨v, hv⟩ := hΓ (s ⁻¹ᵁ V) (rr hV.le c)
    have h0 : s ⁻¹ᵁ (r ⁻¹ᵁ (s ⁻¹ᵁ V)) ≤ s ⁻¹ᵁ V := by rw [hV]
    have h0' : s ⁻¹ᵁ (r ⁻¹ᵁ (s ⁻¹ᵁ V)) = s ⁻¹ᵁ V := by rw [hV]
    have hv1 : v = 1 := by
      have := app_app_eq_rr hsr (s ⁻¹ᵁ V) h0 v
      rw [hv, app_rr, hs1, rr_one] at this
      apply (rr_bijective_of_eq h0').1
      rw [← this, rr_one]
    have := congrArg (rr hV.ge) hv
    rw [rr_rr, rr_self, hv1, map_one, rr_one] at this
    exact this.symm
  rw [hc, hc1, rr_one, one_smul]

/-- **Rigid section-wise isomorphisms exist**: every section-wise isomorphism can be rescaled to
a rigid one. -/
theorem LocIso.exists_isRigid (hsr : s ≫ r = 𝟙 T) {M N : Y.Modules} {V VM VN : Y.Opens}
    (hV : r ⁻¹ᵁ (s ⁻¹ᵁ V) = V) (hMV : IsInvOn M V) (χM : Rig s M VM) (χN : Rig s N VN)
    (hM : V ≤ VM) (hN : V ≤ VN) (Φ : LocIso M N V) :
    ∃ Φ' : LocIso M N V, Φ'.IsRigid χM χN hM hN := by
  obtain ⟨w, hwu, hw⟩ := (Rig.comp Φ χN hN).exists_unit_ratio hMV (χM.restrict hM)
  set a : Γ(Y, V) := rr hV.ge (r.app (s ⁻¹ᵁ V) w) with ha_def
  have ha : IsUnit a := (hwu.map _).map _
  have h0 : s ⁻¹ᵁ (r ⁻¹ᵁ (s ⁻¹ᵁ V)) ≤ s ⁻¹ᵁ V := by rw [hV]
  have hsa : ∀ (W : Y.Opens) (hW : W ≤ V),
      s.app W (rr hW a) = rr (s.preimage_mono hW) w := by
    intro W hW
    rw [ha_def, rr_rr, app_rr, app_app_eq_rr hsr _ h0, rr_rr]
  refine ⟨{ φ := fun W hW ↦ (DistribSMul.toAddMonoidHom _ (rr hW a)).comp (Φ.φ W hW)
            φ_smul := fun W hW c m ↦ by
              simp only [AddMonoidHom.coe_comp, Function.comp_apply,
                DistribSMul.toAddMonoidHom_apply, Φ.φ_smul]
              exact smul_comm' _ _ _
            φ_rs := fun W W' hW h m ↦ by
              simp only [AddMonoidHom.coe_comp, Function.comp_apply,
                DistribSMul.toAddMonoidHom_apply]
              rw [Φ.φ_rs W W' hW h m, rs_smul, rr_rr hW h a]
            bij := fun W hW ↦ by
              rw [AddMonoidHom.coe_comp]
              refine Function.Bijective.comp ?_ (Φ.bij W hW)
              have hu := ha.map (Y.presheaf.map (homOfLE hW).op).hom
              have : (DistribSMul.toAddMonoidHom Γ(N, W) (rr hW a) : Γ(N, W) → Γ(N, W)) =
                  fun n ↦ hu.unit • n := by
                funext n
                rw [Units.smul_def, IsUnit.unit_spec]
                rfl
              rw [this]
              exact MulAction.bijective _ }, ?_⟩
  intro W hW m
  change χN.χ W (hW.trans hN) (rr hW a • Φ.φ W hW m) = _
  rw [χN.χ_smul, hsa]
  have := hw W hW m
  rw [Rig.comp_χ, Rig.restrict_χ] at this
  exact this

end CurvesJacobian.ModulesGlue
