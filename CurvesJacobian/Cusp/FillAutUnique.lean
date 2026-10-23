/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FillAutExt
import CurvesJacobian.LocAn.UniqueReduction

/-!
# Automorphisms of `Π_U` compatible with filling are inner (MR8.6)

**`CurvesJacobian.Cusp.exists_eq_conj_of_fillMap`.** Let `C` be a hyperbolic curve over a
number field `K` with a cusp, `U = C.U ⊆ U'` with `(X̄, U')` hyperbolic with a cusp, and
`fill : Π_U ↠ Π_{U'}` (`fillMap`). Assume the rel-isom-DGC over `K` (`hDGC : RelIsomDGC.Exists K`,
whitelist entry for [LocAn] Theorem A). If a continuous automorphism `ψ` of `Π_U` satisfies
`fill ∘ ψ = conj(s) ∘ fill` for some `s ∈ Π_{U'}`, then `ψ = conj(n)` for some `n ∈ Π_U` with
`fill(n) = s`.

This is the uniqueness input of [AbsTopII] Corollary 3.7 (b) ("the unique lifting of the outer
action", `Topics in Absolute Anabelian Geometry II.txt` l.4698–4775) and Corollary 3.8 (the
isomorphism `φ_U` is unique up to inner automorphisms from `ker(Π_{U_{X₂}} ↠ Π₂)`, which
"follows immediately from our assumption that the rel-isom-DGC holds", l.4840): two lifts differ
by an automorphism of this kind with `s = 1`, hence by an inner automorphism from the kernel.

Proof: after composing with `conj(t)⁻¹` (`fill(t) = s`), `ψ'` satisfies `fill ∘ ψ' = fill`, so it
lies over `G_K`; the DGC gives a `K`-automorphism `F` of `Spec Γ(U)` inducing `ψ'`
(`exists_isConjInduced_of_relIsomDGC`); `π₁ᵉᵗ(F^{±1})` preserves `ker fill`, so `F^*` preserves
`Γ(U') ⊆ Γ(U)` (`exists_resAlg_coverRing`) and extends to a `K`-automorphism `F'` of
`Spec Γ(U')`; `F'` induces an inner automorphism of `Π_{U'}` (`fill` is surjective), so `F' = id`
by DGC uniqueness on `U'` (`eq_refl_of_isConjInduced_conj` for `fillCurve`); then `F = id`
(`Γ(U) ⊆ Frac Γ(U')`), so `ψ'` is inner, by an element `m` with `fill(m)` central, i.e.
`fill(m) = 1` (`Π_{U'}` has trivial centre).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

section ConjInduced

variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- Two maps induced by the same morphism differ by an inner automorphism of the target. -/
lemma IsConjInduced.exists_conj_eq {h : X ⟶ Y} {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} {φ₁ φ₂ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H₁ : IsConjInduced h φ₁)
    (H₂ : IsConjInduced h φ₂) : ∃ u : π₁ᵉᵗ(y), ∀ σ, φ₁ σ = u * φ₂ σ * u⁻¹ := by
  obtain ⟨γ₁, h₁⟩ := H₁
  obtain ⟨γ₂, h₂⟩ := H₂
  obtain ⟨u, hu⟩ := CurvesJacobian.Cusp.exists_conjAut_eq_conj γ₂ γ₁
  exact ⟨u, fun σ ↦ by rw [h₁, h₂]; exact hu _⟩

omit [IsSepClosed Ω] in
/-- A change of base point is induced by the identity. -/
lemma isConjInduced_id_autIso {y₁ y₂ : Spec (.of Ω) ⟶ X} (α : fiber y₁ ≅ fiber y₂) :
    IsConjInduced (𝟙 X) (autContinuousMulEquivOfIso α) :=
  (isConjInduced_iff (𝟙 X) (Category.comp_id y₁) _).2 ⟨α, fun σ ↦ by
    rw [fundamentalGroupMap_id]
    rfl⟩

omit [IsSepClosed Ω] in
/-- "`h` induces an inner automorphism" does not depend on the base point. -/
lemma IsConjInduced.transport_id {h : X ⟶ X} {y₁ y₂ : Spec (.of Ω) ⟶ X}
    (α : fiber y₁ ≅ fiber y₂) (H : IsConjInduced h (id : π₁ᵉᵗ(y₁) → π₁ᵉᵗ(y₁))) :
    IsConjInduced h (id : π₁ᵉᵗ(y₂) → π₁ᵉᵗ(y₂)) := by
  have := ((isConjInduced_id_autIso α.symm).comp H).comp (isConjInduced_id_autIso α)
  refine (this.congr_hom (by simp)).congr_fun fun σ ↦ ?_
  change σ = α.conjAut (α.symm.conjAut σ)
  rw [← Iso.trans_conjAut, Iso.symm_self_id, Iso.conjAut_apply]
  simp

omit [IsSepClosed Ω] in
/-- If `φ ∘ π₁ᵉᵗ(r)` is induced by `r ≫ g` and `π₁ᵉᵗ(r)` is surjective, then `φ` is induced
by `g`. -/
lemma IsConjInduced.of_comp_surjective {r : X ⟶ Y} {g : Y ⟶ Z} {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} {z : Spec (.of Ω) ⟶ Z} (hr : x ≫ r = y) (χ : π₁ᵉᵗ(y) → π₁ᵉᵗ(z))
    (H : IsConjInduced (r ≫ g) (χ ∘ fundamentalGroupMap r hr))
    (hsurj : Function.Surjective (fundamentalGroupMap r hr)) : IsConjInduced g χ := by
  subst hr
  obtain ⟨γ, hγ⟩ := (isConjInduced_iff (r ≫ g) (Category.assoc x r g).symm _).1 H
  refine ⟨γ, fun τ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := hsurj τ
  have c : fundamentalGroupMap g rfl (fundamentalGroupMap r rfl σ) =
      fundamentalGroupMap (r ≫ g) (Category.assoc x r g).symm σ :=
    (DFunLike.congr_fun (fundamentalGroupMap_comp r g rfl rfl _) σ).symm
  rw [c]
  exact hγ σ

end ConjInduced

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U')

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option backward.isDefEq.respectTransparency false

/-! ### Ring maps of `Γ(U)` -/

omit [NumberField K] in
lemma coverRing_comp_apply (F₁ F₂ : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(C.Xbar, C.U))
    (b : Γ(C.Xbar, C.U)) : coverRing C C (F₁ ≫ F₂) b = coverRing C C F₁ (coverRing C C F₂ b) := by
  have e : Spec.preimage (F₁ ≫ F₂) = Spec.preimage F₂ ≫ Spec.preimage F₁ :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
      Spec.map_preimage])
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) b

omit [NumberField K] in
lemma coverRing_id_apply (b : Γ(C.Xbar, C.U)) : coverRing C C (𝟙 _) b = b := by
  have e : Spec.preimage (𝟙 (Spec Γ(C.Xbar, C.U))) = 𝟙 _ :=
    Spec.map_injective (by rw [Spec.map_preimage, Spec.map_id])
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) b

omit [NumberField K] in
include h in
lemma resAlg_injective : Function.Injective (resAlg K h) := fun a b hab ↦ by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  apply C.Xbar.germToFunctionField_injective U'
  rw [← germ_resAlg C h a, ← germ_resAlg C h b, hab]

include hc' in
/-- **A ring endomorphism of `Γ(U)` fixing `Γ(U')` is the identity** (`Γ(U) ⊆ Frac Γ(U')`). -/
lemma eq_of_forall_resAlg (g : Γ(C.Xbar, C.U) →+* Γ(C.Xbar, C.U))
    (hg : ∀ a, g (resAlg K h a) = resAlg K h a) (b : Γ(C.Xbar, C.U)) : g b = b := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  haveI : IsFractionRing Γ(C.Xbar, U') C.Xbar.functionField :=
    functionField_isFractionRing_of_isAffineOpen C.Xbar U' (isAffineOpen_of_le C h hc')
  obtain ⟨a₁, a₂, ha₂, e⟩ := IsFractionRing.div_surjective (A := Γ(C.Xbar, U'))
    (C.Xbar.germToFunctionField C.U b)
  have hne : algebraMap Γ(C.Xbar, U') C.Xbar.functionField a₂ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha₂
  have hgerm : ∀ a, C.Xbar.germToFunctionField C.U (resAlg K h a) =
      algebraMap Γ(C.Xbar, U') C.Xbar.functionField a := fun a ↦ germ_resAlg C h a
  have hmul : resAlg K h a₂ * b = resAlg K h a₁ := by
    apply C.Xbar.germToFunctionField_injective C.U
    rw [map_mul, hgerm, hgerm, ← e, mul_div_cancel₀ _ hne]
  have hmul' : resAlg K h a₂ * g b = resAlg K h a₁ := by
    rw [← hg a₂, ← map_mul, hmul, hg]
  apply C.Xbar.germToFunctionField_injective C.U
  have h1 := congrArg (C.Xbar.germToFunctionField C.U) (hmul'.trans hmul.symm)
  rw [map_mul, map_mul, hgerm] at h1
  exact mul_left_cancel₀ hne h1

/-! ### The extension `F'` of an automorphism `F` of `Spec Γ(U)` -/

section Ext

variable {F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U)}
  (hext : ∀ a : Γ(C.Xbar, U'), ∃ a', coverRing C C F.hom (resAlg K h a) = resAlg K h a')
  (hext' : ∀ a : Γ(C.Xbar, U'), ∃ a', coverRing C C F.inv (resAlg K h a) = resAlg K h a')

omit [NumberField K] in
lemma coverRing_hom_inv (b : Γ(C.Xbar, C.U)) :
    coverRing C C F.hom (coverRing C C F.inv b) = b := by
  rw [← coverRing_comp_apply, F.hom_inv_id, coverRing_id_apply]

omit [NumberField K] in
lemma coverRing_inv_hom (b : Γ(C.Xbar, C.U)) :
    coverRing C C F.inv (coverRing C C F.hom b) = b := by
  rw [← coverRing_comp_apply, F.inv_hom_id, coverRing_id_apply]

/-- The automorphism of `Γ(U')` induced by `F^*` (when `F^{±1*}` preserve `Γ(U')`). -/
def extRing : Γ(C.Xbar, U') ≃+* Γ(C.Xbar, U') where
  toFun a := (hext a).choose
  invFun a := (hext' a).choose
  left_inv a := resAlg_injective C h (by
    have e1 := (hext' (hext a).choose).choose_spec
    have e2 := (hext a).choose_spec
    rw [← e1, ← e2, coverRing_inv_hom])
  right_inv a := resAlg_injective C h (by
    have e1 := (hext (hext' a).choose).choose_spec
    have e2 := (hext' a).choose_spec
    rw [← e1, ← e2, coverRing_hom_inv])
  map_mul' a b := resAlg_injective C h (by
    have e1 := (hext (a * b)).choose_spec
    have e2 := (hext a).choose_spec
    have e3 := (hext b).choose_spec
    have e4 : resAlg K h ((hext a).choose * (hext b).choose) =
        resAlg K h (hext a).choose * resAlg K h (hext b).choose := map_mul _ _ _
    rw [e4, ← e1, ← e2, ← e3, map_mul, map_mul])
  map_add' a b := resAlg_injective C h (by
    have e1 := (hext (a + b)).choose_spec
    have e2 := (hext a).choose_spec
    have e3 := (hext b).choose_spec
    have e4 : resAlg K h ((hext a).choose + (hext b).choose) =
        resAlg K h (hext a).choose + resAlg K h (hext b).choose := map_add _ _ _
    rw [e4, ← e1, ← e2, ← e3, map_add, map_add])

omit [NumberField K] in
lemma resAlg_extRing (a : Γ(C.Xbar, U')) :
    resAlg K h (extRing C h hext hext' a) = coverRing C C F.hom (resAlg K h a) :=
  (hext a).choose_spec.symm

/-- `Spec` of `extRing`. -/
def extIso : Spec Γ(C.Xbar, U') ≅ Spec Γ(C.Xbar, U') where
  hom := Spec.map (CommRingCat.ofHom (extRing C h hext hext').toRingHom)
  inv := Spec.map (CommRingCat.ofHom (extRing C h hext hext').symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 2
    ext a
    exact (extRing C h hext hext').apply_symm_apply a
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 2
    ext a
    exact (extRing C h hext hext').symm_apply_apply a

omit [NumberField K] in
/-- `res ∘ F' = F ∘ res` as morphisms `Spec Γ(U) ⟶ Spec Γ(U')`. -/
lemma specRes_extIso :
    Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom) ≫ (extIso C h hext hext').hom =
      F.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom) := by
  conv_rhs => rw [← Spec.map_preimage F.hom]
  rw [extIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact resAlg_extRing C h hext hext' a

omit [NumberField K] in
/-- `F'` is over `K` if `F` is. -/
lemma extIso_over (hF : F.hom ≫ sKU C = sKU C) :
    (extIso C h hext hext').hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, U'))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, U'))) := by
  have hf : ∀ c : K, coverRing C C F.hom (algebraMap K Γ(C.Xbar, C.U) c) =
      algebraMap K Γ(C.Xbar, C.U) c := by
    have e : CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)) ≫ Spec.preimage F.hom =
        CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)) :=
      Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage]; exact hF)
    intro c
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) c
  rw [extIso, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  apply resAlg_injective C h
  change resAlg K h (extRing C h hext hext' (algebraMap K Γ(C.Xbar, U') c)) =
    resAlg K h (algebraMap K Γ(C.Xbar, U') c)
  rw [resAlg_extRing, AlgHom.commutes, hf]

end Ext

/-! ### Trivial centre of `Π_{U'}` -/

include hc' hyp in
lemma eq_one_of_forall_commute_fill
    (z : π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')))
    (hz : ∀ w, z * w = w * z) : z = 1 := by
  have hsurj : Function.Surjective (projGkFill Ω C hc h) := fun g ↦ by
    obtain ⟨σ, hσ⟩ := projGk_surjective Ω C hc g
    exact ⟨fillMap Ω C hc h σ, (projGkFill_fillMap Ω C hc h σ).trans hσ⟩
  have h1 : projGkFill Ω C hc h z ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun g ↦ by
    obtain ⟨w, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, hz]
  rw [(isSlim_Gk (K := K) Ω).center_eq_bot, Subgroup.mem_bot] at h1
  have h2 : (⟨z, h1⟩ : (projGkFill Ω C hc h).toMonoidHom.ker) ∈ Subgroup.center _ :=
    Subgroup.mem_center_iff.2 fun w ↦ Subtype.ext (hz w).symm
  rw [(isSlim_ker_projGkFill Ω C hc h hc' hyp).center_eq_bot, Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

/-! ### The main theorem -/

include hc' hyp in
/-- **Automorphisms of `Π_U` compatible with filling are inner** ([AbsTopII] Cor 3.7 (b),
Cor 3.8, uniqueness; DGC as the explicit hypothesis `hDGC`): if `fill ∘ ψ = conj(s) ∘ fill`, then
`ψ = conj(n)` with `fill(n) = s`. -/
theorem exists_eq_conj_of_fillMap (hDGC : RelIsomDGC.Exists K)
    (ψ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (s : π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')))
    (hs : ∀ σ, fillMap Ω C hc h (ψ σ) = s * fillMap Ω C hc h σ * s⁻¹) :
    ∃ n, fillMap Ω C hc h n = s ∧ ∀ σ, ψ σ = n * σ * n⁻¹ := by
  haveI : Nonempty (baseChangeOpen K Ω U') := nonempty_fillOpen Ω C h
  set fill := fillMap Ω C hc h
  obtain ⟨t, ht⟩ := fillMap_surjective Ω C hc h hc' s
  let ψ' := ψ.trans (conjCMEquiv t⁻¹)
  have hψ' : ∀ σ, ψ' σ = t⁻¹ * ψ σ * t := fun σ ↦ by
    change t⁻¹ * ψ σ * t⁻¹⁻¹ = _
    rw [inv_inv]
  have hfill : ∀ σ, fill (ψ' σ) = fill σ := fun σ ↦ by
    rw [hψ', map_mul, map_mul, map_inv, hs, ht]
    group
  have hG : ∀ σ, projGk Ω C hc (ψ' σ) = projGk Ω C hc σ := fun σ ↦ by
    rw [← projGkFill_fillMap Ω C hc h, hfill, projGkFill_fillMap]
  obtain ⟨F, hF, HF⟩ := exists_isConjInduced_of_relIsomDGC Ω hDGC ψ' hG
  haveI : IsFiniteEtale F.hom := MorphismProperty.of_isIso @IsFiniteEtale F.hom
  haveI : IsFiniteEtale F.inv := MorphismProperty.of_isIso @IsFiniteEtale F.inv
  -- `π₁ᵉᵗ(F^{±1})` preserves the filling kernel
  have hN : ∀ n ∈ fill.toMonoidHom.ker, coverPiHom Ω C hc C hc F.hom n ∈ fill.toMonoidHom.ker := by
    obtain ⟨u, hu⟩ := (isConjInduced_iff_exists_conj F.hom (coverFib Ω C hc C hc F.hom) ψ').1 HF
    intro n hn
    have h1 : fill (ψ' n) = 1 := (hfill n).trans hn
    rw [hu, map_mul, map_mul, map_inv, conj_eq_one_iff] at h1
    exact h1
  have HF' := IsConjInduced.symm_of_iso F ψ'.toMulEquiv HF
  have hN' : ∀ n ∈ fill.toMonoidHom.ker, coverPiHom Ω C hc C hc F.inv n ∈ fill.toMonoidHom.ker := by
    obtain ⟨u, hu⟩ := (isConjInduced_iff_exists_conj F.inv (coverFib Ω C hc C hc F.inv)
      ψ'.toMulEquiv.symm).1 HF'
    intro n hn
    have h1 : fill (ψ'.toMulEquiv.symm n) = 1 := by
      rw [← hfill]
      exact (congrArg fill (ψ'.toMulEquiv.apply_symm_apply n)).trans hn
    rw [hu, map_mul, map_mul, map_inv, conj_eq_one_iff] at h1
    exact h1
  -- the extension `F'` of `F` to `Spec Γ(U')`
  have hhyp := isHyperbolic_baseChange Ω (fillCurve C h hyp)
  have hext := exists_resAlg_coverRing Ω C hc h hc' hhyp F.hom hN
  have hext' := exists_resAlg_coverRing Ω C hc h hc' hhyp F.inv hN'
  set F' := extIso C h hext hext'
  -- `F'` induces an inner automorphism of `Π_{U'}`
  have Hfill : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) fill :=
    (isConjInduced_iff _ (fillPoint_spec Ω C hc h) fill).2 ⟨Iso.refl _, fun σ ↦ by
      change _ = (Iso.refl _).conjAut _
      rw [Iso.conjAut_apply]
      ext
      simp
      rfl⟩
  have H1 : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom) ≫ F'.hom)
      (id ∘ fill) :=
    ((HF.comp Hfill).congr_hom (specRes_extIso C h hext hext').symm).congr_fun
      fun σ ↦ (hfill σ).symm
  have H2 : IsConjInduced F'.hom (id : π₁ᵉᵗ(fillPoint Ω C hc h ≫
      baseChangeSpec K Ω Γ(C.Xbar, U')) → _) :=
    IsConjInduced.of_comp_surjective (fillPoint_spec Ω C hc h) id H1
      (fillMap_surjective Ω C hc h hc')
  have H3 := H2.transport_id (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl
    (fillAlpha Ω C hc h hc' hyp).symm)
  have hF'K := extIso_over C h hext hext' hF
  have hF'id : F' = Iso.refl _ :=
    eq_refl_of_isConjInduced_conj Ω (fillCurve C h hyp) hc' 1 (fun σ ↦ by simp) hF'K
      (H3.congr_fun fun σ ↦ by simp)
  -- hence `F = id`
  have hf' : ∀ a, extRing C h hext hext' a = a := fun a ↦ by
    have e : CommRingCat.ofHom (extRing C h hext hext').toRingHom = 𝟙 _ :=
      Spec.map_injective (by
        change F'.hom = _
        rw [hF'id, Spec.map_id]
        rfl)
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) a
  have hf : ∀ b, coverRing C C F.hom b = b :=
    eq_of_forall_resAlg C h hc' (coverRing C C F.hom) fun a ↦ by
      rw [← resAlg_extRing C h hext hext', hf']
  have hFid : F.hom = 𝟙 _ := by
    rw [← specMap_coverRing C C F.hom, ← Spec.map_id]
    congr 1
    ext b
    exact hf b
  -- so `ψ'` is inner, by `m` with `fill m` central
  obtain ⟨m₀, hm⟩ := (isConjInduced_iff (𝟙 _) (Category.comp_id _) ψ').1 (HF.congr_hom hFid)
  let m : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) := m₀
  have hm' : ∀ σ, ψ' σ = m * σ * m⁻¹ := fun σ ↦ by
    rw [hm, fundamentalGroupMap_id]
    exact Aut_conjAut_eq m σ
  have hm1 : fill m = 1 := eq_one_of_forall_commute_fill Ω C hc h hc' hyp _ fun w ↦ by
    obtain ⟨σ, rfl⟩ := fillMap_surjective Ω C hc h hc' w
    have := hfill σ
    rw [hm', map_mul, map_mul, map_inv] at this
    calc fill m * fill σ = fill m * fill σ * (fill m)⁻¹ * fill m := by group
      _ = fill σ * fill m := by rw [this]
  refine ⟨t * m, by rw [map_mul, hm1, mul_one, ht], fun σ ↦ ?_⟩
  have := hm' σ
  rw [hψ'] at this
  calc ψ σ = t * (t⁻¹ * ψ σ * t) * t⁻¹ := by group
    _ = t * m * σ * (t * m)⁻¹ := by rw [this]; group

include hc' hyp in
/-- **Uniqueness of lifts along filling** ([AbsTopII] Cor 3.7 (b) "unique lifting", Cor 3.8
uniqueness): two continuous isomorphisms `φ₁, φ₂ : P ≃ₜ* Π_U` whose composites with
`fill : Π_U ↠ Π_{U'}` differ by `conj(s)` differ by `conj(n)` for some `n` with `fill(n) = s`. -/
theorem exists_eq_conj_comp_of_fillMap (hDGC : RelIsomDGC.Exists K) {P : Type*} [Group P]
    [TopologicalSpace P]
    (φ₁ φ₂ : P ≃ₜ* π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (s : π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')))
    (hs : ∀ p, fillMap Ω C hc h (φ₂ p) = s * fillMap Ω C hc h (φ₁ p) * s⁻¹) :
    ∃ n, fillMap Ω C hc h n = s ∧ ∀ p, φ₂ p = n * φ₁ p * n⁻¹ := by
  obtain ⟨n, hn, hψ⟩ := exists_eq_conj_of_fillMap Ω C hc h hc' hyp hDGC (φ₁.symm.trans φ₂) s
    fun σ ↦ by
      have := hs (φ₁.symm σ)
      rwa [ContinuousMulEquiv.apply_symm_apply] at this
  refine ⟨n, hn, fun p ↦ ?_⟩
  have := hψ (φ₁ p)
  rwa [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply] at this

end CurvesJacobian.Cusp
