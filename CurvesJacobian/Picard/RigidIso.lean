/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicRigid

/-!
# Rigidified isomorphisms of invertible sheaves

This file is generic. Let `r : Y ⟶ T` have a section `s : T ⟶ Y` (`s ≫ r = 𝟙 T`). For invertible
sheaves `L`, `L'` on `Y`, every isomorphism `β : s^*L ≅ s^*L'` is the pullback of an isomorphism
`L ≅ L'` as soon as `L ≅ L'` at all (`exists_iso_pullback_map_eq`): rescale a given isomorphism by
the pullback along `r` of the unit of `Γ(T, 𝒪_T)` by which it differs from `β` along `s`. If
moreover `Y` is rigid along `s` (`IsRigidAlong`), this isomorphism is unique
(`iso_ext_of_pullback_map_eq`). This is the content of the choices made in the proof of Stacks,
Lemma 44.4.3 (Tag 0B9N): isomorphisms `φ_ij` rescaled to be compatible with trivialisations
along `σ`, hence (by uniqueness) satisfying the cocycle condition.

* `smulHom c : M ⟶ M`: multiplication by a global function `c`;
  `pullback_map_smulHom` (for invertible `M`): `s^*(c·) = (s^♯ c)·`.
* `hom_ext_of_isInvertible`: morphisms out of an invertible sheaf agreeing on local bases agree.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}}

/-- Two morphisms out of an invertible sheaf agreeing on a basis near every point are equal. -/
lemma hom_ext_of_isInvertible {A B : Y.Modules} [A.IsInvertible] (φ φ' : A ⟶ B)
    (H : ∀ y : Y, ∃ (U : Y.Opens) (e : Γ(A, U)), y ∈ U ∧ A.IsBasisOn U e ∧
      φ.app U e = φ'.app U e) :
    φ = φ' := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext m
  refine CurvesJacobian.sheaf_eq_of_locally_eq ⟨B.presheaf, B.isSheaf⟩ _ _ fun y hy ↦ ?_
  obtain ⟨U, e, hyU, he, hφ⟩ := H y
  refine ⟨W ⊓ U, inf_le_left, ⟨hy, hyU⟩, ?_⟩
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isBasisOn (isBasisOn_rs he (inf_le_right : W ⊓ U ≤ U))
    (rs A inf_le_left m)
  change rs B inf_le_left (φ.app W m) = rs B inf_le_left (φ'.app W m)
  rw [← app_rs, ← app_rs, ← hk, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    app_rs, app_rs, hφ]

lemma smul_natural (M : Y.Modules) (c : Γ(Y, ⊤)) {U W : Y.Opens} (h : W ≤ U) (m : Γ(M, U)) :
    rs M h (rr (le_top : U ≤ ⊤) c • m) = rr (le_top : W ≤ ⊤) c • rs M h m := by
  rw [rs_smul, rr_rr]

lemma smul_comm' {M : Y.Modules} {U : Y.Opens} (a b : Γ(Y, U)) (m : Γ(M, U)) :
    a • b • m = b • a • m := by
  rw [smul_smul, smul_smul, mul_comm]

/-- Multiplication by a global function. -/
def smulHom (M : Y.Modules) (c : Γ(Y, ⊤)) : M ⟶ M :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (_root_.PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (Γ(M, U.unop))
          (rr (le_top : U.unop ≤ ⊤) c))
        naturality U U' f := by
          ext m
          exact (smul_natural M c f.unop.le m).symm }
      (fun U r m ↦ smul_comm' (M := M) (rr (le_top : U.unop ≤ ⊤) c) r m))

lemma smulHom_app (M : Y.Modules) (c : Γ(Y, ⊤)) (U : Y.Opens) (m : Γ(M, U)) :
    (smulHom M c).app U m = rr (le_top : U ≤ ⊤) c • m :=
  rfl

lemma smulHom_one (M : Y.Modules) : smulHom M 1 = 𝟙 M := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  rw [smulHom_app, rr, map_one, one_smul]
  rfl

lemma smulHom_mul (M : Y.Modules) (c c' : Γ(Y, ⊤)) :
    smulHom M (c * c') = smulHom M c' ≫ smulHom M c := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  change rr (le_top : U ≤ ⊤) (c * c') • m = rr (le_top : U ≤ ⊤) c • rr (le_top : U ≤ ⊤) c' • m
  rw [rr_mul, mul_smul]

lemma smulHom_comp {M N : Y.Modules} (φ : M ⟶ N) (c : Γ(Y, ⊤)) :
    smulHom M c ≫ φ = φ ≫ smulHom N c := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  change φ.app U (rr (le_top : U ≤ ⊤) c • m) = rr (le_top : U ≤ ⊤) c • φ.app U m
  rw [Scheme.Modules.Hom.app_smul]

/-- Pullback of multiplication by `c` is multiplication by `s^♯ c` (for invertible sheaves). -/
lemma pullback_map_smulHom (s : T ⟶ Y) (M : Y.Modules) [M.IsInvertible] (c : Γ(Y, ⊤)) :
    (Modules.pullback s).map (smulHom M c) = smulHom _ (s.app ⊤ c) := by
  refine hom_ext_of_isInvertible _ _ fun t ↦ ?_
  obtain ⟨U, e, hsU, he⟩ := IsInvertible.exists_basis (L := M) (s.base t)
  refine ⟨s ⁻¹ᵁ U, pullbackSection s e, hsU, isBasisOn_pullbackSection s U he, ?_⟩
  rw [pullbackSection_naturality, smulHom_app]
  have h2 := pullbackSection_smul s (rr (le_top : U ≤ ⊤) c) e
  change pullbackSection s (rr (le_top : U ≤ ⊤) c • e) = _ at h2
  rw [h2, app_rr]
  rfl

lemma eq_smulHom (L : Y.Modules) [L.IsInvertible] (θ : L ⟶ L) : ∃ c, θ = smulHom L c := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isInvertible L θ
  exact ⟨c, Scheme.Modules.hom_ext _ _ fun U ↦ by ext m; exact hc U m⟩

lemma smulHom_injective (L : Y.Modules) [L.IsInvertible] {c c' : Γ(Y, ⊤)}
    (h : smulHom L c = smulHom L c') : c = c' := by
  refine CurvesJacobian.sheaf_eq_of_locally_eq Y.sheaf (V := ⊤) c c' fun y _ ↦ ?_
  obtain ⟨U, e, hyU, he⟩ := IsInvertible.exists_basis (L := L) y
  refine ⟨U, le_top, hyU, smul_left_injective_of_isBasisOn he ?_⟩
  have := congrArg (fun θ : L ⟶ L ↦ θ.app U e) h
  exact this

lemma app_app_of_section (r : Y ⟶ T) (s : T ⟶ Y) (hsr : s ≫ r = 𝟙 T) (v : Γ(T, ⊤)) :
    s.app ⊤ (r.appTop v) = v := by
  have : (s ≫ r).app ⊤ v = s.app ⊤ (r.appTop v) := by
    rw [Scheme.Hom.comp_app]
    rfl
  rw [hsr, Scheme.Hom.id_app] at this
  exact this.symm

/-- **Rigidified isomorphisms exist**: if `L ≅ L'`, then every isomorphism `s^*L ≅ s^*L'` is the
pullback of an isomorphism `L ≅ L'` (for `s` a section of `r`). -/
theorem exists_iso_pullback_map_eq (r : Y ⟶ T) (s : T ⟶ Y) (hsr : s ≫ r = 𝟙 T)
    {L L' : Y.Modules} [L.IsInvertible] [L'.IsInvertible] (φ : L ≅ L')
    (β : (Modules.pullback s).obj L ≅ (Modules.pullback s).obj L') :
    ∃ φ' : L ≅ L', (Modules.pullback s).map φ'.hom = β.hom := by
  obtain ⟨u', hu'⟩ := eq_smulHom _ (β.hom ≫ (Modules.pullback s).map φ.inv)
  obtain ⟨u, hu⟩ := eq_smulHom _ ((Modules.pullback s).map φ.hom ≫ β.inv)
  have h₁ : u' * u = 1 := by
    refine smulHom_injective ((Modules.pullback s).obj L) ?_
    rw [smulHom_mul, ← hu, ← hu', smulHom_one]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have h₂ : u * u' = 1 := by rw [mul_comm, h₁]
  have e₁ : smulHom L (r.appTop u') ≫ smulHom L (r.appTop u) = 𝟙 L := by
    rw [← smulHom_mul, ← map_mul, h₂, map_one, smulHom_one]
  have e₂ : smulHom L (r.appTop u) ≫ smulHom L (r.appTop u') = 𝟙 L := by
    rw [← smulHom_mul, ← map_mul, h₁, map_one, smulHom_one]
  refine ⟨{ hom := smulHom L (r.appTop u') ≫ φ.hom
            inv := φ.inv ≫ smulHom L (r.appTop u)
            hom_inv_id := by simp [e₁]
            inv_hom_id := by
              rw [Category.assoc, ← Category.assoc (smulHom L _), e₂, Category.id_comp,
                Iso.inv_hom_id] }, ?_⟩
  change (Modules.pullback s).map (smulHom L (r.appTop u') ≫ φ.hom) = β.hom
  rw [Functor.map_comp, pullback_map_smulHom, app_app_of_section r s hsr, ← hu']
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- **Rigidified isomorphisms are unique** if `Y` is rigid along `s`. -/
theorem iso_ext_of_pullback_map_eq (s : T ⟶ Y) (hs : IsRigidAlong s) {L L' : Y.Modules}
    [L.IsInvertible] {φ₁ φ₂ : L ≅ L'}
    (h : (Modules.pullback s).map φ₁.hom = (Modules.pullback s).map φ₂.hom) : φ₁ = φ₂ := by
  have := eq_id_of_pullback_map_eq_id s hs L (φ₁.hom ≫ φ₂.inv) (by
    rw [Functor.map_comp, h, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
  ext1
  rw [← Category.comp_id φ₁.hom, ← φ₂.inv_hom_id, ← Category.assoc, this, Category.id_comp]

end CurvesJacobian.ModulesGlue
