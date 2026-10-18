/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechLineBundle
import CurvesJacobian.Picard.LineBundle

/-!
# Two-set Čech `H⁰` is the module of global sections

For an `𝒪_Y`-module `L` on a scheme `Y` over `S` and opens `U`, `V` with `U ∪ V = Y`, the map
`Γ(L, Y) → Ȟ⁰({U, V}, L)`, `s ↦ (s|_U, s|_V)`, is an isomorphism of `Γ(S)`-modules
(`CurvesJacobian.Cech.globalSectionsEquivH0`): this is the sheaf axiom for the cover `{U, V}`.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.Cech

open scoped Cech

variable (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) (U V : Y.Opens)

lemma mem_H0_iff {U V : Y.Opens} (x : Γ(L, U) × Γ(L, V)) : x ∈ cechModH0 S L U V ↔
    L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x.1 =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x.2 := by
  rw [LinearMap.mem_ker, TwoCech.d, LinearMap.coprod_apply, LinearMap.neg_apply,
    ← sub_eq_add_neg, sub_eq_zero]
  rfl

/-- `s ↦ (s|_U, s|_V)`, from global sections to the two-set Čech `H⁰`. -/
def toH0 : Γ(L, ⊤) →ₗ[Γ(S, ⊤)] cechModH0 S L U V where
  toFun s := ⟨(resModLin S L le_top s, resModLin S L le_top s), by
    rw [mem_H0_iff]
    change (L.presheaf.map _ ≫ L.presheaf.map _) s = (L.presheaf.map _ ≫ L.presheaf.map _) s
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl⟩
  map_add' a b := by ext <;> simp
  map_smul' r a := by ext <;> simp

@[simp]
lemma toH0_apply_fst (s : Γ(L, ⊤)) : ((toH0 S L U V s : _) : Γ(L, U) × Γ(L, V)).1 =
    L.presheaf.map (homOfLE le_top).op s := rfl

@[simp]
lemma toH0_apply_snd (s : Γ(L, ⊤)) : ((toH0 S L U V s : _) : Γ(L, U) × Γ(L, V)).2 =
    L.presheaf.map (homOfLE le_top).op s := rfl

variable {U V}

/-- **The sheaf axiom for a two-set cover**: if `U ∪ V = Y`, global sections of `L` are the
two-set Čech `H⁰`. -/
theorem bijective_toH0 (h : U ⊔ V = ⊤) : Function.Bijective (toH0 S L U V) := by
  let F : TopCat.Sheaf Ab.{u} Y.toTopCat := ⟨L.presheaf, L.isSheaf⟩
  have hmem : ∀ y : Y, y ∈ U ∨ y ∈ V := fun y ↦ by
    have : y ∈ U ⊔ V := h ▸ trivial
    simpa using this
  constructor
  · intro a b hab
    have h1 := congrArg (fun z : cechModH0 S L U V ↦ (z : Γ(L, U) × Γ(L, V)).1) hab
    have h2 := congrArg (fun z : cechModH0 S L U V ↦ (z : Γ(L, U) × Γ(L, V)).2) hab
    simp only [toH0_apply_fst, toH0_apply_snd] at h1 h2
    refine CurvesJacobian.sheaf_eq_of_locally_eq F a b fun y _ ↦ ?_
    rcases hmem y with hy | hy
    · exact ⟨U, le_top, hy, h1⟩
    · exact ⟨V, le_top, hy, h2⟩
  · rintro ⟨⟨a, b⟩, hab⟩
    rw [mem_H0_iff] at hab
    let W : Bool → Y.Opens := fun i ↦ cond i U V
    let sf : ∀ i, ToType (F.1.obj (op (W i))) := fun i ↦ match i with
      | true => a
      | false => b
    have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ ↦ by
      rw [Opens.mem_iSup]
      rcases hmem y with hy | hy
      · exact ⟨true, hy⟩
      · exact ⟨false, hy⟩
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top) hcov sf (by
      rintro (_ | _) (_ | _)
      · rfl
      · change L.presheaf.map (Opens.infLELeft V U).op b =
          L.presheaf.map (Opens.infLERight V U).op a
        rw [show Opens.infLELeft V U = homOfLE (le_of_eq (inf_comm V U)) ≫
            homOfLE (inf_le_right : U ⊓ V ≤ V) from rfl,
          show Opens.infLERight V U = homOfLE (le_of_eq (inf_comm V U)) ≫
            homOfLE (inf_le_left : U ⊓ V ≤ U) from rfl,
          op_comp, op_comp, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply, hab]
      · exact hab
      · rfl)
    exact ⟨s, Subtype.ext (Prod.ext (hs true) (hs false))⟩

/-- Global sections of `L` are the two-set Čech `H⁰` for a cover `U ∪ V = Y`. -/
def globalSectionsEquivH0 (h : U ⊔ V = ⊤) : Γ(L, ⊤) ≃ₗ[Γ(S, ⊤)] cechModH0 S L U V :=
  LinearEquiv.ofBijective (toH0 S L U V) (bijective_toH0 S L h)

@[simp]
lemma globalSectionsEquivH0_apply (h : U ⊔ V = ⊤) (s : Γ(L, ⊤)) :
    globalSectionsEquivH0 S L h s = toH0 S L U V s := rfl

end CurvesJacobian.Cech
