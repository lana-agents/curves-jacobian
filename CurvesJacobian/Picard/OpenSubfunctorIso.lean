/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OpenSubfunctor

/-!
# Representing objects of open subfunctors are open subschemes

This file is generic. Let `F` be a Zariski sheaf on schemes represented by a scheme `X` with
universal element `ξX`, and let `p` be a Zariski-local predicate cutting out an open subfunctor
of `F` (tested on affine schemes). If the subfunctor is represented (on affine schemes) by a
scheme `Y` with universal element `η`, then `Y` is isomorphic to the open subscheme `O ⊆ X` over
which `ξX` satisfies `p`, compatibly with the universal elements
(`AlgebraicGeometry.Scheme.OpenSubfunctor.exists_iso_opens`).

This is how properties of representing schemes of the pieces of a covering by open
subfunctors (e.g. being of finite type) are transferred to the representing scheme of `F`.
-/

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.OpenSubfunctor

variable {F : Sheaf Scheme.zariskiTopology.{u} (Type u)}
  {p : ∀ T : Scheme.{u}, F.obj.obj (op T) → Prop}

/-- **The representing scheme of an open subfunctor is an open subscheme.** Let `ξX ∈ F(X)`
represent `F`, `p` a local predicate defining an open subfunctor, and `η ∈ F(Y)` represent the
subfunctor `p` on affine schemes. Then there are an open `O ⊆ X` (the locus where `ξX`
satisfies `p`) and an isomorphism `O ≅ Y` matching `η` with `ξX|_O`. -/
theorem exists_iso_opens (hp : IsLocalPredicate F p)
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p T' (F.obj.map h.op x) ↔ Set.range h ⊆ U)
    {X : Scheme.{u}} (ξX : F.obj.obj (op X))
    (hXinj : ∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ X ↦ F.obj.map a.op ξX)
    (hXsurj : ∀ (T : Scheme.{u}) (x : F.obj.obj (op T)), ∃ a : T ⟶ X, F.obj.map a.op ξX = x)
    {Y : Scheme.{u}} (η : F.obj.obj (op Y))
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op η)
    (hrange : ∀ (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)),
      p T x ↔ ∃ a : T ⟶ Y, F.obj.map a.op η = x) :
    ∃ (O : X.Opens) (e : O.toScheme ≅ Y),
      (∀ (T' : Scheme.{u}) (h : T' ⟶ X), p T' (F.obj.map h.op ξX) ↔ Set.range h ⊆ O) ∧
        F.obj.map e.hom.op η = F.obj.map O.ι.op ξX := by
  obtain ⟨O, hO⟩ := exists_opens_of_isAffine hp hopen ξX
  have hinj' := injective_of_isAffine η hinj
  have hrange' {T : Scheme.{u}} (x : F.obj.obj (op T)) :=
    iff_exists_of_isAffine η hp hinj hrange x
  -- `ξX|_O` comes from `Y`
  have hpO : p O (F.obj.map O.ι.op ξX) := (hO O O.ι).2 (by rw [Scheme.Opens.range_ι])
  obtain ⟨b, hb⟩ := (hrange' _).1 hpO
  -- `η` comes from `X`, through `O`
  obtain ⟨a, ha⟩ := hXsurj Y η
  have hpη : p Y (F.obj.map a.op ξX) := by
    rw [ha]
    exact (hrange' η).2 ⟨𝟙 Y, by rw [op_id, Functor.map_id_apply]⟩
  have haO : Set.range a ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    exact (hO Y a).1 hpη
  let a' : Y ⟶ O := IsOpenImmersion.lift O.ι a haO
  have ha' : a' ≫ O.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hba : b ≫ a' = 𝟙 O.toScheme := by
    rw [← cancel_mono O.ι, Category.assoc, ha', Category.id_comp]
    apply hXinj
    change F.obj.map (b ≫ a).op ξX = F.obj.map O.ι.op ξX
    rw [op_comp, Functor.map_comp_apply, ha, hb]
  have hab : a' ≫ b = 𝟙 Y := by
    apply hinj'
    change F.obj.map (a' ≫ b).op η = F.obj.map (𝟙 Y).op η
    rw [op_comp, Functor.map_comp_apply, hb, ← Functor.map_comp_apply, ← op_comp, ha', ha,
      op_id, Functor.map_id_apply]
  exact ⟨O, ⟨b, a', hba, hab⟩, hO, hb⟩

end AlgebraicGeometry.Scheme.OpenSubfunctor
