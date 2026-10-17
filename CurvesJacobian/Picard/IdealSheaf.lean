/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicMap
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The ideal sheaf of a locally principal closed subscheme

For an ideal sheaf `I : X.IdealSheafData` we define the presheaf of ideals
`U ↦ {f ∈ 𝒪(U) | f|_V ∈ I(V) for all affine V ≤ U}` (`IdealSheafData.idealPre`) and its
sheafification `I.idealSheaf : X.Modules`. If `I(U) = (g)` with `g` a nonzerodivisor on an affine
open `U`, then (the image of) `g` is a basis of `I.idealSheaf` on `U`
(`IdealSheafData.isBasisOn_idealSheaf`); so if `I` is locally principal with nonzerodivisor
generators (an effective Cartier divisor, cf. Stacks, Tag 01WR), `I.idealSheaf` is invertible.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

lemma CurvesJacobian.isSMulRegular_algebraMap_of_isLocalization {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] {g : R}
    (hg : IsSMulRegular R g) : IsSMulRegular S (algebraMap R S g) := by
  have key : ∀ c : S, algebraMap R S g * c = 0 → c = 0 := by
    intro c hc
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M c
    simp only at hc ⊢
    rw [← IsLocalization.mk'_one (M := M) S g, ← IsLocalization.mk'_mul, one_mul] at hc
    obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hc
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨m, hg ?_⟩
    simp only [smul_eq_mul, mul_zero]
    rw [← mul_assoc, mul_comm g, mul_assoc, hm]
  intro a b hab
  simp only [smul_eq_mul] at hab
  exact sub_eq_zero.mp (key _ (by rw [mul_sub, hab, sub_self]))

namespace AlgebraicGeometry.Scheme

open CurvesJacobian

variable {X : Scheme.{u}}

namespace PresheafOfModules

open _root_.PresheafOfModules

/-- A variant of `isBasisOn_of_isLocallyBijective` where bijectivity is only required on the
members of a basis of the topology. -/
theorem isBasisOn_of_isLocallyBijective_of_basis {P Q : X.PresheafOfModules} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    (hQ : TopCat.Presheaf.IsSheaf ((toPresheaf _).obj Q)) (B : Set X.Opens)
    (hB : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ W ∈ B, x ∈ W ∧ W ≤ V)
    {U : X.Opens} {e : P.obj (op U)}
    (he : ∀ ⦃W : X.Opens⦄, W ∈ B → ∀ h : W ≤ U,
      Function.Bijective (fun r : X.ringCatSheaf.obj.obj (op W) ↦ r • res P h e)) :
    IsBasisOn Q U (η.app _ e) := by
  have inj : ∀ ⦃V⦄ (h : V ≤ U), Function.Injective
      (fun r : X.ringCatSheaf.obj.obj (op V) ↦ r • res Q h (η.app _ e)) := by
    intro V h r r' hrr'
    simp only at hrr'
    rw [← sub_eq_zero]
    have h0 : η.app _ ((r - r') • res P h e) = 0 := by
      rw [map_smul, app_res, sub_smul, hrr', sub_self]
    apply sheaf_eq_of_locally_eq X.sheaf
    intro x hx
    obtain ⟨W₀, hW₀, hxW₀, hW₀0⟩ := exists_res_eq_zero η _ h0 x hx
    obtain ⟨W, hWB, hxW, hWW₀⟩ := hB W₀ x hxW₀
    have hW : W ≤ V := hWW₀.trans hW₀
    refine ⟨W, hW, hxW, ?_⟩
    have hW0 : res P hW ((r - r') • res P h e) = 0 := by
      rw [← res_res P hW₀ hWW₀, hW₀0, res_zero]
    rw [res_smul, res_res] at hW0
    have h1 := (he hWB (hW.trans h)).1 (a₁ := X.ringCatSheaf.obj.map (homOfLE hW).op (r - r'))
      (a₂ := 0) (by simp only; rw [hW0, zero_smul])
    exact h1.trans (map_zero _).symm
  intro V h
  refine ⟨inj h, fun n ↦ ?_⟩
  have hloc : ∀ x ∈ V, ∃ W ∈ B, ∃ hW : W ≤ V, x ∈ W ∧
      ∃ r : X.ringCatSheaf.obj.obj (op W), r • res Q (hW.trans h) (η.app _ e) = res Q hW n := by
    intro x hx
    obtain ⟨W₀, hW₀, hxW₀, p, hp⟩ := exists_res_eq_app η n x hx
    obtain ⟨W, hWB, hxW, hWW₀⟩ := hB W₀ x hxW₀
    refine ⟨W, hWB, hWW₀.trans hW₀, hxW, ?_⟩
    obtain ⟨r, hr⟩ := (he hWB ((hWW₀.trans hW₀).trans h)).2 (res P hWW₀ p)
    simp only at hr
    refine ⟨r, ?_⟩
    rw [← res_res Q hW₀ hWW₀, ← hp]
    refine Eq.trans ?_ (app_res η hWW₀ p)
    rw [← hr]
    exact (congrArg (r • ·) (app_res η _ e).symm).trans
      (_root_.map_smul (η.app (op W)).hom r _).symm
  choose W hWB hW hxW r hr using hloc
  have key : ∀ (x : V) {Z : X.Opens} (hZ : Z ≤ W x.1 x.2),
      X.ringCatSheaf.obj.map (homOfLE hZ).op (r x.1 x.2) •
        res Q (hZ.trans ((hW x.1 x.2).trans h)) (η.app _ e) =
          res Q (hZ.trans (hW x.1 x.2)) n := by
    intro x Z hZ
    rw [← res_res Q ((hW x.1 x.2).trans h) hZ, ← res_smul, hr, res_res]
  obtain ⟨R, hR⟩ := sheaf_exists_glue X.sheaf (V := V) (fun x ↦ W x.1 x.2)
    (fun x ↦ hW x.1 x.2) (fun x ↦ hxW x.1 x.2) (fun x ↦ r x.1 x.2) (by
      intro x y
      apply inj ((inf_le_left : W x.1 x.2 ⊓ W y.1 y.2 ≤ _).trans ((hW x.1 x.2).trans h))
      refine (key x inf_le_left).trans ((key y inf_le_right).trans ?_).symm
      rfl)
  let R' : X.ringCatSheaf.obj.obj (op V) := R
  refine ⟨R', ?_⟩
  apply sheaf_eq_of_locally_eq ⟨(toPresheaf _).obj Q, hQ⟩
  intro x hx
  refine ⟨W x hx, hW x hx, hxW x hx, ?_⟩
  change res Q (hW x hx) (R' • res Q h (η.app _ e)) = res Q (hW x hx) n
  rw [res_smul, res_res]
  have := hR ⟨x, hx⟩
  rw [← ringCatSheaf_map_apply] at this
  rw [this, hr]

end PresheafOfModules

namespace IdealSheafData

variable (I : X.IdealSheafData)

/-- The sub-presheaf of `𝒪_X` of sections lying in `I` on every affine open. -/
def idealSub : (𝟙_ X.PresheafOfModules).Submodule where
  obj U :=
    { carrier := {f | ∀ (V : X.affineOpens) (h : V.1 ≤ U.unop),
        X.presheaf.map (homOfLE h).op f ∈ I.ideal V}
      add_mem' {f g} hf hg V h := by
        rw [show X.presheaf.map (homOfLE h).op (f + g) =
          X.presheaf.map (homOfLE h).op f + X.presheaf.map (homOfLE h).op g from map_add _ _ _]
        exact add_mem (hf V h) (hg V h)
      zero_mem' V h := by
        convert zero_mem (I.ideal V)
        exact map_zero _
      smul_mem' c f hf V h := by
        rw [show X.presheaf.map (homOfLE h).op (c • f : Γ(X, U.unop)) =
          X.presheaf.map (homOfLE h).op c * X.presheaf.map (homOfLE h).op f from map_mul _ _ _]
        exact Ideal.mul_mem_left _ _ (hf V h) }
  map {U U'} g f hf V h := by
    have := hf V (h.trans g.unop.le)
    change X.presheaf.map (homOfLE h).op (X.presheaf.map g f) ∈ I.ideal V
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp]

lemma mem_idealSub_iff_of_isAffine (V : X.affineOpens) (f : Γ(X, V.1)) :
    f ∈ (I.idealSub.obj (op V.1)) ↔ f ∈ I.ideal V := by
  constructor
  · intro hf
    have := hf V le_rfl
    rwa [show X.presheaf.map (homOfLE (le_refl V.1)).op f = f by
      rw [show (homOfLE (le_refl V.1)).op = 𝟙 (op V.1) from rfl, CategoryTheory.Functor.map_id]
      rfl] at this
  · intro hf W h
    exact I.ideal_le_comap_ideal h hf

/-- The presheaf of ideals of `I`. -/
abbrev idealPre : X.PresheafOfModules := I.idealSub.toPresheafOfModules

/-- The ideal sheaf of `I`, as a sheaf of `𝒪_X`-modules. -/
def idealSheaf : X.Modules := (Modules.sheafify X).obj I.idealPre

variable {I}

lemma isBasisOn_idealPre_basicOpen {U : X.affineOpens} {g : Γ(X, U.1)}
    (hI : I.ideal U = Ideal.span {g}) (hg : IsSMulRegular Γ(X, U.1) g) (f : Γ(X, U.1)) :
    Function.Bijective (fun r : X.ringCatSheaf.obj.obj (op (X.basicOpen f)) ↦
      r • Scheme.PresheafOfModules.res I.idealPre (X.basicOpen_le f)
        (⟨g, (I.mem_idealSub_iff_of_isAffine U g).mpr (hI ▸ Ideal.mem_span_singleton_self g)⟩ :
          I.idealSub.obj (op U.1))) := by
  haveI := U.2.isLocalization_basicOpen f
  have hreg := isSMulRegular_algebraMap_of_isLocalization (S := Γ(X, X.basicOpen f))
    (Submonoid.powers f) hg
  constructor
  · intro r r' h
    have h' : (show Γ(X, X.basicOpen f) from r) * X.presheaf.map (homOfLE (X.basicOpen_le f)).op g =
        (show Γ(X, X.basicOpen f) from r') * X.presheaf.map (homOfLE (X.basicOpen_le f)).op g :=
      congrArg Subtype.val h
    refine hreg ?_
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * (show Γ(X, X.basicOpen f) from r) =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * (show Γ(X, X.basicOpen f) from r')
    rw [mul_comm, mul_comm (algebraMap _ _ g)]
    exact h'
  · rintro ⟨y, hy⟩
    have hy' : y ∈ I.ideal (X.affineBasicOpen f) :=
      (I.mem_idealSub_iff_of_isAffine (X.affineBasicOpen f) y).mp hy
    rw [← I.map_ideal_basicOpen, hI, Ideal.map_span, Set.image_singleton] at hy'
    obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton' (α := Γ(X, X.basicOpen f))).mp hy'
    exact ⟨a, Subtype.ext ha⟩

/-- On an affine open where `I` is generated by a nonzerodivisor `g`, the image of `g` is a
basis of the ideal sheaf. -/
lemma isBasisOn_idealSheaf {U : X.affineOpens} {g : Γ(X, U.1)}
    (hI : I.ideal U = Ideal.span {g}) (hg : IsSMulRegular Γ(X, U.1) g) :
    I.idealSheaf.IsBasisOn U.1 ((Modules.toSheafify I.idealPre).app (op U.1)
      ⟨g, (I.mem_idealSub_iff_of_isAffine U g).mpr (hI ▸ Ideal.mem_span_singleton_self g)⟩) := by
  refine Scheme.PresheafOfModules.isBasisOn_of_isLocallyBijective_of_basis
    (Modules.toSheafify I.idealPre) ((Modules.sheafify X).obj I.idealPre).isSheaf
    ({W | ¬ W ≤ U.1} ∪ Set.range (X.basicOpen (U := U.1))) ?_ ?_
  · intro V x hx
    by_cases hxU : x ∈ U.1
    · obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
      exact ⟨X.basicOpen f, Or.inr ⟨f, rfl⟩, hxf, hfV⟩
    · exact ⟨V, Or.inl (fun h ↦ hxU (h hx)), hx, le_rfl⟩
  · rintro W (hW | ⟨f, rfl⟩) h
    · exact absurd h hW
    · exact isBasisOn_idealPre_basicOpen hI hg f

/-- An ideal sheaf which is locally generated by nonzerodivisors is invertible. -/
lemma isInvertible_idealSheaf
    (H : ∀ x : X, ∃ (U : X.affineOpens) (g : Γ(X, U.1)), x ∈ U.1 ∧
      I.ideal U = Ideal.span {g} ∧ IsSMulRegular Γ(X, U.1) g) :
    I.idealSheaf.IsInvertible where
  exists_basis x := by
    obtain ⟨U, g, hxU, hI, hg⟩ := H x
    exact ⟨U.1, _, hxU, isBasisOn_idealSheaf hI hg⟩

end IdealSheafData

end AlgebraicGeometry.Scheme

end
