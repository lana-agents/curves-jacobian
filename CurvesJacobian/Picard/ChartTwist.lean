/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwistCech
import FormalSchemes.ProjectiveLineTwistChart

/-!
# Line bundles glued from two charts

Let `X` be a scheme covered by two opens `U`, `V` and `t ∈ Γ(X, U ∩ V)` a unit. The twist
`𝒪(t) = twoSetTwist 𝒪_X U V t` of formal-schemes (sections over `W`: pairs
`(a, b) ∈ 𝒪(U ∩ W) × 𝒪(V ∩ W)` with `a = t b`) is the invertible sheaf trivialised on `U` and
`V` with transition function `t` (`Scheme.Modules.isInvertible_twist`): it has the bases
`twistBasisLeft` on `U` and `twistBasisRight` on `V`.

For `X → ℙ¹` with pulled-back chart coordinates `τ` on `U`, `σ` on `V` (`τ σ = 1` on `U ∩ V`)
and `t = τⁿ`, this is the pullback of `𝒪_{ℙ¹}(n)`; its global section `(1, σⁿ)`
(`twistSection`) restricts to the basis on `U` and to `σⁿ` times the basis on `V`: it is the
section `x₀ⁿ` whose divisor is `n · π⁻¹(∞)`. These are the twists used in the proof of Stacks,
Lemma 44.6.5 (Tag 0B9Y), to kill `H¹`.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Function

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {U V : X.Opens} {t : Γ(X, U ⊓ V)}

lemma map_map_map_self {W W' W'' : X.Opens} (i : op W ⟶ op W') (j : op W' ⟶ op W'')
    (k : op W'' ⟶ op W) (a : Γ(X, W)) :
    X.presheaf.map k (X.presheaf.map j (X.presheaf.map i a)) = a := by
  have e : i ≫ j ≫ k = 𝟙 _ := Subsingleton.elim _ _
  calc _ = (X.presheaf.map (i ≫ j ≫ k)) a := by
        simp only [Functor.map_comp, CommRingCat.comp_apply]
    _ = a := by rw [e, CategoryTheory.Functor.map_id]; rfl

/-- The basis of `𝒪(t)` on `U`, corresponding to `1 ∈ Γ(X, U)`. -/
def twistBasisLeft (ht : IsUnit t) : Γ(twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t, U) :=
  (twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht (le_refl U)).symm
    (1 : Γ(X, U))

/-- The basis of `𝒪(t)` on `V`, corresponding to `1 ∈ Γ(X, V)`. -/
def twistBasisRight : Γ(twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t, V) :=
  (twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t) (le_refl V)).symm
    (1 : Γ(X, V))

lemma isBasisOn_twistBasisLeft (ht : IsUnit t) :
    (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t).IsBasisOn U (twistBasisLeft ht) := by
  intro W hW
  have key : (fun r : X.ringCatSheaf.obj.obj (op W) ↦ r • Scheme.PresheafOfModules.res
      ((toPresheafOfModules X).obj (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t)) hW
        (twistBasisLeft ht)) =
      (twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht hW).symm ∘
        (fun r : Γ(X, W) ↦ r) := by
    funext r
    apply (twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht hW).injective
    rw [comp_apply, AddEquiv.apply_symm_apply]
    change twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht hW
      ((show Γ(X, W) from r) • (twoSetTwist _ U V t).presheaf.map (homOfLE hW).op
      (twistBasisLeft ht)) = r
    rw [twistAppEquivLeft_smul, twistAppEquivLeft_res ht (le_refl U) hW, twistBasisLeft,
      AddEquiv.apply_symm_apply]
    change (show Γ(X, W) from r) * X.presheaf.map (homOfLE hW).op (1 : Γ(X, U)) = r
    rw [map_one, mul_one]
  rw [key]
  exact (twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht
    hW).symm.bijective.comp
    bijective_id

lemma isBasisOn_twistBasisRight :
    (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t).IsBasisOn V
      (twistBasisRight (U := U) (t := t)) := by
  intro W hW
  have key : (fun r : X.ringCatSheaf.obj.obj (op W) ↦ r • Scheme.PresheafOfModules.res
      ((toPresheafOfModules X).obj (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t)) hW
        (twistBasisRight (U := U) (t := t))) =
      (twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t) hW).symm ∘
        (fun r : Γ(X, W) ↦ r) := by
    funext r
    apply (twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t)
      hW).injective
    rw [comp_apply, AddEquiv.apply_symm_apply]
    change twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t) hW
      ((show Γ(X, W) from r) • (twoSetTwist _ U V t).presheaf.map (homOfLE hW).op
      twistBasisRight) = r
    rw [twistAppEquivRight_smul, twistAppEquivRight_res (le_refl V) hW, twistBasisRight,
      AddEquiv.apply_symm_apply]
    change (show Γ(X, W) from r) * X.presheaf.map (homOfLE hW).op (1 : Γ(X, V)) = r
    rw [map_one, mul_one]
  rw [key]
  exact (twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t)
    hW).symm.bijective.comp bijective_id

/-- **The twist of the structure sheaf by a unit is invertible.** -/
theorem isInvertible_twist (hUV : U ⊔ V = ⊤) (ht : IsUnit t) :
    (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t).IsInvertible where
  exists_basis x := by
    by_cases hx : x ∈ U
    · exact ⟨U, _, hx, isBasisOn_twistBasisLeft ht⟩
    · have hxV : x ∈ V := by
        have : x ∈ U ⊔ V := hUV ▸ trivial
        exact this.resolve_left hx
      exact ⟨V, _, hxV, isBasisOn_twistBasisRight⟩

/-- The global section `(a, b)` of `𝒪(t)` for `a ∈ Γ(X, U)`, `b ∈ Γ(X, V)` with `a = t b` on
`U ∩ V`. -/
def twistSection (a : Γ(X, U)) (b : Γ(X, V))
    (h : X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a =
      t * X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b) :
    Γ(twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t, ⊤) :=
  twoSetTwistMk t (X.presheaf.map (homOfLE inf_le_left : U ⊓ ⊤ ⟶ U).op a)
    (X.presheaf.map (homOfLE inf_le_left : V ⊓ ⊤ ⟶ V).op b) (by
      change X.presheaf.map _ (X.presheaf.map _ a) =
        X.presheaf.map _ t * X.presheaf.map _ (X.presheaf.map _ b)
      rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply (X.presheaf.map _),
        ← Functor.map_comp]
      have := congrArg (X.presheaf.map (homOfLE (inf_le_left : (U ⊓ V) ⊓ ⊤ ≤ U ⊓ V)).op) h
      rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply
        (X.presheaf.map _) (X.presheaf.map _) b, ← Functor.map_comp] at this
      exact this)

variable {a : Γ(X, U)} {b : Γ(X, V)}
  {h : X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a =
      t * X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b}

lemma twistSection_res_left (ht : IsUnit t) :
    (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (twistSection a b h) = a • twistBasisLeft ht := by
  apply (twistAppEquivLeft (M := SheafOfModules.unit X.ringCatSheaf) (V := V) ht
    (le_refl U)).injective
  rw [twistAppEquivLeft_smul, twistBasisLeft, AddEquiv.apply_symm_apply]
  change X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _ a)) = a * (1 : Γ(X, U))
  rw [mul_one]
  exact map_map_map_self _ _ _ a

lemma twistSection_res_right :
    (twoSetTwist (SheafOfModules.unit X.ringCatSheaf) U V t).presheaf.map
      (homOfLE (le_top : V ≤ ⊤)).op (twistSection a b h) = b • twistBasisRight := by
  apply (twistAppEquivRight (M := SheafOfModules.unit X.ringCatSheaf) (U := U) (τ := t)
    (le_refl V)).injective
  rw [twistAppEquivRight_smul, twistBasisRight, AddEquiv.apply_symm_apply]
  change X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _ b)) = b * (1 : Γ(X, V))
  rw [mul_one]
  exact map_map_map_self _ _ _ b

end AlgebraicGeometry.Scheme.Modules
