/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianBaseChange

/-!
# The Galois action on the Jacobian of `C_Ω`

## Generic part (Yoneda)

Let `p : S' ⟶ S` be a morphism of schemes, `P : (Sch/S)ᵒᵖ ⥤ Type` a presheaf and `X` an
`S'`-scheme representing the restriction of `P` to `(Sch/S')` (`T ↦ P(T ⟶ S' ⟶ S)`). Every
automorphism `α` of `S'` over `S` (`α ≫ p = p`) induces a morphism of schemes
`φ_α = (twistHom p P R hα).left : X ⟶ X` lying over `α` (`twistHom_left_comp`), characterised
on points by `homEquiv_twistPt`: the point `x ≫ φ_α` of `X` over `t ≫ α` corresponds to the same
element of `P(T)` as `x`. These satisfy `φ_α ≫ φ_β = φ_{α ≫ β}` (`twistHom_left_comp_left`) and
`φ_𝟙 = 𝟙` (`twistHom_left_id`), so every `φ_α` is an isomorphism.

## The Jacobian

For a curve `C` over a perfect field `k` with a rational point `σ` and a separably closed perfect
`Ω ⊇ k`, the Jacobian `J_Ω` of `C_Ω` represents `Pic⁰_{C/k,σ}` on `(Sch/Ω)`
(`jacobianBCRepresentableBy`), so `Aut(Ω/k)` acts on the scheme `J_Ω`:

* **`CurvesJacobian.jacGal τ : J_Ω ⟶ J_Ω`**, lying over `Spec(τ)` (`jacGal_comp_hom`), with
  `jacGal τ₁ ≫ jacGal τ₂ = jacGal (τ₁ * τ₂)` and `jacGal 1 = 𝟙`; each `jacGal τ` is an
  isomorphism.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

section Twist

variable {S S' : Scheme.{u}} (p : S' ⟶ S) (P : (Over S)ᵒᵖ ⥤ Type u) {X : Over S'}
  (R : ((Over.map p).op ⋙ P).RepresentableBy X) {α β : S' ⟶ S'}

/-- For `α ≫ p = p`, the `S'`-schemes `(T, t ≫ α)` and `(T, t)` have the same image in `Over S`. -/
def twistIso (hα : α ≫ p = p) (T : Over S') :
    (Over.map p).obj (Over.mk (T.hom ≫ α)) ≅ (Over.map p).obj T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom ≫ p = (T.hom ≫ α) ≫ p
    rw [Category.id_comp, Category.assoc, hα])

@[simp]
lemma twistIso_hom_left (hα : α ≫ p = p) (T : Over S') :
    (twistIso p hα T).hom.left = 𝟙 T.left := rfl

/-- **The semilinear automorphism of a representing object** attached to `α : S' ⟶ S'` over `S`:
a morphism `X ⟶ X` over `α` (as a morphism `(X, X.hom ≫ α) ⟶ (X, X.hom)` in `Over S'`),
corresponding to the universal element of `P` transported along `twistIso`. -/
def twistHom (hα : α ≫ p = p) : Over.mk (X.hom ≫ α) ⟶ X :=
  R.homEquiv.symm (P.map (twistIso p hα X).hom.op (R.homEquiv (𝟙 X)))

/-- The underlying morphism of schemes `φ_α : X ⟶ X` of `twistHom`. -/
abbrev twistLeft (hα : α ≫ p = p) : X.left ⟶ X.left := (twistHom p P R hα).left

@[reassoc]
lemma twistHom_left_comp (hα : α ≫ p = p) :
    twistLeft p P R hα ≫ X.hom = X.hom ≫ α :=
  Over.w (twistHom p P R hα)

lemma twistPt_w (hα : α ≫ p = p) {T : Over S'} (x : T ⟶ X) :
    (x.left ≫ twistLeft p P R hα) ≫ X.hom = T.hom ≫ α := by
  rw [Category.assoc, twistHom_left_comp, ← Category.assoc, Over.w x]

/-- The point `x ≫ φ_α` of `X` over `t ≫ α`, for a point `x` of `X` over `t`. -/
def twistPt (hα : α ≫ p = p) {T : Over S'} (x : T ⟶ X) : Over.mk (T.hom ≫ α) ⟶ X :=
  Over.homMk (x.left ≫ twistLeft p P R hα) (twistPt_w p P R hα x)

@[simp]
lemma twistPt_left (hα : α ≫ p = p) {T : Over S'} (x : T ⟶ X) :
    (twistPt p P R hα x).left = x.left ≫ twistLeft p P R hα := rfl

omit R in
lemma map_eq_of_left_eq {Y Z : Over S} {a b : Y ⟶ Z} (h : a.left = b.left) (u : P.obj (op Z)) :
    P.map a.op u = P.map b.op u := by
  rw [Over.OverMorphism.ext h]

omit R in
lemma map_map_op {Y Z W : Over S} (a : Y ⟶ Z) (b : Z ⟶ W) (u : P.obj (op W)) :
    P.map a.op (P.map b.op u) = P.map (a ≫ b).op u := by
  rw [op_comp, Functor.map_comp_apply]

lemma homEquiv_comp_map {T T' : Over S'} (f : T ⟶ T') (g : T' ⟶ X) :
    R.homEquiv (f ≫ g) = P.map ((Over.map p).map f).op (R.homEquiv g) :=
  R.homEquiv_comp f g

lemma homEquiv_eq_map {T : Over S'} (x : T ⟶ X) :
    R.homEquiv x = P.map ((Over.map p).map x).op (R.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.comp_id x]
  exact R.homEquiv_comp x (𝟙 X)

lemma homEquiv_twistHom (hα : α ≫ p = p) :
    R.homEquiv (twistHom p P R hα) = P.map (twistIso p hα X).hom.op (R.homEquiv (𝟙 X)) :=
  Equiv.apply_symm_apply _ _

/-- **`φ_α` on points**: the point `x ≫ φ_α` over `t ≫ α` corresponds to the same element of
`P(T)` as `x`. -/
lemma homEquiv_twistPt (hα : α ≫ p = p) {T : Over S'} (x : T ⟶ X) :
    R.homEquiv (twistPt p P R hα x) = P.map (twistIso p hα T).hom.op (R.homEquiv x) := by
  have e : twistPt p P R hα x = (Over.homMk x.left (by
      change x.left ≫ X.hom ≫ α = T.hom ≫ α
      rw [← Category.assoc, Over.w x]) :
      Over.mk (T.hom ≫ α) ⟶ Over.mk (X.hom ≫ α)) ≫ twistHom p P R hα := by
    ext
    rfl
  rw [e, homEquiv_comp_map, homEquiv_twistHom, homEquiv_eq_map p P R x, map_map_op, map_map_op]
  refine map_eq_of_left_eq P ?_ _
  rw [Over.comp_left, Over.comp_left, Over.map_map_left, Over.map_map_left, twistIso_hom_left,
    twistIso_hom_left]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma twistHom_congr {α' : S' ⟶ S'} (h : α = α') (hα : α ≫ p = p) (hα' : α' ≫ p = p) :
    twistLeft p P R hα = twistLeft p P R hα' := by
  subst h
  rfl

/-- `φ_𝟙 = 𝟙`. -/
lemma twistLeft_id : twistLeft p P R (Category.id_comp p) = 𝟙 X.left := by
  have e : twistHom p P R (Category.id_comp p) =
      (Over.homMk (𝟙 X.left) (by
        change 𝟙 X.left ≫ X.hom = X.hom ≫ 𝟙 S'
        simp) : Over.mk (X.hom ≫ 𝟙 S') ⟶ X) := by
    apply R.homEquiv.injective
    rw [homEquiv_twistHom, homEquiv_eq_map p P R (Over.homMk _ _)]
    refine map_eq_of_left_eq P ?_ _
    rw [Over.map_map_left, twistIso_hom_left]
    rfl
  change (twistHom p P R (Category.id_comp p)).left = _
  rw [e]
  rfl

/-- **The cocycle relation** `φ_α ≫ φ_β = φ_{α ≫ β}`. -/
lemma twistLeft_comp_twistLeft (hα : α ≫ p = p) (hβ : β ≫ p = p) :
    twistLeft p P R hα ≫ twistLeft p P R hβ =
      twistLeft p P R (show (α ≫ β) ≫ p = p by rw [Category.assoc, hβ, hα]) := by
  let ι : Over.mk (X.hom ≫ α ≫ β) ⟶ Over.mk ((Over.mk (X.hom ≫ α)).hom ≫ β) :=
    Over.homMk (𝟙 X.left) (by
      change 𝟙 X.left ≫ (X.hom ≫ α) ≫ β = X.hom ≫ α ≫ β
      simp)
  have e : ι ≫ twistPt p P R hβ (twistHom p P R hα) =
      twistHom p P R (show (α ≫ β) ≫ p = p by rw [Category.assoc, hβ, hα]) := by
    apply R.homEquiv.injective
    rw [homEquiv_comp_map, homEquiv_twistPt, homEquiv_twistHom, homEquiv_twistHom, map_map_op,
      map_map_op]
    refine map_eq_of_left_eq P ?_ _
    rw [Over.comp_left, Over.comp_left, Over.map_map_left, twistIso_hom_left, twistIso_hom_left,
      twistIso_hom_left]
    exact (Category.comp_id _).trans (Category.comp_id (𝟙 X.left))
  calc twistLeft p P R hα ≫ twistLeft p P R hβ =
      (ι ≫ twistPt p P R hβ (twistHom p P R hα)).left := (Category.id_comp _).symm
    _ = _ := congrArg CommaMorphism.left e

end Twist

section BcMap

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Composition of two pullbacks along `bcMap`. -/
lemma map_bcMap_map_bcMap {T₀ T T' : Scheme.{u}} (a : T' ⟶ T) (b : T ⟶ T₀) (g₀ : T₀ ⟶ S)
    (g : T ⟶ S) (g' : T' ⟶ S) (w₁ : b ≫ g₀ = g) (w₂ : a ≫ g = g') (c : T' ⟶ T₀)
    (hc : a ≫ b = c) (w₃ : c ≫ g₀ = g') (v : (pullback f g₀).Pic) :
    Scheme.Pic.map (bcMap f a g g' w₂) (Scheme.Pic.map (bcMap f b g₀ g w₁) v) =
      Scheme.Pic.map (bcMap f c g₀ g' w₃) v := by
  subst hc
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← bcMap_comp]

end BcMap

section Jacobian

open Belyi

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [PerfectField Ω] [IsSepClosed Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "sA" => specAlgebraMap (k₀ := k) Ω

/-- The Jacobian `J_Ω` of `C_Ω`, an abelian variety over `Ω`. -/
abbrev jacobianBC : Over SΩ :=
  Jacobian (pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) Ω))
    (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)

/-- The functor `Pic⁰_{C/k,σ}` (as a presheaf of sets on `(Sch/k)`). -/
abbrev picZeroSet : (Over Sk)ᵒᵖ ⥤ Type u :=
  picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat

omit [PerfectField k] [PerfectField Ω] [IsSepClosed Ω] in
lemma specAut_mul (τ₁ τ₂ : Ω ≃ₐ[k] Ω) : specAut τ₁ ≫ specAut τ₂ = specAut (τ₁ * τ₂) := by
  rw [← Spec.map_comp]
  rfl

omit [PerfectField k] [PerfectField Ω] [IsSepClosed Ω] in
lemma specAut_one : specAut (1 : Ω ≃ₐ[k] Ω) = 𝟙 SΩ := by
  rw [← Spec.map_id]
  rfl

variable {Ω}

/-- **The Galois action on the Jacobian** `J_Ω` of `C_Ω`: for `τ ∈ Aut(Ω/k)`, the automorphism of
the scheme `J_Ω` lying over `Spec(τ)`, induced (Yoneda) by the identity of `Pic⁰_{C/k,σ}(T)` for
`T` over `Ω` (`jacobianBCRepresentableBy`). -/
def jacGal (τ : Ω ≃ₐ[k] Ω) : (jacobianBC C σ hσ Ω).left ⟶ (jacobianBC C σ hσ Ω).left :=
  twistLeft sA (picZeroSet C σ hσ) (jacobianBCRepresentableBy C σ hσ Ω)
    (specAut_comp_specAlgebraMap (k := k) τ)

/-- `jacGal τ` lies over `Spec(τ)`. -/
@[reassoc]
lemma jacGal_comp_hom (τ : Ω ≃ₐ[k] Ω) :
    jacGal C σ hσ τ ≫ (jacobianBC C σ hσ Ω).hom = (jacobianBC C σ hσ Ω).hom ≫ specAut τ :=
  twistHom_left_comp _ _ _ _

lemma jacGal_one : jacGal C σ hσ (1 : Ω ≃ₐ[k] Ω) = 𝟙 _ :=
  (twistHom_congr _ _ _ (specAut_one Ω) _ (Category.id_comp _)).trans (twistLeft_id _ _ _)

/-- **`τ ↦ jacGal τ` is an action**: `jacGal τ₁ ≫ jacGal τ₂ = jacGal (τ₁ * τ₂)`. -/
lemma jacGal_mul (τ₁ τ₂ : Ω ≃ₐ[k] Ω) :
    jacGal C σ hσ τ₁ ≫ jacGal C σ hσ τ₂ = jacGal C σ hσ (τ₁ * τ₂) :=
  (twistLeft_comp_twistLeft _ _ _ _ _).trans (twistHom_congr _ _ _ (specAut_mul Ω τ₁ τ₂) _ _)

instance (τ : Ω ≃ₐ[k] Ω) : IsIso (jacGal C σ hσ τ) :=
  ⟨⟨jacGal C σ hσ τ⁻¹, by rw [jacGal_mul, mul_inv_cancel, jacGal_one],
    by rw [jacGal_mul, inv_mul_cancel, jacGal_one]⟩⟩

omit [PerfectField k] [PerfectField Ω] [IsSepClosed Ω] in
lemma specAut_symm_comp (τ : Ω ≃ₐ[k] Ω) : specAut τ.symm ≫ specAut τ = 𝟙 SΩ := by
  rw [specAut_mul, ← AlgEquiv.aut_inv, inv_mul_cancel, specAut_one]

/-- The morphism `Spec(τ⁻¹) : (Spec Ω, 𝟙) ⟶ (Spec Ω, Spec(τ))` in `Over (Spec Ω)`. -/
def specAutOver (τ : Ω ≃ₐ[k] Ω) :
    Over.mk (𝟙 SΩ) ⟶ Over.mk ((Over.mk (𝟙 SΩ)).hom ≫ specAut τ) :=
  Over.homMk (specAut τ.symm) (by
    change specAut τ.symm ≫ 𝟙 SΩ ≫ specAut τ = 𝟙 SΩ
    rw [Category.id_comp, specAut_symm_comp])

/-- The point `Spec(τ⁻¹) ≫ x ≫ jacGal τ` of `J_Ω` over `Ω`, for an `Ω`-point `x`. -/
def jacGalPt (τ : Ω ≃ₐ[k] Ω) (x : Over.mk (𝟙 SΩ) ⟶ jacobianBC C σ hσ Ω) :
    Over.mk (𝟙 SΩ) ⟶ jacobianBC C σ hσ Ω :=
  specAutOver τ ≫ twistPt sA (picZeroSet C σ hσ) (jacobianBCRepresentableBy C σ hσ Ω)
    (specAut_comp_specAlgebraMap (k := k) τ) x

lemma jacGalPt_left (τ : Ω ≃ₐ[k] Ω) (x : Over.mk (𝟙 SΩ) ⟶ jacobianBC C σ hσ Ω) :
    (jacGalPt C σ hσ τ x).left = specAut τ.symm ≫ x.left ≫ jacGal C σ hσ τ := rfl

variable (Ω) in
/-- The comparison `Pic⁰_{C/k,σ}(Spec Ω, 𝟙 ≫ ι) ≃ J(Ω) = Pic⁰_{C/k,σ}(Spec Ω, ι)`. -/
def picZeroIdComp : picZeroGrp (curveToP1 k C) σ hσ (𝟙 SΩ ≫ sA) ≃+ jacPoints C σ hσ Ω where
  toFun := picZeroMap C σ hσ (curveToP1 k C)
    (Over.homMk (𝟙 SΩ) (by change 𝟙 SΩ ≫ 𝟙 SΩ ≫ sA = sA; simp) :
      Over.mk sA ⟶ Over.mk (𝟙 SΩ ≫ sA))
  invFun := picZeroMap C σ hσ (curveToP1 k C)
    (Over.homMk (𝟙 SΩ) (by change 𝟙 SΩ ≫ sA = 𝟙 SΩ ≫ sA; rfl) :
      Over.mk (𝟙 SΩ ≫ sA) ⟶ Over.mk sA)
  left_inv y := Subtype.ext (Subtype.ext ((map_bcMap_map_bcMap (C ↘ Sk) (𝟙 SΩ) (𝟙 SΩ)
    (𝟙 SΩ ≫ sA) sA (𝟙 SΩ ≫ sA) (Category.id_comp _) (Category.id_comp _) (𝟙 SΩ)
    (Category.id_comp _) (Category.id_comp _) y.1.1).trans (by
      rw [bcMap_id', Scheme.Pic.map_id, AddMonoidHom.id_apply])))
  right_inv y := Subtype.ext (Subtype.ext ((map_bcMap_map_bcMap (C ↘ Sk) (𝟙 SΩ) (𝟙 SΩ)
    sA (𝟙 SΩ ≫ sA) sA (Category.id_comp _) (Category.id_comp _) (𝟙 SΩ)
    (Category.id_comp _) (Category.id_comp _) y.1.1).trans (by
      rw [bcMap_id', Scheme.Pic.map_id, AddMonoidHom.id_apply])))
  map_add' := map_add _

variable (Ω) in
/-- **The `Ω`-points of `J_Ω` are `J(Ω) = Pic⁰_{C/k,σ}(Ω)`** (via `jacobianBCRepresentableBy`). -/
def jacPtEquivBC : (Over.mk (𝟙 SΩ) ⟶ jacobianBC C σ hσ Ω) ≃ jacPoints C σ hσ Ω :=
  (jacobianBCRepresentableBy C σ hσ Ω).homEquiv.trans (picZeroIdComp C σ hσ Ω).toEquiv

/-- **The Galois action on points**: under `J_Ω(Ω) ≃ J(Ω)`, the point `Spec(τ⁻¹) ≫ x ≫ jacGal τ`
corresponds to `τ⁻¹` acting on `J(Ω) ⊆ Pic_{C/k,σ}(Ω)` (`picGal`). -/
lemma jacPtEquivBC_jacGalPt (τ : Ω ≃ₐ[k] Ω) (x : Over.mk (𝟙 SΩ) ⟶ jacobianBC C σ hσ Ω) :
    ((jacPtEquivBC C σ hσ Ω (jacGalPt C σ hσ τ x) : picPt C σ hσ Ω)) =
      picGal C σ hσ τ.symm (jacPtEquivBC C σ hσ Ω x) := by
  have h1 : (jacobianBCRepresentableBy C σ hσ Ω).homEquiv (jacGalPt C σ hσ τ x) =
      (picZeroSet C σ hσ).map (((Over.map sA).map (specAutOver τ)) ≫ (twistIso sA
        (specAut_comp_specAlgebraMap (k := k) τ) (Over.mk (𝟙 SΩ))).hom).op
        ((jacobianBCRepresentableBy C σ hσ Ω).homEquiv x) := by
    rw [jacGalPt, homEquiv_comp_map, homEquiv_twistPt, map_map_op]
    rfl
  apply Subtype.ext
  change Scheme.Pic.map (bcMap (C ↘ Sk) (𝟙 SΩ) (𝟙 SΩ ≫ sA) sA (Category.id_comp _))
      ((jacobianBCRepresentableBy C σ hσ Ω).homEquiv (jacGalPt C σ hσ τ x)).1.1 = _
  rw [h1]
  refine (map_bcMap_map_bcMap _ _ _ _ _ _ _ _ (specAut τ.symm) ?_ ?_ _).trans
    (map_bcMap_map_bcMap _ _ _ _ _ _ _ _ (specAut τ.symm) ?_ ?_ _).symm
  · change 𝟙 SΩ ≫ (specAut τ.symm ≫ 𝟙 SΩ) ≫ 𝟙 SΩ = specAut τ.symm
    simp
  · change specAut τ.symm ≫ 𝟙 SΩ ≫ sA = sA
    rw [Category.id_comp, specAut_comp_specAlgebraMap]
  · exact Category.comp_id _
  · exact specAut_comp_specAlgebraMap _

end Jacobian

end CurvesJacobian
