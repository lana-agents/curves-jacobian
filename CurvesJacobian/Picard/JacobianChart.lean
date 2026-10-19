/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianFinite
import CurvesJacobian.Picard.JacobianGalois

/-!
# Affine charts of a representing object of `Pic⁰` over a field extension (JAC R2)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `π = curveToP1 k C`,
`F ⊆ Pic_{C/k,σ}` the open subfunctor of Stacks, Lemma 44.6.2 (Tag 0B9V), represented by the
open `W ⊆ Hilb^g` with universal point `ξ = xiW` (Stacks, Lemma 44.6.4, Tag 0B9X). Let `E ⊇ k`
be a field and `X` an `E`-scheme representing `Pic⁰_{C/k,σ}` on `(Sch/E)` (e.g. the Jacobian of
`C_E`). For a class `c ∈ Pic_{C/k,σ}(E)` and an open `A ⊆ W` this file constructs

* `CurvesJacobian.chartTranslate R c`: the translate by `c` of the universal point of `X`, as a
  point of `Pic_{C/k,σ}` over `X` (on the `k`-level);
* `CurvesJacobian.chartOpens R c ⊆ X`: the open of points `x` with `x + c ∈ F`, and the
  morphism `chartMap R c : chartOpens R c ⟶ W` classifying `x + c`;
* **`CurvesJacobian.chartA R c A`**: the open of points `x` with `x + c ∈ F` whose classifying
  point of `W` lies in `A`, characterised by `range_subset_chartA_iff` through the predicate
  `InA A` on points of `Pic_{C/k,σ}`.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Function

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi Scheme.OpenSubfunctor

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

section W

/-- The open `W ⊆ Hilb^g` representing `F ⊆ Pic_{C/k,σ}`. -/
abbrev schW : Scheme.{u} :=
  (opensW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)).toScheme

/-- The universal point `ξ` of `F` over `W`. -/
abbrev xiWk : (sigmaG G).obj (op (schW C σ hσ)) :=
  xiW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)

/-- `(W, ξ)` represents `F` on all schemes, injectivity. -/
lemma xiWk_injective (T : Scheme.{u}) :
    Function.Injective fun a : T ⟶ schW C σ hσ ↦ (sigmaG G).map a.op (xiWk C σ hσ) :=
  injective_of_isAffine (F := sheafG G (isSheaf_picSigmaSch_curve k C σ hσ)) (xiWk C σ hσ)
    (injective_xiW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)) T

/-- `(W, ξ)` represents `F` on all schemes. -/
lemma picF_iff_exists_xiWk {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) :
    picF σ hσ (curveToP1 k C) T x ↔
      ∃ a : T ⟶ schW C σ hσ, (sigmaG G).map a.op (xiWk C σ hσ) = x :=
  iff_exists_of_isAffine (F := sheafG G (isSheaf_picSigmaSch_curve k C σ hσ)) (xiWk C σ hσ)
    (isLocalPredicate_picF σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ))
    (injective_xiW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ))
    (picF_iff_exists_xiW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)) x

/-- A point of `Pic_{C/k,σ}` **lies in `F` with classifying point in `A ⊆ W`**. -/
def InA (A : (schW C σ hσ).Opens) (T : Scheme.{u}) (z : (sigmaG G).obj (op T)) : Prop :=
  ∃ a : T ⟶ schW C σ hσ, Set.range a ⊆ A ∧ (sigmaG G).map a.op (xiWk C σ hσ) = z

lemma InA.map {A : (schW C σ hσ).Opens} {T T' : Scheme.{u}} (h : T' ⟶ T)
    {z : (sigmaG G).obj (op T)} (hz : InA C σ hσ A T z) :
    InA C σ hσ A T' ((sigmaG G).map h.op z) := by
  obtain ⟨a, ha, rfl⟩ := hz
  refine ⟨h ≫ a, ?_, by rw [map_map_sigmaG]⟩
  rintro _ ⟨t, rfl⟩
  exact ha ⟨h t, rfl⟩

/-- `InA` descends along surjective morphisms. -/
lemma InA.of_map {A : (schW C σ hσ).Opens} {T T' : Scheme.{u}} (h : T' ⟶ T)
    (hh : Function.Surjective h) {z : (sigmaG G).obj (op T)}
    (hF : picF σ hσ (curveToP1 k C) T z) (hz : InA C σ hσ A T' ((sigmaG G).map h.op z)) :
    InA C σ hσ A T z := by
  obtain ⟨a₀, ha₀⟩ := (picF_iff_exists_xiWk C σ hσ z).1 hF
  obtain ⟨a, ha, haz⟩ := hz
  have e : h ≫ a₀ = a := xiWk_injective C σ hσ T' (by
    change (sigmaG G).map (h ≫ a₀).op _ = (sigmaG G).map a.op _
    rw [haz, ← map_map_sigmaG, ha₀])
  refine ⟨a₀, ?_, ha₀⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨t', rfl⟩ := hh t
  rw [← Scheme.Hom.comp_apply, e]
  exact ha ⟨t', rfl⟩

end W

section Chart

variable {E : Type u} [Field E] [Algebra k E] {X : Over (Spec (CommRingCat.of E))}
  (R : ((Over.map (specAlgebraMap (k₀ := k) E)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat).RepresentableBy X)

/-- The universal point of `Pic⁰_{C/k,σ}` over `X`, as an element of `Pic_{C/k,σ}(X)`. -/
abbrev chartUniv : (G).obj (op (Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E))) :=
  (R.homEquiv (𝟙 X)).1

/-- The translate by `c ∈ Pic_{C/k,σ}(E)` of the universal point, as a point of `Pic_{C/k,σ}`
over `X`. -/
def chartTranslate (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (sigmaG G).obj (op X.left) :=
  ⟨X.hom ≫ specAlgebraMap (k₀ := k) E,
    ((G).map (Over.homMk X.hom rfl : Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
      Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c + chartUniv C σ hσ R⟩

lemma exists_chartOpens (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    ∃ U : X.left.Opens, ∀ (T' : Scheme.{u}) (h : T' ⟶ X.left),
      picF σ hσ (curveToP1 k C) T' ((sigmaG G).map h.op (chartTranslate C σ hσ R c)) ↔
        Set.range h ⊆ U :=
  exists_opens_of_isAffine
    (isLocalPredicate_picF σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ))
    (picF_open σ hσ (curveToP1 k C)) (chartTranslate C σ hσ R c)

/-- The open `O_c ⊆ X` of points `x` with `x + c ∈ F`. -/
def chartOpens (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) : X.left.Opens :=
  (exists_chartOpens C σ hσ R c).choose

lemma chartOpens_spec (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (T' : Scheme.{u}) (h : T' ⟶ X.left) :
    picF σ hσ (curveToP1 k C) T' ((sigmaG G).map h.op (chartTranslate C σ hσ R c)) ↔
      Set.range h ⊆ chartOpens C σ hσ R c :=
  (exists_chartOpens C σ hσ R c).choose_spec T' h

lemma exists_chartMap (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    ∃ a : (chartOpens C σ hσ R c).toScheme ⟶ schW C σ hσ,
      (sigmaG G).map a.op (xiWk C σ hσ) =
        (sigmaG G).map (chartOpens C σ hσ R c).ι.op (chartTranslate C σ hσ R c) :=
  (picF_iff_exists_xiWk C σ hσ _).1 ((chartOpens_spec C σ hσ R c _ _).2 (by
    rw [Scheme.Opens.range_ι]))

/-- The morphism `O_c ⟶ W` classifying `x + c`. -/
def chartMap (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (chartOpens C σ hσ R c).toScheme ⟶ schW C σ hσ :=
  (exists_chartMap C σ hσ R c).choose

lemma chartMap_spec (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (sigmaG G).map (chartMap C σ hσ R c).op (xiWk C σ hσ) =
      (sigmaG G).map (chartOpens C σ hσ R c).ι.op (chartTranslate C σ hσ R c) :=
  (exists_chartMap C σ hσ R c).choose_spec

/-- **The chart `V(c, A) ⊆ X`**: points `x` with `x + c ∈ F` classified by a point of `A`. -/
def chartA (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (A : (schW C σ hσ).Opens) : X.left.Opens :=
  (chartOpens C σ hσ R c).ι ''ᵁ (chartMap C σ hσ R c ⁻¹ᵁ A)

/-- **Points of the chart `V(c, A)`.** -/
theorem range_subset_chartA_iff (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (A : (schW C σ hσ).Opens) {T : Scheme.{u}} (h : T ⟶ X.left) :
    Set.range h ⊆ chartA C σ hσ R c A ↔
      InA C σ hσ A T ((sigmaG G).map h.op (chartTranslate C σ hσ R c)) := by
  have hle : chartA C σ hσ R c A ≤ chartOpens C σ hσ R c := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  constructor
  · intro hh
    have hO : Set.range h ⊆ Set.range (chartOpens C σ hσ R c).ι := by
      rw [Scheme.Opens.range_ι]
      exact hh.trans hle
    let h' := IsOpenImmersion.lift (chartOpens C σ hσ R c).ι h hO
    have hh' : h' ≫ (chartOpens C σ hσ R c).ι = h := IsOpenImmersion.lift_fac _ _ _
    refine ⟨h' ≫ chartMap C σ hσ R c, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨y, hy, hyt⟩ := hh ⟨t, rfl⟩
      have ht : h t = (chartOpens C σ hσ R c).ι (h' t) := by
        rw [← hh']
        exact Scheme.Hom.comp_apply _ _ _
      have : y = h' t := (chartOpens C σ hσ R c).ι.isOpenEmbedding.injective (hyt.trans ht)
      rw [Scheme.Hom.comp_apply, ← this]
      exact hy
    · rw [← map_map_sigmaG, chartMap_spec, map_map_sigmaG, hh']
  · rintro ⟨a, ha, haz⟩
    have hF : picF σ hσ (curveToP1 k C) T ((sigmaG G).map h.op (chartTranslate C σ hσ R c)) :=
      (picF_iff_exists_xiWk C σ hσ _).2 ⟨a, haz⟩
    have hO := (chartOpens_spec C σ hσ R c T h).1 hF
    have hO' : Set.range h ⊆ Set.range (chartOpens C σ hσ R c).ι := by
      rwa [Scheme.Opens.range_ι]
    let h' := IsOpenImmersion.lift (chartOpens C σ hσ R c).ι h hO'
    have hh' : h' ≫ (chartOpens C σ hσ R c).ι = h := IsOpenImmersion.lift_fac _ _ _
    have e : h' ≫ chartMap C σ hσ R c = a := xiWk_injective C σ hσ T (by
      change (sigmaG G).map (h' ≫ chartMap C σ hσ R c).op _ = (sigmaG G).map a.op _
      rw [haz, ← map_map_sigmaG, chartMap_spec, map_map_sigmaG, hh'])
    rintro _ ⟨t, rfl⟩
    refine ⟨h' t, ?_, ?_⟩
    swap
    · rw [← hh']
      exact (Scheme.Hom.comp_apply _ _ _).symm
    change chartMap C σ hσ R c (h' t) ∈ A
    rw [← Scheme.Hom.comp_apply, e]
    exact ha ⟨t, rfl⟩

end Chart

section Affine

variable {E : Type u} [Field E] [Algebra k E] {X : Over (Spec (CommRingCat.of E))}
  (R : ((Over.map (specAlgebraMap (k₀ := k) E)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat).RepresentableBy X)

lemma picDeg_map_sigmaG {d : ℤ} {T T' : Scheme.{u}} (h : T' ⟶ T) {x : (sigmaG G).obj (op T)}
    (hx : picDeg σ hσ (curveToP1 k C) d T x) :
    picDeg σ hσ (curveToP1 k C) d T' ((sigmaG G).map h.op x) := by
  intro T'' _ hF h'
  rw [map_map_sigmaG]
  exact hx T'' hF (h' ≫ h)

/-- The universal point of `F` has degree `g`. -/
lemma picDeg_xiWk : picDeg σ hσ (curveToP1 k C) (genusNat k C) _ (xiWk C σ hσ) := by
  have : picDeg σ hσ (curveToP1 k C) (genusNat k C) _ (xiHilb C σ hσ) := by
    change picDeg σ hσ (curveToP1 k C) (genusNat k C) _
      ((abelMap C σ hσ (genusNat k C)).app (op _) (𝟙 _))
    rw [abelMap_app]
    exact picDeg_abelClass (curveToP1 k C) σ hσ _ _ (hilbCurveEquiv k C _ _ (𝟙 _)).2.2
  exact picDeg_map_sigmaG C σ hσ _ this

omit [PerfectField k] [IsCurveOver k C] in
lemma mapG_congr_left {A B : Over Sk} {f₁ f₂ : A ⟶ B} (h : f₁.left = f₂.left)
    (y : (G).obj (op B)) : ((G).map f₁.op).hom y = ((G).map f₂.op).hom y := by
  rw [Over.OverMorphism.ext h]

omit [PerfectField k] [IsCurveOver k C] in
lemma mapG_mapG_eq {A B D : Over Sk} (f₁ : A ⟶ B) (f₂ : B ⟶ D) (f : A ⟶ D)
    (h : f₁.left ≫ f₂.left = f.left) (y : (G).obj (op D)) :
    ((G).map f₁.op).hom (((G).map f₂.op).hom y) = ((G).map f.op).hom y := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact mapG_congr_left C σ hσ h y

omit [PerfectField k] [IsCurveOver k C] in
/-- Transport of a pulled back class along an equality of structure morphisms. -/
lemma sigma_mk_homMk {T T₀ : Scheme.{u}} {g₁ g₂ : T ⟶ Sk} (e : g₁ = g₂) {g₀ : T₀ ⟶ Sk}
    (m : T ⟶ T₀) (w₁ : m ≫ g₀ = g₁) (w₂ : m ≫ g₀ = g₂) (y : (G).obj (op (Over.mk g₀))) :
    (⟨g₁, ((G).map (Over.homMk m w₁ : Over.mk g₁ ⟶ Over.mk g₀).op).hom y⟩ :
      (sigmaG G).obj (op T)) =
      ⟨g₂, ((G).map (Over.homMk m w₂ : Over.mk g₂ ⟶ Over.mk g₀).op).hom y⟩ := by
  subst e
  rfl

omit [PerfectField k] [IsCurveOver k C] in
/-- Transport of a sum of pulled back classes along an equality of structure morphisms. -/
lemma sigma_mk_homMk_add {T T₁ T₂ : Scheme.{u}} {g₁ g₂ : T ⟶ Sk} (e : g₁ = g₂)
    {g₀ : T₁ ⟶ Sk} {g₀' : T₂ ⟶ Sk} (m : T ⟶ T₁) (m' : T ⟶ T₂) (w₁ : m ≫ g₀ = g₁)
    (w₂ : m ≫ g₀ = g₂) (w₁' : m' ≫ g₀' = g₁) (w₂' : m' ≫ g₀' = g₂)
    (y : (G).obj (op (Over.mk g₀))) (y' : (G).obj (op (Over.mk g₀'))) :
    (⟨g₁, ((G).map (Over.homMk m w₁ : Over.mk g₁ ⟶ Over.mk g₀).op).hom y +
      ((G).map (Over.homMk m' w₁' : Over.mk g₁ ⟶ Over.mk g₀').op).hom y'⟩ :
      (sigmaG G).obj (op T)) =
      ⟨g₂, ((G).map (Over.homMk m w₂ : Over.mk g₂ ⟶ Over.mk g₀).op).hom y +
      ((G).map (Over.homMk m' w₂' : Over.mk g₂ ⟶ Over.mk g₀').op).hom y'⟩ := by
  subst e
  rfl

omit [PerfectField k] [IsCurveOver k C] in
/-- An equality of points of `Pic_{C/k,σ}` with pulled back components, read on a common
structure morphism `g`. -/
lemma eq_of_sigma_mk_eq {T : Scheme.{u}} {g₁ g₂ : T ⟶ Sk} {y₁ : (G).obj (op (Over.mk g₁))}
    {y₂ : (G).obj (op (Over.mk g₂))}
    (h : (⟨g₁, y₁⟩ : (sigmaG G).obj (op T)) = ⟨g₂, y₂⟩) (g : T ⟶ Sk) (e₁ : 𝟙 T ≫ g₁ = g)
    (e₂ : 𝟙 T ≫ g₂ = g) :
    ((G).map (Over.homMk (𝟙 T) e₁ : Over.mk g ⟶ Over.mk g₁).op).hom y₁ =
      ((G).map (Over.homMk (𝟙 T) e₂ : Over.mk g ⟶ Over.mk g₂).op).hom y₂ := by
  obtain ⟨rfl, hy⟩ := Sigma.mk.inj_iff.mp h
  cases eq_of_heq hy
  rfl

/-- The pullback of `chartTranslate` along `b : T ⟶ X`. -/
lemma map_chartTranslate (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    {T : Scheme.{u}} (b : T ⟶ X.left) :
    (sigmaG G).map b.op (chartTranslate C σ hσ R c) =
      ⟨b ≫ X.hom ≫ specAlgebraMap (k₀ := k) E,
        ((G).map (Over.homMk (b ≫ X.hom) (Category.assoc _ _ _) :
          Over.mk (b ≫ X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
            Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c +
        ((G).map (Over.homMk b rfl : Over.mk (b ≫ X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R)⟩ := by
  rw [chartTranslate, sigmaG_map_mk, map_add, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp]
  rfl

/-- The class attached to a morphism `b : T ⟶ X` over `t : T ⟶ Spec E` is the pullback of the
universal class. -/
lemma homEquiv_homMk_val {T : Scheme.{u}} (b : T ⟶ X.left) (t : T ⟶ Spec (CommRingCat.of E))
    (hb : b ≫ X.hom = t) (w : b ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      t ≫ specAlgebraMap (k₀ := k) E) :
    (R.homEquiv (Over.homMk b hb : Over.mk t ⟶ X)).1 =
      ((G).map (Over.homMk b w : Over.mk (t ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) := by
  rw [homEquiv_eq_map (specAlgebraMap (k₀ := k) E) (picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat) R]
  rfl

/-- **Yoneda for `X`**, read on the universal class. -/
lemma chart_hom_ext {T : Scheme.{u}} (f₁ f₂ : T ⟶ X.left) (t : T ⟶ Spec (CommRingCat.of E))
    (h₁ : f₁ ≫ X.hom = t) (h₂ : f₂ ≫ X.hom = t) (w₁ : f₁ ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      t ≫ specAlgebraMap (k₀ := k) E) (w₂ : f₂ ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      t ≫ specAlgebraMap (k₀ := k) E)
    (H : ((G).map (Over.homMk f₁ w₁ : Over.mk (t ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) =
      ((G).map (Over.homMk f₂ w₂ : Over.mk (t ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R)) :
    f₁ = f₂ := by
  have := R.homEquiv.injective (a₁ := (Over.homMk f₁ h₁ : Over.mk t ⟶ X))
    (a₂ := Over.homMk f₂ h₂) (Subtype.ext (by
      rw [homEquiv_homMk_val C σ hσ R f₁ t h₁ w₁, homEquiv_homMk_val C σ hσ R f₂ t h₂ w₂]
      exact H))
  exact congrArg CommaMorphism.left this

/-- The structure morphism of `W`, the base of `ξ`. -/
abbrev xiBase : schW C σ hσ ⟶ Sk := (xiWk C σ hσ).1

section Iso

variable (c : (picSigma (C ↘ Spec (CommRingCat.of k)) σ hσ).obj
    (op (Over.mk (specAlgebraMap (k₀ := k) E))))
  (hc : picDeg σ hσ (curveToP1 k C) (genusNat k C) (Spec (CommRingCat.of E))
    ⟨specAlgebraMap (k₀ := k) E, c⟩)

/-- The class `ξ − c` of `Pic⁰` over `W ×_k E`, classifying the inverse of `O_c ≅ W ×_k E`. -/
def chartTheta : (G).obj (op (Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
    specAlgebraMap (k₀ := k) E))) :=
  ((G).map (Over.homMk (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E))
      pullback.condition : Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
        specAlgebraMap (k₀ := k) E) ⟶ Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2 -
    ((G).map (Over.homMk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) rfl :
      Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
        specAlgebraMap (k₀ := k) E) ⟶ Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c

lemma map_fst_xiWk :
    (sigmaG G).map (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)).op (xiWk C σ hσ) =
      ⟨pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫ specAlgebraMap (k₀ := k) E,
        ((G).map (Over.homMk (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E))
          pullback.condition : Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
            specAlgebraMap (k₀ := k) E) ⟶ Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2⟩ :=
  sigma_mk_homMk C σ hσ pullback.condition _ rfl _ _

include hc in
lemma picDeg_chartTheta :
    picDeg σ hσ (curveToP1 k C) 0 _ ⟨_, chartTheta C σ hσ c⟩ := by
  have h1 := picDeg_map_sigmaG C σ hσ
    (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) (picDeg_xiWk C σ hσ)
  rw [map_fst_xiWk] at h1
  have h2 := picDeg_map_sigmaG C σ hσ
    (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) hc
  rw [sigmaG_map_mk] at h2
  have := picDeg_add (curveToP1 k C) σ hσ _ _ _ h1 (picDeg_neg (curveToP1 k C) σ hσ _ _ h2)
  exact picDeg_congr C (curveToP1 k C) σ hσ (sub_eq_add_neg _ _).symm (by ring) this

/-- The morphism `W ×_k E ⟶ X` classifying `ξ − c`. -/
def chartThetaHom : Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) ⟶ X :=
  R.homEquiv.symm (⟨chartTheta C σ hσ c, picDeg_chartTheta C σ hσ c hc⟩ :
    picZeroGrp (curveToP1 k C) σ hσ
      (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫ specAlgebraMap (k₀ := k) E))

/-- The underlying morphism of `chartThetaHom`. -/
abbrev chartThetaL : pullback (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ⟶ X.left :=
  (chartThetaHom C σ hσ R c hc).left

lemma chartThetaL_w :
    chartThetaL C σ hσ R c hc ≫ X.hom = pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) :=
  Over.w (chartThetaHom C σ hσ R c hc)

lemma chartThetaL_univ (w : chartThetaL C σ hσ R c hc ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
    pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫ specAlgebraMap (k₀ := k) E) :
    ((G).map (Over.homMk (chartThetaL C σ hσ R c hc) w :
      Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
        specAlgebraMap (k₀ := k) E) ⟶ Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom
      (chartUniv C σ hσ R) = chartTheta C σ hσ c := by
  rw [← homEquiv_homMk_val C σ hσ R _ _ (chartThetaL_w C σ hσ R c hc) w]
  have e : (Over.homMk (chartThetaL C σ hσ R c hc) (chartThetaL_w C σ hσ R c hc) :
      Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) ⟶ X) =
      chartThetaHom C σ hσ R c hc := Over.OverMorphism.ext rfl
  rw [e, chartThetaHom, Equiv.apply_symm_apply]

lemma map_chartThetaL :
    (sigmaG G).map (chartThetaL C σ hσ R c hc).op (chartTranslate C σ hσ R c) =
      (sigmaG G).map (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)).op
        (xiWk C σ hσ) := by
  have hw : chartThetaL C σ hσ R c hc ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫ specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, chartThetaL_w]
  rw [map_chartTranslate]
  refine (sigma_mk_homMk_add C σ hσ (T := pullback (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E))
    hw (chartThetaL C σ hσ R c hc ≫ X.hom) (chartThetaL C σ hσ R c hc) (Category.assoc _ _ _)
    (by rw [Category.assoc]; exact hw) rfl hw c (chartUniv C σ hσ R)).trans ?_
  rw [map_homMk_congr C σ hσ (chartThetaL_w C σ hσ R c hc) _ rfl, chartThetaL_univ, map_fst_xiWk]
  congr 1
  rw [chartTheta]
  abel

lemma range_chartThetaL :
    Set.range (chartThetaL C σ hσ R c hc) ⊆ chartOpens C σ hσ R c :=
  (chartOpens_spec C σ hσ R c _ _).1 (by
    rw [map_chartThetaL]
    exact (picF_iff_exists_xiWk C σ hσ _).2 ⟨_, rfl⟩)

/-- `W ×_k E ⟶ O_c`. -/
def chartThetaO : pullback (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ⟶
    (chartOpens C σ hσ R c).toScheme :=
  IsOpenImmersion.lift (chartOpens C σ hσ R c).ι (chartThetaL C σ hσ R c hc) (by
    rw [Scheme.Opens.range_ι]
    exact range_chartThetaL C σ hσ R c hc)

lemma chartThetaO_ι :
    chartThetaO C σ hσ R c hc ≫ (chartOpens C σ hσ R c).ι = chartThetaL C σ hσ R c hc :=
  IsOpenImmersion.lift_fac _ _ _

lemma chartMap_w : chartMap C σ hσ R c ≫ xiBase C σ hσ =
    ((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E :=
  (congrArg Sigma.fst (chartMap_spec C σ hσ R c)).trans (Category.assoc _ _ _).symm

/-- `O_c ⟶ W ×_k E`. -/
def chartPhi : (chartOpens C σ hσ R c).toScheme ⟶
    pullback (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) :=
  pullback.lift (chartMap C σ hσ R c) ((chartOpens C σ hσ R c).ι ≫ X.hom) (chartMap_w C σ hσ R c)

lemma chartThetaO_chartPhi : chartThetaO C σ hσ R c hc ≫ chartPhi C σ hσ R c = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartPhi, pullback.lift_fst, Category.id_comp]
    apply xiWk_injective C σ hσ
    change (sigmaG G).map (chartThetaO C σ hσ R c hc ≫ chartMap C σ hσ R c).op _ =
      (sigmaG G).map (pullback.fst _ _).op _
    rw [← map_map_sigmaG, chartMap_spec, map_map_sigmaG, chartThetaO_ι, map_chartThetaL]
  · rw [Category.assoc, chartPhi, pullback.lift_snd, Category.id_comp, ← Category.assoc,
      chartThetaO_ι, chartThetaL_w]

lemma chartPhi_chartThetaO : chartPhi C σ hσ R c ≫ chartThetaO C σ hσ R c hc = 𝟙 _ := by
  rw [← cancel_mono (chartOpens C σ hσ R c).ι, Category.assoc, chartThetaO_ι, Category.id_comp]
  have hs : chartPhi C σ hσ R c ≫ pullback.snd _ _ = (chartOpens C σ hσ R c).ι ≫ X.hom :=
    pullback.lift_snd _ _ _
  have hf : chartPhi C σ hσ R c ≫ pullback.fst _ _ = chartMap C σ hσ R c :=
    pullback.lift_fst _ _ _
  have wa : chartPhi C σ hσ R c ≫ pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
      specAlgebraMap (k₀ := k) E =
      ((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, hs]
  have wb : chartThetaL C σ hσ R c hc ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫ specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, chartThetaL_w]
  refine chart_hom_ext C σ hσ R _ _ ((chartOpens C σ hσ R c).ι ≫ X.hom)
    (by rw [Category.assoc, chartThetaL_w, hs]) rfl (comp_comp_eq wa wb)
    (Category.assoc _ _ _).symm ?_
  refine Eq.trans (map_homMk_map_homMk C σ hσ (T₁ := (chartOpens C σ hσ R c).toScheme)
    (T₂ := pullback (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) (T₃ := X.left)
    (chartPhi C σ hσ R c) (chartThetaL C σ hσ R c hc) wa wb _).symm ?_
  rw [chartThetaL_univ, chartTheta, map_sub]
  have e1 : ((G).map (Over.homMk (chartPhi C σ hσ R c) wa :
      Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
          specAlgebraMap (k₀ := k) E)).op).hom
      (((G).map (Over.homMk (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E))
        pullback.condition : Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
          specAlgebraMap (k₀ := k) E) ⟶ Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2) =
      ((G).map (Over.homMk (chartMap C σ hσ R c) (chartMap_w C σ hσ R c) :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact mapG_congr_left C σ hσ hf _
  have e2 : ((G).map (Over.homMk (chartPhi C σ hσ R c) wa :
      Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
          specAlgebraMap (k₀ := k) E)).op).hom
      (((G).map (Over.homMk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) rfl :
        Over.mk (pullback.snd (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E) ≫
          specAlgebraMap (k₀ := k) E) ⟶ Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c) =
      ((G).map (Over.homMk ((chartOpens C σ hσ R c).ι ≫ X.hom) rfl :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact mapG_congr_left C σ hσ hs _
  have hspec : ((G).map (Over.homMk (𝟙 _) ((Category.id_comp _).trans (chartMap_w C σ hσ R c)) :
      Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (chartMap C σ hσ R c ≫ xiBase C σ hσ)).op).hom
      (((G).map (Over.homMk (chartMap C σ hσ R c) rfl :
        Over.mk (chartMap C σ hσ R c ≫ xiBase C σ hσ) ⟶ Over.mk (xiBase C σ hσ)).op).hom
          (xiWk C σ hσ).2) =
      ((G).map (Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.assoc _ _ _).symm) :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk ((chartOpens C σ hσ R c).ι ≫ X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom
      (((G).map (Over.homMk (chartOpens C σ hσ R c).ι rfl :
        Over.mk ((chartOpens C σ hσ R c).ι ≫ X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom
        (((G).map (Over.homMk X.hom rfl : Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c + chartUniv C σ hσ R)) :=
    eq_of_sigma_mk_eq C σ hσ (chartMap_spec C σ hσ R c) _ _ _
  have e3 : ((G).map (Over.homMk (chartMap C σ hσ R c) (chartMap_w C σ hσ R c) :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2 =
      ((G).map (Over.homMk ((chartOpens C σ hσ R c).ι ≫ X.hom) rfl :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c +
      ((G).map (Over.homMk (chartOpens C σ hσ R c).ι (Category.assoc _ _ _).symm :
        Over.mk (((chartOpens C σ hσ R c).ι ≫ X.hom) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) := by
    refine Eq.trans ?_ (hspec.trans ?_)
    · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact mapG_congr_left C σ hσ (Category.id_comp _).symm _
    · rw [map_add, map_add, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 1
  rw [e1, e2, e3]
  abel

end Iso

/-- **The charts `V(c, A)` are affine** for `A ⊆ W` affine and `c` of degree `g`
(`V(c, A) ≅ A ×_k E`). -/
theorem isAffineOpen_chartA (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (hc : picDeg σ hσ (curveToP1 k C) (genusNat k C) (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, c⟩) {A : (schW C σ hσ).Opens} (hA : IsAffineOpen A) :
    IsAffineOpen (chartA C σ hσ R c A) := by
  haveI : IsIso (chartPhi C σ hσ R c) :=
    ⟨⟨chartThetaO C σ hσ R c hc, chartPhi_chartThetaO C σ hσ R c hc,
      chartThetaO_chartPhi C σ hσ R c hc⟩⟩
  haveI : IsAffineHom (specAlgebraMap (k₀ := k) E) := by
    unfold specAlgebraMap
    infer_instance
  haveI : IsAffineHom (pullback.fst (xiBase C σ hσ) (specAlgebraMap (k₀ := k) E)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have e : chartMap C σ hσ R c = chartPhi C σ hσ R c ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  have h2 : IsAffineOpen (chartMap C σ hσ R c ⁻¹ᵁ A) := by
    rw [e, Scheme.Hom.comp_preimage]
    exact (hA.preimage _).preimage_of_isIso _
  exact h2.image_of_isOpenImmersion _

end Affine

section Twist

variable {E : Type u} [Field E] [Algebra k E] {X : Over (Spec (CommRingCat.of E))}
  (R : ((Over.map (specAlgebraMap (k₀ := k) E)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat).RepresentableBy X)
  {α : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of E)}
  (hα : α ≫ specAlgebraMap (k₀ := k) E = specAlgebraMap (k₀ := k) E)

/-- The twist `φ_α : X ⟶ X` over `α` (`twistLeft`). -/
abbrev chartTwist : X.left ⟶ X.left :=
  twistLeft (X := X) (specAlgebraMap (k₀ := k) E)
    (picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat) R hα

/-- The conjugate `α^* c` of a class `c ∈ Pic_{C/k,σ}(E)` under `α : Spec E ⟶ Spec E` over `k`. -/
def conjClass (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))) :=
  ((G).map (Over.homMk α hα : Over.mk (specAlgebraMap (k₀ := k) E) ⟶
    Over.mk (specAlgebraMap (k₀ := k) E)).op).hom c

lemma picDeg_conjClass {d : ℤ} (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (hc : picDeg σ hσ (curveToP1 k C) d (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, c⟩) :
    picDeg σ hσ (curveToP1 k C) d (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, conjClass C σ hσ hα c⟩ := by
  have := picDeg_map_sigmaG C σ hσ α hc
  rwa [sigmaG_map_mk, sigma_mk_homMk C σ hσ hα α rfl hα] at this

/-- The twist `φ_α` preserves the universal class. -/
lemma twistLeft_univ (w : chartTwist (E := E) (X := X) C σ hσ R hα ≫ X.hom ≫
        specAlgebraMap (k₀ := k) E = X.hom ≫ specAlgebraMap (k₀ := k) E) :
    ((G).map (Over.homMk (chartTwist (E := E) (X := X) C σ hσ R hα) w :
        Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) =
      chartUniv C σ hσ R := by
  have w' : chartTwist (E := E) (X := X) C σ hσ R hα ≫ X.hom ≫
        specAlgebraMap (k₀ := k) E = (X.hom ≫ α) ≫ specAlgebraMap (k₀ := k) E := by
    rw [Category.assoc, hα, w]
  have h1 : ((G).map (Over.homMk (chartTwist (E := E) (X := X) C σ hσ R hα) w' :
        Over.mk ((X.hom ≫ α) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) =
      ((G).map (twistIso (specAlgebraMap (k₀ := k) E) hα X).hom.op).hom
        (chartUniv C σ hσ R) := by
    rw [← homEquiv_homMk_val C σ hσ R _ (X.hom ≫ α) (twistHom_left_comp _ _ _ hα) w']
    have e : (Over.homMk (chartTwist (E := E) (X := X) C σ hσ R hα)
          (twistHom_left_comp _ _ _ hα) : Over.mk (X.hom ≫ α) ⟶ X) =
        twistHom (specAlgebraMap (k₀ := k) E)
          (picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat) R hα :=
      Over.OverMorphism.ext rfl
    rw [e]
    exact congrArg Subtype.val (homEquiv_twistHom _ _ R hα)
  have h2 := congrArg ((G).map (Over.homMk (𝟙 _)
    ((Category.id_comp _).trans ((Category.assoc _ _ _).trans (congrArg (X.hom ≫ ·) hα))) :
    Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E) ⟶
      Over.mk ((X.hom ≫ α) ≫ specAlgebraMap (k₀ := k) E)).op).hom h1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h2
  exact (mapG_congr_left C σ hσ (Category.id_comp _).symm _).trans (h2.trans
    ((mapG_mapG_eq C σ hσ _ _ (𝟙 _) (Category.comp_id _) _).trans (by rw [op_id, (G).map_id]; rfl)))

/-- **The twist `φ_α` maps the translate by `α^* c` to the translate by `c`.** -/
theorem map_twistLeft_chartTranslate (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (sigmaG G).map (chartTwist (E := E) (X := X) C σ hσ R hα).op
        (chartTranslate C σ hσ R c) = chartTranslate C σ hσ R (conjClass C σ hσ hα c) := by
  have hw : chartTwist (E := E) (X := X) C σ hσ R hα ≫ X.hom = X.hom ≫ α :=
    twistHom_left_comp _ _ _ hα
  have e : chartTwist (E := E) (X := X) C σ hσ R hα ≫ X.hom ≫
        specAlgebraMap (k₀ := k) E = X.hom ≫ specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, hw, Category.assoc, hα]
  rw [map_chartTranslate]
  refine (sigma_mk_homMk_add C σ hσ (T := X.left) e _ _ (Category.assoc _ _ _)
    (by rw [Category.assoc]; exact e) rfl e c (chartUniv C σ hσ R)).trans ?_
  rw [twistLeft_univ]
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine congrArg (· + chartUniv C σ hσ R) ?_
  change _ = ((G).map _).hom (((G).map _).hom c)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  refine mapG_congr_left C σ hσ ?_ _
  exact hw

omit [PerfectField k] [IsCurveOver k C] in
lemma opens_eq_of_range {Y : Scheme.{u}} {U V : Y.Opens}
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ Y), Set.range f ⊆ U ↔ Set.range f ⊆ V) : U = V := by
  ext x
  have := h _ (Y.fromSpecResidueField x)
  rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff,
    Set.singleton_subset_iff] at this
  exact this

/-- **Galois compatibility of the charts**: `φ_α⁻¹ V(c, A) = V(α^* c, A)`. -/
theorem twistLeft_preimage_chartA (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (A : (schW C σ hσ).Opens) :
    chartTwist (E := E) (X := X) C σ hσ R hα ⁻¹ᵁ chartA C σ hσ R c A =
      chartA C σ hσ R (conjClass C σ hσ hα c) A := by
  refine opens_eq_of_range fun T f ↦ ?_
  have e : Set.range f ⊆ chartTwist (E := E) (X := X) C σ hσ R hα ⁻¹ᵁ chartA C σ hσ R c A ↔
      Set.range (f ≫ chartTwist (E := E) (X := X) C σ hσ R hα) ⊆
          chartA C σ hσ R c A := by
    constructor
    · rintro h _ ⟨t, rfl⟩
      exact h ⟨t, rfl⟩
    · rintro h _ ⟨t, rfl⟩
      exact h ⟨t, rfl⟩
  rw [e, range_subset_chartA_iff, range_subset_chartA_iff, ← map_map_sigmaG,
    map_twistLeft_chartTranslate]

end Twist

end CurvesJacobian
