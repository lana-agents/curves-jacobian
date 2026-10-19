/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianFinite
import CurvesJacobian.Picard.TranslateRestrict

/-!
# The Jacobian over a finite Galois extension of `k` (JAC R1)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, and `Ω ⊇ k` an algebraic
closure. By `exists_finite_hfield` there is a finite Galois subextension `L = jacField C σ hσ Ω`
of `Ω/k` over which every field valued point of `Pic_{C/k,σ}` has a translate into
`F ⊆ Pic_{C/k,σ}` by a class defined over `L`.

* `CurvesJacobian.picSigmaBC_map'`: naturality of the base change isomorphism
  `Pic_{C/k,σ}(T) ≃ Pic_{C_L/L,σ_L}(T)` (`picSigmaBC`) for arbitrary structure morphisms;
* **`CurvesJacobian.isRepresentable_jacField`**: `Pic_{C_L/L,σ_L}` is representable (Stacks,
  Lemma 44.5.1, Tag 0B9Q, via `isRepresentable_of_translate_restrict`: `F_L ⊆ Pic_{C_L/L}` is the
  preimage of `F`, represented by `W ×_k L`);
* **`CurvesJacobian.jacL`**: the Jacobian `J_L` of `C_L`, a commutative group scheme over `L`,
  and **`CurvesJacobian.jacLRepresentableBy`**: `Hom_L(T, J_L) ≃ Pic⁰_{C/k,σ}(T)` for `T` over
  `L`, i.e. `J_L` represents `(Over.map (Spec L ⟶ Spec k)).op ⋙ Pic⁰_{C/k,σ}`.
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

section BaseChange

variable (L : Type u) [Field L] [Algebra k L]

omit [PerfectField k] [IsCurveOver k C] in
/-- Naturality of `picSigmaBC` for arbitrary structure morphisms. -/
lemma picSigmaBC_map' {T T' : Scheme.{u}} (a : T' ⟶ T) (t : T ⟶ Spec (CommRingCat.of L))
    (t' : T' ⟶ Spec (CommRingCat.of L)) (w : a ≫ t = t') (g : T ⟶ Sk) (g' : T' ⟶ Sk)
    (hg : t ≫ specAlgebraMap (k₀ := k) L = g) (hg' : t' ≫ specAlgebraMap (k₀ := k) L = g')
    (w' : a ≫ g = g') (x : picSigmaGrp (C ↘ Sk) σ hσ g) :
    picSigmaMap (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
        (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L) a t t' w (picSigmaBC C σ hσ L t g hg x) =
      picSigmaBC C σ hσ L t' g' hg' (picSigmaMap (C ↘ Sk) σ hσ a g g' w' x) := by
  apply Subtype.ext
  simp only [coe_picSigmaMap, coe_picSigmaBC]
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← AddMonoidHom.comp_apply,
    ← Scheme.Pic.map_comp, bcMap_bcHom]

/-- The identification `Pic_{C_L/L,σ_L}(T, t) ≃ Pic_{C/k,σ}(T, t ≫ (Spec L ⟶ Spec k))`. -/
def picRestrictEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) :
    (picSigma (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
      (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)).obj (op (Over.mk t)) ≃+
      (G).obj (op (Over.mk (t ≫ specAlgebraMap (k₀ := k) L))) :=
  (picSigmaBC C σ hσ L t (t ≫ specAlgebraMap (k₀ := k) L) rfl).symm

omit [PerfectField k] [IsCurveOver k C] in
lemma restrictNatural_picRestrictEquiv :
    RestrictNatural (specAlgebraMap (k₀ := k) L) (G)
      (picSigma (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
        (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)) (picRestrictEquiv C σ hσ L) := by
  intro T T' a t t' w y
  apply (picSigmaBC C σ hσ L t' (t' ≫ specAlgebraMap (k₀ := k) L) rfl).injective
  change _ = picSigmaBC C σ hσ L t' _ rfl (picSigmaMap (C ↘ Sk) σ hσ a _ _ _
    ((picSigmaBC C σ hσ L t _ rfl).symm y))
  rw [← picSigmaBC_map' C σ hσ L a t t' w _ _ rfl rfl, AddEquiv.apply_symm_apply]
  exact (AddEquiv.apply_symm_apply _ _)

end BaseChange

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

/-- The **translate property** of a subextension `L` of `Ω/k`: every point of
`Pic_{C/k,σ}` over a field `K ⊇ L` has a translate by a class pulled back from
`Pic_{C/k,σ}(L)` lying in `F`. -/
def HasTranslates (L : IntermediateField k Ω) : Prop :=
  ∀ (K : CommRingCat.{u}) (_ : IsField K) (t : Spec K ⟶ Spec (CommRingCat.of L))
    (y : (G).obj (op (Over.mk (t ≫ specAlgebraMap (k₀ := k) L)))),
    ∃ c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L))),
      picF σ hσ (curveToP1 k C) (Spec K) ⟨t ≫ specAlgebraMap (k₀ := k) L,
        ((G).map (Over.homMk t rfl : Over.mk (t ≫ specAlgebraMap (k₀ := k) L) ⟶
          Over.mk (specAlgebraMap (k₀ := k) L)).op).hom c + y⟩

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
/-- **`Pic_{C_L/L,σ_L}` is representable** for every finite `L` with the translate property
(Stacks, Lemma 44.5.1, Tag 0B9Q, with the translates of `F` over `L`). -/
theorem isRepresentable_of_hasTranslates (L : IntermediateField k Ω) [PerfectField L]
    (hL : HasTranslates C σ hσ Ω L) :
    (picSigmaSch (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
      (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)).IsRepresentable := by
  set π := curveToP1 k C
  have hG := isSheaf_picSigmaSch_curve k C σ hσ
  have hΦ : RestrictNatural (specAlgebraMap (k₀ := k) L) (G)
      (picSigma (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
        (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)) (picRestrictEquiv C σ hσ L) :=
    restrictNatural_picRestrictEquiv C σ hσ L
  refine isRepresentable_of_translate_restrict hΦ hG (isLocalPredicate_picF σ hσ π hG)
    (picF_open σ hσ π) (xiW C σ hσ π hG) (injective_xiW C σ hσ π hG)
    (picF_iff_exists_xiW C σ hσ π hG) (isSheaf_picSigmaSch_curve L _ _ _) ?_
  rintro K hK ⟨t, y⟩
  let y₀ : (picSigma (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
      (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)).obj (op (Over.mk t)) := y
  obtain ⟨c, hc⟩ := hL K hK t (picRestrictEquiv C σ hσ L t y)
  let c₀ : (G).obj (op (Over.mk (𝟙 _ ≫ specAlgebraMap (k₀ := k) L))) :=
    ((G).map (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 _ ≫ specAlgebraMap (k₀ := k) L) ⟶
      Over.mk (specAlgebraMap (k₀ := k) L)).op).hom c
  refine ⟨(picRestrictEquiv C σ hσ L (𝟙 _)).symm c₀, ?_⟩
  convert hc using 2
  refine Sigma.ext rfl (heq_of_eq ?_)
  change picRestrictEquiv C σ hσ L t (restr _ _ t + y₀) = _
  rw [map_add]
  congr 1
  rw [restr]
  unfold toTop
  erw [hΦ t (𝟙 _) t (Category.comp_id t)]
  rw [AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3

/-- **The field of definition of the Jacobian**: a finite Galois subextension `L` of `Ω/k` with
the translate property (`exists_finite_hfield`). -/
def jacField : IntermediateField k Ω := (exists_finite_hfield C σ hσ Ω ⊥).choose

instance : FiniteDimensional k (jacField C σ hσ Ω) :=
  (exists_finite_hfield C σ hσ Ω ⊥).choose_spec.1

instance : IsGalois k (jacField C σ hσ Ω) :=
  (exists_finite_hfield C σ hσ Ω ⊥).choose_spec.2.1

instance : PerfectField (jacField C σ hσ Ω) := Algebra.IsAlgebraic.perfectField k

local notation "L" => jacField C σ hσ Ω

lemma hasTranslates_jacField : HasTranslates C σ hσ Ω L :=
  (exists_finite_hfield C σ hσ Ω ⊥).choose_spec.2.2.2

/-- Every finite subextension is contained in a finite Galois one with the translate property
(over which `Pic_{C_L/L,σ}` is representable, `isRepresentable_of_hasTranslates`). -/
lemma exists_hasTranslates_ge (L₂ : IntermediateField k Ω) [FiniteDimensional k L₂] :
    ∃ (L' : IntermediateField k Ω) (_ : FiniteDimensional k L') (_ : IsGalois k L')
      (_ : L₂ ≤ L'), HasTranslates C σ hσ Ω L' :=
  exists_finite_hfield C σ hσ Ω L₂

/-- **`Pic_{C_L/L,σ_L}` is representable** for `L = jacField C σ hσ Ω`. -/
instance isRepresentable_jacField :
    (picSigmaSch (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L) ↘ Spec (CommRingCat.of L))
      (sigmaExt C σ hσ L) (sigmaExt_comp C σ hσ L)).IsRepresentable :=
  isRepresentable_of_hasTranslates C σ hσ Ω L (hasTranslates_jacField C σ hσ Ω)

/-- **The Jacobian `J_L` over `L = jacField C σ hσ Ω`**: the Jacobian of `C_L`, a commutative
group scheme over `L`. -/
abbrev jacL : Over (Spec (CommRingCat.of L)) :=
  Jacobian (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) L)) (sigmaExt C σ hσ L)
    (sigmaExt_comp C σ hσ L)

/-- **`J_L` represents `Pic⁰_{C/k,σ}` on `(Sch/L)`**: `Hom_L(T, J_L) ≃ Pic⁰_{C/k,σ}(T)`, i.e.
`J_L` represents `(Over.map (Spec L ⟶ Spec k)).op ⋙ Pic⁰_{C/k,σ}` (JAC R1). -/
def jacLRepresentableBy :
    ((Over.map (specAlgebraMap (k₀ := k) L)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
      forget AddCommGrpCat).RepresentableBy (jacL C σ hσ Ω) :=
  jacobianBCRepresentableBy C σ hσ L

end CurvesJacobian
