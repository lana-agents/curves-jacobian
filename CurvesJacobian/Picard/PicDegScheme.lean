/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicScheme

/-!
# The schemes `Pic^d_{C/k,σ}` (Stacks, Lemma 44.6.7, Tag 0BA0)

Let `k` be a separably closed perfect field, `C` a curve over `k` with a rational point `σ` and a
finite morphism `π : C → ℙ¹_k`. For `d : ℤ` let `Pic^d_{C/k,σ} ⊆ Pic_{C/k,σ}` be the subfunctor
of points whose fibres over all field-valued points have degree `d`, i.e. Euler characteristic
`d + 1 − g` (`picDeg`). We show:

* `CurvesJacobian.picDegFun d`: `Pic^d` as a presheaf of sets on `(Sch/k)`;
* **`CurvesJacobian.picDegRepresentableBy`**: `Pic^d` is represented by the open subscheme
  `picDegScheme d` of the Picard scheme (the open `picDegOpens d` of the degree decomposition),
  with the open immersion `picDegι d : Pic^d ⟶ Pic` over `k`;
* `picDegScheme 0 = picZeroScheme` (definitionally).

This is Stacks, Lemma 44.6.7 (Tag 0BA0), part: `Pic_{C/k,σ} = ∐ Pic^d` with `Pic^d` open and
closed, each `Pic^d` a scheme.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Belyi Cech

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π] (d : ℤ)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- The points of `Pic^d` over `T`. -/
abbrev PicDegPt (T : Over Sk) : Type u :=
  {y : ((G) ⋙ forget AddCommGrpCat).obj (op T) // picDeg σ hσ π d T.left ⟨T.hom, y⟩}

/-- **The functor `Pic^d_{C/k,σ}`** on `(Sch/k)`, as a presheaf of sets. -/
def picDegFun : (Over Sk)ᵒᵖ ⥤ Type u where
  obj T := PicDegPt C σ hσ π d T.unop
  map a := ↾fun y ↦ ⟨((G).map a).hom y.1, picDeg_map_over C σ hσ π d a.unop y.1 y.2⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext ?_
    change ((G).map (𝟙 T)).hom y.1 = y.1
    rw [(G).map_id]
    rfl
  map_comp a b := by
    refine ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext ?_
    change ((G).map (a ≫ b)).hom y.1 = ((G).map b).hom (((G).map a).hom y.1)
    rw [(G).map_comp]
    rfl

/-- **The scheme `Pic^d_{C/k,σ}`** over `k`: the open subscheme of degree `d` points. -/
abbrev picDegScheme : Over Sk where
  left := (picDegOpens C σ hσ π d).toScheme
  right := ⟨⟨⟩⟩
  hom := (picDegOpens C σ hσ π d).ι ≫ OverSigmaRep.base (picSchRepr C σ hσ)

example : picDegScheme C σ hσ π 0 = picZeroScheme C σ hσ π := rfl

/-- The open immersion `Pic^d ⟶ Pic` over `k`. -/
def picDegι : picDegScheme C σ hσ π d ⟶ picScheme C σ hσ :=
  Over.homMk (picDegOpens C σ hσ π d).ι rfl

instance : IsOpenImmersion (picDegι C σ hσ π d).left :=
  inferInstanceAs (IsOpenImmersion (picDegOpens C σ hσ π d).ι)

lemma picDeg_iff_range_d {Y : Over Sk} (b : Y ⟶ picScheme C σ hσ) :
    picDeg σ hσ π d Y.left ⟨Y.hom,
      ((picSchemeRepresentableBy C σ hσ).homEquiv b : ((G) ⋙ forget AddCommGrpCat).obj (op Y))⟩ ↔
      Set.range (b.left : Y.left ⟶ picSchX C σ hσ) ⊆
        (picDegOpens C σ hσ π d : Set (picSchX C σ hσ)) := by
  exact (congrArg (picDeg σ hσ π d Y.left)
    (OverSigmaRep.mk_representableBy_homEquiv (picSchRepr C σ hσ) b)).to_iff.trans
      (picDegOpens_spec C σ hσ π d Y.left b.left)

lemma range_comp_ι_subset_d {Y : Scheme.{u}} (b : Y ⟶ (picDegOpens C σ hσ π d).toScheme) :
    Set.range (b ≫ (picDegOpens C σ hσ π d).ι) ⊆
      (picDegOpens C σ hσ π d : Set (picSchX C σ hσ)) := by
  rw [← Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  exact ⟨b y, (Scheme.Hom.comp_apply b _ y).symm⟩

/-- The point of `Pic^d` attached to a morphism to `picDegScheme d`. -/
def picDegHomEquivFun {Y : Over Sk} (b : Y ⟶ picDegScheme C σ hσ π d) :
    PicDegPt C σ hσ π d Y :=
  ⟨(picSchemeRepresentableBy C σ hσ).homEquiv (b ≫ picDegι C σ hσ π d),
    (picDeg_iff_range_d C σ hσ π d _).mpr (range_comp_ι_subset_d C σ hσ π d
      (b.left : Y.left ⟶ (picDegOpens C σ hσ π d).toScheme))⟩

lemma range_homEquiv_symm_subset_d {Y : Over Sk} (z : PicDegPt C σ hσ π d Y) :
    Set.range (((picSchemeRepresentableBy C σ hσ).homEquiv.symm z.1).left :
      Y.left ⟶ picSchX C σ hσ) ⊆ Set.range (picDegOpens C σ hσ π d).ι := by
  have h := (picDeg_iff_range_d C σ hσ π d
    ((picSchemeRepresentableBy C σ hσ).homEquiv.symm z.1)).mp
    (by rw [Equiv.apply_symm_apply]; exact z.2)
  simpa only [Scheme.Opens.range_ι] using h

/-- The morphism to `picDegScheme d` attached to a point of `Pic^d`. -/
def picDegHomEquivInv {Y : Over Sk} (z : PicDegPt C σ hσ π d Y) :
    Y ⟶ picDegScheme C σ hσ π d :=
  Over.homMk (IsOpenImmersion.lift (picDegOpens C σ hσ π d).ι
    (((picSchemeRepresentableBy C σ hσ).homEquiv.symm z.1).left :
      Y.left ⟶ picSchX C σ hσ)
    (range_homEquiv_symm_subset_d C σ hσ π d z)) (by
      change _ ≫ (picDegOpens C σ hσ π d).ι ≫ OverSigmaRep.base (picSchRepr C σ hσ) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac (picDegOpens C σ hσ π d).ι]
      exact Over.w ((picSchemeRepresentableBy C σ hσ).homEquiv.symm z.1))

lemma picDegHomEquivInv_comp_ι {Y : Over Sk} (z : PicDegPt C σ hσ π d Y) :
    picDegHomEquivInv C σ hσ π d z ≫ picDegι C σ hσ π d =
      (picSchemeRepresentableBy C σ hσ).homEquiv.symm z.1 :=
  Over.OverMorphism.ext (by
    simp only [picDegHomEquivInv, picDegι, Over.comp_left, Over.homMk_left]
    exact IsOpenImmersion.lift_fac _ _ _)

/-- **`Pic^d_{C/k,σ}` is represented by the open subscheme `picDegScheme d`** of the Picard
scheme (Stacks, Lemma 44.6.7, Tag 0BA0). -/
def picDegRepresentableBy :
    (picDegFun C σ hσ π d).RepresentableBy (picDegScheme C σ hσ π d) where
  homEquiv {Y} :=
    { toFun := picDegHomEquivFun C σ hσ π d
      invFun := picDegHomEquivInv C σ hσ π d
      left_inv b := by
        have h := (picDegHomEquivInv_comp_ι C σ hσ π d (picDegHomEquivFun C σ hσ π d b)).trans
          ((picSchemeRepresentableBy C σ hσ).homEquiv.symm_apply_apply (b ≫ picDegι C σ hσ π d))
        apply Over.OverMorphism.ext
        exact (cancel_mono (picDegOpens C σ hσ π d).ι).mp (congrArg CommaMorphism.left h)
      right_inv z := by
        apply Subtype.ext
        change (picSchemeRepresentableBy C σ hσ).homEquiv
          (picDegHomEquivInv C σ hσ π d z ≫ picDegι C σ hσ π d) = z.1
        rw [picDegHomEquivInv_comp_ι, Equiv.apply_symm_apply] }
  homEquiv_comp f b := by
    apply Subtype.ext
    change (picSchemeRepresentableBy C σ hσ).homEquiv ((f ≫ b) ≫ picDegι C σ hσ π d) =
      ((G).map f.op).hom ((picSchemeRepresentableBy C σ hσ).homEquiv (b ≫ picDegι C σ hσ π d))
    rw [Category.assoc]
    exact (picSchemeRepresentableBy C σ hσ).homEquiv_comp f _

/-- `Pic^d` is a subfunctor of `Pic`: the inclusion is induced by `picDegι`. -/
lemma picDegRepresentableBy_homEquiv {Y : Over Sk} (b : Y ⟶ picDegScheme C σ hσ π d) :
    ((picDegRepresentableBy C σ hσ π d).homEquiv b).1 =
      (picSchemeRepresentableBy C σ hσ).homEquiv (b ≫ picDegι C σ hσ π d) :=
  rfl

end CurvesJacobian
