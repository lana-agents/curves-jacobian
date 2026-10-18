/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OverSigmaRep
import CurvesJacobian.Picard.PicDegreeAdd
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The Picard scheme and `Pic⁰` as commutative group schemes (JAC6)

Let `k` be a separably closed perfect field and `C` a curve over `k` with a rational point `σ`.
By `isRepresentable_picSigmaSch`, the rigidified Picard functor `Pic_{C/k,σ}` (viewed on all
schemes) is representable. This file turns the representing scheme into

* `CurvesJacobian.picScheme C σ hσ : Over (Spec k)`, representing the presheaf of abelian groups
  `picSigma` on `(Sch/k)` (`picSchemeRepresentableBy`), hence a **commutative group object** in
  schemes over `k` (`GrpObj`, `IsCommMonObj` instances, via `GrpObj.ofRepresentableBy`), with
  `Hom_k(-, Pic) ≅ Pic_{C/k,σ}` as presheaves of groups (`yonedaPicSchemeIso`);
* `CurvesJacobian.picZeroScheme C σ hσ π`: the open subscheme `Pic⁰ ⊆ Pic` of points of degree
  `0` (Stacks, Lemma 44.6.7, Tag 0BA0: `Pic⁰` is open and closed, by the degree decomposition
  `exists_degree_decomposition`), representing the subgroup functor `picZero` (degree is additive,
  `picDeg_add`, `picDeg_neg`), hence also a **commutative group scheme over `k`**, with the open
  immersion `picZeroι : Pic⁰ ⟶ Pic` over `k`.

Group objects are multiplicative in Mathlib, so the presheaves of additive groups are composed
with `AddCommGrpCat.toCommGrp`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Belyi Cech

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

section Pic

/-- A scheme representing `Pic_{C/k,σ}` on all schemes. -/
def picSchX : Scheme.{u} :=
  (isRepresentable_picSigmaSch C σ hσ).has_representation.choose

/-- The representation of `Pic_{C/k,σ}` (on all schemes) by `picSchX`. -/
def picSchRepr : (sigmaG G).RepresentableBy (picSchX C σ hσ) :=
  (isRepresentable_picSigmaSch C σ hσ).has_representation.choose_spec.some

/-- **The Picard scheme** `Pic_{C/k,σ}`, as a scheme over `k`. -/
abbrev picScheme : Over Sk := OverSigmaRep.over (picSchRepr C σ hσ)

/-- `picScheme` represents the Picard functor on `(Sch/k)`. -/
def picSchemeRepresentableBy : (G ⋙ forget AddCommGrpCat).RepresentableBy (picScheme C σ hσ) :=
  OverSigmaRep.representableBy (picSchRepr C σ hσ)

/-- The Picard functor as a presheaf of (multiplicatively written) commutative groups. -/
abbrev picSigmaMul : (Over Sk)ᵒᵖ ⥤ CommGrpCat.{u} := G ⋙ AddCommGrpCat.toCommGrp

/-- `picScheme` represents `picSigmaMul`. -/
def picSchemeRepresentableByMul :
    (picSigmaMul C σ hσ ⋙ forget CommGrpCat).RepresentableBy (picScheme C σ hσ) where
  homEquiv := (picSchemeRepresentableBy C σ hσ).homEquiv
  homEquiv_comp f g := (picSchemeRepresentableBy C σ hσ).homEquiv_comp f g

/-- **The Picard scheme is a group scheme over `k`** (JAC6). -/
instance : GrpObj (picScheme C σ hσ) :=
  GrpObj.ofRepresentableBy _ (picSigmaMul C σ hσ ⋙ forget₂ CommGrpCat GrpCat)
    (picSchemeRepresentableByMul C σ hσ)

/-- **The Picard scheme is commutative.** -/
instance : IsCommMonObj (picScheme C σ hσ) :=
  IsCommMonObj.ofRepresentableBy _ (picSigmaMul C σ hσ ⋙ forget₂ CommGrpCat CommMonCat)
    (picSchemeRepresentableByMul C σ hσ)

/-- **`Hom_k(-, Pic_{C/k,σ}) ≅ Pic_{C/k,σ}` as presheaves of groups**: the group structure of the
Picard scheme induces the group structure of the Picard functor. -/
def yonedaPicSchemeIso :
    yonedaGrpObj (picScheme C σ hσ) ≅ picSigmaMul C σ hσ ⋙ forget₂ CommGrpCat GrpCat :=
  yonedaGrpObjIsoOfRepresentableBy (picScheme C σ hσ)
    (picSigmaMul C σ hσ ⋙ forget₂ CommGrpCat GrpCat) (picSchemeRepresentableByMul C σ hσ)

end Pic

section PicZero

variable (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]

omit [IsSepClosed k] [IsFinite π] in
/-- `Pic^d` is stable under pullback along morphisms over `k`. -/
lemma picDeg_map_over (d : ℤ) {T T' : Over Sk} (a : T' ⟶ T) (y : (G).obj (op T))
    (hy : picDeg σ hσ π d T.left ⟨T.hom, y⟩) :
    picDeg σ hσ π d T'.left ⟨T'.hom, ((G).map a.op).hom y⟩ := by
  have e : (⟨T'.hom, ((G).map a.op).hom y⟩ : (sigmaG G).obj (op T'.left)) =
      (sigmaG G).map a.left.op ⟨T.hom, y⟩ :=
    overSigma_mk_map (G ⋙ forget AddCommGrpCat) a y
  intro T'' _ hF h
  rw [e, map_map_sigmaG]
  exact hy T'' hF _

/-- The restriction of `(G).map a` to `Pic⁰`. -/
def picZeroMap {T T' : Over Sk} (a : T' ⟶ T) :
    picZeroGrp π σ hσ T.hom →+ picZeroGrp π σ hσ T'.hom :=
  ((((G).map a.op).hom.comp (picZeroGrp π σ hσ T.hom).subtype).codRestrict
    (picZeroGrp π σ hσ T'.hom)) fun y ↦ picDeg_map_over C σ hσ π 0 a y.1 y.2

/-- **The functor `Pic⁰_{C/k,σ}`** on `(Sch/k)`, as a presheaf of abelian groups. -/
def picZero : (Over Sk)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (picZeroGrp π σ hσ T.unop.hom)
  map a := AddCommGrpCat.ofHom (picZeroMap C σ hσ π a.unop)
  map_id T := by
    ext y
    change (((G).map (𝟙 T)).hom y.1).1 = y.1.1
    rw [(G).map_id]
    rfl
  map_comp a b := by
    ext y
    change (((G).map (a ≫ b)).hom y.1).1 = (((G).map b).hom (((G).map a).hom y.1)).1
    rw [(G).map_comp]
    rfl

/-- The universal point of `Pic_{C/k,σ}` over `picSchX`. -/
abbrev picUniv : (sigmaG G).obj (op (picSchX C σ hσ)) :=
  ⟨OverSigmaRep.base (picSchRepr C σ hσ), OverSigmaRep.univ (picSchRepr C σ hσ)⟩

/-- The open subschemes `Pic^d ⊆ Pic` (Stacks, Lemma 44.6.7, Tag 0BA0). -/
def picDegOpens : ℤ → (picSchX C σ hσ).Opens :=
  (exists_degree_decomposition σ hσ π (isSheaf_picSigmaSch_curve k C σ hσ)
    (picUniv C σ hσ)).choose

lemma picDegOpens_spec (d : ℤ) (T' : Scheme.{u}) (h : T' ⟶ picSchX C σ hσ) :
    picDeg σ hσ π d T' ((sigmaG G).map h.op (picUniv C σ hσ)) ↔
      Set.range h ⊆ picDegOpens C σ hσ π d :=
  (exists_degree_decomposition σ hσ π (isSheaf_picSigmaSch_curve k C σ hσ)
    (picUniv C σ hσ)).choose_spec.1 d T' h

/-- **`Pic^d_{C/k,σ}` are pairwise disjoint opens covering `Pic_{C/k,σ}`** (Stacks, Lemma 44.6.7,
Tag 0BA0, first step). -/
lemma picDegOpens_disjoint_iSup :
    Pairwise (fun d e ↦ Disjoint (picDegOpens C σ hσ π d) (picDegOpens C σ hσ π e)) ∧
      ⨆ d, picDegOpens C σ hσ π d = ⊤ :=
  (exists_degree_decomposition σ hσ π (isSheaf_picSigmaSch_curve k C σ hσ)
    (picUniv C σ hσ)).choose_spec.2

/-- **The scheme `Pic⁰_{C/k,σ}`** over `k`: the open subscheme of degree `0` points. -/
abbrev picZeroScheme : Over Sk where
  left := (picDegOpens C σ hσ π 0).toScheme
  right := ⟨⟨⟩⟩
  hom := (picDegOpens C σ hσ π 0).ι ≫ OverSigmaRep.base (picSchRepr C σ hσ)

/-- The open immersion `Pic⁰ ⟶ Pic` over `k`. -/
def picZeroι : picZeroScheme C σ hσ π ⟶ picScheme C σ hσ :=
  Over.homMk (picDegOpens C σ hσ π 0).ι rfl

instance : IsOpenImmersion (picZeroι C σ hσ π).left :=
  inferInstanceAs (IsOpenImmersion (picDegOpens C σ hσ π 0).ι)

lemma picDeg_iff_range {Y : Over Sk} (b : Y ⟶ picScheme C σ hσ) :
    picDeg σ hσ π 0 Y.left ⟨Y.hom,
      ((picSchemeRepresentableBy C σ hσ).homEquiv b : ((G) ⋙ forget AddCommGrpCat).obj (op Y))⟩ ↔
      Set.range (b.left : Y.left ⟶ picSchX C σ hσ) ⊆
        (picDegOpens C σ hσ π 0 : Set (picSchX C σ hσ)) := by
  exact (congrArg (picDeg σ hσ π 0 Y.left)
    (OverSigmaRep.mk_representableBy_homEquiv (picSchRepr C σ hσ) b)).to_iff.trans
      (picDegOpens_spec C σ hσ π 0 Y.left b.left)

lemma range_comp_ι_subset {Y : Scheme.{u}} (b : Y ⟶ (picDegOpens C σ hσ π 0).toScheme) :
    Set.range (b ≫ (picDegOpens C σ hσ π 0).ι) ⊆
      (picDegOpens C σ hσ π 0 : Set (picSchX C σ hσ)) := by
  rw [← Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  exact ⟨b y, (Scheme.Hom.comp_apply b _ y).symm⟩

/-- A point of `Pic⁰` as a point of `Pic`. -/
def picZeroVal {Y : Over Sk} (z : picZeroGrp π σ hσ Y.hom) :
    ((G) ⋙ forget AddCommGrpCat).obj (op Y) :=
  z.1

/-- The point of `Pic⁰` attached to a morphism to `picZeroScheme`. -/
def picZeroHomEquivFun {Y : Over Sk} (b : Y ⟶ picZeroScheme C σ hσ π) :
    picZeroGrp π σ hσ Y.hom :=
  ⟨(picSchemeRepresentableBy C σ hσ).homEquiv (b ≫ picZeroι C σ hσ π),
    (picDeg_iff_range C σ hσ π _).mpr (range_comp_ι_subset C σ hσ π
      (b.left : Y.left ⟶ (picDegOpens C σ hσ π 0).toScheme))⟩

lemma range_homEquiv_symm_subset {Y : Over Sk} (z : picZeroGrp π σ hσ Y.hom) :
    Set.range (((picSchemeRepresentableBy C σ hσ).homEquiv.symm (picZeroVal C σ hσ π z)).left :
      Y.left ⟶ picSchX C σ hσ) ⊆ Set.range (picDegOpens C σ hσ π 0).ι := by
  have h := (picDeg_iff_range C σ hσ π
    ((picSchemeRepresentableBy C σ hσ).homEquiv.symm (picZeroVal C σ hσ π z))).mp
    (by rw [Equiv.apply_symm_apply]; exact z.2)
  simpa only [Scheme.Opens.range_ι] using h

/-- The morphism to `picZeroScheme` attached to a point of `Pic⁰`. -/
def picZeroHomEquivInv {Y : Over Sk} (z : picZeroGrp π σ hσ Y.hom) :
    Y ⟶ picZeroScheme C σ hσ π :=
  Over.homMk (IsOpenImmersion.lift (picDegOpens C σ hσ π 0).ι
    (((picSchemeRepresentableBy C σ hσ).homEquiv.symm (picZeroVal C σ hσ π z)).left :
      Y.left ⟶ picSchX C σ hσ)
    (range_homEquiv_symm_subset C σ hσ π z)) (by
      change _ ≫ (picDegOpens C σ hσ π 0).ι ≫ OverSigmaRep.base (picSchRepr C σ hσ) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac (picDegOpens C σ hσ π 0).ι]
      exact Over.w ((picSchemeRepresentableBy C σ hσ).homEquiv.symm (picZeroVal C σ hσ π z)))

lemma picZeroHomEquivInv_comp_ι {Y : Over Sk} (z : picZeroGrp π σ hσ Y.hom) :
    picZeroHomEquivInv C σ hσ π z ≫ picZeroι C σ hσ π =
      (picSchemeRepresentableBy C σ hσ).homEquiv.symm (picZeroVal C σ hσ π z) :=
  Over.OverMorphism.ext (by
    simp only [picZeroHomEquivInv, picZeroι, Over.comp_left, Over.homMk_left]
    exact IsOpenImmersion.lift_fac _ _ _)

/-- **`Pic⁰_{C/k,σ}` is represented by the open subscheme `picZeroScheme`.** -/
def picZeroRepresentableBy :
    (picZero C σ hσ π ⋙ forget AddCommGrpCat).RepresentableBy (picZeroScheme C σ hσ π) where
  homEquiv {Y} :=
    { toFun := picZeroHomEquivFun C σ hσ π
      invFun := picZeroHomEquivInv C σ hσ π
      left_inv b := by
        have h := (picZeroHomEquivInv_comp_ι C σ hσ π (picZeroHomEquivFun C σ hσ π b)).trans
          ((picSchemeRepresentableBy C σ hσ).homEquiv.symm_apply_apply (b ≫ picZeroι C σ hσ π))
        apply Over.OverMorphism.ext
        exact (cancel_mono (picDegOpens C σ hσ π 0).ι).mp (congrArg CommaMorphism.left h)
      right_inv z := by
        apply Subtype.ext
        change (picSchemeRepresentableBy C σ hσ).homEquiv
          (picZeroHomEquivInv C σ hσ π z ≫ picZeroι C σ hσ π) = z.1
        rw [picZeroHomEquivInv_comp_ι, Equiv.apply_symm_apply]
        rfl }
  homEquiv_comp f b := by
    apply Subtype.ext
    change (picSchemeRepresentableBy C σ hσ).homEquiv ((f ≫ b) ≫ picZeroι C σ hσ π) =
      ((G).map f.op).hom ((picSchemeRepresentableBy C σ hσ).homEquiv (b ≫ picZeroι C σ hσ π))
    rw [Category.assoc]
    exact (picSchemeRepresentableBy C σ hσ).homEquiv_comp f _

/-- `Pic⁰` as a presheaf of (multiplicatively written) commutative groups. -/
abbrev picZeroMul : (Over Sk)ᵒᵖ ⥤ CommGrpCat.{u} := picZero C σ hσ π ⋙ AddCommGrpCat.toCommGrp

/-- `picZeroScheme` represents `picZeroMul`. -/
def picZeroRepresentableByMul :
    (picZeroMul C σ hσ π ⋙ forget CommGrpCat).RepresentableBy (picZeroScheme C σ hσ π) where
  homEquiv := (picZeroRepresentableBy C σ hσ π).homEquiv
  homEquiv_comp f g := (picZeroRepresentableBy C σ hσ π).homEquiv_comp f g

/-- **`Pic⁰_{C/k,σ}` is a commutative group scheme over `k`** (JAC6; Stacks, Lemma 44.6.7,
Tag 0BA0). -/
instance : GrpObj (picZeroScheme C σ hσ π) :=
  GrpObj.ofRepresentableBy _ (picZeroMul C σ hσ π ⋙ forget₂ CommGrpCat GrpCat)
    (picZeroRepresentableByMul C σ hσ π)

/-- `Pic⁰_{C/k,σ}` is commutative. -/
instance : IsCommMonObj (picZeroScheme C σ hσ π) :=
  IsCommMonObj.ofRepresentableBy _ (picZeroMul C σ hσ π ⋙ forget₂ CommGrpCat CommMonCat)
    (picZeroRepresentableByMul C σ hσ π)

/-- `Hom_k(-, Pic⁰) ≅ Pic⁰_{C/k,σ}` as presheaves of groups. -/
def yonedaPicZeroSchemeIso :
    yonedaGrpObj (picZeroScheme C σ hσ π) ≅ picZeroMul C σ hσ π ⋙ forget₂ CommGrpCat GrpCat :=
  yonedaGrpObjIsoOfRepresentableBy (picZeroScheme C σ hσ π)
    (picZeroMul C σ hσ π ⋙ forget₂ CommGrpCat GrpCat) (picZeroRepresentableByMul C σ hσ π)

end PicZero

end CurvesJacobian
