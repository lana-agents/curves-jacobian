/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicEffective
import CurvesJacobian.Picard.PicDegreeTranslate
import CurvesJacobian.Picard.PicSeparated
import CurvesJacobian.Picard.PicLft
import CurvesJacobian.Picard.HilbAdd

/-!
# `Pic^d_{C/k,σ}` is proper (Stacks, Lemma 44.6.7, Tag 0BA0)

Let `k` be a separably closed perfect field and `C` a curve of genus `g` over `k` with a rational
point `σ` and a finite morphism `π : C → ℙ¹_k`.

* `CurvesJacobian.picDeg_abelClass`: the Abel class of a relative effective Cartier divisor of
  constant degree `e` lies in `Pic^e` (over a field point `χ(𝒪(D)) = deg D + 1 − g`,
  `chiCurve_ofDivisor`, and the rigidification is trivial since `Pic` of a field is zero).
* `CurvesJacobian.picAbelHom e N d`: for `e = d + N`, the morphism
  `Hilb^e_{C/k} ⟶ Pic^d_{C/k,σ}`, `D ↦ [𝒪(D)] − N·[𝒪(x)]` (Abel map followed by translation by
  a rational point `x`, `picDeg_translate_iff`).
* `CurvesJacobian.surjective_picAbelHom`: it is surjective for `e ≥ g`, since field valued points
  of `Pic^e` are Abel classes (`exists_abelClass_eq_of_isField`).
* **`CurvesJacobian.isProper_picDegScheme`**: `Pic^d_{C/k,σ}` is proper over `k` for every `d`:
  it is separated (`isSeparated_picDegScheme`), locally of finite type (`PicLft`), and universally
  closed as the surjective image of the universally closed `Hilb^e_{C/k}`
  (`universallyClosed_hilbCurveHom`, `UniversallyClosed.of_comp_surjective`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

/-- The Picard group of an affine scheme whose ring of global sections is a field is trivial. -/
lemma subsingleton_pic_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤)) :
    Subsingleton T.Pic := by
  letI := hF.toField
  have key : ∀ x : T.Pic,
      x = Scheme.Pic.map T.isoSpec.hom (Scheme.Pic.map T.isoSpec.inv x) := fun x ↦ by
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, Iso.hom_inv_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply]
  exact ⟨fun x y ↦ by rw [key x, key y, Subsingleton.elim (Scheme.Pic.map T.isoSpec.inv x)]⟩

section Degree

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- Over a field, the Abel class of `D` has Euler characteristic `deg D + 1 − g`. -/
theorem chiCurve_abelClass_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤))
    (g : T ⟶ Sk) (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) (t : T) :
    chiCurve π g (Scheme.Pic.rep (abelClass (C ↘ Sk) σ hσ D : (pullback (C ↘ Sk) g).Pic)) =
      D.degree t + 1 - genusNat k C := by
  haveI := subsingleton_pic_of_isField hF
  letI : T.Over Sk := ⟨g⟩
  have h : (abelClass (C ↘ Sk) σ hσ D : (pullback (C ↘ Sk) g).Pic) = D.picClass := by
    rw [coe_abelClass, Subsingleton.elim (Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) D.picClass) 0,
      map_zero, sub_zero]
  rw [h]
  exact chiCurve_ofDivisor π hF D t

/-- **The Abel class of a divisor of degree `e` lies in `Pic^e`.** -/
theorem picDeg_abelClass {T : Scheme.{u}} (g : T ⟶ Sk)
    (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) {e : ℕ} (hD : ∀ t, D.degree t = e) :
    picDeg σ hσ π e T ⟨g, abelClass (C ↘ Sk) σ hσ D⟩ := by
  intro T' _ hF h
  let P := (hilbEquivRelEffCartier e C (Over.mk g)).symm ⟨D, hD⟩
  let D' := hilbEquivRelEffCartier e C (Over.mk (h ≫ g))
    (P.pullback (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g))
  have hmap : (sigmaG G).map h.op ⟨g, abelClass (C ↘ Sk) σ hσ D⟩ =
      ⟨h ≫ g, abelClass (C ↘ Sk) σ hσ D'.1⟩ := by
    rw [sigmaG_map_mk]
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact picSigmaMap_abelClass (C ↘ Sk) σ hσ h g (h ≫ g) rfl D D'.1
      (pullback_ideal_eq_comap_bcMap (C ↘ Sk) h g (h ≫ g) rfl P)
  rw [hmap]
  obtain ⟨t⟩ := nonempty_of_isField hF
  have h2 : D'.1.degree t = e := D'.2 t
  exact (chiCurve_abelClass_of_isField π σ hσ hF (h ≫ g) D'.1 t).trans
    (congrArg (fun n : ℕ ↦ (n : ℤ) + 1 - genusNat k C) h2)

end Degree

section Proper

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

omit [IsSepClosed k] in
variable {C} in
/-- Translation by `N` times a class `c` shifts the degree by `N`. -/
lemma picDeg_translate_nsmul (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)))
    (d : ℤ) {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) :
    ∀ N : ℕ, picDeg σ hσ π (d + N) T (translate G (N • pointClass C σ hσ xC hx) x) ↔
      picDeg σ hσ π d T x
  | 0 => by
    rw [zero_smul, translate_zero, Nat.cast_zero, add_zero]
  | N + 1 => by
    rw [succ_nsmul', ← translate_translate,
      show d + ((N + 1 : ℕ) : ℤ) = (d + N) + 1 by push_cast; ring,
      picDeg_translate_iff C π σ hσ xC hx hxW]
    exact picDeg_translate_nsmul xC hx hxW d x N

variable (xC : Spec (CommRingCat.of k) ⟶ C)
  (hx : xC ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)))
  (e N : ℕ) (d : ℤ) (he : (e : ℤ) = d + N)

/-- The point `[𝒪(D)] − N·[𝒪(x)]` of `Pic` over `Hilb^e_{C/k}`, `D` the universal divisor. -/
def xiAbel : (sigmaG G).obj (op (hilbCurve k C e)) :=
  translate G (-(N • pointClass C σ hσ xC hx)) (yonedaEquiv (abelMap C σ hσ e))

omit [IsSepClosed k] in
lemma map_xiAbel {T : Scheme.{u}} (a : T ⟶ hilbCurve k C e) :
    (sigmaG G).map a.op (xiAbel C σ hσ xC hx e N) =
      translate G (-(N • pointClass C σ hσ xC hx)) ((abelMap C σ hσ e).app (op T) a) := by
  rw [xiAbel, map_translate]
  congr 1
  exact map_yonedaEquiv (F := picSigmaSch (C ↘ Sk) σ hσ) _ a

omit [IsSepClosed k] in
lemma xiAbel_fst : (xiAbel C σ hσ xC hx e N).1 = hilbCurveHom k C e := by
  have h := map_xiAbel C σ hσ xC hx e N (𝟙 _)
  rw [op_id, Functor.map_id_apply] at h
  rw [h]
  change ((abelMap C σ hσ e).app (op (hilbCurve k C e)) (𝟙 (hilbCurve k C e))).1 = _
  rw [abelMap_app, hilbCurveEquiv_fst, Category.id_comp]

omit [IsSepClosed k] in
include hxW he in
lemma picDeg_xiAbel : picDeg σ hσ π d _ (xiAbel C σ hσ xC hx e N) := by
  rw [← picDeg_translate_nsmul σ hσ π xC hx hxW d _ N, xiAbel, translate_translate_neg, ← he]
  change picDeg σ hσ π e _ ((abelMap C σ hσ e).app (op (hilbCurve k C e)) (𝟙 (hilbCurve k C e)))
  rw [abelMap_app]
  exact picDeg_abelClass π σ hσ _ _ (hilbCurveEquiv k C e _ (𝟙 _)).2.2

/-- The morphism `Hilb^e_{C/k} ⟶ Pic` of the point `xiAbel`. -/
def picAbelX : hilbCurve k C e ⟶ picSchX C σ hσ :=
  (picSchRepr C σ hσ).homEquiv.symm (xiAbel C σ hσ xC hx e N)

lemma map_picAbelX :
    (sigmaG G).map (picAbelX C σ hσ xC hx e N).op (picUniv C σ hσ) =
      xiAbel C σ hσ xC hx e N := by
  rw [← OverSigmaRep.homEquiv_eq, picAbelX, Equiv.apply_symm_apply]

include hxW he in
lemma range_picAbelX_subset :
    Set.range (picAbelX C σ hσ xC hx e N) ⊆ Set.range (picDegOpens C σ hσ π d).ι := by
  rw [Scheme.Opens.range_ι, ← picDegOpens_spec C σ hσ π d, map_picAbelX]
  exact picDeg_xiAbel C σ hσ π xC hx hxW e N d he

/-- **The morphism `Hilb^e_{C/k} ⟶ Pic^d_{C/k,σ}`** (`e = d + N`),
`D ↦ [𝒪(D)] − N·[𝒪(x)]`. -/
def picAbelHom : hilbCurve k C e ⟶ (picDegOpens C σ hσ π d).toScheme :=
  IsOpenImmersion.lift (picDegOpens C σ hσ π d).ι (picAbelX C σ hσ xC hx e N)
    (range_picAbelX_subset C σ hσ π xC hx hxW e N d he)

lemma picAbelHom_ι : picAbelHom C σ hσ π xC hx hxW e N d he ≫ (picDegOpens C σ hσ π d).ι =
    picAbelX C σ hσ xC hx e N :=
  IsOpenImmersion.lift_fac _ _ _

lemma picAbelHom_comp : picAbelHom C σ hσ π xC hx hxW e N d he ≫
    (picDegScheme C σ hσ π d).hom = hilbCurveHom k C e := by
  change picAbelHom C σ hσ π xC hx hxW e N d he ≫ (picDegOpens C σ hσ π d).ι ≫
    OverSigmaRep.base (picSchRepr C σ hσ) = _
  rw [reassoc_of% picAbelHom_ι, ← xiAbel_fst C σ hσ xC hx e N, ← map_picAbelX]
  rfl

/-- **`Hilb^e_{C/k} ⟶ Pic^d_{C/k,σ}` is surjective for `e ≥ g`.** -/
theorem surjective_picAbelHom (hg : genusNat k C ≤ e) :
    Surjective (picAbelHom C σ hσ π xC hx hxW e N d he) := by
  constructor
  intro z
  let w := (picDegOpens C σ hσ π d).ι z
  let p := (picSchX C σ hσ).fromSpecResidueField w
  let x := (sigmaG G).map p.op (picUniv C σ hσ)
  have hxd : picDeg σ hσ π d _ x := by
    refine (picDegOpens_spec C σ hσ π d _ p).mpr ?_
    rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff, ← Scheme.Opens.range_ι]
    exact ⟨z, rfl⟩
  let y := translate G (N • pointClass C σ hσ xC hx) x
  have hy : picDeg σ hσ π e _ y := by
    rw [he]
    exact (picDeg_translate_nsmul σ hσ π xC hx hxW d x N).mpr hxd
  have hF := isField_residueField w
  obtain ⟨D, hD⟩ := exists_abelClass_eq_of_isField π σ hσ hF e (by exact_mod_cast hg) y hy
  have hdeg : ∀ t, D.degree t = e := fun t ↦ by
    have h1 := hy _ hF (𝟙 _)
    rw [op_id, Functor.map_id_apply] at h1
    change chiCurve π y.1 (Scheme.Pic.rep (y.2 : picSigmaGrp (C ↘ Sk) σ hσ y.1).1) = _ at h1
    rw [← hD, chiCurve_abelClass_of_isField π σ hσ hF y.1 D t] at h1
    omega
  let a := (hilbCurveEquiv k C e _).symm ⟨y.1, D, hdeg⟩
  have ha : (sigmaG G).map a.op (xiAbel C σ hσ xC hx e N) = x := by
    rw [map_xiAbel, abelMap_app]
    have hEa : hilbCurveEquiv k C e _ a = ⟨y.1, D, hdeg⟩ := Equiv.apply_symm_apply _ _
    rw [hEa]
    have hy' : (⟨y.1, abelClass (C ↘ Sk) σ hσ D⟩ :
        Σ g : _ ⟶ Sk, (G ⋙ forget AddCommGrpCat).obj (op (Over.mk g))) = y :=
      Sigma.ext rfl (heq_of_eq hD)
    exact (congrArg (translate G (-(N • pointClass C σ hσ xC hx))) hy').trans
      (translate_neg_translate G _ x)
  have hap : a ≫ picAbelX C σ hσ xC hx e N = p := by
    apply (picSchRepr C σ hσ).homEquiv.injective
    rw [(picSchRepr C σ hσ).homEquiv_comp, OverSigmaRep.homEquiv_eq (picSchRepr C σ hσ) p]
    change (sigmaG G).map a.op ((picSchRepr C σ hσ).homEquiv
      ((picSchRepr C σ hσ).homEquiv.symm (xiAbel C σ hσ xC hx e N))) = x
    rw [Equiv.apply_symm_apply, ha]
  refine ⟨a (IsLocalRing.closedPoint _), (picDegOpens C σ hσ π d).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, picAbelHom_ι, hap,
    Scheme.fromSpecResidueField_apply]

/-- **`Pic^d_{C/k,σ}` is universally closed over `k`.** -/
theorem universallyClosed_picDegScheme (d : ℤ) :
    UniversallyClosed (picDegScheme C σ hσ π d).hom := by
  haveI : IsAlgClosed k := IsSepClosed.isAlgClosed_of_perfectField k
  obtain ⟨xC, hx, hxW⟩ := exists_point_chart_inf C π
  obtain ⟨e, N, he, hg⟩ : ∃ e N : ℕ, (e : ℤ) = d + N ∧ genusNat k C ≤ e := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact ⟨genusNat k C + m, genusNat k C, by push_cast; ring, by omega⟩
    · exact ⟨genusNat k C, genusNat k C + m, by push_cast; ring, le_rfl⟩
  haveI := surjective_picAbelHom C σ hσ π xC hx hxW e N d he hg
  haveI : UniversallyClosed (picAbelHom C σ hσ π xC hx hxW e N d he ≫
      (picDegScheme C σ hσ π d).hom) := by
    rw [picAbelHom_comp]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (picAbelHom C σ hσ π xC hx hxW e N d he) _

/-- **`Pic^d_{C/k,σ}` is proper over `k`** (Stacks, Lemma 44.6.7, Tag 0BA0). -/
instance isProper_picDegScheme (d : ℤ) : IsProper (picDegScheme C σ hσ π d).hom :=
  haveI := universallyClosed_picDegScheme C σ hσ π d
  ⟨⟩

end Proper

end CurvesJacobian
