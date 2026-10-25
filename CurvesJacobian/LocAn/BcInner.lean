/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.UniqueProper
import CurvesJacobian.LocAn.DescentBase
import CurvesJacobian.LocAn.EqOfClosedPoints
import CurvesJacobian.Cusp.PullbackCover
import CurvesJacobian.Cusp.CuspDegreeEq

/-!
# Inner automorphisms after a finite base change; closed points (MR7, S8 step R5)

Let `C = (X̄, U)` be a hyperbolic curve over a field `K` of characteristic `0`, `K'/K` finite,
`C' = C_{K'}` its base change (`Belyi.Anabelian.HypCurve.bcExt`) with the projection
`pr : U' ⟶ U` (`CurvesJacobian.LocAn.bcExtPr`, finite étale, a base change of
`Spec K' ⟶ Spec K`).

* **`CurvesJacobian.LocAn.inducedBy_bcExt`** (R5 (b)): if a `K`-automorphism `h` of `U` induces
  the identity of `π₁ᵉᵗ(U, ξ)` up to `Δ`-conjugation (`InducedBy ξ ξ h id`: a path over the base),
  then so does `h_{K'}` at every geometric point `ξ'` of `U'` over `ξ`. Proof: pick a path
  `β : fiber (ξ' ≫ h') ≅ fiber ξ'` over the base; its image `c = γ⁻¹ · pr_*(β)` in `π₁ᵉᵗ(U, ξ)`
  lies in `Δ = ker(π₁ᵉᵗ(U) → G_K)`, hence in `π₁ᵉᵗ(U')` (`im π₁ᵉᵗ(U') = π₁ᵉᵗ(U) ×_{G_K} G_{K'}`,
  `range_fundamentalGroupMap_of_isPullback`); `c = pr_*(d)` and `β · d⁻¹` works (injectivity of
  `pr_*` and of `G_{K'} → G_K`, `fundamentalGroupMap_injective_of_isFiniteEtale'`).
* `CurvesJacobian.LocAn.bcPt`: the geometric point of `U'` over a geometric point of `U`
  (`Ω` a `K'`-algebra); `bcRatPt`: the `K'`-rational point of `U'` over a `K'`-point of `U`, and
  **`comp_eq_of_bcRatPt`** (R5 (a)): if `h_{K'}` fixes it, `h` fixes the `K'`-point.
* `CurvesJacobian.LocAn.RationalPointsFixedMLF p`: the statement of step L1/L2 (helper hL): over
  every finite extension of `ℚ_p`, an automorphism of a proper hyperbolic curve inducing the
  identity up to `Δ`-conjugation fixes every rational point. A plain `Prop`, never assumed; it
  enters `innerRigidProper_padic_of_rationalPointsFixed` as the explicit hypothesis `hRat`.
* **`CurvesJacobian.LocAn.fromSpecResidueField_comp_eq_of_inducedBy`**: under `hRat`, such an
  automorphism fixes every closed point `Spec κ(x) ⟶ U` (base change to `κ(x)`, finite over `K`);
* **`CurvesJacobian.LocAn.innerRigidProper_padic_of_rationalPointsFixed`**: under `hRat`,
  `InnerRigidProper Ω C` for every proper hyperbolic curve over a finite extension of `ℚ_p`
  (R0 `inducedBy_refl_of_isConjInduced_id` + `center_Gk_padic`, R5, R6
  `eq_id_of_fromSpecResidueField_closedPoints`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian HypCurve CurvesJacobian.Cusp

noncomputable section

namespace CurvesJacobian.LocAn

/-! ### The base-changed curve -/

section BaseChange

variable {K : Type u} [Field K] [CharZero K] (K' : Type u) [Field K'] [Algebra K K']

lemma isPullback_bcExtPr (C : HypCurve K) :
    IsPullback (C.bcExt K').toSpec (bcExtPr K' C) (specAlgebraMap K K') C.toSpec :=
  IsPullback.of_iso_pullback ⟨(bcExtPr_toSpec K' C).symm⟩ (bcExtOpenIso K' C)
    (bcExtOpenIso_hom_fst K' C) rfl

lemma isFiniteEtale_bcExtPr [FiniteDimensional K K'] (C : HypCurve K) :
    IsFiniteEtale (bcExtPr K' C) := by
  haveI : IsFiniteEtale (specAlgebraMap K K') := isFiniteEtale_specAlgebraMap (M := K) (M' := K')
  exact MorphismProperty.of_isPullback (P := @IsFiniteEtale) (isPullback_bcExtPr K' C)
    inferInstance

lemma bcExt_hom_bcExtPr {C : HypCurve K} (h : KIso C C) :
    (h.bcExt K').1.hom ≫ bcExtPr K' C = bcExtPr K' C ≫ h.1.hom := by
  simp only [KIso.bcExt, pullbackIsoOfKIso, bcExtPr, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The `K'`-rational point `Spec K' ⟶ U'` over a `K'`-valued point `x : Spec K' ⟶ U`. -/
def bcRatPt {C : HypCurve K} (x : Spec (.of K') ⟶ C.U.toScheme)
    (hx : x ≫ C.toSpec = specAlgebraMap K K') : Spec (.of K') ⟶ (C.bcExt K').U.toScheme :=
  pullback.lift (𝟙 _) x (by rw [hx, Category.id_comp]) ≫ (bcExtOpenIso K' C).inv

lemma bcRatPt_toSpec {C : HypCurve K} (x : Spec (.of K') ⟶ C.U.toScheme)
    (hx : x ≫ C.toSpec = specAlgebraMap K K') : bcRatPt K' x hx ≫ (C.bcExt K').toSpec = 𝟙 _ := by
  rw [bcRatPt, Category.assoc, ← bcExtOpenIso_hom_fst K' C, Iso.inv_hom_id_assoc,
    pullback.lift_fst]

lemma bcRatPt_bcExtPr {C : HypCurve K} (x : Spec (.of K') ⟶ C.U.toScheme)
    (hx : x ≫ C.toSpec = specAlgebraMap K K') : bcRatPt K' x hx ≫ bcExtPr K' C = x := by
  rw [bcRatPt, bcExtPr, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- **R5 (a)**: if `h_{K'}` fixes the rational point of `U'` over `x`, then `h` fixes `x`. -/
theorem comp_eq_of_bcRatPt {C : HypCurve K} (h : KIso C C) (x : Spec (.of K') ⟶ C.U.toScheme)
    (hx : x ≫ C.toSpec = specAlgebraMap K K')
    (H : bcRatPt K' x hx ≫ (h.bcExt K').1.hom = bcRatPt K' x hx) : x ≫ h.1.hom = x := by
  conv_lhs => rw [← bcRatPt_bcExtPr K' x hx]
  rw [Category.assoc, ← bcExt_hom_bcExtPr, ← Category.assoc, H, bcRatPt_bcExtPr]

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]

omit [CharZero K] in
lemma specMap_algebraMap_tower' :
    Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) ≫ specAlgebraMap K K' =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The geometric point `(Spec Ω → Spec K', pt)` of `U' = Spec K' ×_{Spec K} U` over a geometric
point `pt` of `U`, for `Ω` a `K'`-algebra. -/
def bcPt {C : HypCurve K} (pt : GeomPt Ω C) : GeomPt Ω (C.bcExt K') :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap K' Ω))) pt.x
      (by rw [specMap_algebraMap_tower', pt.over]) ≫ (bcExtOpenIso K' C).inv, by
    rw [Category.assoc, ← bcExtOpenIso_hom_fst K' C, Iso.inv_hom_id_assoc, pullback.lift_fst]⟩

lemma bcPt_bcExtPr {C : HypCurve K} (pt : GeomPt Ω C) : (bcPt K' pt).x ≫ bcExtPr K' C = pt.x := by
  simp only [bcPt, bcExtPr, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-! ### R5 (b): innerness after base change -/

variable [FiniteDimensional K K'] [IsSepClosed Ω]

/-- **R5 (b): an automorphism inducing the identity up to `Δ`-conjugation still does so after a
finite base change**, at every geometric point of `U_{K'}` over the given one. -/
theorem inducedBy_bcExt {C : HypCurve K} {pt : GeomPt Ω C} {pt' : GeomPt Ω (C.bcExt K')}
    (hpt : pt'.x ≫ bcExtPr K' C = pt.x) {h : KIso C C}
    (H : InducedBy pt pt h (ContinuousMulEquiv.refl _)) :
    InducedBy pt' pt' (h.bcExt K') (ContinuousMulEquiv.refl _) := by
  haveI : IsFiniteEtale (specAlgebraMap K K') := isFiniteEtale_specAlgebraMap (M := K) (M' := K')
  haveI := isFiniteEtale_bcExtPr K' C
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  obtain ⟨γ, hp, hγ⟩ := H
  rw [isPathOverBase_iff] at hp
  set pr := bcExtPr K' C
  set h' := h.bcExt K'
  have hcomm : h'.1.hom ≫ pr = pr ≫ h.1.hom := bcExt_hom_bcExtPr K' h
  -- `h_*` is conjugation by `γ`
  have hγ' : ∀ σ : π₁ᵉᵗ(pt.x), fiberIsoMap h.1.hom rfl rfl σ = γ ≪≫ σ ≪≫ γ.symm := by
    intro σ
    have e : σ = γ.symm ≪≫ fiberIsoMap h.1.hom rfl rfl σ ≪≫ γ := by
      have := hγ σ
      rw [Iso.conjAut_apply, fundamentalGroupMap_eq_fiberIsoMap] at this
      exact this
    conv_rhs => rw [e]
    simp
  -- a path `β` over the base
  have o1 : (pt'.x ≫ h'.1.hom) ≫ (C.bcExt K').toSpec =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) :=
    comp_over_of_kHom pt' h'.2
  obtain ⟨β₀⟩ : Nonempty (fiber (pt'.x ≫ h'.1.hom) ≅ fiber pt'.x) :=
    nonempty_iso_of_fiberFunctor _ _
  obtain ⟨τ₀, hτ₀⟩ := surjective_fundamentalGroupMap_toSpec (C.bcExt K') pt'
    (fiberIsoMap (C.bcExt K').toSpec o1 pt'.over β₀)
  let β : fiber (pt'.x ≫ h'.1.hom) ≅ fiber pt'.x := β₀ ≪≫ (τ₀ : fiber pt'.x ≅ fiber pt'.x).symm
  have hβ : fiberIsoMap (C.bcExt K').toSpec o1 pt'.over β = Iso.refl _ := by
    rw [fiberIsoMap_trans _ o1 pt'.over pt'.over, fiberIsoMap_symm,
      ← fundamentalGroupMap_eq_fiberIsoMap, hτ₀, Iso.self_symm_id]
  -- its image `c` in `π₁ᵉᵗ(U, pt)`
  have e1 : (pt'.x ≫ h'.1.hom) ≫ pr = pt.x ≫ h.1.hom := by
    rw [Category.assoc, hcomm, ← Category.assoc, hpt]
  let P : fiber (pt.x ≫ h.1.hom) ≅ fiber pt.x := fiberIsoMap pr e1 hpt β
  let c : π₁ᵉᵗ(pt.x) := γ.symm ≪≫ P
  have hsK := specMap_algebraMap_tower' K' (K := K) (Ω := Ω)
  have hP : fiberIsoMap C.toSpec (comp_over_of_kHom pt h.2) pt.over P = Iso.refl _ := by
    have k1 : (pt.x ≫ h.1.hom) ≫ C.toSpec = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
      comp_over_of_kHom pt h.2
    rw [fiberIsoMap_fiberIsoMap pr C.toSpec e1 hpt k1 pt.over (by rw [← Category.assoc, e1, k1])
      (by rw [← Category.assoc, hpt, pt.over])]
    rw [fiberIsoMap_congr (bcExtPr_toSpec K' C) _ _ (by rw [← Category.assoc, o1, hsK])
      (by rw [← Category.assoc, pt'.over, hsK])]
    rw [← fiberIsoMap_fiberIsoMap (C.bcExt K').toSpec (specAlgebraMap K K') o1 pt'.over hsK hsK, hβ,
      fiberIsoMap_refl]
  have hc : fundamentalGroupMap C.toSpec pt.over c = 1 := by
    change (fundamentalGroupMap C.toSpec pt.over c : _ ≅ _) = Iso.refl _
    rw [fundamentalGroupMap_eq_fiberIsoMap, fiberIsoMap_trans _ pt.over
      (comp_over_of_kHom pt h.2) pt.over, fiberIsoMap_symm, hp, hP]
    simp
  -- `c` lies in `π₁ᵉᵗ(U')`
  have hv : (pt'.x ≫ (C.bcExt K').toSpec) ≫ specAlgebraMap K K' =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by rw [pt'.over, hsK]
  have hrange := range_fundamentalGroupMap_of_isPullback (isPullback_bcExtPr K' C) pt.over
    (surjective_fundamentalGroupMap_toSpec C pt) hpt hv
  have hmem : c ∈ (fundamentalGroupMap pr hpt).toMonoidHom.range := by
    rw [hrange, Subgroup.mem_comap]
    change fundamentalGroupMap C.toSpec pt.over c ∈ _
    rw [hc]
    exact Subgroup.one_mem _
  obtain ⟨d, hd⟩ := hmem
  have hd' : fiberIsoMap pr hpt hpt d = c := by
    rw [← fundamentalGroupMap_eq_fiberIsoMap]
    exact congrArg (fun g : π₁ᵉᵗ(pt.x) ↦ (g : fiber pt.x ≅ fiber pt.x)) hd
  -- `β`-conjugation after `h'_*` is conjugation by `d`
  have hinj := fundamentalGroupMap_injective_of_isFiniteEtale' pr pt'.x hpt
  have key : ∀ τ : π₁ᵉᵗ(pt'.x),
      (β.symm ≪≫ fiberIsoMap h'.1.hom rfl rfl τ ≪≫ β : π₁ᵉᵗ(pt'.x)) = d.symm ≪≫ τ ≪≫ d := by
    intro τ
    apply hinj
    rw [fundamentalGroupMap_eq_fiberIsoMap, fundamentalGroupMap_eq_fiberIsoMap,
      fiberIsoMap_trans _ hpt e1 hpt, fiberIsoMap_trans _ e1 e1 hpt, fiberIsoMap_symm,
      fiberIsoMap_trans _ hpt hpt hpt, fiberIsoMap_trans _ hpt hpt hpt, fiberIsoMap_symm, hd']
    have e2 : fiberIsoMap pr e1 e1 (fiberIsoMap h'.1.hom rfl rfl τ) =
        fiberIsoMap h.1.hom rfl rfl (fiberIsoMap pr hpt hpt τ) := by
      have a1 : pt'.x ≫ h'.1.hom ≫ pr = pt.x ≫ h.1.hom := by rw [← Category.assoc, e1]
      have a2 : pt'.x ≫ pr ≫ h.1.hom = pt.x ≫ h.1.hom := by rw [← Category.assoc, hpt]
      rw [fiberIsoMap_fiberIsoMap h'.1.hom pr rfl rfl e1 e1 a1 a1,
        fiberIsoMap_fiberIsoMap pr h.1.hom hpt hpt rfl rfl a2 a2]
      exact fiberIsoMap_congr hcomm _ _ _ _ _
    rw [e2, hγ']
    simp [P, c]
  -- the path `β · d⁻¹`
  refine ⟨β ≪≫ (d : fiber pt'.x ≅ fiber pt'.x).symm, ?_, fun τ ↦ ?_⟩
  · rw [isPathOverBase_iff, fiberIsoMap_trans _ o1 pt'.over pt'.over, hβ, fiberIsoMap_symm,
      Iso.refl_trans]
    -- `d` maps to `1` in `G_{K'}`
    have hd1 : fundamentalGroupMap (C.bcExt K').toSpec pt'.over d = 1 := by
      apply fundamentalGroupMap_injective_of_isFiniteEtale' (specAlgebraMap K K')
        (Spec.map (CommRingCat.ofHom (algebraMap K' Ω))) hsK
      rw [map_one]
      change (fundamentalGroupMap (specAlgebraMap K K') hsK
        (fundamentalGroupMap (C.bcExt K').toSpec pt'.over d) : _ ≅ _) = Iso.refl _
      rw [fundamentalGroupMap_eq_fiberIsoMap, fundamentalGroupMap_eq_fiberIsoMap,
        fiberIsoMap_fiberIsoMap (C.bcExt K').toSpec (specAlgebraMap K K') pt'.over pt'.over hsK hsK
          (by rw [← Category.assoc, pt'.over, hsK]) (by rw [← Category.assoc, pt'.over, hsK]),
        ← fiberIsoMap_congr (bcExtPr_toSpec K' C) (by rw [← Category.assoc, hpt, pt.over])
          (by rw [← Category.assoc, hpt, pt.over]),
        ← fiberIsoMap_fiberIsoMap pr C.toSpec hpt hpt pt.over pt.over, hd',
        ← fundamentalGroupMap_eq_fiberIsoMap, hc]
      rfl
    have : (fundamentalGroupMap (C.bcExt K').toSpec pt'.over d : _ ≅ _) = Iso.refl _ := by
      rw [hd1]
      rfl
    rw [fundamentalGroupMap_eq_fiberIsoMap] at this
    rw [this, Iso.refl_symm]
  · change τ = _
    rw [Iso.conjAut_apply, fundamentalGroupMap_eq_fiberIsoMap]
    have := key τ
    calc τ = (d : fiber pt'.x ≅ fiber pt'.x) ≪≫ (d.symm ≪≫ τ ≪≫ d) ≪≫ d.symm := by simp
      _ = _ := by
        rw [← this]
        simp

end BaseChange

/-! ### Closed points and the assembly over finite extensions of `ℚ_p` -/

section Assembly

variable (p : ℕ) [Fact p.Prime]

/-- **Step L1/L2 (helper hL) as a statement**: over every finite extension `K'` of `ℚ_p`, a
`K'`-automorphism of a proper hyperbolic curve inducing the identity of `π₁ᵉᵗ(U, pt)` up to
`Δ`-conjugation (a path over the base) fixes every `K'`-rational point. A plain proposition
(proved from [LocAn] Thm C, `SectionBridge.eq_of_schSection_conj_padic'`, by helper hL); it is
never assumed. -/
def RationalPointsFixedMLF : Prop :=
  ∀ (K' : Type u) [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K']
    (Ω : Type u) [Field Ω] [Algebra K' Ω] [IsSepClosed Ω] (C' : HypCurve K'),
    (C'.U : Set C'.Xbar)ᶜ = ∅ → ∀ (pt : GeomPt Ω C') (h : KIso C' C'),
    InducedBy pt pt h (ContinuousMulEquiv.refl _) →
    ∀ x : Spec (.of K') ⟶ C'.U.toScheme, x ≫ C'.toSpec = 𝟙 _ → x ≫ h.1.hom = x

variable {p} {K : Type u} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- **R5: points over finite extensions.** Under `hRat`, a `K`-automorphism of a proper
hyperbolic curve inducing the identity up to `Δ`-conjugation fixes every `K'`-valued point
`Spec K' ⟶ U`, `K'/K` finite (base change to `K'`, embedded into `Ω`). -/
theorem comp_eq_of_inducedBy_of_finite (hRat : RationalPointsFixedMLF.{u} p)
    (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅) (pt : GeomPt Ω C) (h : KIso C C)
    (H : InducedBy pt pt h (ContinuousMulEquiv.refl _)) (K' : Type u) [Field K'] [Algebra K K']
    [FiniteDimensional K K'] (x : Spec (.of K') ⟶ C.U.toScheme)
    (hx : x ≫ C.toSpec = specAlgebraMap K K') : x ≫ h.1.hom = x := by
  haveI := charZero_of_padic p K
  let ι : K' →ₐ[K] Ω := IsSepClosed.lift
  letI : Algebra K' Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  letI : Algebra ℚ_[p] K' := ((algebraMap K K').comp (algebraMap ℚ_[p] K)).toAlgebra
  haveI : IsScalarTower ℚ_[p] K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional ℚ_[p] K' := Module.Finite.trans K K'
  have H' := inducedBy_bcExt K' (bcPt_bcExtPr K' pt) H
  exact comp_eq_of_bcRatPt K' h x hx (hRat K' Ω (C.bcExt K') (bcExt_proper K' C hC) _ _ H'
    (bcRatPt K' x hx) (bcRatPt_toSpec K' x hx))

/-- **R5: closed points.** Under `hRat`, a `K`-automorphism of a proper hyperbolic curve inducing
the identity up to `Δ`-conjugation fixes every closed point `Spec κ(x) ⟶ U` (`κ(x)` is finite
over `K`). -/
theorem fromSpecResidueField_comp_eq_of_inducedBy (hRat : RationalPointsFixedMLF.{u} p)
    (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅) (pt : GeomPt Ω C) (h : KIso C C)
    (H : InducedBy pt pt h (ContinuousMulEquiv.refl _)) (x : C.U.toScheme)
    (hx : IsClosed {x}) :
    C.U.toScheme.fromSpecResidueField x ≫ h.1.hom = C.U.toScheme.fromSpecResidueField x := by
  letI : C.U.toScheme.Over (Spec (.of K)) := ⟨C.toSpec⟩
  haveI : LocallyOfFiniteType (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : LocallyOfFiniteType (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  letI := Anabelian.residueFieldAlgebra K C.U.toScheme x
  haveI : Module.Finite K (C.U.toScheme.residueField x) := finite_residueField K hx
  exact comp_eq_of_inducedBy_of_finite hRat C hC pt h H (C.U.toScheme.residueField x)
    (C.U.toScheme.fromSpecResidueField x) (fromSpecResidueField_comp_structure K x)

variable [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

/-- **Inner rigidity of proper hyperbolic curves over finite extensions of `ℚ_p`, given the
rational-point statement `hRat`** (MR7 S8: R0 + R5 + R6; `hRat` is step L1/L2). -/
theorem innerRigidProper_padic_of_rationalPointsFixed (hRat : RationalPointsFixedMLF.{u} p)
    (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅) : InnerRigidProper Ω C := by
  intro pt h H
  have HI := inducedBy_refl_of_isConjInduced_id pt h H (center_Gk_padic p Ω)
  haveI := IsCurveOver.isIntegral K C.Xbar
  letI : C.U.toScheme.Over (Spec (.of K)) := ⟨C.toSpec⟩
  haveI : h.1.hom.IsOver (Spec (.of K)) := ⟨h.2⟩
  haveI : IsReduced C.U.toScheme := isReduced_of_isOpenImmersion C.U.ι
  haveI : LocallyOfFiniteType (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : LocallyOfFiniteType (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  haveI : IsSeparated (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : IsSeparated (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  haveI : JacobsonSpace C.U.toScheme :=
    LocallyOfFiniteType.jacobsonSpace (C.U.toScheme ↘ Spec (.of K))
  refine KIso.ext (Iso.ext ?_)
  exact eq_id_of_fromSpecResidueField_closedPoints (S := Spec (.of K)) fun x hx ↦
    fromSpecResidueField_comp_eq_of_inducedBy hRat C hC pt h HI x hx

end Assembly

end CurvesJacobian.LocAn
