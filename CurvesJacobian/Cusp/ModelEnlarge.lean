/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelEnlargeFill
import CurvesJacobian.Cusp.ModelEnlargeToG
import CurvesJacobian.Cusp.ModelEnlargeCore

/-!
# Enlarging a geometric model (MR8 option (Q), final assembly)

Let `D` be a geometric model of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`) with the
rel-isom-DGC over its field of definition, and `ι(Π_Y) ≤ P' ≤ N_A(ι(Π_Y))` with `ι(Π_Y)` of finite
index in `P'`, `P'` open in `A`, normalised by `Δ_A`, with `P' ∩ Δ_A` torsion-free. The filled
quotient curve `Z` over `M₀` (`GeomModel.enlFillCurve`) comes with `Π_Z ≃ₜ* P'`
(`GeomModel.enlFillEquiv`). Here:

* `GeomModel.enlIotaZ`: the embedding `ι' : Π_Z ≃ P' ⊆ A`, with image `P'`
  (`GeomModel.range_enlIotaZ`), over `G_K` up to conjugation (`GeomModel.exists_toGk_enlIotaZ`);
* `GeomModel.enlJZ`: `j = ι'⁻¹ ∘ ι : Π_Y → Π_Z`, with `j ∘ ψ_{V''} = fill ∘ ι_{V''}`
  (`GeomModel.enlJZ_enlPsiV`); it maps cuspidal inertia groups of `Π_Y` to the trivial group or
  to subgroups commensurable with cuspidal inertia groups of `Π_Z` (`GeomModel.enlJZ_map_cusp`);
* **`GeomModel.enlarge`**: the geometric model `(Z, ι')` of `A`, with image `P'`
  (`GeomModel.range_enlarge`);
* **`GeomModel.exists_enlarge`** (option (Q)): assuming the rel-isom-DGC over all number fields,
  every open subgroup `P' ⊆ A` normalised by `Δ_A` with `P' ∩ Δ_A` torsion-free is the image of a
  geometric model of `A`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section GroupTheory

variable {P Q G : Type*} [Group P] [Group Q] [Group G]

/-- If `X ≤ C` and `C ∩ N ≤ X` for `N` of finite index, then `X` and `C` are commensurable. -/
lemma commensurable_of_le_of_inf_le_enl {N X C : Subgroup Q} (hN : N.index ≠ 0) (h1 : X ≤ C)
    (h2 : C ⊓ N ≤ X) : X.Commensurable C := by
  refine ⟨fun h0 ↦ ?_, by rw [Subgroup.relIndex_eq_one.2 h1]; exact one_ne_zero⟩
  have h3 : (N ⊓ C).relIndex C ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_ne_zero_of_index_ne_zero hN C
  have h4 := Subgroup.relIndex_dvd_of_le_left (L := C) ((inf_comm N C).le.trans h2)
  rw [h0] at h4
  exact h3 (Nat.eq_zero_of_zero_dvd h4)

/-- **Preimages along `ι'` and images along `j`**: if `ι' ∘ j = ι`, `ι'` is injective and
`ι'⁻¹(ι(P))` has finite index, then `ι'⁻¹(S)` is commensurable with `j(ι⁻¹(S))`. -/
lemma commensurable_comap_map_enl (ι : P →* G) (ι' : Q →* G) (j : P →* Q)
    (hj : ∀ σ, ι' (j σ) = ι σ) (hinj : Function.Injective ι') (hR : (ι.range.comap ι').index ≠ 0)
    (S : Subgroup G) : (S.comap ι').Commensurable ((S.comap ι).map j) := by
  have e : ι.range.comap ι' ⊓ S.comap ι' = (S.comap ι).map j := by
    ext x
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 h1)
      refine Subgroup.mem_map.2 ⟨σ, Subgroup.mem_comap.2 ?_, hinj ((hj σ).trans hσ)⟩
      rw [hσ]
      exact Subgroup.mem_comap.1 h2
    · intro hx
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (MonoidHom.mem_range.2 ⟨σ, (hj σ).symm⟩),
        Subgroup.mem_comap.2 ?_⟩
      rw [hj]
      exact Subgroup.mem_comap.1 hσ
  rw [← e]
  exact (Subgroup.commensurable_inf_of_index_ne_zero hR _).symm

end GroupTheory

namespace GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

/-- **`ι(Π_Y)` has finite index in every subgroup of `N_A(ι(Π_Y))`** (it is open in `A`). -/
lemma relIndex_ιNHom_ne_zero (P' : Subgroup D.Nrm) : D.ιNHom.range.relIndex P' ≠ 0 := by
  have e : D.ιNHom.range = (D.ι : D.Pi →* A.grp).range.comap D.Nrm.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 hx
      exact Subgroup.mem_comap.2 (MonoidHom.mem_range.2 ⟨σ, congrArg Subtype.val hσ⟩)
    · intro hx
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hx)
      exact MonoidHom.mem_range.2 ⟨σ, Subtype.ext hσ⟩
  refine Subgroup.relIndex_ne_zero_of_index_ne_zero ?_ P'
  rw [e, Subgroup.index_comap]
  exact Subgroup.relIndex_ne_zero_of_index_ne_zero D.index_range_ne_zero _

variable (hDGC : RelIsomDGC.Exists D.M) {P' : Subgroup D.Nrm}
  (hrel : D.ιNHom.range.relIndex P' ≠ 0) (hPP' : D.ιNHom.range ≤ P')
  (hopen : IsOpen ((P'.map D.Nrm.subtype : Subgroup A.grp) : Set A.grp))
  (hnorm : A.Delta ≤ Subgroup.normalizer ((P'.map D.Nrm.subtype : Subgroup A.grp) : Set A.grp))
  (htf : IsTorsionFreeSubgroup (P'.map D.Nrm.subtype ⊓ A.Delta))

attribute [local instance] isAlgClosure_of_isAlgebraic enlAlgebraM₀ enlFill_isAlgebraic
  enlFill_isScalarTower

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-! ### The filled curve `Z` and `ι' : Π_Z ↪ A` -/

/-- The hypothesis `hΔ` of the filling (`GeomModel.mem_ker_projGk_enlZ0_iff`). -/
theorem enlHDelta : ∀ γ,
    γ ∈ (projGk Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel)).toMonoidHom.ker ↔
      ((D.enlPhiZ hDGC hrel hPP' γ : D.Nrm) : A.grp) ∈ A.Delta :=
  D.mem_ker_projGk_enlZ0_iff hDGC hrel hPP'

/-- **The filled quotient curve `Z`** over `M₀` (`GeomModel.enlFillCurve`). -/
abbrev enlZ : HypCurve (D.enlM₀ hDGC hrel) :=
  D.enlFillCurve hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf

/-- `Π_Z`. -/
abbrev enlPiZ := π₁ᵉᵗ(D.enlFillPt hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)

/-- `Π_{Z₀} ↠ Π_Z` (`GeomModel.enlFillPiHom`). -/
abbrev enlZFill : π₁ᵉᵗ(D.enlZ0Pt hDGC hrel) →ₜ* D.enlPiZ hDGC hrel hPP' htf :=
  D.enlFillPiHom hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf

/-- `Π_Z ≃ₜ* P'` (`GeomModel.enlFillEquiv`). -/
abbrev enlZEquiv : D.enlPiZ hDGC hrel hPP' htf ≃ₜ* P' :=
  D.enlFillEquiv hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf

/-- **The embedding `ι' : Π_Z ≃ P' ⊆ N_A(ι(Π_Y)) ⊆ A`.** -/
def enlIotaZ : D.enlPiZ hDGC hrel hPP' htf →ₜ* A.grp where
  toMonoidHom := (D.Nrm.subtype.comp P'.subtype).comp
    (D.enlZEquiv hDGC hrel hPP' htf).toMulEquiv.toMonoidHom
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).comp
    (D.enlZEquiv hDGC hrel hPP' htf).continuous

lemma enlIotaZ_apply (σ : D.enlPiZ hDGC hrel hPP' htf) :
    D.enlIotaZ hDGC hrel hPP' htf σ = ((D.enlZEquiv hDGC hrel hPP' htf σ : D.Nrm) : A.grp) :=
  rfl

lemma enlIotaZ_injective : Function.Injective (D.enlIotaZ hDGC hrel hPP' htf) := by
  intro a b h
  have h' : (((D.enlZEquiv hDGC hrel hPP' htf a : P') : D.Nrm) : A.grp) =
      ((D.enlZEquiv hDGC hrel hPP' htf b : P') : D.Nrm) := h
  exact (D.enlZEquiv hDGC hrel hPP' htf).injective (Subtype.ext (Subtype.ext h'))

/-- **The image of `ι'` is `P'`.** -/
lemma range_enlIotaZ : Set.range (D.enlIotaZ hDGC hrel hPP' htf) =
    ((P'.map D.Nrm.subtype : Subgroup A.grp) : Set A.grp) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact Subgroup.mem_map.2 ⟨_, (D.enlZEquiv hDGC hrel hPP' htf σ).2, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨σ, hσ⟩ := (D.enlZEquiv hDGC hrel hPP' htf).surjective ⟨y, hy⟩
    exact ⟨σ, congrArg (fun z : P' ↦ ((z : D.Nrm) : A.grp)) hσ⟩

/-- **`ι'` lies over `res : G_{M₀} → G_K` up to conjugation**: from
`toG_A ∘ Φ_Z = conj g ∘ res ∘ pr_{Z₀}` (`GeomModel.exists_toGk_enlPhi_enlZ0`), the relation of
`pr_Z` and `pr_{Z₀}` along `Π_{Z₀} ↠ Π_Z` (K0) and `ι' ∘ fill = Φ_Z`. -/
theorem exists_toGk_enlIotaZ : ∃ g₀ : π₁ᵉᵗ(sK), ∀ σ,
    toGk A (D.enlIotaZ hDGC hrel hPP' htf σ) = g₀ * resGal K Ω (D.enlM₀ hDGC hrel)
      (projGk Ω (D.enlZ hDGC hrel hPP' htf)
        (D.enlFillCurve_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf) σ) * g₀⁻¹ := by
  obtain ⟨g, hg⟩ := D.exists_toGk_enlPhi_enlZ0 hDGC hrel hPP'
  have hF : Spec.map (CommRingCat.ofHom (resAlg (D.enlM₀ hDGC hrel)
      (D.enlFillU_le hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (D.enlM₀ hDGC hrel)
          Γ((D.enlZ0 hDGC hrel).Xbar, D.enlFillU hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap K (D.enlM₀ hDGC hrel))) =
      Spec.map (CommRingCat.ofHom (algebraMap (D.enlM₀ hDGC hrel)
        Γ((D.enlZ0 hDGC hrel).Xbar, (D.enlZ0 hDGC hrel).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (D.enlM₀ hDGC hrel))) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (specMap_resAlg_structure _ _))
  obtain ⟨c, hc⟩ := exists_resGal_projGk_conj_of_conjInduced Ω (K := K)
    (D.enlZ0_cusp hDGC hrel) (D.enlFillCurve_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
    _ hF (isConjInduced_fillPiHom Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel)
      (D.enlFillU_le hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
      (D.enlFillU_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
      (D.enlFillU_hyp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf))
  refine ⟨g * c⁻¹, fun σ ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := D.enlFillPiHom_surjective hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf σ
  have h1 : D.enlIotaZ hDGC hrel hPP' htf (D.enlZFill hDGC hrel hPP' htf γ) =
      ((D.enlPhi hDGC hrel hPP' (D.enlZ0PiEquiv hDGC hrel γ) : D.Nrm) : A.grp) :=
    congrArg (fun z : P' ↦ ((z : D.Nrm) : A.grp))
      (D.enlFillEquiv_fillPiHom hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf γ)
  refine ((congrArg (toGk A) h1).trans (hg γ)).trans ?_
  exact Eq.trans (by group) (congrArg (fun z ↦ (g * c⁻¹) * z * (g * c⁻¹)⁻¹) (hc γ).symm)

/-! ### `j = ι'⁻¹ ∘ ι : Π_Y → Π_Z` and the cusps -/

/-- **`j = ι'⁻¹ ∘ ι : Π_Y → Π_Z`.** -/
def enlJZ : D.Pi →* D.enlPiZ hDGC hrel hPP' htf :=
  (D.enlZEquiv hDGC hrel hPP' htf).symm.toMulEquiv.toMonoidHom.comp
    (D.ιNHom.codRestrict P' fun σ ↦ hPP' ⟨σ, rfl⟩)

lemma enlJZ_apply (σ : D.Pi) :
    D.enlJZ hDGC hrel hPP' htf σ =
      (D.enlZEquiv hDGC hrel hPP' htf).symm ⟨D.ιN σ, hPP' ⟨σ, rfl⟩⟩ :=
  rfl

/-- `ι' ∘ j = ι`. -/
lemma enlIotaZ_enlJZ (σ : D.Pi) :
    D.enlIotaZ hDGC hrel hPP' htf (D.enlJZ hDGC hrel hPP' htf σ) = D.ι σ :=
  congrArg (fun z : P' ↦ ((z : D.Nrm) : A.grp))
    ((D.enlZEquiv hDGC hrel hPP' htf).apply_symm_apply ⟨D.ιN σ, hPP' ⟨σ, rfl⟩⟩)

/-- **`j ∘ ψ_{V''} = fill ∘ ι_{V''}`** (`Φ_Z ∘ ι_{V''} = ι ∘ ψ_{V''}`, `ι' ∘ fill = Φ_Z`). -/
lemma enlJZ_enlPsiV (y : π₁ᵉᵗ(D.enlVPt hDGC hrel)) :
    D.enlJZ hDGC hrel hPP' htf (D.enlPsiV hDGC hrel y) =
      D.enlZFill hDGC hrel hPP' htf (D.enlIotaV hDGC hrel y) := by
  apply (D.enlZEquiv hDGC hrel hPP' htf).injective
  refine ((D.enlZEquiv hDGC hrel hPP' htf).apply_symm_apply
    ⟨D.ιN (D.enlPsiV hDGC hrel y), hPP' ⟨_, rfl⟩⟩).trans ?_
  refine Eq.trans ?_
    (D.enlFillEquiv_fillPiHom hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf _).symm
  exact Subtype.ext (Subtype.ext (D.coe_enlPhiZ_enlIotaV hDGC hrel hPP' y).symm)

/-- **`j` on cuspidal inertia groups**: the image under `j` of a cuspidal inertia group `J` of
`Π_Y` is trivial or commensurable with a cuspidal inertia group of `Π_Z`. Write `J = ψ_{V''}(J'')`
(K2 d), take `C ⊇ ι_{V''}(J'')` (`GeomModel.exists_arithCusps_enlIotaV`); then
`j(J) = fill(ι_{V''}(J''))` and `C` is killed by `fill` or maps onto a cuspidal inertia group
(K2 c), commensurable with `fill(ι_{V''}(J''))`. -/
theorem enlJZ_map_cusp {J} (hJ : J ∈ arithCusps Ω D.Y D.hY) :
    J.map (D.enlJZ hDGC hrel hPP' htf) = ⊥ ∨
      ∃ J' ∈ arithCusps Ω (D.enlZ hDGC hrel hPP' htf)
          (D.enlFillCurve_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf),
        (J.map (D.enlJZ hDGC hrel hPP' htf)).Commensurable J' := by
  haveI : Nonempty (baseChangeOpen D.M Ω (X := (D.enlV hDGC hrel).Xbar) D.Y.U) :=
    (nonempty_baseChangeOpen D.M Ω D.Y.nonempty).to_subtype
  obtain ⟨J'', hJ'', rfl⟩ := exists_map_eq_of_conjInduced_fill Ω (D.enlV hDGC hrel)
    (D.enlV_cusp hDGC hrel) (D.Y.Xbar.basicOpen_le (D.enlR hDGC hrel)) D.hY D.Y.hyperbolic
    (D.enlPsiV hDGC hrel).toMonoidHom (D.isConjInduced_enlPsiV hDGC hrel) hJ
  have e : (J''.map (D.enlPsiV hDGC hrel).toMonoidHom).map (D.enlJZ hDGC hrel hPP' htf) =
      (J''.map (D.enlIotaV hDGC hrel).toMonoidHom).map
        (D.enlZFill hDGC hrel hPP' htf).toMonoidHom :=
    (Subgroup.map_map _ _ _).trans ((congrArg (fun f ↦ J''.map f)
      (MonoidHom.ext fun y ↦ D.enlJZ_enlPsiV hDGC hrel hPP' htf y)).trans
        (Subgroup.map_map _ _ _).symm)
  obtain ⟨C, hC, h1, h2⟩ := D.exists_arithCusps_enlIotaV hDGC hrel hJ''
  rcases le_ker_or_map_mem_arithCusps_of_conjInduced_fill Ω (D.enlZ0 hDGC hrel)
      (D.enlZ0_cusp hDGC hrel) (D.enlFillU_le hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
      (D.enlFillU_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
      (D.enlFillU_hyp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
      (D.enlZFill hDGC hrel hPP' htf).toMonoidHom
      (isConjInduced_fillPiHom Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel)
        (D.enlFillU_le hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
        (D.enlFillU_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)
        (D.enlFillU_hyp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf)) hC with hk | hm
  · left
    refine e.trans (eq_bot_iff.2 ?_)
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_bot.2 (MonoidHom.mem_ker.1 (hk (h1 hz)))
  · right
    refine ⟨_, hm, ?_⟩
    exact (congrArg (fun H ↦ H.Commensurable (C.map (D.enlZFill hDGC hrel hPP' htf).toMonoidHom))
      e).mpr ((commensurable_of_le_of_inf_le_enl (D.index_enlN_ne_zero hDGC hrel) h1 h2).map' _)

/-- **Cusp compatibility of `ι'`.** For a cuspidal inertia group `I` of `Π_X` with image
`S = ρ_A(I)`, `ι'⁻¹(S)` is commensurable with `j(ι⁻¹(S))` (`ι'⁻¹(ι(Π_Y))` has finite index), and
`ι⁻¹(S)` is finite or commensurable with a cuspidal inertia group of `Π_Y`
(`GeomModel.cusp`), whose image under `j` is controlled by `GeomModel.enlJZ_map_cusp`. -/
theorem enlIotaZ_cusp : ∀ I ∈ (arithmeticExt Ω CX hcX).cusps,
    ((A.image I).comap
        (D.enlIotaZ hDGC hrel hPP' htf : D.enlPiZ hDGC hrel hPP' htf →* A.grp)).Commensurable ⊥ ∨
      ∃ J ∈ arithCusps Ω (D.enlZ hDGC hrel hPP' htf)
          (D.enlFillCurve_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf),
        ((A.image I).comap
          (D.enlIotaZ hDGC hrel hPP' htf : D.enlPiZ hDGC hrel hPP' htf →* A.grp)).Commensurable J
    := by
  intro I hI
  have hR : ((D.ι : D.Pi →* A.grp).range.comap
      (D.enlIotaZ hDGC hrel hPP' htf : D.enlPiZ hDGC hrel hPP' htf →* A.grp)).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact Subgroup.relIndex_ne_zero_of_index_ne_zero D.index_range_ne_zero _
  have hS := commensurable_comap_map_enl (D.ι : D.Pi →* A.grp)
    (D.enlIotaZ hDGC hrel hPP' htf : D.enlPiZ hDGC hrel hPP' htf →* A.grp)
    (D.enlJZ hDGC hrel hPP' htf) (fun σ ↦ D.enlIotaZ_enlJZ hDGC hrel hPP' htf σ)
    (D.enlIotaZ_injective hDGC hrel hPP' htf) hR (A.image I)
  rcases D.cusp I hI with h | ⟨J, hJ, h⟩
  · left
    have h' := h.map' (D.enlJZ hDGC hrel hPP' htf)
    rw [Subgroup.map_bot] at h'
    exact hS.trans h'
  · rcases D.enlJZ_map_cusp hDGC hrel hPP' htf hJ with hb | ⟨J', hJ', hc⟩
    · left
      have h' := h.map' (D.enlJZ hDGC hrel hPP' htf)
      rw [hb] at h'
      exact hS.trans h'
    · exact Or.inr ⟨J', hJ', hS.trans ((h.map' _).trans hc)⟩

/-! ### The enlarged model -/

/-- **The enlarged geometric model** (MR8 option (Q)): for `ι(Π_Y) ≤ P' ≤ N_A(ι(Π_Y))` of finite
relative index with `P'` open in `A`, normalised by `Δ_A` and `P' ∩ Δ_A` torsion-free, the filled
quotient curve `Z` over `M₀` with `ι' : Π_Z ≃ P' ⊆ A` is a geometric model of `A` with image `P'`
(`GeomModel.range_enlarge`). -/
def enlarge : GeomModel Ω CX hcX A where
  M := D.enlM₀ hDGC hrel
  algΩ := D.enlAlgebraM₀ hDGC hrel
  tower := D.isScalarTower_enlAlgebraM₀ hDGC hrel
  finDim := Module.Finite.of_restrictScalars_finite ℚ K (D.enlM₀ hDGC hrel)
  Y := D.enlZ hDGC hrel hPP' htf
  hY := D.enlFillCurve_cusp hDGC hrel hPP' (D.enlHDelta hDGC hrel hPP') htf
  ι := D.enlIotaZ hDGC hrel hPP' htf
  inj := D.enlIotaZ_injective hDGC hrel hPP' htf
  isOpen_range := by
    rw [range_enlIotaZ]
    exact hopen
  normal := by
    rw [range_enlIotaZ]
    exact hnorm
  toG_eq := D.exists_toGk_enlIotaZ hDGC hrel hPP' htf
  cusp := D.enlIotaZ_cusp hDGC hrel hPP' htf

/-- **The image of the enlarged model is `P'`.** -/
theorem range_enlarge : Set.range (D.enlarge hDGC hrel hPP' hopen hnorm htf).ι =
    ((P'.map D.Nrm.subtype : Subgroup A.grp) : Set A.grp) :=
  D.range_enlIotaZ hDGC hrel hPP' htf

/-- **Option (Q): every open subgroup `P' ⊆ A` normalised by `Δ_A`, with `P' ∩ Δ_A` torsion-free,
is the image of a geometric model of `A`** (assuming the rel-isom-DGC over all number fields).
Shrink `D` to a model `D₂` with image `T ⊆ P'` normal in `A` (`GeomModel.exists_model_normal_le`),
so that `N_A(T) = A`, and enlarge `D₂` to `P'` (`GeomModel.enlarge`). -/
theorem exists_enlarge (D : GeomModel Ω CX hcX A)
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (P' : Subgroup A.grp) (hP' : IsOpen (P' : Set A.grp))
    (hnorm : A.Delta ≤ Subgroup.normalizer (P' : Set A.grp))
    (htf : IsTorsionFreeSubgroup (P' ⊓ A.Delta)) :
    ∃ D' : GeomModel Ω CX hcX A, Set.range D'.ι = P' := by
  obtain ⟨D₂, T, hTn, -, hrange, hTP, -⟩ := D.exists_model_normal_le P' hP'
  haveI := hTn
  have hN : ∀ x, x ∈ D₂.Nrm := fun x ↦ le_normalizer_of_normal T hrange ⊤ (Subgroup.mem_top x)
  have hmap : (P'.comap D₂.Nrm.subtype).map D₂.Nrm.subtype = P' := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact hy
    · intro hx
      exact Subgroup.mem_map.2 ⟨⟨x, hN x⟩, hx, rfl⟩
  have hPP' : D₂.ιNHom.range ≤ P'.comap D₂.Nrm.subtype := by
    rintro _ ⟨σ, rfl⟩
    refine Subgroup.mem_comap.2 (hTP ?_)
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨σ, rfl⟩
  have hopen' : IsOpen (((P'.comap D₂.Nrm.subtype).map D₂.Nrm.subtype : Subgroup A.grp) :
      Set A.grp) := by
    rw [hmap]
    exact hP'
  have hnorm' : A.Delta ≤ Subgroup.normalizer
      (((P'.comap D₂.Nrm.subtype).map D₂.Nrm.subtype : Subgroup A.grp) : Set A.grp) := by
    rw [hmap]
    exact hnorm
  have htf' : IsTorsionFreeSubgroup ((P'.comap D₂.Nrm.subtype).map D₂.Nrm.subtype ⊓ A.Delta) := by
    rw [hmap]
    exact htf
  refine ⟨D₂.enlarge (hDGC D₂.M) (D₂.relIndex_ιNHom_ne_zero _) hPP' hopen' hnorm' htf', ?_⟩
  rw [range_enlarge, hmap]

end GeomModel

end CurvesJacobian.Cusp
