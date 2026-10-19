/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GaloisQuotient
import CurvesJacobian.Cusp.DGCArith

/-!
# Conjugation by a lift of a deck transformation is induced by the deck transformation

Let `f : V ⟶ U` be a connected finite étale cover, `η` a geometric point of `V` over
`η' = η ≫ f`, `p = coverPt f η h` the point `η` of the fibre of `V` over `η'`, and let
`φ : V ≅ V` be an automorphism over `U` (in `FiniteEtale U`). Let `σ ∈ π₁ᵉᵗ(U, η')` with
`σ • p = φ(p)`. Then:

* `conj_mem_coverSubgroup_of_smul`: `σ` normalises `π₁ᵉᵗ(V, η) = coverSubgroup f η h`
  (the `π₁ᵉᵗ(U)`-action commutes with `φ`);
* `coverAutConj`: the induced continuous endomorphism `c_σ` of `π₁ᵉᵗ(V, η)`, characterised by
  `f_* (c_σ τ) = σ * f_* τ * σ⁻¹` (`fundamentalGroupMap_coverAutConj`);
* **`isConjInduced_coverAutConj`**: `c_σ` is induced by the automorphism `φ⁻¹` of `V`
  (i.e. by `φ.inv.left`) up to a change of base point: `IsConjInduced φ.inv.left c_σ`.

The orientation: a change of base point `γ : fiber (η ≫ φ⁻¹) ≅ fiber η` induces, after pushing
forward along `f`, conjugation by an element `δ ∈ π₁ᵉᵗ(U, η')` with `δ • φ⁻¹(p) = p`; then
`σ * δ⁻¹` fixes `p`, i.e. lies in `π₁ᵉᵗ(V, η)`, so the two conjugations agree up to an inner
automorphism of `π₁ᵉᵗ(V, η)`.

* `isConjInduced_coverAutConj_stabQuot`: for a finite group `ρ : G →* Aut V` (injective),
  `b = q(p)` the image in the quotient `V / G` and `σ ∈ stabilizer b`, the conjugation `c_σ` is
  induced by `(ρ g).hom.left` with `g = stabQuotHom σ` (recall `σ • p = ρ(g)⁻¹ • p`).
-/

open CategoryTheory PreGaloisCategory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section QuotConj

variable {U V : Scheme.{u}} {f : V ⟶ U} [IsFiniteEtale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ V) {η' : Spec (.of Ω) ⟶ U} (h : η ≫ f = η')

omit [IsSepClosed Ω] in
include h in
/-- The point `η ≫ ψ` lies over `η'` for an endomorphism `ψ` of `V` over `U`. -/
lemma coverPtComp_spec (ψ : coverObj f ⟶ coverObj f) : (η ≫ ψ.left) ≫ f = η' :=
  have hψ : ψ.left ≫ f = f := Over.w ψ.hom
  (Category.assoc _ _ _).trans ((congrArg (η ≫ ·) hψ).trans h)

/-- An endomorphism `ψ` of `V` over `U` maps the point `η` of the fibre to the point `η ≫ ψ`. -/
lemma map_coverPt_eq_coverPt (ψ : coverObj f ⟶ coverObj f) :
    (fiber η').map ψ (coverPt f η h) = coverPt f (η ≫ ψ.left) (coverPtComp_spec η h ψ) := by
  rw [coverPt, fiberObjEquivHom_symm_naturality]
  rfl

/-- `pullbackFiberIso` maps the diagonal point to the cover point, for any base point. -/
lemma pullbackFiberIso_hom_app_diagPt' :
    (pullbackFiberIso f h).hom.app (coverObj f) (diagPt f η) = coverPt f η h := by
  subst h
  exact pullbackFiberIso_hom_app_diag f η

/-- An isomorphism of fibre functors of `FiniteEtale V` preserves the diagonal points. -/
lemma iso_hom_app_diagPt {ζ : Spec (.of Ω) ⟶ V} (γ : fiber ζ ≅ fiber η) :
    γ.hom.app ((pullback f).obj (coverObj f)) (diagPt f ζ) = diagPt f η := by
  unfold diagPt
  rw [NatTrans.naturality_apply γ.hom (diagHom f)]
  haveI := subsingleton_fiber_id η
  congr 1
  exact Subsingleton.elim _ _

/-- The change of base point `fiberIsoMap f h₀ h γ` maps the cover point at `ζ` to the cover
point at `η`. -/
lemma fiberIsoMap_hom_app_coverPt {ζ : Spec (.of Ω) ⟶ V} (h₀ : ζ ≫ f = η')
    (γ : fiber ζ ≅ fiber η) :
    (fiberIsoMap f h₀ h γ).hom.app (coverObj f) (coverPt f ζ h₀) = coverPt f η h := by
  have hi : (pullbackFiberIso f h₀).inv.app (coverObj f) (coverPt f ζ h₀) = diagPt f ζ := by
    rw [← pullbackFiberIso_hom_app_diagPt' ζ h₀]
    exact FintypeCat.hom_inv_id_apply ((pullbackFiberIso f h₀).app (coverObj f)) _
  change (pullbackFiberIso f h).hom.app (coverObj f)
    (γ.hom.app ((pullback f).obj (coverObj f))
      ((pullbackFiberIso f h₀).inv.app (coverObj f) (coverPt f ζ h₀))) = _
  rw [hi, iso_hom_app_diagPt, pullbackFiberIso_hom_app_diagPt']

/-- If `σ • p = φ(p)` then `σ⁻¹ • p = φ⁻¹(p)`. -/
lemma inv_smul_coverPt (φ : coverObj f ≅ coverObj f) {σ : π₁ᵉᵗ(η')}
    (hσ : σ • coverPt f η h = (fiber η').map φ.hom (coverPt f η h)) :
    σ⁻¹ • coverPt f η h = (fiber η').map φ.inv (coverPt f η h) := by
  have e : (fiber η').map φ.inv ((fiber η').map φ.hom (coverPt f η h)) = coverPt f η h :=
    FintypeCat.hom_inv_id_apply ((fiber η').mapIso φ) _
  calc σ⁻¹ • coverPt f η h = σ⁻¹ • (fiber η').map φ.inv (σ • coverPt f η h) := by rw [hσ, e]
    _ = (fiber η').map φ.inv (coverPt f η h) := by
      rw [mulAction_naturality, inv_smul_smul]

/-- **A lift `σ` of an automorphism `φ` normalises `π₁ᵉᵗ(V, η)`**: if `σ • p = φ(p)` then
`σ * s * σ⁻¹` fixes `p` for every `s` fixing `p`. -/
theorem conj_mem_coverSubgroup_of_smul (φ : coverObj f ≅ coverObj f) {σ : π₁ᵉᵗ(η')}
    (hσ : σ • coverPt f η h = (fiber η').map φ.hom (coverPt f η h)) {s : π₁ᵉᵗ(η')}
    (hs : s ∈ coverSubgroup f η h) : σ * s * σ⁻¹ ∈ coverSubgroup f η h := by
  have hs' : s • coverPt f η h = coverPt f η h := hs
  have e : (fiber η').map φ.inv ((fiber η').map φ.hom (coverPt f η h)) = coverPt f η h :=
    FintypeCat.hom_inv_id_apply ((fiber η').mapIso φ) _
  change (σ * s * σ⁻¹) • coverPt f η h = coverPt f η h
  rw [mul_smul, mul_smul, inv_smul_coverPt η h φ hσ, mulAction_naturality, hs',
    mulAction_naturality, hσ, e]

variable [ConnectedSpace V]

/-- **Conjugation by a normalising element `σ`, as an endomorphism of `π₁ᵉᵗ(V, η)`**:
`f_* (coverAutConj σ τ) = σ * f_* τ * σ⁻¹`. -/
def coverAutConj (σ : π₁ᵉᵗ(η'))
    (hσ : ∀ s ∈ coverSubgroup f η h, σ * s * σ⁻¹ ∈ coverSubgroup f η h) :
    π₁ᵉᵗ(η) →ₜ* π₁ᵉᵗ(η) :=
  have hmem : ∀ τ, σ * fundamentalGroupMap f h τ * σ⁻¹ ∈
      (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) := fun τ ↦ hσ _ (by
    have hτ : fundamentalGroupMap f h τ ∈ (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) := by
      rw [← range_fundamentalGroupMap_eq_coverSubgroup]
      exact ⟨τ, rfl⟩
    exact hτ)
  let k : π₁ᵉᵗ(η) →ₜ* (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) :=
    { toMonoidHom := ((MulAut.conj σ).toMonoidHom.comp
        (fundamentalGroupMap f h).toMonoidHom).codRestrict _ hmem
      continuous_toFun := ((continuous_const.mul (map_continuous (fundamentalGroupMap f h))).mul
        continuous_const).subtype_mk _ }
  (ContinuousMonoidHom.toContinuousMonoidHom (coverEquiv f η h).symm).comp k

/-- The defining property of `coverAutConj`. -/
theorem fundamentalGroupMap_coverAutConj (σ : π₁ᵉᵗ(η'))
    (hσ : ∀ s ∈ coverSubgroup f η h, σ * s * σ⁻¹ ∈ coverSubgroup f η h) (τ : π₁ᵉᵗ(η)) :
    fundamentalGroupMap f h (coverAutConj η h σ hσ τ) =
      σ * fundamentalGroupMap f h τ * σ⁻¹ := by
  rw [← coe_coverEquiv_apply]
  exact congrArg Subtype.val ((coverEquiv f η h).apply_symm_apply _)

/-- **Main theorem: conjugation by a lift `σ` of `φ` is induced by `φ⁻¹`.** If
`σ • p = φ(p)` for the point `p = coverPt f η h`, then the conjugation `c_σ` of
`π₁ᵉᵗ(V, η)` (`f_* (c_σ τ) = σ * f_* τ * σ⁻¹`) is `π₁ᵉᵗ(φ.inv.left)` followed by a change of
base point `fiber (η ≫ φ.inv.left) ≅ fiber η`. -/
theorem isConjInduced_coverAutConj (φ : coverObj f ≅ coverObj f) {σ : π₁ᵉᵗ(η')}
    (hσ : σ • coverPt f η h = (fiber η').map φ.hom (coverPt f η h)) :
    IsConjInduced φ.inv.left
      (coverAutConj η h σ fun _ hs ↦ conj_mem_coverSubgroup_of_smul η h φ hσ hs) := by
  haveI : ConnectedSpace (coverObj f).left := ‹ConnectedSpace V›
  obtain ⟨γ₀⟩ := nonempty_iso_of_fiberFunctor (fiber (η ≫ φ.inv.left)) (fiber η)
  rw [isConjInduced_iff_exists_conj φ.inv.left γ₀]
  have h₀ : (η ≫ φ.inv.left) ≫ f = η' := coverPtComp_spec η h φ.inv
  set δ : π₁ᵉᵗ(η') := fiberIsoMap f h₀ h γ₀ with hδdef
  have hδ : δ • coverPt f (η ≫ φ.inv.left) h₀ = coverPt f η h :=
    fiberIsoMap_hom_app_coverPt η h h₀ γ₀
  have hmem : σ * δ⁻¹ ∈ (fundamentalGroupMap f h).toMonoidHom.range := by
    rw [range_fundamentalGroupMap_eq_coverSubgroup]
    have h1 : δ⁻¹ • coverPt f η h = (fiber η').map φ.inv (coverPt f η h) := by
      rw [map_coverPt_eq_coverPt]
      exact inv_smul_eq_iff.mpr hδ.symm
    change (σ * δ⁻¹) • coverPt f η h = coverPt f η h
    rw [mul_smul, h1, mulAction_naturality, hσ]
    exact FintypeCat.hom_inv_id_apply ((fiber η').mapIso φ) _
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t, fun τ ↦ fundamentalGroupMap_injective_of_isFiniteEtale' f η h ?_⟩
  have hfφ : φ.inv.left ≫ f = f := Over.w φ.inv.hom
  have h₂ : η ≫ φ.inv.left ≫ f = η' := (Category.assoc _ _ _).symm.trans h₀
  have hc : fundamentalGroupMap f h₀ (fundamentalGroupMap φ.inv.left rfl τ) =
      fundamentalGroupMap f h τ := by
    have c := (DFunLike.congr_fun (fundamentalGroupMap_comp φ.inv.left f rfl h₀ h₂) τ).symm
    rw [fundamentalGroupMap_congr hfφ h₂ h] at c
    exact c
  have hγ : fundamentalGroupMap f h
      (autContinuousMulEquivOfIso γ₀ (fundamentalGroupMap φ.inv.left rfl τ)) =
        δ * fundamentalGroupMap f h τ * δ⁻¹ :=
    (fundamentalGroupMap_autContinuousMulEquivOfIso f h₀ h γ₀ _).trans
      ((congrArg (autContinuousMulEquivOfIso δ) hc).trans (Aut_conjAut_eq δ _))
  have ht' : fundamentalGroupMap f h t = σ * δ⁻¹ := ht
  have key : ∀ x, fundamentalGroupMap f h x = δ * fundamentalGroupMap f h τ * δ⁻¹ →
      σ * fundamentalGroupMap f h τ * σ⁻¹ = fundamentalGroupMap f h (t * x * t⁻¹) := by
    intro x hx
    rw [map_mul, map_mul, map_inv, hx, ht']
    group
  exact (fundamentalGroupMap_coverAutConj η h σ _ τ).trans (key _ hγ)

variable [ConnectedSpace U] {G : Type*} [Group G] [Finite G] {ρ : G →* Aut (coverObj f)}

/-- **Specialisation to Galois quotients.** For an injective `ρ : G →* Aut V` from a finite
group, `b = q(p)` the image of `p = coverPt f η h` in the quotient `V / G`, and
`σ ∈ stabilizer b` with `g = stabQuotHom σ` (so `σ • p = ρ(g)⁻¹ • p`), the conjugation `c_σ` of
`π₁ᵉᵗ(V, η)` is induced by the automorphism `(ρ g).hom.left` of `V`. -/
theorem isConjInduced_coverAutConj_stabQuot (hρ : Function.Injective ρ)
    {b : (fiber η').obj (qObj ρ)} (hb : (fiber η').map (qMap ρ) (coverPt f η h) = b)
    (σ : MulAction.stabilizer π₁ᵉᵗ(η') b) :
    IsConjInduced (ρ (stabQuotHom (fiber η') (coverPt f η h) hb hρ σ)).hom.left
      (coverAutConj η h (σ : π₁ᵉᵗ(η')) fun _ hs ↦ conj_mem_coverSubgroup_of_smul η h
        (ρ (stabQuotHom (fiber η') (coverPt f η h) hb hρ σ)⁻¹)
        (smul_eq_stabQuotHom (fiber η') (coverPt f η h) hb hρ σ) hs) := by
  refine (isConjInduced_coverAutConj η h _
    (smul_eq_stabQuotHom (fiber η') (coverPt f η h) hb hρ σ)).congr_hom ?_
  rw [map_inv]
  rfl

end QuotConj

end CurvesJacobian.Cusp
