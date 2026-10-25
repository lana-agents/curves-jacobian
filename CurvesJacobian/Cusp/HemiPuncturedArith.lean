/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiConstArith
import CurvesJacobian.Cusp.HemiPuncturedConst
import CurvesJacobian.Cusp.EllipticChainEN
import CurvesJacobian.Cusp.WeierAutVNE

/-!
# `Π_{U_V}` is the arithmetic `π₁` of `U_V = (E ∖ E[N])_M`, compatibly with filling (MR8)

Let `E` be an elliptic curve over a number field `K`, `N ≥ 1`, `Ω = K(Ē)^alg` and `M ⊆ K̄` a
finite Galois extension of `K`. In `HemiPuncturedConst` the groups `Π_{U_V}` (for
`U_V = (E ∖ E[N])_M`, `hemiDataNM E N M`) and `Π_V` (for `V = X_M = (E ∖ {O})_M`,
`hemiDataM E M`) and the filling `hemiFillNM : Π_{U_V} ↠ Π_V` are defined in Galois form
(`H_L ⧸ ⟨⟨S⟩⟩`), and `HemiConstArith` identifies `Π_V` with cj's arithmetic fundamental group of
`X_M` (`hemiMPiXGal`). This file does the same for `U_V` and shows that the Galois-form filling is
cj's scheme filling `fillPiHom` of `(E ∖ E[N])_M ⊆ (E ∖ {O})_M` up to an inner automorphism
([AbsTopII] Cor. 3.3 (iii), IUT I Def. 3.1 (b), Rem. 3.1.7 (i)).

## Main statements

Generic:

* `CurvesJacobian.Cusp.equivPi1Spec_fill₃`: for a ring map `R₂ → R₁` compatible with the
  embeddings into `Ω`, `π₁ᵉᵗ(Spec R₁) → π₁ᵉᵗ(Spec R₂)` sends the class of `σ₁` to the class of
  any `σ₂` with the same underlying automorphism of `Ω` (naturality of the generic-point Galois
  action).
* `CurvesJacobian.Cusp.exists_conj_of_isConjInduced_iso₃`: transport of a map induced by
  `g : Y₁ ⟶ Y₂` up to a change of base point along isomorphisms `X_j ≅ Y_j`.
* `CurvesJacobian.Cusp.exists_piXGalG₃_fill`: for hyperbolic curves `W₁, W₂` over `M` with
  `Γ(W_j) ≅ R_j` and `r : Γ(W₂) → Γ(W₁)` compatible with `Ω`, every map `Π_{W₁} → Π_{W₂}` induced
  by `Spec r` is, under `piXGalG₃`, the Galois-form map up to an inner automorphism.
* `CurvesJacobian.Cusp.constCompat_of_res₃`: compatibility with the constants descends along
  `M`-algebra maps.

For the hemi-elliptic orbicurve:

* `CurvesJacobian.Cusp.hemiNMPiXGal`: `Π_{U_V} ≃ₜ* (H_L ⊓ Gal(Ω/M)) ⧸ ⟨⟨S_τ⟩⟩`, with
  `hemiNMGkEquiv_pr` (`pr` is the restriction to the constants).
* `CurvesJacobian.Cusp.hemiNM_fillPiHom_conj`: the scheme filling `hemiFillPiNM₃` (cj's
  `fillPiHom` of `(E ∖ E[N])_M ⊆ (E ∖ {O})_M`) is `hemiFillNM` up to an inner automorphism of
  `Π_V`. Together with `HemiPuncturedConst` (`hemiFillN_surjective`, `comap_hemiFillN_range`,
  `hemiFillNM_surjective`, `hemiFillN_infInclC₃`) this is the square
  `Π_{U_V} ⊆ Π_{U_X} ↠ Π_C ⊇ Π_V` of [AbsTopII] Cor. 3.3 (iii) with `Π_{U_V}`, `Π_V` the
  arithmetic fundamental groups of `(E ∖ E[N])_M` and `(E ∖ {O})_M`.

The hemi-specific statements are kept few: their types mention `M ⊆ ConstField₂ K Ω` many times,
and the olean serialization of such types is slow (their expression trees are exponentially
larger than their DAGs).

No hypotheses beyond the data; no DGC input.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Orbifold AffOrbicurve
open PreGaloisCategory Topology Belyi Belyi.Anabelian Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section GaloisFillGen

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
  (D₁ : GaloisData k t₁) (D₂ : GaloisData k t₂) (f : D₂.R →+* D₁.R)
  (hf : ∀ r, algebraMap D₁.R Ω (f r) = algebraMap D₂.R Ω r)

include hf in
/-- A ring map `R₂ → R₁` compatible with the embeddings into `Ω` maps base points. -/
lemma specPoint_comp_fill₃ :
    specPoint D₁.R Ω ≫ Spec.map (CommRingCat.ofHom f) = specPoint D₂.R Ω := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact hf r

variable [IsAlgClosed Ω] [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω]

/-- **The Galois actions through the generic points are compatible with `Spec R₁ → Spec R₂`**:
`σ₁ ∈ H_{L,1}` and `σ₂ ∈ H_{L,2}` with the same underlying automorphism of `Ω` correspond. -/
theorem fundamentalGroupMap_galoisHomL_fill₃ (σ₁ : D₁.HL) (σ₂ : D₂.HL)
    (hσ : ∀ a, (σ₁ : Ω ≃ₐ[K₀ k t₁] Ω) a = (σ₂ : Ω ≃ₐ[K₀ k t₂] Ω) a) :
    fundamentalGroupMap (Spec.map (CommRingCat.ofHom f)) (specPoint_comp_fill₃ D₁ D₂ f hf)
      (D₁.galoisHomL σ₁) = D₂.galoisHomL σ₂ := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap D₁.L Ω)) ≫ D₁.genericPoint ≫
      Spec.map (CommRingCat.ofHom f) = specPoint D₂.R Ω := by
    rw [← Category.assoc, D₁.genericPoint_comp]
    exact specPoint_comp_fill₃ D₁ D₂ f hf
  refine (fundamentalGroupMap_galoisAction D₁.L D₁.genericPoint _ D₁.genericPoint_comp
    (specPoint_comp_fill₃ D₁ D₂ f hf) h (D₁.toGalL σ₁)).trans ?_
  exact galoisAction_eq_of_apply_eq D₁.L _ _ h D₂.genericPoint_comp _ _ hσ

variable [CharZero k]

/-- **`π₁ᵉᵗ(Spec R₁) → π₁ᵉᵗ(Spec R₂)` in the Galois form** (`H_i ≤ H_{L,i}`): the class of
`σ₁ ∈ H₁` goes to the class of any `σ₂ ∈ H₂` with the same underlying automorphism of `Ω`. -/
theorem equivPi1Spec_fill₃ (hH₁ : D₁.H ≤ D₁.HL) (hH₂ : D₂.H ≤ D₂.HL) (σ₁ : D₁.H) (σ₂ : D₂.H)
    (hσ : ∀ a, (σ₁ : Ω ≃ₐ[K₀ k t₁] Ω) a = (σ₂ : Ω ≃ₐ[K₀ k t₂] Ω) a) :
    D₂.equivPi1Spec hH₂ (fundamentalGroupMap (Spec.map (CommRingCat.ofHom f))
      (specPoint_comp_fill₃ D₁ D₂ f hf) ((D₁.equivPi1Spec hH₁).symm
        (QuotientGroup.mk (s := GaloisPi1.kernel D₁.H D₁.S) σ₁))) =
      QuotientGroup.mk (s := GaloisPi1.kernel D₂.H D₂.S) σ₂ := by
  rw [GaloisData.equivPi1Spec_symm_mk, GaloisData.galoisHom_apply,
    fundamentalGroupMap_galoisHomL_fill₃ D₁ D₂ f hf _ (Subgroup.inclusion hH₂ σ₂) hσ,
    ← GaloisData.galoisHom_apply, ← GaloisData.equivPi1Spec_symm_mk]
  exact ContinuousMulEquiv.apply_symm_apply _ _

end GaloisFillGen

section ConjIsoGen

/-! ### Generic form: transporting an induced map along isomorphisms of schemes -/

variable {X₁ X₂ Y₁ Y₂ : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω']

omit [IsSepClosed Ω] in
/-- Naturality of `π₁ᵉᵗ` for a commutative square `i₁ ≫ g = f ≫ i₂`. -/
lemma fundamentalGroupMap_square₃ (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (hsq : i₁ ≫ g = f ≫ i₂) {x₁ : Spec (.of Ω) ⟶ X₁} {x₂ : Spec (.of Ω) ⟶ X₂}
    (hx : x₁ ≫ f = x₂) (hρ : (x₁ ≫ i₁) ≫ g = x₂ ≫ i₂) (τ : π₁ᵉᵗ(x₁)) :
    fundamentalGroupMap g hρ (fundamentalGroupMap i₁ rfl τ) =
      fundamentalGroupMap i₂ rfl (fundamentalGroupMap f hx τ) := by
  have h13 : x₁ ≫ i₁ ≫ g = x₂ ≫ i₂ := by rw [← Category.assoc]; exact hρ
  have h23 : x₁ ≫ f ≫ i₂ = x₂ ≫ i₂ := by rw [← Category.assoc, hx]
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp i₁ g rfl hρ h13) τ
  have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp f i₂ hx rfl h23) τ
  have c3 := DFunLike.congr_fun (fundamentalGroupMap_congr hsq h13 h23) τ
  exact c1.symm.trans (c3.trans c2)

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
/-- **Transport of an induced map along isomorphisms.** Let `i_j : X_j ≅ Y_j`, `f : X₁ ⟶ X₂`,
`g : Y₁ ⟶ Y₂` with `i₁ ≫ g = f ≫ i₂`, and let `φ : π₁ᵉᵗ(Y₁, y₁) → π₁ᵉᵗ(Y₂, y₂)` be induced by
`g` up to a change of base point. Identifying `π₁ᵉᵗ(Y_j, y_j)` with `π₁ᵉᵗ(X_j, x_j)` through
changes of base point `F_j` and `i_j`, `φ` becomes `π₁ᵉᵗ(f)` up to an inner automorphism. -/
theorem exists_conj_of_isConjInduced_iso₃ (i₁ : X₁ ≅ Y₁) (i₂ : X₂ ≅ Y₂) (f : X₁ ⟶ X₂)
    (g : Y₁ ⟶ Y₂) (hsq : i₁.hom ≫ g = f ≫ i₂.hom) {x₁ : Spec (.of Ω) ⟶ X₁}
    {x₂ : Spec (.of Ω) ⟶ X₂} (hx : x₁ ≫ f = x₂) {y₁ : Spec (.of Ω') ⟶ Y₁}
    {y₂ : Spec (.of Ω') ⟶ Y₂} (F₁ : fiber y₁ ≅ fiber (x₁ ≫ i₁.hom))
    (F₂ : fiber y₂ ≅ fiber (x₂ ≫ i₂.hom)) {φ : π₁ᵉᵗ(y₁) → π₁ᵉᵗ(y₂)}
    (hφ : IsConjInduced g φ) :
    ∃ t : π₁ᵉᵗ(x₂), ∀ γ, (fundamentalGroupEquivOfIso i₂ x₂).symm
      (autContinuousMulEquivOfIso F₂ (φ γ)) = t * fundamentalGroupMap f hx
        ((fundamentalGroupEquivOfIso i₁ x₁).symm (autContinuousMulEquivOfIso F₁ γ)) * t⁻¹ := by
  obtain ⟨c, hc⟩ := hφ
  have hρ : (x₁ ≫ i₁.hom) ≫ g = x₂ ≫ i₂.hom := by
    rw [Category.assoc, hsq, ← Category.assoc, hx]
  obtain ⟨B, hB⟩ : ∃ B : π₁ᵉᵗ(x₂ ≫ i₂.hom), fiberIsoMap g rfl hρ F₁ ≪≫ B = c ≪≫ F₂ :=
    ⟨_, Iso.self_symm_id_assoc _ _⟩
  refine ⟨(fundamentalGroupEquivOfIso i₂ x₂).symm B, fun γ => ?_⟩
  set τ := (fundamentalGroupEquivOfIso i₁ x₁).symm (autContinuousMulEquivOfIso F₁ γ)
  have hτ : fundamentalGroupMap i₁.hom rfl τ = autContinuousMulEquivOfIso F₁ γ :=
    (fundamentalGroupEquivOfIso i₁ x₁).apply_symm_apply _
  have s2 := fundamentalGroupMap_autContinuousMulEquivOfIso g rfl hρ F₁ γ
  have s3 : autContinuousMulEquivOfIso F₂ (φ γ) =
      B * fundamentalGroupMap g hρ (autContinuousMulEquivOfIso F₁ γ) * B⁻¹ :=
    calc autContinuousMulEquivOfIso F₂ (φ γ)
        = F₂.conjAut (c.conjAut (fundamentalGroupMap g rfl γ)) :=
          congrArg (autContinuousMulEquivOfIso F₂) (hc γ)
      _ = (c ≪≫ F₂).conjAut (fundamentalGroupMap g rfl γ) := (Iso.trans_conjAut _ _ _).symm
      _ = (fiberIsoMap g rfl hρ F₁ ≪≫ B).conjAut (fundamentalGroupMap g rfl γ) :=
          congrArg (fun i => Iso.conjAut i (fundamentalGroupMap g rfl γ)) hB.symm
      _ = B.conjAut (autContinuousMulEquivOfIso (fiberIsoMap g rfl hρ F₁)
            (fundamentalGroupMap g rfl γ)) := Iso.trans_conjAut _ _ _
      _ = B.conjAut (fundamentalGroupMap g hρ (autContinuousMulEquivOfIso F₁ γ)) :=
          congrArg B.conjAut s2.symm
      _ = _ := Aut_conjAut_eq _ _
  have s4 : fundamentalGroupMap g hρ (autContinuousMulEquivOfIso F₁ γ) =
      fundamentalGroupEquivOfIso i₂ x₂ (fundamentalGroupMap f hx τ) :=
    (congrArg (fundamentalGroupMap g hρ) hτ.symm).trans
      (fundamentalGroupMap_square₃ i₁.hom i₂.hom f g hsq hx hρ τ)
  rw [ContinuousMulEquiv.symm_apply_eq, map_mul, map_mul, map_inv,
    ContinuousMulEquiv.apply_symm_apply, s3, s4]

end ConjIsoGen

section ArithFillGen

/-! ### Generic form: an open immersion `W₁ ⊆ W₂` of hyperbolic curves over `M` -/

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
  (D₁ : GaloisData k t₁) (D₂ : GaloisData k t₂)
  (M : IntermediateField k (ConstField₂ k Ω)) [NumberField M]
  (W₁ W₂ : HypCurve M) (hW₁ : (W₁.U : Set W₁.Xbar)ᶜ.Nonempty)
  (hW₂ : (W₂.U : Set W₂.Xbar)ᶜ.Nonempty)
  (e₁ : Γ(W₁.Xbar, W₁.U) ≃+* D₁.R) (e₂ : Γ(W₂.Xbar, W₂.U) ≃+* D₂.R)
  (r : Γ(W₂.Xbar, W₂.U) →+* Γ(W₁.Xbar, W₁.U))

/-- The ring map `R₂ ≅ Γ(W₂) → Γ(W₁) ≅ R₁` induced by `r`. -/
abbrev fillRingG₃ : D₂.R →+* D₁.R := e₁.toRingHom.comp (r.comp e₂.symm.toRingHom)

omit [NumberField M] in
lemma specIsoG₃_fill : (specIsoG₃ D₁ M W₁ e₁).hom ≫ Spec.map (CommRingCat.ofHom r) =
    Spec.map (CommRingCat.ofHom (fillRingG₃ D₁ D₂ M W₁ W₂ e₁ e₂ r)) ≫
      (specIsoG₃ D₂ M W₂ e₂).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change e₁ (r x) = e₁ (r (e₂.symm (e₂ x)))
  rw [RingEquiv.symm_apply_apply]

variable (hr : ∀ s, algebraMap D₁.R Ω (e₁ (r s)) = algebraMap D₂.R Ω (e₂ s))

omit [NumberField M] in
include hr in
lemma fillRingG₃_compat (x : D₂.R) :
    algebraMap D₁.R Ω (fillRingG₃ D₁ D₂ M W₁ W₂ e₁ e₂ r x) = algebraMap D₂.R Ω x :=
  (hr _).trans (congrArg (algebraMap D₂.R Ω) (e₂.apply_symm_apply x))

variable [IsAlgClosed Ω] [CharZero k] (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω']
  [Algebra.IsAlgebraic M Ω'] [CharZero Ω']

include hr in
/-- **Filling, generic form.** Let `W₁ ⊆ W₂` be hyperbolic curves over `M` with `Γ(W_i) ≅ R_i`
(Galois data `D_i`), `r : Γ(W₂) → Γ(W₁)` compatible with the embeddings `R_i ⊆ Ω` (`hr`), and
`Ψ : Π_{1} → Π_{2}` (Galois form) sending the class of `σ₁` to the class of some `σ₂` with the
same underlying automorphism of `Ω`. Then every map `φ : Π_{W₁} → Π_{W₂}` induced by `Spec r` up
to a change of base point is `Ψ` up to an inner automorphism, under `piXGalG₃`. -/
theorem exists_piXGalG₃_fill [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω]
    (Ψ : GaloisPi1.pi1 D₁.HL D₁.S D₁.isClosed_HL →* GaloisPi1.pi1 D₂.HL D₂.S D₂.isClosed_HL)
    (hΨ : ∀ σ₁ : D₁.HL, ∃ σ₂ : D₂.HL,
      (∀ a, (σ₁ : Ω ≃ₐ[K₀ k t₁] Ω) a = (σ₂ : Ω ≃ₐ[K₀ k t₂] Ω) a) ∧
        Ψ (QuotientGroup.mk (s := GaloisPi1.kernel D₁.HL D₁.S) σ₁) =
          QuotientGroup.mk (s := GaloisPi1.kernel D₂.HL D₂.S) σ₂)
    {φ : (arithmeticExt Ω' W₁ hW₁).Pi → (arithmeticExt Ω' W₂ hW₂).Pi}
    (hφ : IsConjInduced (Spec.map (CommRingCat.ofHom r)) φ) :
    ∃ x : GaloisPi1.pi1 D₂.HL D₂.S D₂.isClosed_HL, ∀ γ,
      piXGalG₃ D₂ M W₂ hW₂ e₂ Ω' (φ γ) = x * Ψ (piXGalG₃ D₁ M W₁ hW₁ e₁ Ω' γ) * x⁻¹ := by
  have hη := specPoint_comp_fill₃ D₁ D₂ (fillRingG₃ D₁ D₂ M W₁ W₂ e₁ e₂ r)
    (fillRingG₃_compat D₁ D₂ M W₁ W₂ e₁ e₂ r hr)
  obtain ⟨t, ht⟩ := exists_conj_of_isConjInduced_iso₃ (specIsoG₃ D₁ M W₁ e₁)
    (specIsoG₃ D₂ M W₂ e₂) (Spec.map (CommRingCat.ofHom (fillRingG₃ D₁ D₂ M W₁ W₂ e₁ e₂ r)))
    (Spec.map (CommRingCat.ofHom r)) (specIsoG₃_fill D₁ D₂ M W₁ W₂ e₁ e₂ r) hη
    (fiberIsoG₃ D₁ M W₁ hW₁ e₁ Ω') (fiberIsoG₃ D₂ M W₂ hW₂ e₂ Ω') hφ
  have key : ∀ y : GaloisPi1.pi1 D₁.HL D₁.S D₁.isClosed_HL,
      (galoisDataHL D₂).equivPi1Spec (galoisDataHL_H_le D₂)
        (fundamentalGroupMap _ hη (((galoisDataHL D₁).equivPi1Spec
          (galoisDataHL_H_le D₁)).symm y)) = Ψ y := by
    intro y
    obtain ⟨σ₁, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨σ₂, hσ, hΨσ⟩ := hΨ σ₁
    rw [hΨσ]
    exact equivPi1Spec_fill₃ (galoisDataHL D₁) (galoisDataHL D₂)
      (fillRingG₃ D₁ D₂ M W₁ W₂ e₁ e₂ r) (fillRingG₃_compat D₁ D₂ M W₁ W₂ e₁ e₂ r hr)
      (galoisDataHL_H_le D₁) (galoisDataHL_H_le D₂) σ₁ σ₂ hσ
  refine ⟨(galoisDataHL D₂).equivPi1Spec (galoisDataHL_H_le D₂) t, fun γ => ?_⟩
  have s1 : piXGalG₃ D₂ M W₂ hW₂ e₂ Ω' (φ γ) = (galoisDataHL D₂).equivPi1Spec
      (galoisDataHL_H_le D₂) ((fundamentalGroupEquivOfIso (specIsoG₃ D₂ M W₂ e₂)
        (specPoint D₂.R Ω)).symm (autContinuousMulEquivOfIso (fiberIsoG₃ D₂ M W₂ hW₂ e₂ Ω')
          (φ γ))) := rfl
  have s2 : (fundamentalGroupEquivOfIso (specIsoG₃ D₁ M W₁ e₁) (specPoint D₁.R Ω)).symm
      (autContinuousMulEquivOfIso (fiberIsoG₃ D₁ M W₁ hW₁ e₁ Ω') γ) =
      ((galoisDataHL D₁).equivPi1Spec (galoisDataHL_H_le D₁)).symm
        (piXGalG₃ D₁ M W₁ hW₁ e₁ Ω' γ) :=
    (ContinuousMulEquiv.symm_apply_apply _ _).symm
  rw [s1, ht γ]
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl ?_)) (map_inv _ _))
  rw [s2]
  exact key _

end ArithFillGen

/-- **`ConstCompat₃` is inherited along an `M`-algebra map compatible with the embeddings.** -/
lemma constCompat_of_res₃ {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
    {D₁ : GaloisData k t₁} {D₂ : GaloisData k t₂} {M : IntermediateField k (ConstField₂ k Ω)}
    {W₁ W₂ : HypCurve M} {e₁ : Γ(W₁.Xbar, W₁.U) ≃+* D₁.R} {e₂ : Γ(W₂.Xbar, W₂.U) ≃+* D₂.R}
    (r : Γ(W₂.Xbar, W₂.U) →ₐ[M] Γ(W₁.Xbar, W₁.U))
    (hr : ∀ s, algebraMap D₁.R Ω (e₁ (r s)) = algebraMap D₂.R Ω (e₂ s))
    (he₂ : ConstCompat₃ D₂ M W₂ e₂) : ConstCompat₃ D₁ M W₁ e₁ := fun m =>
  (congrArg (fun z => algebraMap D₁.R Ω (e₁ z)) (r.commutes m).symm).trans ((hr _).trans (he₂ m))

section HemiNM

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N] (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E))))
  [FiniteDimensional K M] [IsGalois K M]

/-- **`Γ(U_V) ≅ R_{U_V}`**: `Γ((E ∖ E[N])_M) ≃ M[E][1/ψ_N] ≃ R` (`sectionsVNEEquiv`,
`hemiRNMEquiv`), for `U_V = hypCurveVN (E.baseChange M) N`. -/
def hemiNMRingEquiv₃ : Γ((hypCurveVN (E.baseChange M) N).Xbar,
    (hypCurveVN (E.baseChange M) N).U) ≃+* (hemiDataNM E N M).R :=
  (sectionsVNEEquiv (E.baseChange M) N).trans (hemiRNMEquiv E N M).toRingEquiv

/-- The restriction `Γ(X_M) → Γ(U_V)` along `U_V = (E ∖ E[N])_M ⊆ X_M = (E ∖ {O})_M`. -/
def hemiResNM₃ : Γ((hypCurveX (E.baseChange M)).Xbar, (hypCurveX (E.baseChange M)).U) →ₐ[M]
    Γ((hypCurveVN (E.baseChange M) N).Xbar, (hypCurveVN (E.baseChange M) N).U) :=
  resAlg M (VNE_le_XE (E.baseChange M) N)

omit [NeZero N] [FiniteDimensional K M] [IsGalois K M] in
/-- `Γ(X_M) → Γ(U_V) ≅ M[E][1/ψ_N]` is `M[E] → M[E][1/ψ_N]`. -/
lemma sectionsVNEEquiv_hemiRes₃ (s : Γ((hypCurveX (E.baseChange M)).Xbar,
    (hypCurveX (E.baseChange M)).U)) :
    sectionsVNEEquiv (E.baseChange M) N (resAlg M (VNE_le_XE (E.baseChange M) N) s) =
      algebraMap _ (coverRingN (E.baseChange M) N) (sectionsXEHyp₃ (E.baseChange M) s) :=
  (congrArg (sectionsVNEEquiv (E.baseChange M) N) (resAlg_apply_VNE (E.baseChange M) N s)).trans
    (sectionsVNEEquiv_algebraMap (E.baseChange M) N s)

/-- **The restriction `Γ(X_M) → Γ(U_V)` is the inclusion `R_V ⊆ R_{U_V}` inside `Ω`.** -/
theorem hemiNMRingEquiv₃_res (s : Γ((hypCurveX (E.baseChange M)).Xbar,
    (hypCurveX (E.baseChange M)).U)) :
    algebraMap (hemiDataNM E N M).R (FFClosure (curveE E))
      (hemiNMRingEquiv₃ E N M (hemiResNM₃ E N M s)) =
      algebraMap (hemiDataM E M).R (FFClosure (curveE E)) (hemiMRingEquiv₃ E M s) := by
  have h1 : hemiNMRingEquiv₃ E N M (hemiResNM₃ E N M s) = hemiRNMEquiv E N M
      (sectionsVNEEquiv (E.baseChange M) N (resAlg M (VNE_le_XE (E.baseChange M) N) s)) := rfl
  have h2 : hemiMRingEquiv₃ E M s = hemiConstREquiv E M (sectionsXEHyp₃ (E.baseChange M) s) :=
    rfl
  exact (congrArg (algebraMap (hemiDataNM E N M).R (FFClosure (curveE E)))
    (h1.trans (congrArg (hemiRNMEquiv E N M) (sectionsVNEEquiv_hemiRes₃ E N M s)))).trans
    ((algebraMap_hemiRNMEquiv_algebraMap E N M _).trans
      (congrArg (algebraMap (hemiDataM E M).R (FFClosure (curveE E))) h2.symm))

/-- **Compatibility with `M`** for `U_V`: `M → Γ(U_V) ≅ R_{U_V} ⊆ Ω` is `m ↦ m`. -/
theorem algebraMap_hemiNMRingEquiv₃ :
    ConstCompat₃ (hemiDataNM E N M) M (hypCurveVN (E.baseChange M) N)
      (hemiNMRingEquiv₃ E N M) :=
  constCompat_of_res₃ (hemiResNM₃ E N M) (hemiNMRingEquiv₃_res E N M)
    (algebraMap_hemiMRingEquiv₃ E M)

variable (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic M Ω']
  [CharZero Ω']

/-- **`Π_{U_V} ≃ₜ* (H_L ⊓ Gal(Ω / M)) ⧸ ⟨⟨S⟩⟩`** for `U_V = (E ∖ E[N])_M`: cj's arithmetic
fundamental group of `hypCurveVN (E.baseChange M) N` is `Π_{U_V}` of `hemiDataNM E N M`. -/
def hemiNMPiXGal :
    (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).Pi ≃ₜ*
    GaloisPi1.pi1 (hemiDataNM E N M).HL (hemiDataNM E N M).S (hemiDataNM E N M).isClosed_HL :=
  piXGalG₃ (hemiDataNM E N M) M (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N) (hemiNMRingEquiv₃ E N M) Ω'

/-- **`G_M ≃ₜ* Gal(k̄ / M)`** for `U_V` (the change of base point of `hemiNMPiXGal`). -/
def hemiNMGkEquiv :
    (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).G ≃ₜ*
    (ConstField₂ K (FFClosure (curveE E)) ≃ₐ[M] ConstField₂ K (FFClosure (curveE E))) :=
  gkEquivG₃ (hemiDataNM E N M) M (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N) (hemiNMRingEquiv₃ E N M)
    (algebraMap_hemiNMRingEquiv₃ E N M) Ω'

/-- **`pr : Π_{U_V} → G_M` is the restriction to the constants**: under `hemiNMPiXGal` and
`hemiNMGkEquiv`, `pr` corresponds to `piConstX (hemiDataNM E N M)`. -/
theorem hemiNMGkEquiv_pr
    (γ : (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).Pi) :
    (hemiNMGkEquiv E N M Ω' ((arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).pr γ)).restrictScalars K =
      piConstX (hemiDataNM E N M) (hemiNMPiXGal E N M Ω' γ) :=
  gkEquivG₃_pr (hemiDataNM E N M) M (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N) (hemiNMRingEquiv₃ E N M)
    (algebraMap_hemiNMRingEquiv₃ E N M) Ω' inf_le_right γ

/-- `hemiFillNM` sends the class of `σ` to the class of the same automorphism of `Ω`. -/
lemma hemiFillNM_mk₃ (σ₁ : (hemiDataNM E N M).HL) :
    ∃ σ₂ : (hemiDataM E M).HL,
      (∀ a, (σ₁ : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (tauN₃ E N))] FFClosure (curveE E)) a =
        (σ₂ : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E)) a) ∧
      hemiFillNM E N M (QuotientGroup.mk (s := GaloisPi1.kernel (hemiDataNM E N M).HL
        (hemiDataNM E N M).S) σ₁) =
        QuotientGroup.mk (s := GaloisPi1.kernel (hemiDataM E M).HL (hemiDataM E M).S) σ₂ :=
  ⟨fillInfHom₃ (hemiDataN E N) (hemiData E) (hemiHHomN E N) (constFixer₃ _ M)
    (isOpen_constFixer₃ M) (constFixer₃_normal M) (constFixer₃ _ M) (isOpen_constFixer₃ M)
    (constFixer₃_normal M) (mem_inf_hemiHHomN E N M) σ₁,
    fun a => (hemiHHomN_apply E N (Subgroup.inclusion (hemiDataNM E N M).le σ₁) a).symm, rfl⟩

/-- cj's scheme filling `Π_{U_V} → Π_{X_M}` of the open immersion
`U_V = (E ∖ E[N])_M ⊆ X_M = (E ∖ {O})_M` (`fillPiHom`, as in
`exists_ellipticCandidate_oncePuncturedN`). -/
def hemiFillPiNM₃ :
    (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).Pi →ₜ*
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi :=
  fillPiHom Ω' (hypCurveVN (E.baseChange M) N) (compl_VNE_nonempty (E.baseChange M) N)
    (VNE_le_XE (E.baseChange M) N) (compl_XE_nonempty (E.baseChange M))
    (hyperbolic_of_le (E.baseChange M) (VE_le_XE (E.baseChange M)) le_rfl)

/-- **[AbsTopII] Cor. 3.3 (iii): the Galois-form filling `Π_{U_V} ↠ Π_V` is the scheme filling.**
Under `hemiNMPiXGal` and `hemiMPiXGal`, cj's `fillPiHom` of `(E ∖ E[N])_M ⊆ (E ∖ {O})_M` is
`hemiFillNM` up to an inner automorphism of `Π_V`. -/
theorem hemiNM_fillPiHom_conj :
    ∃ x : GaloisPi1.pi1 (hemiDataM E M).HL (hemiDataM E M).S (hemiDataM E M).isClosed_HL,
      ∀ γ, hemiMPiXGal E M Ω' (hemiFillPiNM₃ E N M Ω' γ) =
        x * hemiFillNM E N M (hemiNMPiXGal E N M Ω' γ) * x⁻¹ :=
  exists_piXGalG₃_fill (hemiDataNM E N M) (hemiDataM E M) M (hypCurveVN (E.baseChange M) N)
    (hypCurveX (E.baseChange M)) (compl_VNE_nonempty (E.baseChange M) N)
    (compl_XE_nonempty (E.baseChange M)) (hemiNMRingEquiv₃ E N M) (hemiMRingEquiv₃ E M)
    (hemiResNM₃ E N M).toRingHom (hemiNMRingEquiv₃_res E N M) Ω' (hemiFillNM E N M).toMonoidHom
    (hemiFillNM_mk₃ E N M)
    (isConjInduced_fillPiHom Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N) (VNE_le_XE (E.baseChange M) N)
      (compl_XE_nonempty (E.baseChange M))
      (hyperbolic_of_le (E.baseChange M) (VE_le_XE (E.baseChange M)) le_rfl))

end HemiNM

end CurvesJacobian.Cusp
