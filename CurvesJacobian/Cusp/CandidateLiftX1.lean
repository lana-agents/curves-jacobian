/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor37bBelyi
import CurvesJacobian.Cusp.ConjInducedCusps

/-!
# [AbsTopII] Corollary 3.8, the `X₁` side: `Π_U` inside `Π_{U_X}` and lifts (MR8.5)

`Topics in Absolute Anabelian Geometry II.txt` l.4794–4842 (Corollary 3.8) and Corollary 3.7 (b)
(l.4698–4775). Let `X = CX.U` be an affine hyperbolic curve over a number field `K`, `U_X ⊆ X` a
nonempty open, `Π_{U_X} ↠ Π_X` the filling map `cor38Fill`, and `D` Belyi data for `X` with a
stage `U = UW_i ⊆ V = UW_r` of its run of fillings such that `U = V ×_X U_X` (as produced by
`exists_belyiCandidate`), and `V → X` Galois (the hypothesis `hgal`).

* `resSquareFU`, **`isPullback_resSquareFU`**: for affine opens `U₀ ⊆ V₀` and `U_X ⊆ X₀` and a
  finite étale `FV : Spec Γ(V₀) ⟶ Spec Γ(X₀)` with `U₀ = V₀ ×_{X₀} U_X` (the preimage formula),
  the square `Spec Γ(U₀) ⟶ Spec Γ(V₀)`, `FU : Spec Γ(U₀) ⟶ Spec Γ(U_X)` is cartesian and `FU`
  is finite étale (generalising `StrictlyBelyiInput.isPullback_belyiFU`).
* **`exists_candidate_comap_equiv`**: for a cuspidalisation candidate `Π_U ↠ Π_V ↪ Π_X`
  identified with `π₁ᵉᵗ(Spec Γ(U)) → π₁ᵉᵗ(Spec Γ(V)) → Π_X` (`stepHom`, `φ₄`), `Π_U` is
  isomorphic to the preimage of `Π_V` under `Π_{U_X} ↠ Π_X`, compatibly with the projections up
  to an inner automorphism of `Π_X`.
* **`exists_candidate_lift`**: every continuous automorphism of `Π_V` induced by an inner
  automorphism of `Π_X` lifts along `Π_U ↠ Π_V` to a continuous automorphism of `Π_U`
  (the group-theoretic part is `exists_lift_of_comap_equiv`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-! ### Changes of base point and induced maps -/

namespace AlgebraicGeometry.FiniteEtale

section ConjInduced

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- `π₁ᵉᵗ(h)` with an arbitrary target point is induced by `h`. -/
lemma isConjInduced_fundamentalGroupMap₂ (h : X ⟶ Y) {x : Spec (.of Ω) ⟶ X}
    {η : Spec (.of Ω) ⟶ Y} (hη : x ≫ h = η) :
    IsConjInduced h (fundamentalGroupMap h hη) := by
  subst hη
  exact isConjInduced_fundamentalGroupMap h x

/-- The inverse of a change of base point is the change of base point along the inverse. -/
lemma autContinuousMulEquivOfIso_symm_apply₂ {y₁ y₂ : Spec (.of Ω) ⟶ X}
    (α : fiber y₁ ≅ fiber y₂) (σ : π₁ᵉᵗ(y₂)) :
    (autContinuousMulEquivOfIso α).symm σ = autContinuousMulEquivOfIso α.symm σ := by
  apply (autContinuousMulEquivOfIso α).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  change σ = α.conjAut (α.symm.conjAut σ)
  rw [← Iso.trans_conjAut, Iso.symm_self_id, Iso.conjAut_apply]
  ext
  simp

/-- The inverse of a change of base point is induced by the identity. -/
lemma isConjInduced_id_autIso_symm₂ {y₁ y₂ : Spec (.of Ω) ⟶ X} (α : fiber y₁ ≅ fiber y₂) :
    IsConjInduced (𝟙 X) (autContinuousMulEquivOfIso α).symm :=
  (isConjInduced_id_autIso α.symm).congr_fun fun σ ↦ autContinuousMulEquivOfIso_symm_apply₂ α σ

/-- Precomposing with a change of base point keeps a map induced by `h`. -/
lemma IsConjInduced.comp_autIso₂ {h : X ⟶ Y} {x x' : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} {φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H : IsConjInduced h φ)
    (α : fiber x' ≅ fiber x) : IsConjInduced h (φ ∘ autContinuousMulEquivOfIso α) :=
  ((isConjInduced_id_autIso α).comp H).congr_hom (Category.id_comp h)

end ConjInduced

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

/-! ### The cartesian square `U₀ = V₀ ×_{X₀} U_X` -/

section Square

/-- `Spec Γ(V) ⟶ Spec Γ(U)` for opens `U ≤ V`, typed with `Spec Γ`. -/
abbrev resSpecHom₂ (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {U V : X.Opens} (h : U ≤ V) : Spec Γ(X, U) ⟶ Spec Γ(X, V) :=
  Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom)

/-- The images of the two open immersions `Spec Γ(U₀) ⟶ Spec Γ(V₀)`, `Spec Γ(U_X) ⟶ Spec Γ(X₀)`
correspond under `FV`. -/
lemma opensRange_resSquare (k k' : Type u) [Field k] [Field k'] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {Y : Scheme.{u}} [Y.Over (Spec (.of k'))] {X₀ UX : X.Opens}
    {V₀ U₀ : Y.Opens} (hX : IsAffineOpen X₀)
    (hUXa : IsAffineOpen UX) (hUX : UX ≤ X₀) (hV : IsAffineOpen V₀) (hU₀ : IsAffineOpen U₀)
    (hle : U₀ ≤ V₀) (FV : Spec Γ(Y, V₀) ⟶ Spec Γ(X, X₀))
    (hU : U₀ = hV.fromSpec ''ᵁ (FV ⁻¹ᵁ (hX.fromSpec ⁻¹ᵁ UX))) :
    haveI : IsOpenImmersion (resSpecHom₂ k hUX) := isOpenImmersion_specMap_resAlg k hX hUXa hUX
    haveI : IsOpenImmersion (resSpecHom₂ k' hle) := isOpenImmersion_specMap_resAlg k' hV hU₀ hle
    (resSpecHom₂ k' hle).opensRange =
      FV ⁻¹ᵁ (resSpecHom₂ k hUX).opensRange := by
  haveI : IsOpenImmersion (resSpecHom₂ k hUX) := isOpenImmersion_specMap_resAlg k hX hUXa hUX
  haveI : IsOpenImmersion (resSpecHom₂ k' hle) := isOpenImmersion_specMap_resAlg k' hV hU₀ hle
  unfold resSpecHom₂
  rw [opensRange_specMap_resAlg k' hV hU₀ hle, opensRange_specMap_resAlg k hX hUXa hUX]
  ext x
  change hV.fromSpec x ∈ U₀ ↔ _
  rw [hU]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [hV.fromSpec.isOpenEmbedding.injective hyx] at hy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **`U₀ = V₀ ×_{X₀} U_X`: the cover `FU : Spec Γ(U₀) ⟶ Spec Γ(U_X)`.** -/
def resSquareFU (k k' : Type u) [Field k] [Field k'] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {Y : Scheme.{u}} [Y.Over (Spec (.of k'))] {X₀ UX : X.Opens}
    {V₀ U₀ : Y.Opens} (hX : IsAffineOpen X₀)
    (hUXa : IsAffineOpen UX) (hUX : UX ≤ X₀) (hV : IsAffineOpen V₀) (hU₀ : IsAffineOpen U₀)
    (hle : U₀ ≤ V₀) (FV : Spec Γ(Y, V₀) ⟶ Spec Γ(X, X₀))
    (hU : U₀ = hV.fromSpec ''ᵁ (FV ⁻¹ᵁ (hX.fromSpec ⁻¹ᵁ UX))) : Spec Γ(Y, U₀) ⟶ Spec Γ(X, UX) :=
  haveI : IsOpenImmersion (resSpecHom₂ k hUX) := isOpenImmersion_specMap_resAlg k hX hUXa hUX
  haveI : IsOpenImmersion (resSpecHom₂ k' hle) := isOpenImmersion_specMap_resAlg k' hV hU₀ hle
  ((resSpecHom₂ k' hle).isoOpensRange ≪≫
    Scheme.isoOfEq _ (opensRange_resSquare k k' hX hUXa hUX hV hU₀ hle FV hU)).hom ≫
    (FV ∣_ (resSpecHom₂ k hUX).opensRange) ≫
      (resSpecHom₂ k hUX).isoOpensRange.inv

/-- **The square `U₀ = V₀ ×_{X₀} U_X` is cartesian.** -/
theorem isPullback_resSquareFU (k k' : Type u) [Field k] [Field k'] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {Y : Scheme.{u}} [Y.Over (Spec (.of k'))] {X₀ UX : X.Opens}
    {V₀ U₀ : Y.Opens} (hX : IsAffineOpen X₀)
    (hUXa : IsAffineOpen UX) (hUX : UX ≤ X₀) (hV : IsAffineOpen V₀) (hU₀ : IsAffineOpen U₀)
    (hle : U₀ ≤ V₀) (FV : Spec Γ(Y, V₀) ⟶ Spec Γ(X, X₀))
    (hU : U₀ = hV.fromSpec ''ᵁ (FV ⁻¹ᵁ (hX.fromSpec ⁻¹ᵁ UX))) :
    IsPullback (resSpecHom₂ k' hle)
      (resSquareFU k k' hX hUXa hUX hV hU₀ hle FV hU) FV
      (resSpecHom₂ k hUX) := by
  haveI : IsOpenImmersion (resSpecHom₂ k hUX) := isOpenImmersion_specMap_resAlg k hX hUXa hUX
  haveI : IsOpenImmersion (resSpecHom₂ k' hle) := isOpenImmersion_specMap_resAlg k' hV hU₀ hle
  refine (isPullback_morphismRestrict FV
      (resSpecHom₂ k hUX).opensRange).flip.of_iso
    ((resSpecHom₂ k' hle).isoOpensRange ≪≫
      Scheme.isoOfEq _ (opensRange_resSquare k k' hX hUXa hUX hV hU₀ hle FV hU)).symm (Iso.refl _)
    (resSpecHom₂ k hUX).isoOpensRange.symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι]
  · rw [Iso.symm_hom, Iso.symm_hom, resSquareFU, Iso.inv_hom_id_assoc]
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.Hom.isoOpensRange_inv_comp]

instance isFiniteEtale_resSquareFU (k k' : Type u) [Field k] [Field k'] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {Y : Scheme.{u}} [Y.Over (Spec (.of k'))] {X₀ UX : X.Opens}
    {V₀ U₀ : Y.Opens} (hX : IsAffineOpen X₀)
    (hUXa : IsAffineOpen UX) (hUX : UX ≤ X₀) (hV : IsAffineOpen V₀) (hU₀ : IsAffineOpen U₀)
    (hle : U₀ ≤ V₀) (FV : Spec Γ(Y, V₀) ⟶ Spec Γ(X, X₀))
    (hU : U₀ = hV.fromSpec ''ᵁ (FV ⁻¹ᵁ (hX.fromSpec ⁻¹ᵁ UX))) [IsFiniteEtale FV] :
    IsFiniteEtale (resSquareFU k k' hX hUXa hUX hV hU₀ hle FV hU) :=
  MorphismProperty.of_isPullback (P := @IsFiniteEtale)
    (isPullback_resSquareFU k k' hX hUXa hUX hV hU₀ hle FV hU) inferInstance

end Square

/-! ### Group theory -/

section GroupTheory

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- Conjugation by `a` on a normal subgroup, as a continuous isomorphism. -/
def normalConjContinuousEquiv₂ (N : Subgroup P) [hN : N.Normal] (a : P) : N ≃ₜ* N where
  toFun n := ⟨a * n * a⁻¹, hN.conj_mem n n.2 a⟩
  invFun n := ⟨a⁻¹ * n * a⁻¹⁻¹, hN.conj_mem n n.2 a⁻¹⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

lemma coe_continuousSubgroupCongr₂ {G : Type*} [Group G] [TopologicalSpace G]
    {H H' : Subgroup G} (h : H = H') (z : H) : ((continuousSubgroupCongr h z : H') : G) = z := by
  subst h
  rfl

lemma coe_normalConjContinuousEquiv₂ (N : Subgroup P) [N.Normal] (a : P) (n : N) :
    (normalConjContinuousEquiv₂ N a n : P) = a * n * a⁻¹ := rfl

/-- An injective continuous homomorphism `f₃ ∘ f₂ ∘ f₁` of a compact group onto `F⁻¹(N)` gives
`U ≃ₜ* F⁻¹(N)`, keeping `F ∘ f₃ ∘ f₂ ∘ f₁`. -/
theorem exists_comap_equiv_of_injective₂ {U Q₁ Q₂ G : Type*} [Group U] [TopologicalSpace U]
    [IsTopologicalGroup U] [CompactSpace U] [Group Q₁] [TopologicalSpace Q₁] [Group Q₂]
    [TopologicalSpace Q₂] [T2Space P] [Group G] (f₁ : U ≃ₜ* Q₁) (f₂ : Q₁ ≃ₜ* Q₂)
    (f₃ : Q₂ →ₜ* P) (hf₃ : Function.Injective f₃) (F : P →* G) (N : Subgroup G)
    (hrange : ∀ z, (∃ u, f₃ (f₂ (f₁ u)) = z) ↔ F z ∈ N) (R : U → G) (c : G)
    (hc : ∀ u, F (f₃ (f₂ (f₁ u))) = c * R u * c⁻¹) :
    ∃ J : U ≃ₜ* N.comap F, ∀ u, F (J u) = c * R u * c⁻¹ := by
  have hf : Function.Injective ((f₃.comp (ContinuousMonoidHom.toContinuousMonoidHom f₂)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom f₁)) :=
    hf₃.comp (f₂.injective.comp f₁.injective)
  have hr : (((f₃.comp (ContinuousMonoidHom.toContinuousMonoidHom f₂)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom f₁) : U →ₜ* P) : U →* P).range =
        N.comap F := by
    ext z
    exact MonoidHom.mem_range.trans (hrange z)
  exact ⟨(rangeEquiv _ hf).trans (continuousSubgroupCongr hr), fun u ↦
    (congrArg F ((coe_continuousSubgroupCongr₂ hr _).trans (coe_rangeEquiv_apply _ hf u))).trans
      (hc u)⟩

/-- **Lifting automorphisms through `Π_U ≅ f⁻¹(H)`** (group theory): let `f : P ↠ G` be
surjective, `H ⊴ G`, `e : Π_V → G` injective, and `J : Π_U ≃ₜ* f⁻¹(H)` with
`f ∘ J = conj(c) ∘ e ∘ s`. Then every `B` of `Π_V` with `e ∘ B = conj(g) ∘ e` lifts along `s`
to a continuous automorphism of `Π_U`. -/
theorem exists_lift_of_comap_equiv {U V G : Type*} [Group U] [TopologicalSpace U] [Group G]
    (s : U → V) (e : V → G) (he : Function.Injective e) (f : P →* G)
    (hf : Function.Surjective f) (H : Subgroup G) [H.Normal] (c : G) (J : U ≃ₜ* H.comap f)
    (hJ : ∀ u, f (J u) = c * e (s u) * c⁻¹) (B : V → V) (g : G)
    (hB : ∀ v, e (B v) = g * e v * g⁻¹) :
    ∃ ψ : U ≃ₜ* U, ∀ u, s (ψ u) = B (s u) := by
  obtain ⟨a, ha⟩ := hf (c * g * c⁻¹)
  haveI : (H.comap f).Normal := Subgroup.Normal.comap inferInstance f
  refine ⟨(J.trans (normalConjContinuousEquiv₂ (H.comap f) a)).trans J.symm, fun u ↦ he ?_⟩
  have h2 : (J (((J.trans (normalConjContinuousEquiv₂ (H.comap f) a)).trans J.symm) u) : P) =
      a * J u * a⁻¹ := by
    change (J (J.symm (normalConjContinuousEquiv₂ (H.comap f) a (J u))) : P) = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl
  have h3 : c * e (s (((J.trans (normalConjContinuousEquiv₂ (H.comap f) a)).trans J.symm) u)) *
      c⁻¹ = c * e (B (s u)) * c⁻¹ := by
    rw [← hJ, h2, map_mul, map_mul, map_inv, ha, hJ, hB]
    group
  exact mul_left_cancel (mul_right_cancel h3)

end GroupTheory

/-! ### `Π_U` inside `Π_{U_X}` -/

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))
  (D : BelyiData (M := M) CX) (i : Fin (D.r + 1)) (hVa : IsAffineOpen (D.UW (Fin.last D.r)))
  (hU : D.UW i = hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### The `π₁`-square of `U = V ×_X U_X` (generic) -/

section Generic

variable (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens}
  (h : C.U ≤ U') (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral M C.Xbar
    2 < 2 * Anabelian.curveGenus M C.Xbar + cuspDegree M C.Xbar U')
  (FV' : Spec Γ(C.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U))
  (FU : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(CX.Xbar, UX))

/-- **The `π₁`-square of `U ⊆ U'` over `U_X ⊆ X` commutes up to conjugation**: for a
commutative square `U ⟶ U'`, `FU : U ⟶ U_X`, `FV' : U' ⟶ X`, `U_X ⟶ X`, the two maps
`Π_U → Π_X` (`cor38Fill ∘ π₁(FU)` and `π₁(FV') ∘ fillPiHom`) differ by an inner automorphism. -/
theorem exists_conj_cor38Fill_coverPiHom
    (hw : Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) ≫ FV' =
      FU ≫ Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)) :
    ∃ c : (arithmeticExt Ω CX hcX).Pi, ∀ y,
      cor38Fill Ω CX hcX UX hUX hne α₀
          (coverPiHom Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) C hc FU y) =
        c * coverPiHom Ω CX hcX (fillCurve C h hyp) hc' FV' (fillPiHom Ω C hc h hc' hyp y) *
          c⁻¹ := by
  have hcUX : (UX : Set CX.Xbar)ᶜ.Nonempty := compl_nonempty_of_le hUX hcX
  have hU : IsConjInduced FU
      (fun σ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ↦
        (coverPiHom Ω (subCurve CX UX hUX hne) hcUX C hc FU σ :
          π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
            baseChangeSpec K Ω Γ(CX.Xbar, UX)))) :=
    ⟨coverFib Ω (subCurve CX UX hUX hne) hcUX C hc FU, fun _ ↦ rfl⟩
  have hfill : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))
      (fun σ : π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, UX)) ↦
        (cor38Fill Ω CX hcX UX hUX hne α₀ σ :
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) := by
    have hη : (basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
        baseChangeSpec K Ω Γ(CX.Xbar, UX)) ≫
          Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) =
        fillPoint Ω (subCurve CX UX hUX hne) hcUX hUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, CX.U) :=
      fillPoint_spec Ω (subCurve CX UX hUX hne) hcUX hUX
    refine (isConjInduced_iff _ hη _).2 ⟨(fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U))
      rfl rfl α₀).symm, fun σ ↦ ?_⟩
    exact autContinuousMulEquivOfIso_symm_apply₂ _ _
  have hV : IsConjInduced FV'
      (fun σ : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫
          baseChangeSpec M Ω Γ(C.Xbar, U')) ↦
        (coverPiHom Ω CX hcX (fillCurve C h hyp) hc' FV' σ :
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) :=
    ⟨coverFib Ω CX hcX (fillCurve C h hyp) hc' FV', fun _ ↦ rfl⟩
  have hL := hU.comp hfill
  have hR := ((isConjInduced_fillPiHom Ω C hc h hc' hyp).comp hV).congr_hom hw
  exact hL.exists_conj_eq hR

/-- **[AbsTopII] Cor 3.7 (b), generic form**: for a cartesian square `U = U' ×_X U_X` with
`U' → X` Galois, `Π_U ≃ₜ*` the preimage of `im(Π_{U'} → Π_X)` under `Π_{U_X} ↠ Π_X`, via
`π₁(FU)`. -/
theorem exists_continuousMulEquiv_comap_cor38Fill [IsFiniteEtale FV'] [IsFiniteEtale FU]
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV'))
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)) FU FV'
      (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))) :
    ∃ J : (arithmeticExt Ω C hc).Pi ≃ₜ*
        (cor37bPiV Ω CX hcX (fillCurve C h hyp) hc' FV').comap
          (cor38Fill Ω CX hcX UX hUX hne α₀),
      ∀ y, (J y : (arithmeticExt Ω (subCurve CX UX hUX hne)
        (compl_nonempty_of_le hUX hcX)).Pi) =
          coverPiHom Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) C hc FU y := by
  have hcomap := cor37b_comap Ω CX hcX UX hUX hne α₀ (fillCurve C h hyp) hc' FV' C hc FU
    (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)) hgal hsq
  have hinj := coverPiHom_injective Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)
    C hc FU
  refine ⟨(rangeEquiv _ hinj).trans (continuousSubgroupCongr hcomap), fun y ↦ ?_⟩
  exact coe_continuousSubgroupCongr₂ hcomap (rangeEquiv _ hinj y)

end Generic

namespace BelyiData

include hne hU in
/-- **`U = V ×_X U_X`: the cover `FU : U ⟶ U_X`** for a stage `U = UW_i` of the run of
fillings of `D` given by the preimage formula. -/
def candFU : Spec Γ(D.CW.Xbar, D.UW i) ⟶ Spec Γ(CX.Xbar, UX) :=
  resSquareFU K M (isAffineOpen_U CX hcX)
    (isAffineOpen_U (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)) hUX hVa
    (isAffineOpen_of_le D.CW (D.hleW i) (D.hcUW i)) (D.monoW (Fin.le_last i)) D.FV hU

include hne hU in
instance isFiniteEtale_candFU : IsFiniteEtale (D.candFU CX hcX UX hUX hne i hVa hU) :=
  isFiniteEtale_resSquareFU K M _ _ _ _ _ _ _ _

include hne hU in
/-- **The square `U = V ×_X U_X` is cartesian.** -/
theorem isPullback_candFU :
    IsPullback (Spec.map (CommRingCat.ofHom (resAlg M (D.monoW (Fin.le_last i))).toRingHom))
      (D.candFU CX hcX UX hUX hne i hVa hU) D.FV
      (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)) :=
  isPullback_resSquareFU K M _ _ _ _ _ _ _ _

end BelyiData

/-- `im(Π_V ↪ Π_X) = im(π₁(FV))` for a candidate identified with `φ₄`. -/
lemma candidate_range_emb (x : CuspCandidate (arithmeticExt Ω CX hcX))
    (eV : x.PiV ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))
    (he : ∀ y, x.emb y = D.φ₄ Ω hcX (eV y)) :
    x.emb.toMonoidHom.range = cor37bPiV Ω CX hcX D.CV D.hcV D.FV := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (he y).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨eV.symm (D.TV Ω w), ?_⟩
    change x.emb _ = D.φ₁ Ω hcX w
    rw [he, ContinuousMulEquiv.apply_symm_apply]
    change D.φ₁ Ω hcX ((D.TV Ω).symm (D.TV Ω w)) = D.φ₁ Ω hcX w
    rw [ContinuousMulEquiv.symm_apply_apply]

/-- `exists_candidate_comap_equiv` for an arbitrary finite étale `FU : U ⟶ U_X` making
`U = V ×_X U_X` cartesian. -/
theorem exists_candidate_comap_equiv_of_isPullback
    (FU : Spec Γ(D.CW.Xbar, D.UW i) ⟶ Spec Γ(CX.Xbar, UX)) [IsFiniteEtale FU]
    (hsq : IsPullback
      (Spec.map (CommRingCat.ofHom (resAlg M (D.monoW (Fin.le_last i))).toRingHom)) FU D.FV
      (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV))
    (x : CuspCandidate (arithmeticExt Ω CX hcX))
    (eU : x.PiU ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)))
    (eV : x.PiV ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))
    (hs : ∀ u, eV (x.surj u) = D.stepHom Ω i (Fin.last D.r) (Fin.le_last _) (eU u))
    (he : ∀ y, x.emb y = D.φ₄ Ω hcX (eV y)) :
    ∃ (c : (arithmeticExt Ω CX hcX).Pi)
      (J : x.PiU ≃ₜ* (x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀))),
      ∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) = c * x.emb (x.surj u) * c⁻¹ := by
  have hcUX : (UX : Set CX.Xbar)ᶜ.Nonempty := compl_nonempty_of_le hUX hcX
  -- the cartesian square and Cor 3.7 (b)
  have hcomap := cor37b_comap Ω CX hcX UX hUX hne α₀ D.CV D.hcV D.FV
    (fillCurve D.CW (D.hleW i) (D.hypW i)) (D.hcUW i) (FU)
    (Spec.map (CommRingCat.ofHom (resAlg M (D.monoW (Fin.le_last i))).toRingHom)) hgal hsq
  -- `Ψ : π₁ᵉᵗ(Spec Γ(U), fillPoint) → Π_{U_X}`
  have hΨ : IsConjInduced (FU)
      (fun σ : π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)) ↦
        (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (fillCurve D.CW (D.hleW i) (D.hypW i))
          (D.hcUW i) (FU)
          ((fillTransport Ω D.CW D.hcW (D.hleW i) (D.hcUW i) (D.hypW i)).symm σ) :
          π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
            baseChangeSpec K Ω Γ(CX.Xbar, UX)))) := by
    have H : IsConjInduced (FU)
        (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (fillCurve D.CW (D.hleW i) (D.hypW i))
          (D.hcUW i) (FU)) :=
      ⟨coverFib Ω (subCurve CX UX hUX hne) hcUX (fillCurve D.CW (D.hleW i) (D.hypW i))
        (D.hcUW i) (FU), fun _ ↦ rfl⟩
    exact ((isConjInduced_id_autIso_symm₂ _).comp H).congr_hom (Category.id_comp _)
  -- `cor38Fill` is induced by `U_X ⊆ X`
  have hfill : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))
      (fun σ : π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, UX)) ↦
        (cor38Fill Ω CX hcX UX hUX hne α₀ σ :
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) := by
    have hη : (basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
        baseChangeSpec K Ω Γ(CX.Xbar, UX)) ≫
          Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) =
        fillPoint Ω (subCurve CX UX hUX hne) hcUX hUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, CX.U) :=
      fillPoint_spec Ω (subCurve CX UX hUX hne) hcUX hUX
    refine (isConjInduced_iff _ hη _).2 ⟨(fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U))
      rfl rfl α₀).symm, fun σ ↦ ?_⟩
    exact autContinuousMulEquivOfIso_symm_apply₂ _ _
  have hL := hΨ.comp hfill
  -- the composite `Π_U ↠ Π_V ↪ Π_X` is induced by `U ⊆ V ⟶ X`
  have hstep : IsConjInduced
      (Spec.map (CommRingCat.ofHom (resAlg M (D.monoW (Fin.le_last i))).toRingHom))
      (fun σ : π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)) ↦
        (D.stepHom Ω i (Fin.last D.r) (Fin.le_last _) σ :
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
            baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))) :=
    isConjInduced_fundamentalGroupMap₂ _
      (fillPoint_step Ω D.CW D.hcW (D.hleW i) (D.monoW (Fin.le_last i)))
  have hTV : IsConjInduced (𝟙 _)
      (fun σ : π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))) ↦
        ((D.TV Ω).symm σ : π₁ᵉᵗ(basePoint Ω D.CV D.hcV ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))) :=
    isConjInduced_id_autIso_symm₂ _
  have hφ₁ : IsConjInduced D.FV
      (fun σ : π₁ᵉᵗ(basePoint Ω D.CV D.hcV ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))) ↦
        (D.φ₁ Ω hcX σ : π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) :=
    ⟨coverFib Ω CX hcX D.CV D.hcV D.FV, fun _ ↦ rfl⟩
  have hw : (Spec.map (CommRingCat.ofHom (resAlg M (D.monoW (Fin.le_last i))).toRingHom) ≫
      𝟙 _) ≫ D.FV = FU ≫
        Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) := by
    rw [Category.comp_id]
    exact hsq.w
  have hR := ((hstep.comp hTV).comp hφ₁).congr_hom hw
  obtain ⟨c, hc⟩ := hL.exists_conj_eq hR
  -- the range
  have hrangeV : ∀ z, z ∈ x.emb.toMonoidHom.range ↔
      z ∈ cor37bPiV Ω CX hcX D.CV D.hcV D.FV := fun z ↦ by
    rw [candidate_range_emb Ω CX hcX D x eV he]
  refine ⟨c, ?_⟩
  refine exists_comap_equiv_of_injective₂ eU
    (fillTransport Ω D.CW D.hcW (D.hleW i) (D.hcUW i) (D.hypW i)).symm
    (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (fillCurve D.CW (D.hleW i) (D.hypW i))
      (D.hcUW i) FU) (coverPiHom_injective _ _ _ _ _ _)
    (cor38Fill Ω CX hcX UX hUX hne α₀) x.emb.toMonoidHom.range (fun z ↦ ?_)
    (fun u ↦ x.emb (x.surj u)) c (fun u ↦ ?_)
  · rw [hrangeV, ← Subgroup.mem_comap, ← hcomap]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨eU.symm (fillTransport Ω D.CW D.hcW (D.hleW i) (D.hcUW i) (D.hypW i) w),
        (congrArg (fun t ↦ coverPiHom Ω (subCurve CX UX hUX hne) hcUX
          (fillCurve D.CW (D.hleW i) (D.hypW i)) (D.hcUW i) FU
          ((fillTransport Ω D.CW D.hcW (D.hleW i) (D.hcUW i) (D.hypW i)).symm t))
          (eU.apply_symm_apply _)).trans
        (congrArg (coverPiHom Ω (subCurve CX UX hUX hne) hcUX
          (fillCurve D.CW (D.hleW i) (D.hypW i)) (D.hcUW i) FU)
          ((fillTransport Ω D.CW D.hcW (D.hleW i) (D.hcUW i) (D.hypW i)).symm_apply_apply w))⟩
  · rw [he, hs]
    exact hc (eU u)

include hVa hU in
/-- **[AbsTopII] Cor 3.8 / 3.7 (b), the `X₁` side: `Π_U` is the preimage of `Π_V`.** For Belyi
data `D` with `U = UW_i = V ×_X U_X` and `V → X` Galois, and a candidate `x` identified with
`π₁ᵉᵗ(Spec Γ(U)) → π₁ᵉᵗ(Spec Γ(V)) → Π_X` (`eU`, `eV`, `hs`, `he`), `x.PiU` is isomorphic to
the preimage of `im(x.emb)` under `Π_{U_X} ↠ Π_X`, compatibly with the projections up to an
inner automorphism of `Π_X`. -/
theorem exists_candidate_comap_equiv
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV))
    (x : CuspCandidate (arithmeticExt Ω CX hcX))
    (eU : x.PiU ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)))
    (eV : x.PiV ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))
    (hs : ∀ u, eV (x.surj u) = D.stepHom Ω i (Fin.last D.r) (Fin.le_last _) (eU u))
    (he : ∀ y, x.emb y = D.φ₄ Ω hcX (eV y)) :
    ∃ (c : (arithmeticExt Ω CX hcX).Pi)
      (J : x.PiU ≃ₜ* (x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀))),
      ∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) = c * x.emb (x.surj u) * c⁻¹ :=
  exists_candidate_comap_equiv_of_isPullback Ω CX hcX UX hUX hne α₀ D i
    (D.candFU CX hcX UX hUX hne i hVa hU) (D.isPullback_candFU CX hcX UX hUX hne i hVa hU) hgal
    x eU eV hs he

include UX hUX hne α₀ hVa hU in
/-- **Lifting automorphisms of `Π_V` to `Π_U`** ([AbsTopII] Cor 3.7 (b), Cor 3.8, the `X₁`
side): under the hypotheses of `exists_candidate_comap_equiv`, every continuous automorphism `B`
of `x.PiV` with `x.emb ∘ B = conj(g) ∘ x.emb` lifts along `x.surj` to a continuous automorphism
of `x.PiU`. -/
theorem exists_candidate_lift
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV))
    (x : CuspCandidate (arithmeticExt Ω CX hcX))
    (eU : x.PiU ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)))
    (eV : x.PiV ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))
    (hs : ∀ u, eV (x.surj u) = D.stepHom Ω i (Fin.last D.r) (Fin.le_last _) (eU u))
    (he : ∀ y, x.emb y = D.φ₄ Ω hcX (eV y))
    (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi)
    (hB : ∀ v, x.emb (B v) = g * x.emb v * g⁻¹) :
    ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u) := by
  obtain ⟨c, J, hJ⟩ := exists_candidate_comap_equiv Ω CX hcX UX hUX hne α₀ D i hVa hU hgal x eU
    eV hs he
  have hN := candidate_range_emb Ω CX hcX D x eV he
  haveI : x.emb.toMonoidHom.range.Normal := by
    rw [hN]
    exact cor37b_normal Ω CX hcX D.CV D.hcV D.FV hgal
  have hsurj : Function.Surjective (cor38Fill Ω CX hcX UX hUX hne α₀) := fun z ↦ by
    obtain ⟨w, hw⟩ := fillMap_surjective Ω (subCurve CX UX hUX hne)
      (compl_nonempty_of_le hUX hcX) hUX hcX
      (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
        α₀) z)
    exact ⟨w, (congrArg (autContinuousMulEquivOfIso _).symm hw).trans
      ((autContinuousMulEquivOfIso _).symm_apply_apply z)⟩
  exact exists_lift_of_comap_equiv x.surj x.emb x.emb_injective _ hsurj _ c J hJ B g hB

end CurvesJacobian.Cusp
