/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiConstRing

/-!
# `Π_{X_M} ↪ Π_C` in the normalisation of `arithmeticExt` (MR8, [AbsTopII] Cor. 3.3 (iii))

Let `K` be a number field, `E` an elliptic curve over `K`, `Ω = K(Ē)^alg`, `k̄ ⊆ Ω` the algebraic
closure of `K` in `Ω`, `M ⊆ k̄` a finite Galois extension of `K`, `E_M = E ×_K M` and
`X_M = E_M ∖ {O}` (`hypCurveX (E.baseChange M)`, a hyperbolic curve over the number field `M`).
Let `Ω' ⊇ M` be an algebraic closure and `Π_{X_M} ↠ G_M` the arithmetic fundamental group of
`arithmeticExt Ω' (hypCurveX (E.baseChange M)) _`. The Galois data `hemiDataM E M` of `V = X_M`
inside `C = [(E ∖ {O}) / ±1]` (`CurvesJacobian.Cusp.HemiConstExt`) has ring
`R_M ≅ M[E]` (`hemiConstREquiv`).

* Generic part: `CurvesJacobian.Cusp.genConstGalEquiv₃ F C Ω : Gal(C / F) ≃ₜ* π₁ᵉᵗ(Spec F, Spec Ω)`
  for a separably closed Galois extension `C / F` inside an algebraically closed `Ω ⊇ C`, with
  the Galois action through field points being the restriction to `C`
  (`galoisAction_eq_genConstGalEquiv₃`). For Galois data `D` with `H_L ⊆ Gal(Ω / M)` and a
  ring map `c : M → R` restricting to `M ⊆ Ω`, the map `π₁ᵉᵗ(Spec R) → π₁ᵉᵗ(Spec M)` is the
  restriction to the constants (`fundamentalGroupMap_equivPi1Spec_symm₃`).
* Generic in the curve (`section ArithConstGen`): for any hyperbolic curve `W` over `M` and
  `e : Γ(W) ≃+* R` compatible with the constants (`ConstCompat₃`), the change of base point
  `piXGalG₃ : Π_W ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩`, `gkEquivG₃ : G_M ≃ₜ* Gal(k̄ / M)` and `gkEquivG₃_pr`
  (`pr` is the restriction to the constants). Everything is stated for an abstract `W` and only
  instantiated at `W = X_M` (unfolding `Γ(X_M)` during unification is prohibitively expensive).
* `CurvesJacobian.Cusp.hemiMSpecIso : Spec R_M ≅ Spec Γ(X_M)` from `sectionsXEAlgEquiv` and
  `hemiConstREquiv`; its `M`-structures match (`algebraMap_hemiMRingEquiv₃`: `m ↦ m ∈ Ω`).
* `hemiMPiXGal : Π_{X_M} ≃ₜ* (H_L ⊓ Gal(Ω / M)) ⧸ ⟨⟨S⟩⟩ = Π_V` (change of base point).
* `hemiMGkEquiv : G_M ≃ₜ* Gal(k̄ / M)` (`k̄` is an algebraic closure of `M`), and
  **compatibility** `hemiMGkEquiv_pr`: `(hemiMGkEquiv (pr γ))|_K = piConstX (hemiDataM E M)
  (hemiMPiXGal γ)` in `Gal(k̄ / K)`.
* **`hemiM_arith_emb`**: `hemiMEmbC₃ : Π_{X_M} → Π_C = etalePi1 R A Ω` is an open embedding with
  normal image of index `2 · [M : K]`, compatible with the projections to `Gal(k̄ / K)`; with
  `hemiPrC` (`G_K` of `arithmeticExt` for `X = E ∖ {O}`) this reads
  `hemiGkEquiv (hemiPrC (ι γ)) = (hemiMGkEquiv (pr γ))|_K` (`hemiGkEquiv_hemiPrC_hemiMEmbC₃`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Orbifold AffOrbicurve
open PreGaloisCategory Topology Belyi Belyi.Anabelian Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section GenConstantsPi1

variable (F C Ω : Type u) [Field F] [Field C] [Field Ω] [Algebra F C] [Algebra C Ω]
  [IsSepClosed C] [IsAlgClosed Ω]

/-- The geometric point `Spec C ⟶ Spec F`. -/
abbrev genConstPoint₃ : Spec (.of C) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F C))

/-- `Spec Ω ⟶ Spec C`. -/
abbrev genConstIncl₃ : Spec (.of Ω) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C Ω))

/-- The geometric point `Spec Ω ⟶ Spec C ⟶ Spec F`. -/
abbrev genConstEta₃ : Spec (.of Ω) ⟶ Spec (.of F) := genConstIncl₃ C Ω ≫ genConstPoint₃ F C

omit [IsSepClosed C] [IsAlgClosed Ω] in
lemma epi_genConstIncl₃ : Epi (genConstIncl₃ C Ω) := by
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap C Ω))).2 (by
      rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
      haveI : Module.Free C Ω := Module.Free.of_divisionRing _ _
      exact Module.FaithfullyFlat.of_linearEquiv _ _ (Module.Free.chooseBasis C Ω).repr)
  haveI := h.1
  haveI := h.2
  exact Flat.epi_of_flat_of_surjective _

variable {F C Ω}

/-- A `C`-point of a finite étale `F`-scheme gives an `Ω`-point. -/
def genConstFiberMap₃ (A : FiniteEtale (Spec (.of F))) :
    (fiber (genConstPoint₃ F C)).obj A → (fiber (genConstEta₃ F C Ω)).obj A := fun q =>
  (fiberObjEquivHom _ A).symm (Over.homMk (genConstIncl₃ C Ω ≫ (fiberObjEquivHom _ A q).left)
    ((Category.assoc _ _ _).trans
      (congrArg (genConstIncl₃ C Ω ≫ ·) (Over.w (fiberObjEquivHom _ A q)))))

lemma genConstFiberMap₃_left (A : FiniteEtale (Spec (.of F)))
    (q : (fiber (genConstPoint₃ F C)).obj A) :
    (fiberObjEquivHom _ A (genConstFiberMap₃ (Ω := Ω) A q)).left =
      genConstIncl₃ C Ω ≫ (fiberObjEquivHom _ A q).left := by
  rw [genConstFiberMap₃, Equiv.apply_symm_apply]
  rfl

lemma genConstFiberMap₃_naturality {A B : FiniteEtale (Spec (.of F))} (g : A ⟶ B)
    (q : (fiber (genConstPoint₃ F C)).obj A) :
    (fiber (genConstEta₃ F C Ω)).map g (genConstFiberMap₃ A q) =
      genConstFiberMap₃ B ((fiber (genConstPoint₃ F C)).map g q) := by
  apply (fiberObjEquivHom _ B).injective
  apply Over.OverMorphism.ext
  rw [← fiberObjEquivHom_naturality, genConstFiberMap₃_left, ← fiberObjEquivHom_naturality]
  change (fiberObjEquivHom _ A (genConstFiberMap₃ A q)).left ≫ g.hom.left = _
  rw [genConstFiberMap₃_left]
  exact Category.assoc _ _ _

lemma genConstFiberMap₃_injective (A : FiniteEtale (Spec (.of F))) :
    Function.Injective (genConstFiberMap₃ (Ω := Ω) (C := C) A) := by
  intro q₁ q₂ h
  have h1 := congrArg (fun q => (fiberObjEquivHom _ A q).left) h
  simp only [genConstFiberMap₃_left] at h1
  haveI := epi_genConstIncl₃ C Ω
  exact (fiberObjEquivHom _ A).injective
    (Over.OverMorphism.ext ((cancel_epi (genConstIncl₃ C Ω)).1 h1))

lemma genConstFiberMap₃_bijective (A : FiniteEtale (Spec (.of F))) :
    Function.Bijective (genConstFiberMap₃ (Ω := Ω) (C := C) A) := by
  obtain ⟨γ⟩ := nonempty_iso_of_fiberFunctor (fiber (genConstPoint₃ F C))
    (fiber (genConstEta₃ F C Ω))
  exact (genConstFiberMap₃_injective A).bijective_of_nat_card_le
    (Nat.card_congr (FintypeCat.equivEquivIso.symm (γ.app A))).symm.le

variable (F C Ω)

/-- **The fibre functors of `Spec F` at `Spec C` and at `Spec Ω` are isomorphic.** -/
def genConstFiberIso₃ : fiber (genConstPoint₃ F C) ≅ fiber (genConstEta₃ F C Ω) :=
  NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (Equiv.ofBijective _ (genConstFiberMap₃_bijective A)))
    fun {A B} g => by
      ext q
      exact (genConstFiberMap₃_naturality g q).symm

variable [IsGalois F C]

/-- **`Gal(C / F) ≃ₜ* π₁ᵉᵗ(Spec F, Spec Ω)`** for `C` a separable closure of `F` inside `Ω`. -/
def genConstGalEquiv₃ : (C ≃ₐ[F] C) ≃ₜ* π₁ᵉᵗ(genConstEta₃ F C Ω) :=
  ContinuousMulEquiv.trans
    { mulEquivAutFiber F C with
      continuous_toFun := (isHomeomorph_mulEquivAutFiber F C).continuous
      continuous_invFun := (isHomeomorph_mulEquivAutFiber F C).homeomorph.symm.continuous }
    (autContinuousMulEquivOfIso (genConstFiberIso₃ F C Ω))

lemma genConstGalEquiv₃_hom_app (g' : C ≃ₐ[F] C) (A : FiniteEtale (Spec (.of F)))
    (q : (fiber (genConstPoint₃ F C)).obj A) :
    (genConstGalEquiv₃ F C Ω g').hom.app A (genConstFiberMap₃ A q) =
      genConstFiberMap₃ A ((mulEquivAutFiber F C g').hom.app A q) := by
  have h : (genConstFiberIso₃ F C Ω).inv.app A ((genConstFiberIso₃ F C Ω).hom.app A q) = q :=
    FintypeCat.hom_inv_id_apply ((genConstFiberIso₃ F C Ω).app A) q
  change (genConstFiberIso₃ F C Ω).hom.app A ((mulEquivAutFiber F C g').hom.app A
    ((genConstFiberIso₃ F C Ω).inv.app A ((genConstFiberIso₃ F C Ω).hom.app A q))) = _
  rw [h]
  rfl

omit [IsAlgClosed Ω] in
/-- `Gal(C / F)` acts on `C`-points by precomposition. -/
lemma mulEquivAutFiber_genConst₃_left (g' : C ≃ₐ[F] C) (A : FiniteEtale (Spec (.of F)))
    (q : (fiber (genConstPoint₃ F C)).obj A) :
    (fiberObjEquivHom _ A ((mulEquivAutFiber F C g').hom.app A q)).left =
      Spec.map (CommRingCat.ofHom (g' : C →+* C)) ≫ (fiberObjEquivHom _ A q).left := by
  have hz : Spec.map (CommRingCat.ofHom (algebraMap F C)) ≫ 𝟙 _ = genConstPoint₃ F C :=
    Category.comp_id _
  have he : galoisAction F (𝟙 _) hz g' = mulEquivAutFiber F C g' := by
    change fundamentalGroupMap (𝟙 _) hz _ = _
    rw [fundamentalGroupMap_id]
    rfl
  rw [← he]
  exact galoisAction_hom_app_left F (𝟙 _) hz g' A q

/-- **The Galois action through a field-valued point of `Spec F` is the restriction to `C`**:
for `j : Spec L ⟶ Spec F` and `g ∈ Gal(Ω / L)` restricting to `g' ∈ Gal(C / F)`,
`galoisAction L j g = genConstGalEquiv₃ g'`. -/
theorem galoisAction_eq_genConstGalEquiv₃ (L : Type u) [Field L] [Algebra L Ω] [IsGalois L Ω]
    (j : Spec (.of L) ⟶ Spec (.of F))
    (h : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j = genConstEta₃ F C Ω)
    (g : Ω ≃ₐ[L] Ω) (g' : C ≃ₐ[F] C) (hg : ∀ c : C, algebraMap C Ω (g' c) = g (algebraMap C Ω c)) :
    galoisAction L j h g = genConstGalEquiv₃ F C Ω g' := by
  refine ext_of_hom_app_left fun A p => ?_
  obtain ⟨q, rfl⟩ := (genConstFiberMap₃_bijective A).2 p
  rw [galoisAction_hom_app_left, genConstGalEquiv₃_hom_app, genConstFiberMap₃_left,
    genConstFiberMap₃_left, mulEquivAutFiber_genConst₃_left]
  have hring : CommRingCat.ofHom (algebraMap C Ω) ≫ CommRingCat.ofHom (g : Ω →+* Ω) =
      CommRingCat.ofHom (g' : C →+* C) ≫ CommRingCat.ofHom (algebraMap C Ω) := by
    ext c
    exact (hg c).symm
  have hs : Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ genConstIncl₃ C Ω =
      genConstIncl₃ C Ω ≫ Spec.map (CommRingCat.ofHom (g' : C →+* C)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  rw [← Category.assoc, hs, Category.assoc]

end GenConstantsPi1

section GaloisDataConstM

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] {t : Ω}

instance isGalois_constField_of₃ (M : IntermediateField k (ConstField₂ k Ω)) :
    IsGalois M (ConstField₂ k Ω) :=
  IsGalois.tower_top_of_isGalois k M _

variable (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω)) (c : M →+* D.R)
  (hc : ∀ m : M, algebraMap D.R Ω (c m) = ((m : ConstField₂ k Ω) : Ω))

omit [IsAlgClosed Ω] [CharZero k] in
include hc in
lemma specPoint_comp_constM₃ :
    specPoint D.R Ω ≫ Spec.map (CommRingCat.ofHom c) = genConstEta₃ M (ConstField₂ k Ω) Ω := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext m
  exact hc m

variable [IsGalois (K₀ k t) Ω]

/-- **`π₁ᵉᵗ(Spec R) → π₁ᵉᵗ(Spec M)` is the restriction to the constants**: if `H_L` fixes
`M ⊆ k̄` and `c : M → R` restricts to `M ⊆ Ω`, then under `π₁ᵉᵗ(Spec R) ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩` and
`genConstGalEquiv₃ : Gal(k̄ / M) ≃ₜ* π₁ᵉᵗ(Spec M)`, the map induced by `Spec c` sends `x` to an
element of `Gal(k̄ / M)` restricting to `piConstX D x ∈ Gal(k̄ / k)`. -/
theorem fundamentalGroupMap_equivPi1Spec_symm₃ (hle : D.HL ≤ constFixer₃ t M)
    (x : GaloisPi1.pi1 D.HL D.S D.isClosed_HL) :
    ∃ g' : ConstField₂ k Ω ≃ₐ[M] ConstField₂ k Ω, g'.restrictScalars k = piConstX D x ∧
      fundamentalGroupMap (Spec.map (CommRingCat.ofHom c)) (specPoint_comp_constM₃ D M c hc)
        (((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm x) =
        genConstGalEquiv₃ M (ConstField₂ k Ω) Ω g' := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  have hσ : galResConst t (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ M.fixingSubgroup := hle σ.2
  refine ⟨IntermediateField.fixingSubgroupEquiv M ⟨_, hσ⟩, AlgEquiv.ext fun _ => rfl, ?_⟩
  have h1 : ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm
      (QuotientGroup.mk (s := GaloisPi1.kernel (galoisDataHL D).H (galoisDataHL D).S) σ) =
      (galoisDataHL D).galoisHom (galoisDataHL_H_le D) σ :=
    (galoisDataHL D).equivPi1Spec_symm_mk (galoisDataHL_H_le D) σ
  have h₁ := (galoisDataHL D).genericPoint_comp
  have h : Spec.map (CommRingCat.ofHom (algebraMap (galoisDataHL D).L Ω)) ≫
      (galoisDataHL D).genericPoint ≫ Spec.map (CommRingCat.ofHom c) =
      genConstEta₃ M (ConstField₂ k Ω) Ω := by
    rw [← Category.assoc, h₁]
    exact specPoint_comp_constM₃ D M c hc
  have key := fundamentalGroupMap_galoisAction (galoisDataHL D).L (galoisDataHL D).genericPoint
    (Spec.map (CommRingCat.ofHom c)) h₁ (specPoint_comp_constM₃ D M c hc) h
    ((galoisDataHL D).toGalL (Subgroup.inclusion (galoisDataHL_H_le D) σ))
  have key2 := galoisAction_eq_genConstGalEquiv₃ M (ConstField₂ k Ω) Ω (galoisDataHL D).L
    ((galoisDataHL D).genericPoint ≫ Spec.map (CommRingCat.ofHom c)) h
    ((galoisDataHL D).toGalL (Subgroup.inclusion (galoisDataHL_H_le D) σ))
    (IntermediateField.fixingSubgroupEquiv M ⟨_, hσ⟩) fun _ => rfl
  exact (congrArg (fundamentalGroupMap (Spec.map (CommRingCat.ofHom c))
    (specPoint_comp_constM₃ D M c hc)) h1).trans (key.trans key2)

end GaloisDataConstM

section HypW

variable {F : Type u} [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- `Γ(X) ≃ₐ[F] F[W]` for `X = W ∖ {O}` (`sectionsXEAlgEquiv`, typed with `hypCurveX`). -/
def sectionsXEHyp₃ :
    Γ((hypCurveX W).Xbar, (hypCurveX W).U) ≃ₐ[F] W.toAffine.CoordinateRing :=
  sectionsXEAlgEquiv W

lemma sectionsXEHyp₃_algebraMap (m : F) :
    sectionsXEHyp₃ W (algebraMap F Γ((hypCurveX W).Xbar, (hypCurveX W).U) m) =
      AdjoinRoot.of W.toAffine.polynomial (C m) := by
  rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq', RingHom.comp_apply,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

end HypW

section ArithConstGen

/-! ### Generic form: a hyperbolic curve `W` over `M ⊆ k̄` with `Γ(W) ≅ R` -/

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω)) [NumberField M]
  (W : HypCurve M) (hW : (W.U : Set W.Xbar)ᶜ.Nonempty) (e : Γ(W.Xbar, W.U) ≃+* D.R)

/-- `Spec R ≅ Spec Γ(W)`. -/
def specIsoG₃ : Spec (.of D.R) ≅ Spec (.of Γ(W.Xbar, W.U)) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

/-- The constants `M → Γ(W) ≅ R`. -/
abbrev constRG₃ : M →+* D.R :=
  e.toRingHom.comp (algebraMap M Γ(W.Xbar, W.U))

omit [NumberField M] in
lemma specIsoG₃_hom_comp : (specIsoG₃ D M W e).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))) =
      Spec.map (CommRingCat.ofHom (constRG₃ D M W e)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The compatibility of `e : Γ(W) ≃ R` with the constants: `M → Γ(W) ≅ R ⊆ Ω` is
`M ⊆ k̄ ⊆ Ω`. -/
def ConstCompat₃ : Prop :=
  ∀ m : M, algebraMap D.R Ω (e (algebraMap M Γ(W.Xbar, W.U) m)) = ((m : ConstField₂ k Ω) : Ω)

variable (he : ConstCompat₃ D M W e)

omit [NumberField M] in
include he in
lemma structure_compG₃ :
    (specPoint D.R Ω ≫ (specIsoG₃ D M W e).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))) =
      genConstEta₃ M (ConstField₂ k Ω) Ω := by
  rw [Category.assoc, specIsoG₃_hom_comp]
  exact specPoint_comp_constM₃ D M (constRG₃ D M W e) he

variable [IsAlgClosed Ω] [CharZero k] (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω']
  [Algebra.IsAlgebraic M Ω'] [CharZero Ω']

/-- The change of base point on `Spec Γ(W)`: from the base point of `arithmeticExt` to
`Spec Ω ⟶ Spec R ≅ Spec Γ(W)` (any two fibre functors are isomorphic). -/
def fiberIsoG₃ :
    fiber (basePoint Ω' W hW ≫
      baseChangeSpec M Ω' Γ(W.Xbar, W.U)) ≅
    fiber (specPoint D.R Ω ≫ (specIsoG₃ D M W e).hom) :=
  haveI := isIntegral_specSections W hW
  (nonempty_iso_of_fiberFunctor _ _).some

/-- `Π_W ≃ₜ* π₁ᵉᵗ(Spec R, Spec Ω)`. -/
def piXEquivG₃ : (arithmeticExt Ω' W hW).Pi ≃ₜ*
    π₁ᵉᵗ(specPoint D.R Ω) :=
  (autContinuousMulEquivOfIso (fiberIsoG₃ D M W hW e Ω')).trans
    (fundamentalGroupEquivOfIso (specIsoG₃ D M W e) _).symm

/-- `Π_W ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩`. -/
def piXGalG₃ [IsGalois (K₀ k t) Ω] : (arithmeticExt Ω' W hW).Pi ≃ₜ*
    GaloisPi1.pi1 D.HL D.S D.isClosed_HL :=
  (piXEquivG₃ D M W hW e Ω').trans ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D))

/-- The change of base point on `Spec M` induced by `fiberIsoG₃`. -/
def gkFiberIsoG₃ : fiber (Spec.map (CommRingCat.ofHom (algebraMap M Ω'))) ≅
    fiber (genConstEta₃ M (ConstField₂ k Ω) Ω) :=
  fiberIsoMap (Spec.map (CommRingCat.ofHom
      (algebraMap M Γ(W.Xbar, W.U))))
    (basePoint_spec₂ Ω' W hW) (structure_compG₃ D M W e he)
    (fiberIsoG₃ D M W hW e Ω')

/-- `G_M ≃ₜ* Gal(k̄ / M)`. -/
def gkEquivG₃ : (arithmeticExt Ω' W hW).G ≃ₜ*
    (ConstField₂ k Ω ≃ₐ[M] ConstField₂ k Ω) :=
  (autContinuousMulEquivOfIso (gkFiberIsoG₃ D M W hW e he Ω')).trans
    (genConstGalEquiv₃ M (ConstField₂ k Ω) Ω).symm

omit [CharZero k] in
lemma fundamentalGroupMap_piXEquivG₃
    (γ : (arithmeticExt Ω' W hW).Pi) :
    fundamentalGroupMap (Spec.map (CommRingCat.ofHom (constRG₃ D M W e)))
        (specPoint_comp_constM₃ D M (constRG₃ D M W e) he) (piXEquivG₃ D M W hW e Ω' γ) =
      fundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (algebraMap M Γ(W.Xbar, W.U))))
        (structure_compG₃ D M W e he)
        (autContinuousMulEquivOfIso (fiberIsoG₃ D M W hW e Ω') γ) := by
  have hcomp : specPoint D.R Ω ≫ (specIsoG₃ D M W e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))) =
      genConstEta₃ M (ConstField₂ k Ω) Ω := by
    rw [← Category.assoc]
    exact structure_compG₃ D M W e he
  have e1 := fundamentalGroupMap_congr (specIsoG₃_hom_comp D M W e).symm
    (specPoint_comp_constM₃ D M (constRG₃ D M W e) he) hcomp
  have e2 := fundamentalGroupMap_comp (specIsoG₃ D M W e).hom
    (Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))))
    rfl (structure_compG₃ D M W e he) hcomp
  have e3 : fundamentalGroupMap (specIsoG₃ D M W e).hom rfl (piXEquivG₃ D M W hW e Ω' γ) =
      autContinuousMulEquivOfIso (fiberIsoG₃ D M W hW e Ω') γ :=
    (fundamentalGroupEquivOfIso (specIsoG₃ D M W e) _).apply_symm_apply _
  exact (DFunLike.congr_fun (e1.trans e2) (piXEquivG₃ D M W hW e Ω' γ)).trans
    (congrArg (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))))
      (structure_compG₃ D M W e he)) e3)

/-- **`pr : Π_W → G_M` is the restriction to the constants** (generic form). -/
theorem gkEquivG₃_pr [IsGalois (K₀ k t) Ω] (hle : D.HL ≤ constFixer₃ t M)
    (γ : (arithmeticExt Ω' W hW).Pi) :
    (gkEquivG₃ D M W hW e he Ω'
      ((arithmeticExt Ω' W hW).pr γ)).restrictScalars k =
      piConstX D (piXGalG₃ D M W hW e Ω' γ) := by
  have h1 := fundamentalGroupMap_autContinuousMulEquivOfIso
    (Spec.map (CommRingCat.ofHom (algebraMap M Γ(W.Xbar, W.U))))
    (basePoint_spec₂ Ω' W hW) (structure_compG₃ D M W e he)
    (fiberIsoG₃ D M W hW e Ω') γ
  obtain ⟨g', hg', h3⟩ := fundamentalGroupMap_equivPi1Spec_symm₃ D M (constRG₃ D M W e) he hle
    (piXGalG₃ D M W hW e Ω' γ)
  have h4 : ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm
      (piXGalG₃ D M W hW e Ω' γ) = piXEquivG₃ D M W hW e Ω' γ :=
    ContinuousMulEquiv.symm_apply_apply _ _
  rw [h4, fundamentalGroupMap_piXEquivG₃ D M W hW e he Ω', h1] at h3
  have h5 : gkEquivG₃ D M W hW e he Ω'
      ((arithmeticExt Ω' W hW).pr γ) = g' := by
    change (genConstGalEquiv₃ M (ConstField₂ k Ω) Ω).symm
      (autContinuousMulEquivOfIso (gkFiberIsoG₃ D M W hW e he Ω')
        (projGk Ω' W hW γ)) = g'
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact h3
  rw [h5, hg']

end ArithConstGen

section ConstCompatW

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω)) [NumberField M]
  (W₀ : WeierstrassCurve M) [W₀.IsElliptic] (e₂ : W₀.toAffine.CoordinateRing ≃+* D.R)

/-- **`ConstCompat₃` for `W₀ ∖ {O}`**, `Γ(W₀ ∖ {O}) ≃ M[W₀] ≃ R`, from the constants of
`M[W₀]`. -/
theorem constCompat_hypCurveX₃
    (h₂ : ∀ m : M, algebraMap D.R Ω (e₂ (AdjoinRoot.of W₀.toAffine.polynomial (C m))) =
      ((m : ConstField₂ k Ω) : Ω)) :
    ConstCompat₃ D M (hypCurveX W₀) ((sectionsXEHyp₃ W₀).toRingEquiv.trans e₂) := fun m =>
  (congrArg (fun a => algebraMap D.R Ω (e₂ a)) (sectionsXEHyp₃_algebraMap W₀ m)).trans (h₂ m)

end ConstCompatW

section HemiM

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E)))) [FiniteDimensional K M]
  [IsGalois K M]

/-- `M` (finite over the number field `K`) is a number field. -/
instance numberField_hemiM₃ : NumberField M := NumberField.of_module_finite K M

/-- **`Γ(X_M) ≅ R_M`**: `Γ(E_M ∖ {O}) ≃ M[E] ≃ R_M` (`sectionsXEAlgEquiv`, `hemiConstREquiv`). -/
def hemiMRingEquiv₃ : Γ((hypCurveX (E.baseChange M)).Xbar, (hypCurveX (E.baseChange M)).U) ≃+*
    (hemiDataM E M).R :=
  (sectionsXEHyp₃ (E.baseChange M)).toRingEquiv.trans (hemiConstREquiv E M).toRingEquiv

/-- **Compatibility with `M`**: the `M`-structure of `Γ(X_M)` corresponds to the constants
`M ⊆ k̄ ⊆ Ω` of `R_M` (`m ↦ m`). -/
theorem algebraMap_hemiMRingEquiv₃ :
    ConstCompat₃ (hemiDataM E M) M (hypCurveX (E.baseChange M)) (hemiMRingEquiv₃ E M) :=
  constCompat_hypCurveX₃ (hemiDataM E M) M (E.baseChange M) (hemiConstREquiv E M).toRingEquiv
    fun m => algebraMap_hemiConstREquiv_C E M m

/-- **`Spec R_M ≅ Spec Γ(X_M)`**, `X_M = E_M ∖ {O}`. -/
def hemiMSpecIso : Spec (.of (hemiDataM E M).R) ≅
    Spec (.of Γ((hypCurveX (E.baseChange M)).Xbar, (hypCurveX (E.baseChange M)).U)) :=
  specIsoG₃ (hemiDataM E M) M (hypCurveX (E.baseChange M)) (hemiMRingEquiv₃ E M)

/-- The structure maps: `Spec R_M ≅ Spec Γ(X_M) ⟶ Spec M` is `Spec (M → R_M)` for the
constants `M → R_M` (`algebraMap_hemiMRingEquiv₃`). -/
lemma hemiMSpecIso_hom_comp : (hemiMSpecIso E M).hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap M Γ((hypCurveX (E.baseChange M)).Xbar, (hypCurveX (E.baseChange M)).U))) =
      Spec.map (CommRingCat.ofHom (constRG₃ (hemiDataM E M) M (hypCurveX (E.baseChange M))
        (hemiMRingEquiv₃ E M))) :=
  specIsoG₃_hom_comp (hemiDataM E M) M (hypCurveX (E.baseChange M)) (hemiMRingEquiv₃ E M)

variable (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic M Ω']
  [CharZero Ω']

/-- **`Π_{X_M} ≃ₜ* π₁ᵉᵗ(Spec R_M, Spec Ω)`**: change of base point, then
`Spec R_M ≅ Spec Γ(X_M)`. -/
def hemiMPiXEquiv :
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi ≃ₜ*
    π₁ᵉᵗ(specPoint (hemiDataM E M).R (FFClosure (curveE E))) :=
  piXEquivG₃ (hemiDataM E M) M (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))
    (hemiMRingEquiv₃ E M) Ω'

/-- **`Π_{X_M} ≃ₜ* Π_V = (H_L ⊓ Gal(Ω / M)) ⧸ ⟨⟨S⟩⟩`.** -/
def hemiMPiXGal :
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi ≃ₜ*
    GaloisPi1.pi1 (hemiDataM E M).HL (hemiDataM E M).S (hemiDataM E M).isClosed_HL :=
  piXGalG₃ (hemiDataM E M) M (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))
    (hemiMRingEquiv₃ E M) Ω'

/-- **`G_M ≃ₜ* Gal(k̄ / M)`** (`k̄` is an algebraic closure of `M`): the change of base point
induced by the one of `hemiMPiXEquiv`, then `genConstGalEquiv₃⁻¹`. -/
def hemiMGkEquiv :
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).G ≃ₜ*
    (ConstField₂ K (FFClosure (curveE E)) ≃ₐ[M] ConstField₂ K (FFClosure (curveE E))) :=
  gkEquivG₃ (hemiDataM E M) M (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))
    (hemiMRingEquiv₃ E M) (algebraMap_hemiMRingEquiv₃ E M) Ω'

/-- **`pr : Π_{X_M} → G_M` is the restriction to the constants**: under `hemiMPiXGal` and
`hemiMGkEquiv`, `pr` corresponds to `piConstX (hemiDataM E M)`, after restricting
`Gal(k̄ / M) ⊆ Gal(k̄ / K)`. -/
theorem hemiMGkEquiv_pr
    (γ : (arithmeticExt Ω' (hypCurveX (E.baseChange M))
      (compl_XE_nonempty (E.baseChange M))).Pi) :
    (hemiMGkEquiv E M Ω' ((arithmeticExt Ω' (hypCurveX (E.baseChange M))
      (compl_XE_nonempty (E.baseChange M))).pr γ)).restrictScalars K =
      piConstX (hemiDataM E M) (hemiMPiXGal E M Ω' γ) :=
  gkEquivG₃_pr (hemiDataM E M) M (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M)) (hemiMRingEquiv₃ E M) (algebraMap_hemiMRingEquiv₃ E M) Ω'
    inf_le_right γ

/-- **`Π_{X_M} → Π_C = H ⧸ ⟨⟨S⟩⟩`** (Galois form): `hemiMPiXGal`, then `infInclC₃`. -/
def hemiMEmb₃ :
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi →ₜ*
    GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H :=
  (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (hemiMPiXGal E M Ω'))

/-- **`Π_{X_M} → Π_C = etalePi1 R A Ω`**: `hemiMEmb₃`, then `equivPi1⁻¹`. -/
def hemiMEmbC₃ :
    (arithmeticExt Ω' (hypCurveX (E.baseChange M)) (compl_XE_nonempty (E.baseChange M))).Pi →ₜ*
    etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (hemiData E).equivPi1.symm).comp (hemiMEmb₃ E M Ω')

lemma range_hemiMEmbC₃ : (hemiMEmbC₃ E M Ω').toMonoidHom.range =
    (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
      (constFixer₃_normal M)).toMonoidHom.range.map
        ((hemiData E).equivPi1.symm.toMulEquiv : _ →* _) := by
  ext y
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, ⟨hemiMPiXGal E M Ω' γ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(hemiMPiXGal E M Ω').symm x, ?_⟩
    change (hemiData E).equivPi1.symm ((infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
      (constFixer₃_normal M)) (hemiMPiXGal E M Ω' ((hemiMPiXGal E M Ω').symm x))) = _
    exact congrArg (fun z => (hemiData E).equivPi1.symm ((infInclC₃ (hemiData E) _
      (isOpen_constFixer₃ M) (constFixer₃_normal M)) z))
        ((hemiMPiXGal E M Ω').apply_symm_apply x)

/-- `piConstC ∘ hemiMEmbC₃ = (pr, restricted to Gal(k̄ / K))`. -/
lemma piConstC_hemiMEmbC₃
    (γ : (arithmeticExt Ω' (hypCurveX (E.baseChange M))
      (compl_XE_nonempty (E.baseChange M))).Pi) :
    piConstC (hemiData E) ((hemiData E).equivPi1 (hemiMEmbC₃ E M Ω' γ)) =
      (hemiMGkEquiv E M Ω' ((arithmeticExt Ω' (hypCurveX (E.baseChange M))
        (compl_XE_nonempty (E.baseChange M))).pr γ)).restrictScalars K := by
  have h1 : (hemiData E).equivPi1 (hemiMEmbC₃ E M Ω' γ) =
      infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)
        (hemiMPiXGal E M Ω' γ) :=
    (hemiData E).equivPi1.apply_symm_apply _
  exact (congrArg (piConstC (hemiData E)) h1).trans
    ((DFunLike.congr_fun (piConstC_comp_infInclC₃ (hemiData E) M) (hemiMPiXGal E M Ω' γ)).trans
      (hemiMGkEquiv_pr E M Ω' γ).symm)

/-- **`Π_{X_M} ↪ Π_C`** for `X_M = (E ∖ {O})_M`, `M / K` finite Galois inside `k̄`, and the
hemi-elliptic orbicurve `C = [(E ∖ {O}) / ±1]` ([AbsTopII] Cor. 3.3 (iii), IUT I Def. 3.1 (b)),
in the normalisation of `arithmeticExt` for `X_M`: `hemiMEmbC₃` is an open embedding with normal
image of index `2 · [M : K]`, compatible with the projections to `Gal(k̄ / K)`
(`Π_C → Gal(k̄ / K)` and `pr : Π_{X_M} ↠ G_M ≅ Gal(k̄ / M) ⊆ Gal(k̄ / K)`). -/
theorem hemiM_arith_emb :
    IsOpenEmbedding (hemiMEmbC₃ E M Ω') ∧ (hemiMEmbC₃ E M Ω').toMonoidHom.range.Normal ∧
      (hemiMEmbC₃ E M Ω').toMonoidHom.range.index = 2 * Module.finrank K M ∧
      ∀ γ, piConstC (hemiData E) ((hemiData E).equivPi1 (hemiMEmbC₃ E M Ω' γ)) =
        (hemiMGkEquiv E M Ω' ((arithmeticExt Ω' (hypCurveX (E.baseChange M))
          (compl_XE_nonempty (E.baseChange M))).pr γ)).restrictScalars K := by
  have hSU := S_subset_constFixer₃ (hemiData E) M
  refine ⟨(hemiData E).equivPi1.symm.toHomeomorph.isOpenEmbedding.comp
      ((isOpenEmbedding_infInclC₃ hSU).comp (hemiMPiXGal E M Ω').toHomeomorph.isOpenEmbedding),
    ?_, ?_, piConstC_hemiMEmbC₃ E M Ω'⟩
  · rw [range_hemiMEmbC₃]
    exact Subgroup.Normal.map (range_infInclC₃_normal hSU) _
      (hemiData E).equivPi1.symm.toMulEquiv.surjective
  · rw [range_hemiMEmbC₃, Subgroup.index_map_equiv]
    exact (hemi_constExt_numberField E M).2

/-- With `G_K` of `arithmeticExt` for `X = E ∖ {O}` (`Ω''` an algebraic closure of `K`):
`hemiGkEquiv (hemiPrC (ι γ)) = (hemiMGkEquiv (pr γ))|_K`. -/
theorem hemiGkEquiv_hemiPrC_hemiMEmbC₃ (Ω'' : Type u) [Field Ω''] [Algebra K Ω'']
    [IsAlgClosed Ω''] [Algebra.IsAlgebraic K Ω''] [CharZero Ω'']
    (γ : (arithmeticExt Ω' (hypCurveX (E.baseChange M))
      (compl_XE_nonempty (E.baseChange M))).Pi) :
    hemiGkEquiv E Ω'' (hemiPrC E Ω'' (hemiMEmbC₃ E M Ω' γ)) =
      (hemiMGkEquiv E M Ω' ((arithmeticExt Ω' (hypCurveX (E.baseChange M))
        (compl_XE_nonempty (E.baseChange M))).pr γ)).restrictScalars K :=
  (hemiGkEquiv_hemiPrC E Ω'' (hemiMEmbC₃ E M Ω' γ)).trans (piConstC_hemiMEmbC₃ E M Ω' γ)

end HemiM

end CurvesJacobian.Cusp
