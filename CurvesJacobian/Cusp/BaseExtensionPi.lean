/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GeomInvariance
import Pi1.FundamentalGroup.HomotopyExact

/-!
# `Π_{X_{K'}} ≅ Π_X ×_{π₁(Spec K)} π₁(Spec K')` for an extension `K ⊆ K'`

Let `X = Spec R` be an affine scheme of finite type over a field `K` of characteristic `0`,
`K ⊆ K'` an arbitrary field extension (e.g. `K` a number field and `K' = K_v` a completion),
`Ω` a countable algebraic closure of `K` and `Ω' ⊇ Ω` an algebraic closure of `K'`, and
`X' = X_{K'} = Spec (K' ⊗[K] R)`. If `X_Ω` is connected, then for every geometric point
`ξ : Spec Ω' ⟶ X'` over `Spec Ω' ⟶ Spec K'` the square

  `π₁ᵉᵗ(X', ξ) ⟶ π₁ᵉᵗ(X, ξ)`
  `     ↓              ↓    `
  `π₁ᵉᵗ(Spec K') ⟶ π₁ᵉᵗ(Spec K)`

is **cartesian** (`AlgebraicGeometry.FiniteEtale.existsUnique_baseExtension`): this is the
identification `Π_{X_L} = Π_{X_K} ×_{Γ_K} Γ_L` used in the proof of [LocAn] Corollary 15.5
(`The Local Pro-p Anabelian Geometry of Curves.txt` l.4340–4370) to base change an isomorphism
`Π_{X_K} ≅ Π_{Y_K}` over `Γ_K` to `L`.

## Proof

Both columns are extensions by geometric fundamental groups (homotopy exact sequences, here at
an arbitrary geometric point: `exists_fundamentalGroupMap_baseChange_eq'`,
`fundamentalGroupMap_baseChange_injective'`), and the map on geometric parts is
`π₁ᵉᵗ(X'_{Ω'}) = π₁ᵉᵗ(X_{Ω'}) ≅ π₁ᵉᵗ(X_Ω)` (`fundamentalGroupMap_extendSpec_bijective`,
finite étale descent along `Ω ⊆ Ω'`). A diagram chase gives injectivity and surjectivity onto the
fibre product.
-/

universe u

open CategoryTheory Limits TensorProduct AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

section Generic

variable {k Ω R : Type u} [Field k] [Field Ω] [Algebra k Ω] [CommRing R] [Algebra k R]

/-- **`Δ_X → Π_X` is injective at every geometric point** (pi1's
`fundamentalGroupMap_baseChange_injective` at an `L`-valued point, `L` any separably closed
field). -/
theorem fundamentalGroupMap_baseChange_injective' [Algebra.IsSeparable k Ω]
    [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))] {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) {η : Spec (.of L) ⟶ Spec (.of R)}
    (h : x ≫ baseChangeSpec k Ω R = η) :
    Function.Injective (fundamentalGroupMap (baseChangeSpec k Ω R) h) := by
  subst h
  exact fun _ _ hab ↦ PreGaloisCategory.fiberAutMap_injective (fiber x) (pullbackFiberIso _ rfl)
    (fun A _ ↦ exists_mono_pullback_baseChange A) hab

open Algebra.FiniteEtale in
/-- **Exactness in the middle of `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k)` at every geometric point**
(pi1's `exists_fundamentalGroupMap_baseChange_eq` at an `L`-valued point of `X_Ω`, `L` any
separably closed field; same proof). -/
theorem exists_fundamentalGroupMap_baseChange_eq' [Algebra.IsSeparable k Ω]
    [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))]
    {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) {η : Spec (.of L) ⟶ Spec (.of k)}
    (h : (x ≫ baseChangeSpec k Ω R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = η)
    (γ : π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R))
    (hγ : fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap k R))) h γ = 1) :
    ∃ δ, fundamentalGroupMap (baseChangeSpec k Ω R) rfl δ = γ := by
  let g := baseChangeSpec k Ω R
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have htriv (W : FiniteEtale (Spec (.of k))) (z : (fiber (x ≫ g)).obj ((pullback f).obj W)) :
      γ.hom.app _ z = z :=
    PreGaloisCategory.fiberAutMap_eq_one_apply (pullbackFiberIso f h) hγ W z
  suffices hmem : γ ∈ (PreGaloisCategory.fiberAutMap (pullbackFiberIso g rfl)).range by
    obtain ⟨δ, hδ⟩ := hmem
    exact ⟨δ, hδ⟩
  refine PreGaloisCategory.mem_range_fiberAutMap (pullbackFiberIso g rfl) γ fun Y s p ↦ ?_
  let T₀ := self (Spec (.of (Ω ⊗[k] R)))
  let i : T₀ ≅ ⊤_ _ := (isTerminalSelf _).uniqueUpToIso terminalIsTerminal
  let s₀ := i.hom ≫ s
  let σ := s₀.left ≫ pullback.fst Y.hom g
  have hs₀ : s₀.left ≫ pullback.snd Y.hom g = 𝟙 _ := MorphismProperty.Over.w s₀
  let q : Y.left ⟶ Spec (.of R) := Y.hom
  haveI : IsFiniteEtale q := Y.prop
  have hσ : σ ≫ q = g := by
    have h1 : s₀.left ≫ pullback.snd Y.hom g ≫ g = g := by
      erw [← Category.assoc, hs₀, Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (s₀.left ≫ ·) pullback.condition).trans h1)
  obtain ⟨K, hK, ψ, hψ1, hψ2⟩ := exists_section_descent q σ hσ
  haveI := isFiniteEtale_Spec_intermediateField K
  let W : FiniteEtale (Spec (.of k)) := mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let Z := (pullback f).obj W
  let φ : Z ⟶ Y := MorphismProperty.Over.homMk ((pullbackSpecIso k K R).hom ≫ ψ)
    (by
      change ((pullbackSpecIso k K R).hom ≫ ψ) ≫ Y.hom = pullback.snd _ _
      erw [Category.assoc, hψ1, pullbackSpecIso_hom_snd]) trivial
  have hinc : Spec.map (CommRingCat.ofHom (inclTensor R K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom) = g := by
    rw [← Spec.map_comp]
    rfl
  let t₀ : T₀ ⟶ (pullback g).obj Z := MorphismProperty.Over.homMk
    (pullback.lift (Spec.map (CommRingCat.ofHom (inclTensor R K).toRingHom) ≫
      (pullbackSpecIso k K R).inv) (𝟙 _)
      (by
        change _ ≫ pullback.snd _ _ = _
        erw [Category.assoc, pullbackSpecIso_inv_snd, hinc, Category.id_comp]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      rw [pullback.lift_snd]) trivial
  have ht : t₀ ≫ (pullback g).map φ = s₀ := by
    apply MorphismProperty.Over.Hom.ext
    change t₀.left ≫ ((pullback g).map φ).left = s₀.left
    rw [MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst]
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ (pullbackSpecIso k K R).hom ≫ ψ = σ
      erw [pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hψ2]
    · erw [Category.assoc, pullback.lift_snd, hs₀]
      exact pullback.lift_snd _ _ _
  let e := pullbackFiberIso (Ω := L) g (rfl : x ≫ g = x ≫ g)
  have hsp : s = i.inv ≫ s₀ := by simp [s₀]
  have key : (pullback g ⋙ fiber x).map φ ≫ e.hom.app Y = e.hom.app Z ≫ (fiber (x ≫ g)).map φ :=
    e.hom.naturality φ
  rw [hsp, ← ht, Functor.map_comp, Functor.map_comp, FintypeCat.comp_apply,
    FintypeCat.comp_apply]
  set w := (fiber x).map t₀ ((fiber x).map i.inv p)
  have hw : e.hom.app Y ((fiber x).map ((pullback g).map φ) w) =
      (fiber (x ≫ g)).map φ (e.hom.app Z w) := congr($key w)
  rw [hw, ← FintypeCat.comp_apply, γ.hom.naturality, FintypeCat.comp_apply, htriv W]

/-- `exists_fundamentalGroupMap_baseChange_eq'` with the geometric point of `X` given by an
equation. -/
theorem exists_fundamentalGroupMap_baseChange_eq'' [Algebra.IsSeparable k Ω]
    [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))]
    {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) {pt : Spec (.of L) ⟶ Spec (.of R)}
    (hx : x ≫ baseChangeSpec k Ω R = pt) {η : Spec (.of L) ⟶ Spec (.of k)}
    (h : pt ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = η) (γ : π₁ᵉᵗ(pt))
    (hγ : fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap k R))) h γ = 1) :
    ∃ δ, fundamentalGroupMap (baseChangeSpec k Ω R) hx δ = γ := by
  subst hx
  exact exists_fundamentalGroupMap_baseChange_eq' x h γ hγ

end Generic

section Helpers

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- `π₁ᵉᵗ(Spec Ω)` is trivial at any point equal to `Spec Ω ⟶ Spec Ω` (`Ω` separably closed). -/
lemma eq_one_of_eq_specSelf {η : Spec (.of Ω) ⟶ Spec (.of Ω)}
    (h : η = Spec.map (CommRingCat.ofHom (algebraMap Ω Ω))) (γ : π₁ᵉᵗ(η)) : γ = 1 := by
  subst h
  haveI := subsingleton_fundamentalGroup_self (Ω := Ω)
  exact Subsingleton.elim _ _

end Helpers

section BaseExtension

variable (K K' Ω Ω' R : Type u) [Field K] [Field K'] [Field Ω] [Field Ω'] [CommRing R]
  [Algebra K R] [Algebra K K'] [Algebra K Ω] [Algebra Ω Ω'] [Algebra K Ω'] [Algebra K' Ω']
  [IsScalarTower K Ω Ω'] [IsScalarTower K K' Ω']

/-- `X_{K'} = Spec (K' ⊗[K] R) ⟶ Spec K'`. -/
abbrev strSpec : Spec (.of (K' ⊗[K] R)) ⟶ Spec (.of K') :=
  Spec.map (CommRingCat.ofHom (algebraMap K' (K' ⊗[K] R)))

/-- `X = Spec R ⟶ Spec K`. -/
abbrev strSpecR : Spec (.of R) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K R))

/-- `Spec K' ⟶ Spec K`. -/
abbrev specExt : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))

/-- `X'_{Ω'} = Spec (Ω' ⊗[K'] (K' ⊗[K] R)) ≅ X_{Ω'} = Spec (Ω' ⊗[K] R)`. -/
def cancelSpecIso' : Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))) ≅ Spec (.of (Ω' ⊗[K] R)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.cancelBaseChange K K' Ω' Ω' R).symm.toRingEquiv).op

/-- `X'_{Ω'} ⟶ X_{Ω'}`, an isomorphism. -/
abbrev cancelSpec : Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))) ⟶ Spec (.of (Ω' ⊗[K] R)) :=
  (cancelSpecIso' K K' Ω' R).hom

lemma cancelSpec_eq : cancelSpec K K' Ω' R = Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.cancelBaseChange K K' Ω' Ω' R).symm.toRingEquiv.toRingHom) := rfl

omit [Algebra K Ω] [Algebra Ω Ω'] [IsScalarTower K Ω Ω'] in
lemma bcSpec_strSpecR :
    baseChangeSpec K K' R ≫ strSpecR K R = strSpec K K' R ≫ specExt K K' := by
  simp only [baseChangeSpec, strSpecR, strSpec, specExt, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := R),
    TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := K'), TensorProduct.smul_tmul']
  simp [Algebra.smul_def]

lemma baseChangeSpec_bcSpec :
    baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R =
      cancelSpec K K' Ω' R ≫ extendSpec K Ω Ω' R ≫ baseChangeSpec K Ω R := by
  simp only [baseChangeSpec, cancelSpec_eq, extendSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, extendTensor_tmul, map_one,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul]

omit [Algebra K Ω] [Algebra Ω Ω'] [IsScalarTower K Ω Ω'] [Algebra K Ω'] [IsScalarTower K K' Ω'] in
lemma baseChangeSpec_strSpec :
    baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ strSpec K K' R =
      Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) := by
  simp only [baseChangeSpec, strSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  have e1 : (c ⊗ₜ[K] (1 : R) : K' ⊗[K] R) = c • (1 : K' ⊗[K] R) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    Algebra.TensorProduct.one_def]

variable {K K' Ω Ω' R}

omit [Algebra K Ω] [Algebra Ω Ω'] [IsScalarTower K Ω Ω'] [Algebra K Ω'] [IsScalarTower K K' Ω'] in
/-- A geometric point `pt : Spec Ω' ⟶ X_{K'}` over `Spec Ω' ⟶ Spec K'` lifts to an `Ω'`-rational
point of `X'_{Ω'} = Spec (Ω' ⊗[K'] (K' ⊗[K] R))`. -/
lemma exists_rationalLift (pt : Spec (.of Ω') ⟶ Spec (.of (K' ⊗[K] R)))
    (hpt : pt ≫ strSpec K K' R = Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))) :
    ∃ x : Spec (.of Ω') ⟶ Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))),
      x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) = pt ∧
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R)))) =
        Spec.map (CommRingCat.ofHom (algebraMap Ω' Ω')) := by
  set φ := (Spec.preimage pt).hom with hφ
  have hpt0 : pt = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomm : φ.comp (algebraMap K' (K' ⊗[K] R)) = algebraMap K' Ω' := by
    have := hpt
    rw [hpt0, strSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  let φa : (K' ⊗[K] R) →ₐ[K'] Ω' :=
    { φ with commutes' := fun c ↦ congrArg (fun f : K' →+* Ω' ↦ f c) hcomm }
  let ψ := AlgHom.liftEquiv K' Ω' (K' ⊗[K] R) Ω' φa
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_, ?_⟩
  · rw [baseChangeSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hpt0]
    congr 2
    refine RingHom.ext fun z ↦ ?_
    change ψ (1 ⊗ₜ z) = φ z
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]

variable [Algebra.FiniteType K R] [IsAlgClosed Ω] [CharZero Ω] [Countable Ω] [IsAlgClosed Ω']
  [Algebra.IsSeparable K Ω] [Algebra.IsSeparable K' Ω']
  [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))]
  [ConnectedSpace (Spec (.of (K' ⊗[K] R)))]
  [ConnectedSpace (Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))]

variable (Ω) in
include Ω in
omit [ConnectedSpace (Spec (.of (K' ⊗[K] R)))] [ConnectedSpace (Spec (.of R))]
  [Algebra.IsSeparable K' Ω'] [Algebra.FiniteType K R] [IsAlgClosed Ω] [CharZero Ω] [Countable Ω]
  [IsAlgClosed Ω'] [Algebra.IsSeparable K Ω] [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))]
  [ConnectedSpace (Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))] in
/-- `π₁ᵉᵗ(X'_{Ω'}) → π₁ᵉᵗ(X)` factors as `π₁ᵉᵗ(X'_{Ω'}) ≅ π₁ᵉᵗ(X_{Ω'}) ≅ π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)`. -/
lemma fundamentalGroupMap_comp_bc (x : Spec (.of Ω') ⟶ Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))
    {η : Spec (.of Ω') ⟶ Spec (.of R)}
    (h : x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R = η)
    (h' : ((x ≫ cancelSpec K K' Ω' R) ≫ extendSpec K Ω Ω' R) ≫ baseChangeSpec K Ω R = η)
    (δ : π₁ᵉᵗ(x)) :
    fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R) h δ =
      fundamentalGroupMap (baseChangeSpec K Ω R) h'
        (fundamentalGroupMap (extendSpec K Ω Ω' R) rfl
          (fundamentalGroupMap (cancelSpec K K' Ω' R) rfl δ)) := by
  have hsq := baseChangeSpec_bcSpec K K' Ω Ω' R
  have h1 : x ≫ cancelSpec K K' Ω' R ≫ extendSpec K Ω Ω' R ≫ baseChangeSpec K Ω R = η := by
    rw [← h']
    simp only [Category.assoc]
  have h2 : (x ≫ cancelSpec K K' Ω' R) ≫ extendSpec K Ω Ω' R ≫ baseChangeSpec K Ω R = η := by
    rw [← h']
    simp only [Category.assoc]
  rw [fundamentalGroupMap_congr hsq h h1,
    fundamentalGroupMap_comp (cancelSpec K K' Ω' R) _ rfl h2 h1,
    fundamentalGroupMap_comp (extendSpec K Ω Ω' R) (baseChangeSpec K Ω R) rfl h' h2]
  rfl

variable (Ω) in
include Ω in
omit [ConnectedSpace (Spec (.of (K' ⊗[K] R)))] [ConnectedSpace (Spec (.of R))]
  [Algebra.IsSeparable K' Ω'] [ConnectedSpace (Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))] in
/-- **`π₁ᵉᵗ(X'_{Ω'}) → π₁ᵉᵗ(X)` is injective.** -/
lemma injective_comp_bc (x : Spec (.of Ω') ⟶ Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))
    {η : Spec (.of Ω') ⟶ Spec (.of R)}
    (h : x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R = η) :
    Function.Injective
      (fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R) h) := by
  have h' : ((x ≫ cancelSpec K K' Ω' R) ≫ extendSpec K Ω Ω' R) ≫ baseChangeSpec K Ω R = η := by
    rw [← h, baseChangeSpec_bcSpec K K' Ω Ω' R]
    simp only [Category.assoc]
  intro δ₁ δ₂ hδ
  rw [fundamentalGroupMap_comp_bc Ω x h h', fundamentalGroupMap_comp_bc Ω x h h'] at hδ
  exact (fundamentalGroupMap_bijective_of_isIso _ rfl).1
    ((fundamentalGroupMap_extendSpec_bijective K (x ≫ cancelSpec K K' Ω' R)).1
      (fundamentalGroupMap_baseChange_injective' _ h' hδ))

omit [Algebra K Ω] [Algebra Ω Ω'] [IsScalarTower K Ω Ω'] [Algebra.FiniteType K R] [IsAlgClosed Ω]
  [CharZero Ω] [Countable Ω] [IsAlgClosed Ω'] [Algebra.IsSeparable K Ω]
  [Algebra.IsSeparable K' Ω'] [ConnectedSpace (Spec (.of R))]
  [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))] [ConnectedSpace (Spec (.of (K' ⊗[K] R)))]
  [ConnectedSpace (Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))] [Algebra K Ω'] [IsScalarTower K K' Ω'] in
/-- **`π₁ᵉᵗ(X'_{Ω'}) → π₁ᵉᵗ(Spec K')` is trivial** (it factors through `π₁ᵉᵗ(Spec Ω') = 1`). -/
lemma fundamentalGroupMap_bc_strSpec_eq_one
    [IsSepClosed Ω'] (x : Spec (.of Ω') ⟶ Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R))))
    (hxr : x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R)))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω' Ω')))
    {pt : Spec (.of Ω') ⟶ Spec (.of (K' ⊗[K] R))}
    (hx : x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) = pt)
    (hpt : pt ≫ strSpec K K' R = Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))) (δ : π₁ᵉᵗ(x)) :
    fundamentalGroupMap (strSpec K K' R) hpt (fundamentalGroupMap _ hx δ) = 1 := by
  have hstr := baseChangeSpec_strSpec K K' R (Ω' := Ω')
  have h1 : x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ strSpec K K' R =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) := by
    rw [← Category.assoc, hx, hpt]
  have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp _ (strSpec K K' R) hx hpt h1) δ
  have h2 : x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) =
        Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) := by
    rw [← hstr, h1]
  have h3 : (x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) =
        Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) := by
    rw [Category.assoc, h2]
  have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap Ω' (Ω' ⊗[K'] (K' ⊗[K] R)))))
    (Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))) rfl h3 h2) δ
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply] at e1 e2
  rw [← e1, fundamentalGroupMap_congr hstr h1 h2, e2,
    eq_one_of_eq_specSelf hxr (fundamentalGroupMap _ rfl δ), map_one]

variable (Ω) in
include Ω in
/-- **`Π_{X_{K'}} = Π_X ×_{π₁(Spec K)} π₁(Spec K')`** ([LocAn] Cor. 15.5, proof; SGA 1 IX/X in
characteristic `0`): for every geometric point `pt` of `X_{K'}` over `Spec Ω' ⟶ Spec K'`,
every pair `a ∈ π₁ᵉᵗ(X, pt)`, `b ∈ π₁ᵉᵗ(Spec K')` with the same image in `π₁ᵉᵗ(Spec K)` comes from a
unique `γ ∈ π₁ᵉᵗ(X_{K'}, pt)`. Hypotheses: `Ω` a countable algebraically closed separable
extension of `K` inside the algebraically closed separable extension `Ω'` of `K'`, `X_Ω`
connected, and `π₁ᵉᵗ(X_{K'}) → π₁ᵉᵗ(Spec K')` surjective (`hsurj`; e.g. `X` geometrically
connected). -/
theorem existsUnique_baseExtension (pt : Spec (.of Ω') ⟶ Spec (.of (K' ⊗[K] R)))
    (hpt : pt ≫ strSpec K K' R = Spec.map (CommRingCat.ofHom (algebraMap K' Ω')))
    (hsurj : Function.Surjective (fundamentalGroupMap (strSpec K K' R) hpt))
    (hb : Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) ≫ specExt K K' =
      (pt ≫ baseChangeSpec K K' R) ≫ strSpecR K R)
    (a : π₁ᵉᵗ(pt ≫ baseChangeSpec K K' R))
    (b : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hab : fundamentalGroupMap (strSpecR K R) rfl a = fundamentalGroupMap (specExt K K') hb b) :
    ∃! γ : π₁ᵉᵗ(pt), fundamentalGroupMap (baseChangeSpec K K' R) rfl γ = a ∧
      fundamentalGroupMap (strSpec K K' R) hpt γ = b := by
  obtain ⟨x, hx, hxr⟩ := exists_rationalLift pt hpt
  have hxg : x ≫ baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R =
      pt ≫ baseChangeSpec K K' R := by
    rw [← Category.assoc, hx]
  have hy : ((x ≫ cancelSpec K K' Ω' R) ≫ extendSpec K Ω Ω' R) ≫ baseChangeSpec K Ω R =
      pt ≫ baseChangeSpec K K' R := by
    rw [← hxg, baseChangeSpec_bcSpec K K' Ω Ω' R]
    simp only [Category.assoc]
  -- `p_* ∘ g'_* = (g' ≫ p)_*`
  have hpg (δ : π₁ᵉᵗ(x)) : fundamentalGroupMap (baseChangeSpec K K' R) rfl
      (fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R)) hx δ) =
        fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R) hxg δ := by
    have := DFunLike.congr_fun (fundamentalGroupMap_comp (baseChangeSpec K' Ω' (K' ⊗[K] R))
      (baseChangeSpec K K' R) hx rfl hxg) δ
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply] at this
    exact this.symm
  -- uniqueness
  have huniq : ∀ γ₁ γ₂ : π₁ᵉᵗ(pt),
      fundamentalGroupMap (baseChangeSpec K K' R) rfl γ₁ =
        fundamentalGroupMap (baseChangeSpec K K' R) rfl γ₂ →
      fundamentalGroupMap (strSpec K K' R) hpt γ₁ = fundamentalGroupMap (strSpec K K' R) hpt γ₂ →
        γ₁ = γ₂ := by
    intro γ₁ γ₂ h1 h2
    rw [← mul_inv_eq_one]
    have hk : fundamentalGroupMap (strSpec K K' R) hpt (γ₁ * γ₂⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    obtain ⟨δ, hδ⟩ := exists_fundamentalGroupMap_baseChange_eq'' (k := K') (Ω := Ω')
      (R := K' ⊗[K] R) x hx hpt (γ₁ * γ₂⁻¹) hk
    have hp : fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R) ≫ baseChangeSpec K K' R)
        hxg δ = 1 := by
      rw [← hpg, hδ, map_mul, map_inv, h1, mul_inv_cancel]
    have hδ1 : δ = 1 := injective_comp_bc Ω x hxg (hp.trans (map_one _).symm)
    rw [← hδ, hδ1, map_one]
  -- existence
  obtain ⟨γ₀, hγ₀⟩ := hsurj b
  have hsq' := bcSpec_strSpecR K K' R
  have ha₁1 : fundamentalGroupMap (strSpecR K R) rfl
      (a * (fundamentalGroupMap (baseChangeSpec K K' R) rfl γ₀)⁻¹) = 1 := by
    have h0 : pt ≫ baseChangeSpec K K' R ≫ strSpecR K R =
        (pt ≫ baseChangeSpec K K' R) ≫ strSpecR K R := (Category.assoc _ _ _).symm
    have h0' : pt ≫ strSpec K K' R ≫ specExt K K' =
        (pt ≫ baseChangeSpec K K' R) ≫ strSpecR K R := by
      rw [← hsq', h0]
    have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp (baseChangeSpec K K' R)
      (strSpecR K R) rfl rfl h0) γ₀
    have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp (strSpec K K' R) (specExt K K') hpt
      hb h0') γ₀
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply] at e1 e2
    rw [map_mul, map_inv, ← e1, fundamentalGroupMap_congr hsq' h0 h0', e2, hγ₀, hab,
      mul_inv_cancel]
  obtain ⟨δ₀, hδ₀⟩ := exists_fundamentalGroupMap_baseChange_eq'' (k := K) (Ω := Ω) (R := R)
    ((x ≫ cancelSpec K K' Ω' R) ≫ extendSpec K Ω Ω' R) hy rfl _ ha₁1
  obtain ⟨δ, hδ⟩ := ((fundamentalGroupMap_extendSpec_bijective K
    (x ≫ cancelSpec K K' Ω' R)).comp (fundamentalGroupMap_bijective_of_isIso
      (cancelSpec K K' Ω' R) (rfl : x ≫ _ = _))).2 δ₀
  have hA : fundamentalGroupMap (baseChangeSpec K K' R) rfl
      (fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R)) hx δ * γ₀) = a := by
    rw [map_mul, hpg, fundamentalGroupMap_comp_bc Ω x hxg hy]
    change fundamentalGroupMap (baseChangeSpec K Ω R) hy
      ((fun δ ↦ fundamentalGroupMap (extendSpec K Ω Ω' R) rfl
        (fundamentalGroupMap (cancelSpec K K' Ω' R) rfl δ)) δ) * _ = a
    rw [show (fun δ ↦ fundamentalGroupMap (extendSpec K Ω Ω' R) rfl
        (fundamentalGroupMap (cancelSpec K K' Ω' R) rfl δ)) δ = δ₀ from hδ, hδ₀,
      inv_mul_cancel_right]
  have hB : fundamentalGroupMap (strSpec K K' R) hpt
      (fundamentalGroupMap (baseChangeSpec K' Ω' (K' ⊗[K] R)) hx δ * γ₀) = b := by
    rw [map_mul, fundamentalGroupMap_bc_strSpec_eq_one x hxr hx hpt, one_mul, hγ₀]
  exact ⟨_, ⟨hA, hB⟩, fun γ hγ ↦ huniq _ _ (hγ.1.trans hA.symm) (hγ.2.trans hB.symm)⟩

end BaseExtension

/-- Base change of a property stable under base change from `Spec R ⟶ Spec K` to
`Spec (L ⊗[K] R) ⟶ Spec L`. -/
lemma of_strSpecR {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (L : Type u) [Field L] [Algebra K L] (h : P (strSpecR K R)) : P (strSpec K L R) := by
  have e : strSpec K L R = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] R).toRingHom) := rfl
  rw [e]
  exact MorphismProperty.of_isPullback (isPullback_baseChangeSpec (k := K) (Ω := L) (R := R)) h

section BaseExtensionGC

variable {K K' Ω Ω' R : Type u} [Field K] [Field K'] [Field Ω] [Field Ω'] [CommRing R]
  [Algebra K R] [Algebra K K'] [Algebra K Ω] [Algebra Ω Ω'] [Algebra K Ω'] [Algebra K' Ω']
  [IsScalarTower K Ω Ω'] [IsScalarTower K K' Ω']
  [Algebra.FiniteType K R] [IsAlgClosed Ω] [CharZero Ω] [Countable Ω] [IsAlgClosed Ω']
  [Algebra.IsSeparable K Ω] [Algebra.IsSeparable K' Ω']
  [GeometricallyConnected (strSpecR K R)] [UniversallyOpen (strSpecR K R)]

omit [Algebra K Ω] [Algebra Ω Ω'] [IsScalarTower K Ω Ω'] [Algebra.FiniteType K R] [IsAlgClosed Ω]
  [CharZero Ω] [Countable Ω] [IsAlgClosed Ω'] [Algebra.IsSeparable K Ω]
  [Algebra.IsSeparable K' Ω'] [UniversallyOpen (strSpecR K R)] in
/-- `X_{K'}` is connected if `X` is geometrically connected. -/
lemma connectedSpace_baseExt : ConnectedSpace (Spec (.of (K' ⊗[K] R))) :=
  haveI : GeometricallyConnected (strSpec K K' R) := of_strSpecR K' ‹_›
  GeometricallyConnected.connectedSpace_of_subsingleton (f := strSpec K K' R)

variable (Ω) in
include Ω in
/-- **`Π_{X_{K'}} = Π_X ×_{π₁(Spec K)} π₁(Spec K')`** for `X = Spec R` geometrically connected
over `K` (`existsUnique_baseExtension` with the connectedness and surjectivity hypotheses
discharged). -/
theorem existsUnique_baseExtension_of_geometricallyConnected
    (pt : Spec (.of Ω') ⟶ Spec (.of (K' ⊗[K] R)))
    (hpt : pt ≫ strSpec K K' R = Spec.map (CommRingCat.ofHom (algebraMap K' Ω')))
    (hb : Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) ≫ specExt K K' =
      (pt ≫ baseChangeSpec K K' R) ≫ strSpecR K R)
    (a : π₁ᵉᵗ(pt ≫ baseChangeSpec K K' R))
    (b : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hab : fundamentalGroupMap (strSpecR K R) rfl a = fundamentalGroupMap (specExt K K') hb b) :
    ∃! γ : π₁ᵉᵗ(pt), fundamentalGroupMap (baseChangeSpec K K' R) rfl γ = a ∧
      fundamentalGroupMap (strSpec K K' R) hpt γ = b := by
  haveI hR : ConnectedSpace (Spec (.of R)) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := strSpecR K R)
  haveI : ConnectedSpace (Spec (.of (Ω ⊗[K] R))) :=
    haveI : GeometricallyConnected (strSpec K Ω R) := of_strSpecR Ω ‹_›
    GeometricallyConnected.connectedSpace_of_subsingleton (f := strSpec K Ω R)
  haveI : GeometricallyConnected (strSpec K K' R) := of_strSpecR K' ‹_›
  haveI : UniversallyOpen (strSpec K K' R) := of_strSpecR K' ‹_›
  haveI : ConnectedSpace (Spec (.of (K' ⊗[K] R))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := strSpec K K' R)
  haveI : ConnectedSpace (Spec (.of (Ω' ⊗[K'] (K' ⊗[K] R)))) :=
    haveI : GeometricallyConnected (strSpec K' Ω' (K' ⊗[K] R)) := of_strSpecR Ω' ‹_›
    GeometricallyConnected.connectedSpace_of_subsingleton (f := strSpec K' Ω' (K' ⊗[K] R))
  exact existsUnique_baseExtension Ω pt hpt
    (fundamentalGroupMap_surjective_of_geometricallyConnected _ hpt) hb a b hab

end BaseExtensionGC


end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

open AlgebraicGeometry.FiniteEtale Belyi.Anabelian

variable {K : Type u} [Field K] [NumberField K] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

include hc in
lemma geometricallyConnected_strSpecR : GeometricallyConnected (strSpecR K Γ(C.Xbar, C.U)) := by
  haveI := isIntegral_specSections C hc
  have hU := isAffineOpen_U C hc
  haveI : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))) := by
    rw [← isoSpec_inv_ι_structure K hU, ← Category.assoc]
    infer_instance
  change GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
  infer_instance

omit [NumberField K] in
lemma universallyOpen_strSpecR : UniversallyOpen (strSpecR K Γ(C.Xbar, C.U)) := by
  change UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
  infer_instance

variable (K' Ω Ω' : Type u) [Field K'] [Field Ω] [Field Ω'] [Algebra K K'] [Algebra K Ω]
  [Algebra Ω Ω'] [Algebra K Ω'] [Algebra K' Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K K' Ω']
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω']

include hc Ω in
/-- **`Π_{U_{K'}} = Π_U ×_{G_K} G_{K'}`** for an affine hyperbolic curve `U` (with a cusp) over a
number field `K` and any field extension `K'` of `K` (e.g. `K' = K_v`), at geometric points over
an algebraic closure `Ω'` of `K'` containing an algebraic closure `Ω` of `K` ([LocAn]
Cor. 15.5, proof, l.4344–4350: "By base-changing to `L`"). Here `U_{K'} = Spec (K' ⊗[K] Γ(U))`
and `π₁ᵉᵗ(Spec K)`, `π₁ᵉᵗ(Spec K')` are taken at `Spec Ω'`. -/
theorem existsUnique_baseExtension_hypCurve
    (pt : Spec (.of Ω') ⟶ Spec (.of (K' ⊗[K] Γ(C.Xbar, C.U))))
    (hpt : pt ≫ strSpec K K' Γ(C.Xbar, C.U) = Spec.map (CommRingCat.ofHom (algebraMap K' Ω')))
    (hb : Spec.map (CommRingCat.ofHom (algebraMap K' Ω')) ≫ specExt K K' =
      (pt ≫ baseChangeSpec K K' Γ(C.Xbar, C.U)) ≫ strSpecR K Γ(C.Xbar, C.U))
    (a : π₁ᵉᵗ(pt ≫ baseChangeSpec K K' Γ(C.Xbar, C.U)))
    (b : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hab : fundamentalGroupMap (strSpecR K Γ(C.Xbar, C.U)) rfl a =
      fundamentalGroupMap (specExt K K') hb b) :
    ∃! γ : π₁ᵉᵗ(pt), fundamentalGroupMap (baseChangeSpec K K' Γ(C.Xbar, C.U)) rfl γ = a ∧
      fundamentalGroupMap (strSpec K K' Γ(C.Xbar, C.U)) hpt γ = b := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI := countable_of_numberField Ω K
  haveI := finiteType_sectionsU C hc
  haveI := geometricallyConnected_strSpecR C hc
  haveI := universallyOpen_strSpecR C
  exact existsUnique_baseExtension_of_geometricallyConnected Ω pt hpt hb a b hab

end CurvesJacobian.Cusp
