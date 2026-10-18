/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PicAction
import CurvesJacobian.Cusp.CurveGaloisData
import CurvesJacobian.Cusp.ArithmeticFill
import CurvesJacobian.Picard.GaloisPoints
import CurvesJacobian.Scheme.CurvePlaces
import CurvesJacobian.Scheme.CurveFunctionField

/-!
# The function field of `X_{k̄}` in the Galois model

Let `X` be a curve over a field `k` of characteristic `0`, `τ ∈ K(X)` transcendental, and
`D = curveGaloisData k hτ` its Galois model (`Ω = K(X)^alg`, `H = Gal(Ω/K(X))`). Let
`k̄ = kbar k Ω` and `X_{k̄} = X ×_k k̄` (`baseChangeKbar k X`, a curve over `k̄`). The function
field `F' = F (baseChange D)` of the base-changed Galois model is the function field of `X_{k̄}`:

* `CurvesJacobian.Kummer.functionFieldMap f hf`: `K(Z) → K(Y)` for a morphism of integral schemes
  preserving generic points; `ffMap k X : K(X) → K(X_{k̄})` for the projection `X_{k̄} ⟶ X`.
* `CurvesJacobian.Kummer.bcSecEquiv`: `Γ(X_K, U_K) ≃ K ⊗[k] Γ(X, U)` for an affine open `U`.
* `CurvesJacobian.Kummer.tensorToOmega_injective`: `k̄ ⊗[k] Γ(X, U) → Ω`, `c ⊗ r ↦ c r`, is
  injective (the tensor product is a domain by geometric integrality and integral over
  `Γ(X, U)`; `Ideal.eq_bot_of_comap_eq_bot`); hence an embedding
  `ffToOmega : K(X_{k̄}) → Ω`, which is the identity on `k̄` and on `K(X)`.
* Its image is `F'` (`exists_ffToOmega_eq`, by the infinite Galois correspondence:
  `Gal(Ω/image)` fixes `k̄` and `L = K(X)`, so lies in `H' = H ∩ Gal(Ω/k̄(t))`).
* **`CurvesJacobian.Kummer.ffEquiv k hτ : F (baseChange D) ≃ₐ[k̄] K(X_{k̄})`**, with
  `coe_ffEquiv_symm_ffMap`, `ffEquiv_eq_ffMap`, `ffEquiv_curveEquivL` (compatibility with
  `K(X) ≃ L` and `K(X) → K(X_{k̄})`).

Galois action: for `g ∈ G_k`, `galMap k g = α_g = 𝟙_X ×_k Spec(g) : X_{k̄} ⟶ X_{k̄}` (`bcMap` along
`specAut g`, as in `CurvesJacobian.picGal`) is an isomorphism; `galFF k g = φ_g` is the pull-back
`f ↦ f ∘ α_g` on `K(X_{k̄})` (stalk map at the generic point).

* **`CurvesJacobian.Kummer.ffEquiv_autF`**: `ffEquiv (h x) = φ_g (ffEquiv x)` for `h ∈ H`,
  `g = hToGk h` (on sections over `U_{k̄}`, `α_g` is `g ⊗ id`, `bcSecEquiv_galMap`).
* **`CurvesJacobian.Kummer.galFF_mem_stalkValuationSubring_iff`**: `φ_g f ∈ 𝒪_{X_{k̄}, y}` iff
  `f ∈ 𝒪_{X_{k̄}, α_g y}` (general form: `functionFieldMap_mem_stalkValuationSubring_iff`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open scoped TensorProduct

universe u
noncomputable section
namespace CurvesJacobian.Kummer
open CurvesJacobian.Cusp

section FunctionFieldMap

variable {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
  (hf : f (genericPoint Y) = genericPoint Z)

/-- The map `K(Z) → K(Y)` of function fields induced by a morphism `f : Y ⟶ Z` of integral
schemes mapping the generic point to the generic point (pull-back of rational functions). -/
def functionFieldMap : Z.functionField →+* Y.functionField :=
  (Z.presheaf.stalkSpecializes (hf ▸ specializes_rfl :
    f (genericPoint Y) ⤳ genericPoint Z) ≫ f.stalkMap (genericPoint Y)).hom

lemma functionFieldMap_germ (V : Z.Opens) [Nonempty V] [Nonempty (f ⁻¹ᵁ V)] (s : Γ(Z, V)) :
    functionFieldMap f hf (Z.germToFunctionField V s) =
      Y.germToFunctionField (f ⁻¹ᵁ V) (f.app V s) := by
  change (Z.presheaf.germ V _ _ ≫ Z.presheaf.stalkSpecializes _ ≫ f.stalkMap _).hom s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  rfl

end FunctionFieldMap

section General

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The projection `X_K ⟶ X` maps the generic point to the generic point. -/
lemma fst_genericPoint [IsIntegral X] [IsIntegral (Cusp.baseChange k K X)] :
    pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k K) (genericPoint (Cusp.baseChange k K X))
      = genericPoint X := by
  haveI := surjective_specAlgebraMap k K
  set f := pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k K)
  have h := (genericPoint_spec (Cusp.baseChange k K X)).image f.continuous
  rw [Set.image_univ, f.surjective.range_eq, closure_univ] at h
  exact ((genericPoint_spec X).eq h).symm

lemma isAffineOpen_baseChangeOpen' {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (baseChangeOpen k K U) :=
  IsAffine.of_isIso (specTensorIsoBaseChangeOpen k K hU).inv

/-- `Spec (K ⊗[k] Γ(X, U)) ≅ U_K ≅ Spec Γ(X_K, U_K)`. -/
abbrev bcSpecIso {U : X.Opens} (hU : IsAffineOpen U) :
    Spec (.of (K ⊗[k] Γ(X, U))) ≅ Spec Γ(Cusp.baseChange k K X, baseChangeOpen k K U) :=
  specTensorIsoBaseChangeOpen k K hU ≪≫ (isAffineOpen_baseChangeOpen' k K hU).isoSpec

/-- **`Γ(X_K, U_K) ≃ K ⊗[k] Γ(X, U)`** for an affine open `U ⊆ X`. -/
def bcSecEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(Cusp.baseChange k K X, baseChangeOpen k K U) ≃+* K ⊗[k] Γ(X, U) where
  toFun := (Spec.preimage (bcSpecIso k K hU).hom).hom
  invFun := (Spec.preimage (bcSpecIso k K hU).inv).hom
  left_inv s := by
    have h : Spec.preimage (bcSpecIso k K hU).hom ≫ Spec.preimage (bcSpecIso k K hU).inv = 𝟙 _ := by
      apply Spec.map_injective
      simp
    exact congrArg (fun φ ↦ φ.hom s) h
  right_inv s := by
    have h : Spec.preimage (bcSpecIso k K hU).inv ≫ Spec.preimage (bcSpecIso k K hU).hom = 𝟙 _ := by
      apply Spec.map_injective
      simp
    exact congrArg (fun φ ↦ φ.hom s) h
  map_mul' := map_mul _
  map_add' := map_add _

lemma specMap_bcSecEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (bcSecEquiv k K hU).toRingHom) = (bcSpecIso k K hU).hom := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage (bcSpecIso k K hU).hom).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The `K`-algebra structure: `bcSecEquiv` maps the constant `c` to `c ⊗ 1`. -/
lemma bcSecEquiv_algebraMap {U : X.Opens} (hU : IsAffineOpen U) (c : K) :
    bcSecEquiv k K hU (letI := sectionsAlgebra K (Cusp.baseChange k K X) (baseChangeOpen k K U)
      algebraMap K _ c) = algebraMap K (K ⊗[k] Γ(X, U)) c := by
  letI := sectionsAlgebra K (Cusp.baseChange k K X) (baseChangeOpen k K U)
  have key : CommRingCat.ofHom ((bcSecEquiv k K hU).toRingHom.comp
      (algebraMap K Γ(Cusp.baseChange k K X, baseChangeOpen k K U))) =
      CommRingCat.ofHom (algebraMap K (K ⊗[k] Γ(X, U))) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_bcSecEquiv,
      ← fromSpec_comp_structure K (Cusp.baseChange k K X) (isAffineOpen_baseChangeOpen' k K hU),
      ← specTensorIso_hom_ι_snd k K hU, ← IsAffineOpen.isoSpec_inv_ι]
    simp
    rfl
  exact congrArg (fun φ ↦ φ.hom c) key

/-- `bcSecEquiv` maps the pull-back of `r ∈ Γ(X, U)` to `1 ⊗ r`. -/
lemma bcSecEquiv_app {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    bcSecEquiv k K hU ((pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k K)).app U r) =
      (1 : K) ⊗ₜ r := by
  set f := pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k K)
  have key : CommRingCat.ofHom ((bcSecEquiv k K hU).toRingHom.comp (f.app U).hom) =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Γ(X, U) →ₐ[k] K ⊗[k] Γ(X, U)).toRingHom := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec]
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_baseChangeOpen' k K hU)
      (le_refl _)
    rw [← Scheme.Hom.app_eq_appLE] at h1
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_bcSecEquiv, CommRingCat.ofHom_hom,
      Category.assoc, h1, ← FiniteEtale.baseChangeSpec, ← specTensorIso_hom_ι_fst k K hU,
      ← IsAffineOpen.isoSpec_inv_ι]
    simp [f]
  exact congrArg (fun φ ↦ φ.hom r) key

end General

section Model

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- `Γ(X, U) → K(X) → Ω = K(X)^alg`, as a `k`-algebra map. -/
def secToOmega (U : X.Opens) [Nonempty U] : Γ(X, U) →ₐ[k] FFClosure X :=
  { (algebraMap X.functionField (FFClosure X)).comp (X.germToFunctionField U).hom with
    commutes' c := by
      rw [IsScalarTower.algebraMap_apply k X.functionField (FFClosure X),
        algebraMap_functionField_eq_germ k X U c]
      rfl }

lemma secToOmega_apply (U : X.Opens) [Nonempty U] (r : Γ(X, U)) :
    secToOmega k U r = algebraMap X.functionField (FFClosure X) (X.germToFunctionField U r) :=
  rfl

lemma secToOmega_injective (U : X.Opens) [Nonempty U] :
    Function.Injective (secToOmega k U) :=
  (algebraMap X.functionField (FFClosure X)).injective.comp (X.germToFunctionField_injective U)

/-- `θ_U : k̄ ⊗[k] Γ(X, U) → Ω`, `c ⊗ r ↦ c · r`. -/
def tensorToOmega (U : X.Opens) [Nonempty U] :
    kbar k (FFClosure X) ⊗[k] Γ(X, U) →ₐ[k] FFClosure X :=
  Algebra.TensorProduct.lift (kbar k (FFClosure X)).val (secToOmega k U)
    fun _ _ ↦ Commute.all _ _

@[simp]
lemma tensorToOmega_tmul (U : X.Opens) [Nonempty U] (c : kbar k (FFClosure X)) (r : Γ(X, U)) :
    tensorToOmega k U (c ⊗ₜ r) = (c : FFClosure X) * secToOmega k U r :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **`θ_U` is injective**: `k̄ ⊗[k] Γ(X, U)` is a domain (geometric integrality), integral over
`Γ(X, U)`, and `θ_U` is injective on `Γ(X, U)`. -/
lemma tensorToOmega_injective [IsCurveOver k X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    Function.Injective (tensorToOmega k U) := by
  set R := Γ(X, U)
  set kb := kbar k (FFClosure X)
  haveI : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsDomain (kb ⊗[k] R) :=
    isDomain_tensorProduct_of_geometricallyIntegral (K := kb) (X ↘ Spec (CommRingCat.of k))
      hU.fromSpec (fromSpec_comp_structure k X hU)
  let c := Algebra.TensorProduct.comm k R kb
  haveI : IsDomain (R ⊗[k] kb) := c.toMulEquiv.isDomain
  haveI : Nontrivial R := inferInstance
  let θ' : R ⊗[k] kb →+* FFClosure X := (tensorToOmega k U).toRingHom.comp c.toRingHom
  have hθ' : Function.Injective θ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : (RingHom.ker θ').comap (algebraMap R (R ⊗[k] kb)) = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker] at hr
      change tensorToOmega k U (c (r ⊗ₜ 1)) = 0 at hr
      rw [Algebra.TensorProduct.comm_tmul, tensorToOmega_tmul] at hr
      simp only [OneMemClass.coe_one, one_mul] at hr
      rw [Ideal.mem_bot]
      exact secToOmega_injective k U (hr.trans (map_zero _).symm)
    have := Ideal.eq_bot_of_comap_eq_bot hker
    rw [← RingHom.mem_ker, this, Ideal.mem_bot] at hx
    exact hx
  intro a b hab
  apply c.symm.injective
  apply hθ'
  change tensorToOmega k U (c (c.symm a)) = tensorToOmega k U (c (c.symm b))
  simpa using hab

end Model

section Embedding

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X]

/-- The base change `X_{k̄} = X ×_k k̄` to the algebraic closure `k̄` of `k` in `Ω = K(X)^alg`. -/
abbrev baseChangeKbar : Scheme.{u} := Cusp.baseChange k (kbar k (FFClosure X)) X

instance isIntegral_baseChangeKbar : IsIntegral (baseChangeKbar k X) :=
  IsCurveOver.isIntegral (kbar k (FFClosure X)) _

/-- The map `K(X) → K(X_{k̄})` induced by the projection `X_{k̄} ⟶ X`. -/
abbrev ffMap : X.functionField →+* (baseChangeKbar k X).functionField :=
  functionFieldMap _ (fst_genericPoint k (kbar k (FFClosure X)))

variable {X}

instance nonempty_baseChangeOpen' (K : Type u) [Field K] [Algebra k K] (U : X.Opens)
    [Nonempty U] : Nonempty (baseChangeOpen k K U) :=
  (nonempty_baseChangeOpen k K ⟨_, (Classical.arbitrary U).2⟩).to_subtype

/-- `Γ(X_{k̄}, U_{k̄}) ≃ k̄ ⊗[k] Γ(X, U) → Ω`. -/
def secBarToOmega {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U) →+* FFClosure X :=
  (tensorToOmega k U).toRingHom.comp (bcSecEquiv k (kbar k (FFClosure X)) hU).toRingHom

lemma secBarToOmega_injective {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    Function.Injective (secBarToOmega k hU) :=
  (tensorToOmega_injective k hU).comp (bcSecEquiv k _ hU).injective

/-- **The embedding `K(X_{k̄}) → Ω`**, extending `secBarToOmega` to the fraction field. -/
def ffToOmega {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (baseChangeKbar k X).functionField →+* FFClosure X :=
  haveI := functionField_isFractionRing_of_isAffineOpen (baseChangeKbar k X) _
    (isAffineOpen_baseChangeOpen' k (kbar k (FFClosure X)) hU)
  IsFractionRing.lift (secBarToOmega_injective k hU)

lemma ffToOmega_germ {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (s : Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U)) :
    ffToOmega k hU ((baseChangeKbar k X).germToFunctionField _ s) =
      tensorToOmega k U (bcSecEquiv k _ hU s) := by
  haveI := functionField_isFractionRing_of_isAffineOpen (baseChangeKbar k X) _
    (isAffineOpen_baseChangeOpen' k (kbar k (FFClosure X)) hU)
  exact IsFractionRing.lift_algebraMap (secBarToOmega_injective k hU) s

/-- `K(X_{k̄}) → Ω` is the identity on `k̄`. -/
lemma ffToOmega_algebraMap {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (c : kbar k (FFClosure X)) :
    ffToOmega k hU (algebraMap (kbar k (FFClosure X)) (baseChangeKbar k X).functionField c) =
      c := by
  rw [algebraMap_functionField_eq_germ (kbar k (FFClosure X)) (baseChangeKbar k X)
    (baseChangeOpen k (kbar k (FFClosure X)) U) c, ffToOmega_germ, bcSecEquiv_algebraMap,
    Algebra.TensorProduct.algebraMap_apply, tensorToOmega_tmul, map_one, mul_one]
  rfl

lemma ffToOmega_ffMap_germ {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (r : Γ(X, U)) :
    ffToOmega k hU (ffMap k X (X.germToFunctionField U r)) =
      algebraMap X.functionField (FFClosure X) (X.germToFunctionField U r) := by
  rw [ffMap, functionFieldMap_germ, ffToOmega_germ, bcSecEquiv_app, tensorToOmega_tmul,
    secToOmega_apply]
  simp

/-- **`K(X) → K(X_{k̄}) → Ω` is the inclusion `K(X) ⊆ Ω`.** -/
lemma ffToOmega_ffMap {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (e : X.functionField) :
    ffToOmega k hU (ffMap k X e) = algebraMap X.functionField (FFClosure X) e := by
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) e
  simp only [map_div₀]
  exact congrArg₂ (· / ·) (ffToOmega_ffMap_germ k hU r) (ffToOmega_ffMap_germ k hU s)

end Embedding

section GaloisModel

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- `K(X) ⊆ L ⊆ F ⊆ F k̄`. -/
lemma algebraMap_mem_F (e : X.functionField) :
    algebraMap X.functionField (FFClosure X) e ∈
      F (Kummer.baseChange (curveGaloisData k hτ)) := by
  apply le_F_baseChange
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change σ ∈ (imageL (k := k) τ).fixingSubgroup at hσ
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨e, rfl⟩

lemma tensorToOmega_mem_F (U : X.Opens) [Nonempty U]
    (x : kbar k (FFClosure X) ⊗[k] Γ(X, U)) :
    tensorToOmega k U x ∈ F (Kummer.baseChange (curveGaloisData k hτ)) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c r =>
    rw [tensorToOmega_tmul, secToOmega_apply]
    exact mul_mem (kbar_le_F_baseChange _ c.2) (algebraMap_mem_F k hτ _)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The image of `K(X_{k̄}) → Ω` lies in `F k̄`. -/
lemma ffToOmega_mem_F {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (z : (baseChangeKbar k X).functionField) :
    ffToOmega k hU z ∈ F (Kummer.baseChange (curveGaloisData k hτ)) := by
  haveI := functionField_isFractionRing_of_isAffineOpen (baseChangeKbar k X) _
    (isAffineOpen_baseChangeOpen' k (kbar k (FFClosure X)) hU)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U)) z
  rw [map_div₀]
  exact div_mem (by
      rw [show algebraMap _ (baseChangeKbar k X).functionField a =
        (baseChangeKbar k X).germToFunctionField _ a from rfl, ffToOmega_germ]
      exact tensorToOmega_mem_F k hτ U _)
    (by
      rw [show algebraMap _ (baseChangeKbar k X).functionField b =
        (baseChangeKbar k X).germToFunctionField _ b from rfl, ffToOmega_germ]
      exact tensorToOmega_mem_F k hτ U _)

/-- **Every element of `F k̄` comes from `K(X_{k̄})`** (Galois correspondence: an element of
`Gal(Ω/k̄(t))` fixing the image of `K(X_{k̄})` fixes `k̄` and `K(X) = L`, hence lies in
`H' = H ∩ Gal(Ω/k̄(t))`). -/
lemma exists_ffToOmega_eq {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {x : FFClosure X}
    (hx : x ∈ F (Kummer.baseChange (curveGaloisData k hτ))) :
    ∃ z, ffToOmega k hU z = x := by
  set ψ := ffToOmega k hU
  let E₁ : IntermediateField (kbar k (FFClosure X)) (FFClosure X) :=
    ψ.fieldRange.toIntermediateField fun c ↦ ⟨_, ffToOmega_algebraMap k hU c⟩
  have hle : K₀ (kbar k (FFClosure X)) (coordT τ) ≤ E₁ :=
    IntermediateField.adjoin_simple_le_iff.2 ⟨ffMap k X τ, ffToOmega_ffMap k hU τ⟩
  let E : IntermediateField (K₀ (kbar k (FFClosure X)) (coordT τ)) (FFClosure X) :=
    ψ.fieldRange.toIntermediateField fun y ↦ hle y.2
  change x ∈ E
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσH : σ ∈ (Kummer.baseChange (curveGaloisData k hτ)).H := by
    rw [mem_baseChange_H]
    change resK₀ k (coordT τ) σ ∈ (imageL (k := k) τ).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨e, rfl⟩ := (mem_imageL_iff y).1 hy
    rw [resK₀_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
      ⟨ffMap k X e, ffToOmega_ffMap k hU e⟩
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσH

/-- `K(X_{k̄}) ≃ F k̄`, for a given chart `U`. -/
def ffEquivAux {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (baseChangeKbar k X).functionField ≃+* F (Kummer.baseChange (curveGaloisData k hτ)) :=
  RingEquiv.ofBijective ((ffToOmega k hU).codRestrict _ (ffToOmega_mem_F k hτ hU))
    ⟨fun _ _ h ↦ (ffToOmega k hU).injective (congrArg Subtype.val h), fun x ↦
      let ⟨z, hz⟩ := exists_ffToOmega_eq k hτ hU x.2
      ⟨z, Subtype.ext hz⟩⟩

lemma coe_ffEquivAux {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (z : (baseChangeKbar k X).functionField) :
    (ffEquivAux k hτ hU z : FFClosure X) = ffToOmega k hU z := rfl

variable (X) in
lemma exists_isAffineOpen_nonempty : ∃ U : X.Opens, IsAffineOpen U ∧ Nonempty U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := genericPoint X) (u := ((⊤ : X.Opens) : Set X)) trivial (⊤ : X.Opens).2
  exact ⟨V, hV, ⟨⟨_, hx⟩⟩⟩

variable (X) in
/-- A chosen nonempty affine open of `X`. -/
def chartU : X.Opens := (exists_isAffineOpen_nonempty X).choose

variable (X) in
lemma isAffineOpen_chartU : IsAffineOpen (chartU X) :=
  (exists_isAffineOpen_nonempty X).choose_spec.1

instance nonempty_chartU : Nonempty (chartU X) :=
  (exists_isAffineOpen_nonempty X).choose_spec.2

/-- **The function field of `X_{k̄}` is `F k̄`**: `F (baseChange D) ≃ₐ[k̄] K(X_{k̄})` for the Galois
model `D = curveGaloisData k hτ` of the curve `X`. -/
def ffEquiv : F (Kummer.baseChange (curveGaloisData k hτ)) ≃ₐ[kbar k (FFClosure X)]
    (baseChangeKbar k X).functionField :=
  AlgEquiv.ofRingEquiv (f := (ffEquivAux k hτ (isAffineOpen_chartU X)).symm) fun c ↦ by
    apply (ffEquivAux k hτ (isAffineOpen_chartU X)).injective
    rw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (ffToOmega_algebraMap k (isAffineOpen_chartU X) c).symm

/-- `ffEquiv⁻¹ : K(X_{k̄}) → F k̄ ⊆ Ω` is the embedding `ffToOmega` of the chart `chartU X`. -/
lemma coe_ffEquiv_symm (z : (baseChangeKbar k X).functionField) :
    ((ffEquiv k hτ).symm z : FFClosure X) = ffToOmega k (isAffineOpen_chartU X) z := rfl

/-- **Compatibility with `K(X)`**: `ffEquiv⁻¹` maps the pull-back of `e ∈ K(X)` to `e ∈ Ω`. -/
lemma coe_ffEquiv_symm_ffMap (e : X.functionField) :
    ((ffEquiv k hτ).symm (ffMap k X e) : FFClosure X) =
      algebraMap X.functionField (FFClosure X) e :=
  ffToOmega_ffMap k _ e

lemma ffEquiv_eq_ffMap {x : F (Kummer.baseChange (curveGaloisData k hτ))} {e : X.functionField}
    (h : (x : FFClosure X) = algebraMap X.functionField (FFClosure X) e) :
    ffEquiv k hτ x = ffMap k X e := by
  apply (ffEquiv k hτ).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact Subtype.ext ((coe_ffEquiv_symm_ffMap k hτ e).trans h.symm).symm

/-- **Compatibility with `K(X) ≃ L`**: `ffEquiv` maps `curveEquivL e ∈ L ⊆ F k̄` to the pull-back
of `e` along `X_{k̄} ⟶ X`. -/
lemma ffEquiv_curveEquivL (e : X.functionField) :
    ffEquiv k hτ ⟨(curveEquivL k hτ e : FFClosure X), algebraMap_mem_F k hτ e⟩ = ffMap k X e :=
  ffEquiv_eq_ffMap k hτ (curveEquivL_apply k hτ e)

end GaloisModel

section Places

variable {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
  (hf : f (genericPoint Y) = genericPoint Z)

lemma functionFieldMap_germ_appLE (V : Z.Opens) (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ V) [Nonempty V]
    [Nonempty W] (s : Γ(Z, V)) :
    functionFieldMap f hf (Z.germToFunctionField V s) =
      Y.germToFunctionField W (f.appLE V W hW s) := by
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hW (Classical.arbitrary W).2⟩⟩
  rw [functionFieldMap_germ, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

/-- The stalk map at `y` and the function field map are compatible with `𝒪_{Z,f y} ⊆ K(Z)` and
`𝒪_{Y,y} ⊆ K(Y)`. -/
lemma algebraMap_stalkMap (y : Y) (s : Z.presheaf.stalk (f y)) :
    algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y s) =
      functionFieldMap f hf (algebraMap (Z.presheaf.stalk (f y)) Z.functionField s) := by
  have h1 := f.stalkSpecializes_stalkMap (genericPoint Y) y (genericPoint_specializes y)
  change (f.stalkMap y ≫ Y.presheaf.stalkSpecializes _).hom s =
    (Z.presheaf.stalkSpecializes _ ≫ Z.presheaf.stalkSpecializes _ ≫ f.stalkMap _).hom s
  rw [← h1, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

variable (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
  (hZ : ∀ z : Z, ValuationRing (Z.presheaf.stalk z))

/-- **Isomorphisms transport the stalk valuation rings**: for an isomorphism `f : Y ⟶ Z` of
integral schemes, `a ∈ 𝒪_{Z, f y}` iff its pull-back `f^♯ a ∈ 𝒪_{Y, y}`. -/
lemma functionFieldMap_mem_stalkValuationSubring_iff [IsIso f] (y : Y) (a : Z.functionField) :
    functionFieldMap f hf a ∈ stalkValuationSubring hY y ↔
      a ∈ stalkValuationSubring hZ (f y) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).2 t
    refine ⟨s, (functionFieldMap f hf).injective ?_⟩
    rw [← ht]
    exact (algebraMap_stalkMap f hf y s).symm
  · rintro ⟨s, rfl⟩
    exact ⟨f.stalkMap y s, algebraMap_stalkMap f hf y s⟩

end Places

section GaloisAction

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- **The Galois action on `X_{k̄}`**: for `g ∈ G_k = Gal(k̄/k)`, the automorphism
`α_g = 𝟙_X ×_k Spec(g)` of `X_{k̄}` (`bcMap` along `specAut g`, as for `picGal`). -/
def galMap (g : Gk k (FFClosure X)) : baseChangeKbar k X ⟶ baseChangeKbar k X :=
  bcMap (X ↘ Spec (.of k)) (specAut g) (specAlgebraMap k (kbar k (FFClosure X)))
    (specAlgebraMap k (kbar k (FFClosure X))) (specAut_comp_specAlgebraMap g)

@[reassoc (attr := simp)]
lemma galMap_fst (g : Gk k (FFClosure X)) :
    galMap k g ≫ pullback.fst _ _ = pullback.fst _ _ :=
  bcMap_fst _ _ _ _ _

@[reassoc (attr := simp)]
lemma galMap_snd (g : Gk k (FFClosure X)) :
    galMap k g ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specAut g :=
  bcMap_snd _ _ _ _ _

lemma galMap_mul (a b : Gk k (FFClosure X)) : galMap k (a * b) = galMap k a ≫ galMap k b := by
  apply pullback.hom_ext
  · simp
  · rw [galMap_snd, Category.assoc, galMap_snd, galMap_snd_assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

lemma galMap_one : galMap k (1 : Gk k (FFClosure X)) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · have : specAut (1 : Gk k (FFClosure X)) = 𝟙 _ := by
      rw [← Spec.map_id]
      rfl
    rw [galMap_snd, Category.id_comp, this, Category.comp_id]

instance isIso_galMap (g : Gk k (FFClosure X)) : IsIso (galMap k g) :=
  ⟨galMap k g⁻¹, by rw [← galMap_mul, mul_inv_cancel, galMap_one],
    by rw [← galMap_mul, inv_mul_cancel, galMap_one]⟩

variable [IsCurveOver k X]

lemma galMap_genericPoint (g : Gk k (FFClosure X)) :
    galMap k g (genericPoint (baseChangeKbar k X)) = genericPoint (baseChangeKbar k X) :=
  genericPoint_eq_of_isOpenImmersion _

/-- **The action of `g ∈ G_k` on `K(X_{k̄})`**: pull-back of rational functions along `α_g`,
`φ_g(f) = f ∘ α_g` (the stalk map of `α_g` at the generic point). -/
abbrev galFF (g : Gk k (FFClosure X)) :
    (baseChangeKbar k X).functionField →+* (baseChangeKbar k X).functionField :=
  functionFieldMap (galMap k g) (galMap_genericPoint k g)

/-- `g ⊗ id` on `k̄ ⊗[k] Γ(X, U)`. -/
abbrev tensorGal (g : Gk k (FFClosure X)) (U : X.Opens) :
    kbar k (FFClosure X) ⊗[k] Γ(X, U) →ₐ[k] kbar k (FFClosure X) ⊗[k] Γ(X, U) :=
  Algebra.TensorProduct.map (g : kbar k (FFClosure X) →ₐ[k] kbar k (FFClosure X))
    (AlgHom.id k Γ(X, U))

omit [IsCurveOver k X] in
lemma specMap_tensorGal_baseChangeSpec (g : Gk k (FFClosure X)) (U : X.Opens) :
    Spec.map (CommRingCat.ofHom (tensorGal k g U).toRingHom) ≫
      FiniteEtale.baseChangeSpec k (kbar k (FFClosure X)) Γ(X, U) =
      FiniteEtale.baseChangeSpec k (kbar k (FFClosure X)) Γ(X, U) := by
  rw [FiniteEtale.baseChangeSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

omit [IsCurveOver k X] in
lemma specTensorIso_galMap (g : Gk k (FFClosure X)) {U : X.Opens} (hU : IsAffineOpen U) :
    (specTensorIsoBaseChangeOpen k (kbar k (FFClosure X)) hU).hom ≫
        (baseChangeOpen k (kbar k (FFClosure X)) U).ι ≫ galMap k g =
      Spec.map (CommRingCat.ofHom (tensorGal k g U).toRingHom) ≫
        (specTensorIsoBaseChangeOpen k (kbar k (FFClosure X)) hU).hom ≫
          (baseChangeOpen k (kbar k (FFClosure X)) U).ι := by
  apply pullback.hom_ext
  · simp only [Category.assoc, galMap_fst, specTensorIso_hom_ι_fst]
    rw [← Category.assoc, specMap_tensorGal_baseChangeSpec]
  · simp only [Category.assoc, galMap_snd]
    rw [reassoc_of% (specTensorIso_hom_ι_snd k (kbar k (FFClosure X)) hU),
      specTensorIso_hom_ι_snd, ← Spec.map_comp, ← Spec.map_comp]
    congr 1

omit [IsCurveOver k X] in
lemma le_preimage_galMap (g : Gk k (FFClosure X)) (U : X.Opens) :
    baseChangeOpen k (kbar k (FFClosure X)) U ≤
      galMap k g ⁻¹ᵁ baseChangeOpen k (kbar k (FFClosure X)) U :=
  (congrArg (fun φ ↦ φ ⁻¹ᵁ U) (galMap_fst k g)).symm.le

omit [IsCurveOver k X] in
/-- On sections over `U_{k̄} ≅ Spec (k̄ ⊗[k] Γ(X, U))`, `α_g` is `g ⊗ id`. -/
lemma bcSecEquiv_galMap (g : Gk k (FFClosure X)) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U)) :
    bcSecEquiv k _ hU ((galMap k g).appLE _ _ (le_preimage_galMap k g U) s) =
      tensorGal k g U (bcSecEquiv k _ hU s) := by
  have hU' := isAffineOpen_baseChangeOpen' k (kbar k (FFClosure X)) hU
  have key : CommRingCat.ofHom ((bcSecEquiv k _ hU).toRingHom.comp
      ((galMap k g).appLE _ _ (le_preimage_galMap k g U)).hom) =
      CommRingCat.ofHom ((tensorGal k g U).toRingHom.comp (bcSecEquiv k _ hU).toRingHom) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec]
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (galMap k g) hU' hU'
      (le_preimage_galMap k g U)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_bcSecEquiv, CommRingCat.ofHom_hom,
      Category.assoc, h1, CommRingCat.ofHom_comp, Spec.map_comp, specMap_bcSecEquiv,
      ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact specTensorIso_galMap k g hU
  exact congrArg (fun φ ↦ φ.hom s) key

/-- **Places**: `f ∈ 𝒪_{X_{k̄}, α_g(y)}` iff `φ_g(f) ∈ 𝒪_{X_{k̄}, y}`; with `ffEquiv_autF`, the
action of `h` on `F k̄` moves the place at `α_g(y)` to the place at `y`. -/
theorem galFF_mem_stalkValuationSubring_iff
    (hY : ∀ y : baseChangeKbar k X, ValuationRing ((baseChangeKbar k X).presheaf.stalk y))
    (g : Gk k (FFClosure X)) (y : baseChangeKbar k X) (f : (baseChangeKbar k X).functionField) :
    galFF k g f ∈ stalkValuationSubring hY y ↔ f ∈ stalkValuationSubring hY (galMap k g y) :=
  functionFieldMap_mem_stalkValuationSubring_iff _ _ hY hY y f

variable [CharZero k] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

omit [IsGalois (K₀ k (coordT τ)) (FFClosure X)] in
lemma tensorToOmega_tensorGal (h : (curveGaloisData k hτ).H) (U : X.Opens) [Nonempty U]
    (x : kbar k (FFClosure X) ⊗[k] Γ(X, U)) :
    tensorToOmega k U (tensorGal k (hToGk _ h) U x) =
      (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X) (tensorToOmega k U x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c r =>
    rw [Algebra.TensorProduct.map_tmul, tensorToOmega_tmul, tensorToOmega_tmul, map_mul,
      AlgHom.id_apply]
    congr 1
    · exact algebraMap_hToGk_apply _ h c
    · have hh : (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X) ∈
          (imageL (k := k) τ).fixingSubgroup := h.2
      rw [secToOmega_apply]
      exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _ ⟨_, rfl⟩).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [IsGalois (K₀ k (coordT τ)) (FFClosure X)] in
/-- **`K(X_{k̄}) → Ω` intertwines `φ_g` and `h`** for `g = hToGk h`. -/
lemma ffToOmega_galFF (h : (curveGaloisData k hτ).H) {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (z : (baseChangeKbar k X).functionField) :
    ffToOmega k hU (galFF k (hToGk _ h) z) =
      (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X) (ffToOmega k hU z) := by
  haveI := functionField_isFractionRing_of_isAffineOpen (baseChangeKbar k X) _
    (isAffineOpen_baseChangeOpen' k (kbar k (FFClosure X)) hU)
  have hgerm : ∀ s : Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U),
      ffToOmega k hU (galFF k (hToGk _ h) ((baseChangeKbar k X).germToFunctionField _ s)) =
        (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X)
          (ffToOmega k hU ((baseChangeKbar k X).germToFunctionField _ s)) := by
    intro s
    rw [galFF, functionFieldMap_germ_appLE _ _ _ _ (le_preimage_galMap k _ U), ffToOmega_germ,
      ffToOmega_germ, bcSecEquiv_galMap, tensorToOmega_tensorGal]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := Γ(baseChangeKbar k X, baseChangeOpen k (kbar k (FFClosure X)) U)) z
  rw [map_div₀, map_div₀, map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hgerm a) (hgerm b)

/-- **Galois compatibility of `ffEquiv`**: the action `autF h` of `h ∈ H` on `F k̄` corresponds to
the pull-back `φ_g` along `α_g = 𝟙_X ×_k Spec(g)`, `g = hToGk h ∈ G_k`:
`ffEquiv (h x) = φ_g (ffEquiv x)`. -/
theorem ffEquiv_autF (h : (curveGaloisData k hτ).H)
    (x : F (Kummer.baseChange (curveGaloisData k hτ))) :
    ffEquiv k hτ ((autF (curveGaloisData k hτ) h : F (Kummer.baseChange (curveGaloisData k hτ))
      ≃+* F (Kummer.baseChange (curveGaloisData k hτ))) x) =
      galFF k (hToGk _ h) (ffEquiv k hτ x) := by
  apply (ffEquiv k hτ).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [coe_ffEquiv_symm k hτ, ffToOmega_galFF k hτ, ← coe_ffEquiv_symm k hτ,
    AlgEquiv.symm_apply_apply]
  rfl

end GaloisAction

end CurvesJacobian.Kummer
