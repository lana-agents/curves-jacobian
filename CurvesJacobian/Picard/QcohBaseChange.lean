/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.QcohLocal
import Mathlib.RingTheory.IsTensorProduct

/-!
# Sections of pullbacks of invertible sheaves over affine opens

Let `φ : Y ⟶ X` be a morphism of schemes, `L` an invertible `𝒪_X`-module, `U ⊆ X` and
`U' ⊆ φ⁻¹U` affine opens. Restricting the unit `L → φ_* φ^* L` gives a map
`θ : Γ(L, U) → Γ(φ^*L, U')` (`Scheme.Modules.pullbackRes`), semilinear along
`φ.appLE : Γ(X, U) → Γ(Y, U')` and compatible with restrictions. The main result is

* `Scheme.Modules.isBaseChange_pullbackRes`: `Γ(φ^*L, U') = Γ(Y, U') ⊗_{Γ(X, U)} Γ(L, U)`,
  i.e. `θ` is a base change (sections of the pullback of a quasi-coherent module over affines;
  Stacks, Lemma 26.7.3, Tag 01I9, for invertible modules).

The proof is local on `Γ(X, U)`: on the basic opens `D(f)` on which `L` has a basis `m₀|_{D(f)}`,
`θ(m₀)` restricts to a basis of `φ^*L` on `D(φ^♯ f)` (`isBasisOn_pullbackSection`), and the
algebraic criterion `CurvesJacobian.isBaseChange_of_local` applies.
-/

open CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

section Algebra

variable {A A' M N : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [AddCommGroup M]
  [Module A M] [AddCommGroup N] [Module A' N] [Module A N] [IsScalarTower A A' N]

lemma ideal_eq_top_of_pow_mem (s : Set A) (hs : Ideal.span s = ⊤) (I : Ideal A')
    (h : ∀ f ∈ s, ∃ k : ℕ, algebraMap A A' f ^ k ∈ I) : I = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff]
  have : Ideal.span (algebraMap A A' '' s) = ⊤ := by
    rw [← Ideal.map_span, hs, Ideal.map_top]
  rw [← this, Ideal.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- **A local criterion for base change.** Let `θ : M → N` be `A`-linear, `N` an `A'`-module.
Suppose `s ⊆ A` generates the unit ideal and for each `f ∈ s` some `m₀ ∈ M` generates `M` after
inverting `f`, while `θ m₀` is a basis of `N` after inverting `f`. Then `N = A' ⊗_A M`. -/
theorem isBaseChange_of_local (θ : M →ₗ[A] N) (s : Set A) (hs : Ideal.span s = ⊤) (m₀ : A → M)
    (hM : ∀ f ∈ s, ∀ m : M, ∃ (i : ℕ) (c : A), f ^ i • m = c • m₀ f)
    (hN : ∀ f ∈ s, ∀ n : N, ∃ (k : ℕ) (a : A'), algebraMap A A' f ^ k • n = a • θ (m₀ f))
    (hN' : ∀ f ∈ s, ∀ a : A', a • θ (m₀ f) = 0 → ∃ k : ℕ, algebraMap A A' f ^ k * a = 0) :
    IsBaseChange A' θ := by
  set β : A' ⊗[A] M →ₗ[A'] N := θ.liftBaseChange A'
  have hβ : ∀ (a : A') (m : M), β (a ⊗ₜ m) = a • θ m := fun a m ↦ by
    simp [β, LinearMap.liftBaseChange_tmul]
  -- every element becomes a multiple of `1 ⊗ m₀` after multiplying by a power of `f`
  have hloc : ∀ f ∈ s, ∀ y : A' ⊗[A] M, ∃ (i : ℕ) (a : A'),
      algebraMap A A' f ^ i • y = a ⊗ₜ m₀ f := by
    intro f hf y
    induction y with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a m =>
      obtain ⟨i, c, hc⟩ := hM f hf m
      refine ⟨i, c • a, ?_⟩
      rw [TensorProduct.smul_tmul', ← map_pow, algebraMap_smul, TensorProduct.smul_tmul, hc,
        ← TensorProduct.smul_tmul]
    | add y z hy hz =>
      obtain ⟨i, a, ha⟩ := hy
      obtain ⟨j, b, hb⟩ := hz
      refine ⟨i + j, algebraMap A A' f ^ j * a + algebraMap A A' f ^ i * b, ?_⟩
      have e1 : algebraMap A A' f ^ (i + j) • y = algebraMap A A' f ^ j • (a ⊗ₜ m₀ f) := by
        rw [pow_add, mul_comm, mul_smul, ha]
      have e2 : algebraMap A A' f ^ (i + j) • z = algebraMap A A' f ^ i • (b ⊗ₜ m₀ f) := by
        rw [pow_add, mul_smul, hb]
      rw [smul_add, e1, e2, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        ← TensorProduct.add_tmul, smul_eq_mul, smul_eq_mul]
  have hbij : Function.Bijective β := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      let I : Ideal A' := LinearMap.ker (LinearMap.toSpanSingleton A' (A' ⊗[A] M) x)
      have hI : I = ⊤ := by
        refine ideal_eq_top_of_pow_mem s hs I fun f hf ↦ ?_
        obtain ⟨i, a, ha⟩ := hloc f hf x
        have h0 : a • θ (m₀ f) = 0 := by
          rw [← hβ, ← ha, map_smul, hx, smul_zero]
        obtain ⟨k, hk⟩ := hN' f hf a h0
        refine ⟨k + i, ?_⟩
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, pow_add, mul_smul, ha,
          TensorProduct.smul_tmul', smul_eq_mul, hk, TensorProduct.zero_tmul]
      have h1 : (1 : A') ∈ I := hI ▸ Submodule.mem_top
      simpa [I] using h1
    · intro n
      let P := LinearMap.range β
      let I : Ideal A' := P.comap (LinearMap.toSpanSingleton A' N n)
      have hI : I = ⊤ := by
        refine ideal_eq_top_of_pow_mem s hs I fun f hf ↦ ?_
        obtain ⟨k, a, ha⟩ := hN f hf n
        refine ⟨k, ?_⟩
        rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, ha]
        exact ⟨a ⊗ₜ m₀ f, hβ a (m₀ f)⟩
      have h1 : (1 : A') ∈ I := hI ▸ Submodule.mem_top
      simpa [I, P] using h1
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective β hbij) fun m ↦ by
    simp [hβ]

end Algebra

end CurvesJacobian

namespace AlgebraicGeometry.Scheme.Modules

open CurvesJacobian

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- If `m₀|_{D(f)}` is a basis of the quasi-coherent `M` on `D(f)` (`U` affine), every section
over `U` becomes a multiple of `m₀` after multiplication by a power of `f`. -/
lemma exists_pow_smul_eq_smul_of_isBasisOn [M.IsQuasicoherent] (hU : IsAffineOpen U)
    (f : Γ(X, U)) (m₀ : Γ(M, U)) (hb : M.IsBasisOn (X.basicOpen f) (M.resBasicOpen f m₀))
    (m : Γ(M, U)) : ∃ (i : ℕ) (c : Γ(X, U)), f ^ i • m = c • m₀ := by
  haveI := hU.isLocalization_basicOpen f
  obtain ⟨a, ha⟩ := hb.equiv.surjective (M.resBasicOpen f m)
  obtain ⟨⟨c, ⟨_, j, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) a
  have h0 : M.resBasicOpen f (f ^ j • m - c • m₀) = 0 := by
    rw [map_sub, LinearMap.map_smul, LinearMap.map_smul, ← ha]
    change (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ j)) • (a • M.resBasicOpen f m₀) -
      algebraMap Γ(X, U) Γ(X, X.basicOpen f) c • M.resBasicOpen f m₀ = 0
    rw [smul_smul, mul_comm, hc, sub_self]
  obtain ⟨i, hi⟩ := exists_pow_smul_eq_zero hU M f (f ^ j • m - c • m₀) h0
  refine ⟨i + j, f ^ i * c, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul, ← pow_add] at hi
  rw [hi, mul_smul]

/-- If `m₀|_{D(f)}` is a basis on `D(f)`, the annihilator of `m₀` is `f`-power torsion. -/
lemma exists_pow_mul_eq_zero_of_isBasisOn (hU : IsAffineOpen U) (f : Γ(X, U)) (m₀ : Γ(M, U))
    (hb : M.IsBasisOn (X.basicOpen f) (M.resBasicOpen f m₀)) (c : Γ(X, U)) (hc : c • m₀ = 0) :
    ∃ k : ℕ, f ^ k * c = 0 := by
  haveI := hU.isLocalization_basicOpen f
  have h0 : hb.equiv (algebraMap Γ(X, U) Γ(X, X.basicOpen f) c) = 0 := by
    change c • M.resBasicOpen f m₀ = 0
    rw [← LinearMap.map_smul (M.resBasicOpen f) c m₀, hc, map_zero]
  have h1 : algebraMap Γ(X, U) Γ(X, X.basicOpen f) c = 0 :=
    hb.equiv.injective (h0.trans (map_zero _).symm)
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ c).mp h1
  exact ⟨k, hk⟩

/-! ### The base change map -/

variable (φ : Y ⟶ X) (L : X.Modules) {U' : Y.Opens} (h : U' ≤ φ ⁻¹ᵁ U)

/-- `θ : Γ(L, U) → Γ(φ^*L, U')`, `m ↦ (φ^* m)|_{U'}`. -/
def pullbackRes : Γ(L, U) →+ Γ((pullback φ).obj L, U') :=
  (((pullback φ).obj L).presheaf.map (homOfLE h).op).hom.comp
    (((pullbackPushforwardAdjunction φ).unit.app L).app U).hom

lemma pullbackRes_apply (m : Γ(L, U)) :
    pullbackRes φ L h m =
      ((pullback φ).obj L).presheaf.map (homOfLE h).op (pullbackSection φ m) := rfl

lemma pullbackSection_smul' (r : Γ(X, U)) (m : Γ(L, U)) :
    pullbackSection φ (r • m) = φ.app U r • pullbackSection φ m :=
  Hom.app_smul _ r m

lemma pullbackRes_smul (r : Γ(X, U)) (m : Γ(L, U)) :
    pullbackRes φ L h (r • m) = φ.appLE U U' h r • pullbackRes φ L h m := by
  rw [pullbackRes_apply, pullbackRes_apply, pullbackSection_smul', map_smul]
  rfl

/-- `θ` commutes with restrictions. -/
lemma pullbackRes_res {V : X.Opens} {V' : Y.Opens} (hV : V ≤ U) (hV' : V' ≤ U')
    (h' : V' ≤ φ ⁻¹ᵁ V) (m : Γ(L, U)) :
    pullbackRes φ L h' (L.presheaf.map (homOfLE hV).op m) =
      ((pullback φ).obj L).presheaf.map (homOfLE hV').op (pullbackRes φ L h m) := by
  rw [pullbackRes_apply, pullbackRes_apply, pullbackSection_res φ]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

include h in
/-- The restriction of `θ(m₀)` to `D(φ^♯ f)` is a basis if `m₀|_{D(f)}` is. -/
lemma isBasisOn_pullbackRes (f : Γ(X, U)) (m₀ : Γ(L, U))
    (hb : L.IsBasisOn (X.basicOpen f) (L.resBasicOpen f m₀)) :
    ((pullback φ).obj L).IsBasisOn (Y.basicOpen (φ.appLE U U' h f))
      (((pullback φ).obj L).resBasicOpen (φ.appLE U U' h f) (pullbackRes φ L h m₀)) := by
  have hle : Y.basicOpen (φ.appLE U U' h f) ≤ φ ⁻¹ᵁ X.basicOpen f := by
    rw [basicOpen_appLE]; exact inf_le_right
  have h1 := Scheme.PresheafOfModules.IsBasisOn.restrict
    (isBasisOn_pullbackSection φ (X.basicOpen f) hb) hle
  have heq : ((pullback φ).obj L).resBasicOpen (φ.appLE U U' h f) (pullbackRes φ L h m₀) =
      Scheme.PresheafOfModules.res ((toPresheafOfModules Y).obj ((pullback φ).obj L)) hle
        (pullbackSection φ (L.resBasicOpen f m₀)) := by
    rw [resBasicOpen_apply, pullbackRes_apply, resBasicOpen_apply, pullbackSection_res φ]
    change _ = ((pullback φ).obj L).presheaf.map (homOfLE hle).op
      (((pullback φ).obj L).presheaf.map _ (pullbackSection φ m₀))
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [heq]
  exact h1

variable [L.IsInvertible] (hU : IsAffineOpen U) (hU' : IsAffineOpen U')

/-- `θ` as a `Γ(X, U)`-linear map, for the module structure on `Γ(φ^*L, U')` through
`φ.appLE`. -/
def pullbackResₗ :
    letI := (φ.appLE U U' h).hom.toAlgebra
    letI : Module Γ(X, U) Γ((pullback φ).obj L, U') :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(Y, U'))
    Γ(L, U) →ₗ[Γ(X, U)] Γ((pullback φ).obj L, U') :=
  letI := (φ.appLE U U' h).hom.toAlgebra
  letI : Module Γ(X, U) Γ((pullback φ).obj L, U') :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, U'))
  { toFun := pullbackRes φ L h
    map_add' := map_add _
    map_smul' := pullbackRes_smul φ L h }

include hU hU' in
/-- **Sections of the pullback of an invertible sheaf over affines**:
`Γ(φ^*L, U') = Γ(Y, U') ⊗_{Γ(X, U)} Γ(L, U)` for affine `U ⊆ X` and affine `U' ⊆ φ⁻¹U`. -/
theorem isBaseChange_pullbackRes :
    letI := (φ.appLE U U' h).hom.toAlgebra
    letI : Module Γ(X, U) Γ((pullback φ).obj L, U') :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(Y, U'))
    haveI : IsScalarTower Γ(X, U) Γ(Y, U') Γ((pullback φ).obj L, U') :=
      IsScalarTower.of_compHom _ _ _
    IsBaseChange Γ(Y, U') (pullbackResₗ φ L h) := by
  letI := (φ.appLE U U' h).hom.toAlgebra
  letI : Module Γ(X, U) Γ((pullback φ).obj L, U') :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, U'))
  haveI : IsScalarTower Γ(X, U) Γ(Y, U') Γ((pullback φ).obj L, U') :=
    IsScalarTower.of_compHom _ _ _
  haveI := isQuasicoherent_of_isInvertible L
  haveI := isQuasicoherent_of_isInvertible ((pullback φ).obj L)
  classical
  let m₀ : Γ(X, U) → Γ(L, U) := fun f ↦
    if hf : f ∈ L.trivSet U then hf.choose else 0
  have hm₀ : ∀ f ∈ L.trivSet U, L.IsBasisOn (X.basicOpen f) (L.resBasicOpen f (m₀ f)) :=
    fun f hf ↦ by simpa [m₀, hf] using hf.choose_spec
  refine isBaseChange_of_local (pullbackResₗ φ L h) (L.trivSet U) (span_trivSet_eq_top L hU) m₀
    (fun f hf m ↦ exists_pow_smul_eq_smul_of_isBasisOn hU f (m₀ f) (hm₀ f hf) m)
    (fun f hf n ↦ ?_) (fun f hf a ha ↦ ?_)
  · obtain ⟨k, a, hka⟩ := exists_pow_smul_eq_smul_of_isBasisOn hU' (φ.appLE U U' h f)
      (pullbackRes φ L h (m₀ f)) (isBasisOn_pullbackRes φ L h f (m₀ f) (hm₀ f hf)) n
    exact ⟨k, a, hka⟩
  · exact exists_pow_mul_eq_zero_of_isBasisOn hU' (φ.appLE U U' h f) (pullbackRes φ L h (m₀ f))
      (isBasisOn_pullbackRes φ L h f (m₀ f) (hm₀ f hf)) a ha

end AlgebraicGeometry.Scheme.Modules
