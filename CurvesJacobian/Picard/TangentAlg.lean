/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tangent vectors and Kähler differentials

This file is generic linear algebra. Let `A` be an `R`-algebra with an `R`-point
`x : A →ₐ[R] R`, and suppose `Ω[A⁄R]` is free with basis `b` indexed by a finite type `ι`.
For an `R`-module `M`, the *tangent vectors at `x` with values in `M`* are the `R`-algebra maps
`φ : A → R[M] = TrivSqZeroExt R M` lifting `x`. They are parametrised by `ι → M`
(`TangentAlg.tanFun`, injective `TangentAlg.tanFun_injective` and surjective onto the lifts
`TangentAlg.exists_tanFun_eq`): `v ↦ (a ↦ (x a, Σᵢ x(b.repr (d a) i) • vᵢ))`, naturally in
`M` (`TangentAlg.map_tanFun`). In particular the tangent space at `x` has dimension
`#ι = rank Ω[A⁄R]` (Stacks, Tag 00RW/00TU: tangent vectors are derivations, and derivations
are `Hom(Ω, -)`).

`TangentAlg.finrank_eq_card_of_natural`: a "naturally additive" bijection detects dimensions.
If `θ_M : (ι → M) → K(M)` are bijections for `M = R` and `M = R²`, compatible with the maps
induced by the projections, the sum `R² → R` and the scalings `R → R`, and `c : H → K(R)` is a
bijection with the same compatibilities (expressed through a family `c₂ : H × H → K(R²)`), then
`θ_R⁻¹ ∘ c : H → ι → R` is `R`-linear, so `H ≃ₗ[R] (ι → R)`.
-/

open TrivSqZeroExt

universe u

noncomputable section

namespace CurvesJacobian.TangentAlg

variable {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A] (x : A →ₐ[R] R)
  [Fintype ι] (b : Module.Basis ι A Ω[A⁄R])

section Tan

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The derivation part of the tangent vector `v`. -/
def tanDer (v : ι → M) (a : A) : M :=
  ∑ i, x (b.repr (KaehlerDifferential.D R A a) i) • v i

lemma tanDer_mul (v : ι → M) (a a' : A) :
    tanDer x b M v (a * a') = x a • tanDer x b M v a' + x a' • tanDer x b M v a := by
  simp only [tanDer, Derivation.leibniz, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_smul, mul_smul, mul_smul]

lemma tanDer_add (v : ι → M) (a a' : A) :
    tanDer x b M v (a + a') = tanDer x b M v a + tanDer x b M v a' := by
  simp only [tanDer, map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]

lemma tanDer_algebraMap (v : ι → M) (r : R) : tanDer x b M v (algebraMap R A r) = 0 := by
  simp [tanDer]

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- **The tangent vector with coordinates `v`**: `a ↦ (x a, Σᵢ x(b.repr (d a) i) • vᵢ)`. -/
def tanFun (v : ι → M) : A →ₐ[R] TrivSqZeroExt R M where
  toFun a := (x a, tanDer x b M v a)
  map_one' := by
    refine TrivSqZeroExt.ext (map_one x) ?_
    simp [tanDer]
  map_mul' a a' := by
    refine TrivSqZeroExt.ext (map_mul x a a') ?_
    simp only [snd_mul, tanDer_mul, op_smul_eq_smul]
    change _ = x a • tanDer x b M v a' + x a' • tanDer x b M v a
    rfl
  map_zero' := TrivSqZeroExt.ext (map_zero x) (by simp [tanDer])
  map_add' a a' := TrivSqZeroExt.ext (map_add x a a') (tanDer_add x b M v a a')
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [TrivSqZeroExt.algebraMap_eq_inl, tanDer_algebraMap]

lemma fst_tanFun (v : ι → M) (a : A) : (tanFun x b M v a).fst = x a := rfl

lemma snd_tanFun (v : ι → M) (a : A) : (tanFun x b M v a).snd = tanDer x b M v a := rfl

/-- **Naturality** in `M`. -/
lemma map_tanFun {M' : Type u} [AddCommGroup M'] [Module R M'] [Module Rᵐᵒᵖ M']
    [IsCentralScalar R M'] (l : M →ₗ[R] M') (v : ι → M) :
    (TrivSqZeroExt.map l).comp (tanFun x b M v) = tanFun x b M' (l ∘ v) := by
  ext a
  · simp [fst_tanFun]
  · simp [snd_tanFun, tanDer, map_sum]

lemma tanFun_injective : Function.Injective (tanFun x b M) := by
  intro v w h
  have hD : ∀ a, tanDer x b M v a = tanDer x b M w a := fun a ↦
    congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h a)
  -- the linear functional `y ↦ Σ yᵢ • (vᵢ - wᵢ)` on `A`-coordinates
  let F : Ω[A⁄R] →ₗ[R] M :=
    { toFun := fun ω ↦ ∑ i, x (b.repr ω i) • (v i - w i)
      map_add' := fun ω ω' ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r ω ↦ by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← IsScalarTower.algebraMap_smul A r ω, map_smul, Finsupp.smul_apply, smul_eq_mul,
          map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_smul] }
  have hF : ∀ (c : A) (ω : Ω[A⁄R]), F (c • ω) = x c • F ω := by
    intro c ω
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul, mul_smul, Finset.smul_sum]
  have hF0 : ∀ a, F (KaehlerDifferential.D R A a) = 0 := by
    intro a
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hD a)
  have hall : ∀ ω, F ω = 0 := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hF0 a
    | zero => exact map_zero F
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [hF, hy, smul_zero]
  funext j
  have := hall (b j)
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self] at this
  rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [Finsupp.single_eq_of_ne hij]; simp)
    (by simp), Finsupp.single_eq_same, map_one, one_smul, sub_eq_zero] at this
  exact this

/-- **Every tangent vector has coordinates.** -/
lemma exists_tanFun_eq (φ : A →ₐ[R] TrivSqZeroExt R M) (hφ : ∀ a, (φ a).fst = x a) :
    ∃ v : ι → M, tanFun x b M v = φ := by
  letI : Module A M := Module.compHom M x.toRingHom
  haveI : IsScalarTower R A M := ⟨fun r a m ↦ by
    change x (r • a) • m = r • (x a • m)
    rw [map_smul, smul_assoc]⟩
  let D : Derivation R A M :=
    { toFun := fun a ↦ (φ a).snd
      map_add' := fun a a' ↦ by
        change (φ (a + a')).snd = (φ a).snd + (φ a').snd
        rw [map_add, snd_add]
      map_smul' := fun r a ↦ by
        change (φ (r • a)).snd = r • (φ a).snd
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, snd_smul]
      map_one_eq_zero' := by
        change (φ 1).snd = 0
        rw [map_one, snd_one]
      leibniz' := fun a a' ↦ by
        change (φ (a * a')).snd = a • (φ a').snd + a' • (φ a).snd
        rw [map_mul, snd_mul, hφ, hφ, op_smul_eq_smul]
        rfl }
  let f : Ω[A⁄R] →ₗ[A] M := D.liftKaehlerDifferential
  refine ⟨fun i ↦ f (b i), ?_⟩
  ext a
  · exact (hφ a).symm
  · change ∑ i, x (b.repr (KaehlerDifferential.D R A a) i) • f (b i) = (φ a).snd
    have h1 : f (KaehlerDifferential.D R A a) = (φ a).snd :=
      Derivation.liftKaehlerDifferential_comp_D D a
    rw [← h1]
    conv_rhs => rw [← b.sum_repr (KaehlerDifferential.D R A a)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
    rfl

end Tan

/-! ### Linear algebra: naturally additive bijections -/

section Natural

variable {R : Type u} [CommRing R] {ι : Type u} {P H K₁ K₂ : Type*}

/-- **Dimension from natural bijections.** Let `θ₁ : (ι → R) → K₁` and `θ₂ : (ι → R²) → K₂`
be injective, `p₁, p₂, s : K₂ → K₁` and `μ_λ : K₁ → K₁` maps compatible with `θ` and the
projections, the sum and the scalings. Let `π : P → H` be a surjective linear map and
`c : P → K₁` with `c a = c a' ↔ π a = π a'`, whose image is the image of `θ₁`, and
`c₂ : P → P → K₂` with image in the image of `θ₂`, such that `p_j (c₂ a₁ a₂) = c a_j`,
`s (c₂ a₁ a₂) = c (a₁ + a₂)` and `μ_λ (c a) = c (λ a)`. Then `H ≃ₗ[R] (ι → R)`. -/
def linearEquivOfNatural [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    (π : P →ₗ[R] H) (hπ : Function.Surjective π)
    (θ₁ : (ι → R) → K₁) (θ₂ : (ι → R × R) → K₂) (hθ₁ : Function.Injective θ₁)
    (p₁ p₂ s : K₂ → K₁) (μ : R → K₁ → K₁)
    (hp₁ : ∀ v, p₁ (θ₂ v) = θ₁ (Prod.fst ∘ v)) (hp₂ : ∀ v, p₂ (θ₂ v) = θ₁ (Prod.snd ∘ v))
    (hs : ∀ v, s (θ₂ v) = θ₁ (fun i ↦ (v i).1 + (v i).2))
    (hμ : ∀ r v, μ r (θ₁ v) = θ₁ (r • v))
    (c : P → K₁) (hc : ∀ a a', c a = c a' ↔ π a = π a')
    (hcθ : ∀ a, ∃ v, θ₁ v = c a) (hθc : ∀ v, ∃ a, c a = θ₁ v)
    (c₂ : P → P → K₂) (hc₂θ : ∀ a a', ∃ w, θ₂ w = c₂ a a')
    (hc₁ : ∀ a a', p₁ (c₂ a a') = c a) (hc₂ : ∀ a a', p₂ (c₂ a a') = c a')
    (hcs : ∀ a a', s (c₂ a a') = c (a + a')) (hcμ : ∀ (r : R) a, μ r (c a) = c (r • a)) :
    H ≃ₗ[R] (ι → R) :=
  let Λ : P → (ι → R) := fun a ↦ (hcθ a).choose
  have hΛ : ∀ a, θ₁ (Λ a) = c a := fun a ↦ (hcθ a).choose_spec
  have hadd : ∀ a a', Λ (a + a') = Λ a + Λ a' := by
    intro a a'
    obtain ⟨w, hw⟩ := hc₂θ a a'
    have w1 : Prod.fst ∘ w = Λ a := hθ₁ (by rw [← hp₁, hw, hc₁, hΛ])
    have w2 : Prod.snd ∘ w = Λ a' := hθ₁ (by rw [← hp₂, hw, hc₂, hΛ])
    refine hθ₁ ?_
    rw [hΛ, ← hcs, ← hw, hs, ← w1, ← w2]
    rfl
  have hsmul : ∀ (r : R) a, Λ (r • a) = r • Λ a := by
    intro r a
    refine hθ₁ ?_
    rw [hΛ, ← hcμ, ← hΛ, hμ]
  let L : P →ₗ[R] (ι → R) := { toFun := Λ, map_add' := hadd, map_smul' := hsmul }
  have hL : Function.Surjective L := by
    intro v
    obtain ⟨a, ha⟩ := hθc v
    exact ⟨a, hθ₁ ((hΛ a).trans ha)⟩
  have hker : LinearMap.ker π = LinearMap.ker L := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : c a = c 0 := (hc a 0).mpr (by rw [h, map_zero])
      refine hθ₁ ?_
      change θ₁ (Λ a) = θ₁ 0
      rw [hΛ, h', ← hΛ, show Λ 0 = 0 from by
        have := hadd 0 0
        rw [add_zero] at this
        exact left_eq_add.mp this]
    · intro h
      have h' : c a = c 0 := by
        rw [← hΛ, ← hΛ]
        change θ₁ (L a) = θ₁ (L 0)
        rw [h, map_zero]
      rw [(hc a 0).mp h', map_zero]
  (π.quotKerEquivOfSurjective hπ).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    L.quotKerEquivOfSurjective hL

end Natural

end CurvesJacobian.TangentAlg
