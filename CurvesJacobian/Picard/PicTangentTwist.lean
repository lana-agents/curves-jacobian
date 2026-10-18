/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicTangentSetup

/-!
# First-order deformations of line bundles on a curve: the twists `𝒪(1 + aε)`

Let `C` be a scheme over a field `k` covered by two opens `U`, `V`, and let
`k[ε] = TrivSqZeroExt R₀ R₀`, `k[ε₁, ε₂] = TrivSqZeroExt R₀ R₀²` over `R₀ = Γ(Spec k)`. For
`a, a' ∈ Γ(C, U ∩ V)` let `c₁ a = [𝒪(1 + aε)] ∈ Pic(C_{k[ε]})` and
`c₂ a a' = [𝒪(1 + aε₁ + a'ε₂)] ∈ Pic(C_{k[ε₁, ε₂]})` (`PicTangent.c₁`, `PicTangent.c₂`, twists of
the two-chart covering by square-zero perturbations of `1`, `TwoChart.twPic`).

* Naturality for the maps of dual numbers: `PicTangent.map_c₂_fst`, `map_c₂_snd` (the two
  projections `k[ε₁, ε₂] → k[ε]`), `map_c₂_add` (`ε₁, ε₂ ↦ ε`), `map_c₁_smul` (`ε ↦ rε`).
* `PicTangent.map_c₁_aug`, `map_c₂_aug`: the twists are trivial on `C` itself.

These compatibilities make the bijection `Ȟ¹(U, V; 𝒪_C) ≅ ker(Pic C_{k[ε]} → Pic C)` induced by
`c₁` (the tangent space of `Pic` at the origin is `H¹(C, 𝒪_C)`, used in Stacks, Lemma 44.6.7,
Tag 0BA0) `k`-linear.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TrivSqZeroExt

universe u

noncomputable section

namespace CurvesJacobian.PicTangent

open Scheme ModulesGlue MatSheaf Cech

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "R₀" => Γ(Sk, ⊤)

variable (U V : C.Opens) (hUV : U ⊔ V = ⊤)

variable (k) in
/-- The dual numbers over `R₀`. -/
abbrev B₁ : Type u := TrivSqZeroExt R₀ R₀

variable (k) in
/-- `R₀[ε₁, ε₂]`. -/
abbrev B₂ : Type u := TrivSqZeroExt R₀ (R₀ × R₀)

variable (k) {C} in
/-- The square-zero function `a e` on the overlap of the charts of `C_B`. -/
def nE {B : Type u} [CommRing B] [Algebra R₀ B] (a : Γ(C, U ⊓ V)) (e : B) :
    Γ(CT k C B, pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V) :=
  fA k C B (O' := pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V) le_rfl a *
    fE k C B (pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V) e

variable {U V}

lemma nE_mul_nE {B : Type u} [CommRing B] [Algebra R₀ B] (a a' : Γ(C, U ⊓ V)) {e e' : B}
    (h : e * e' = 0) : nE k U V a e * nE k U V a' e' = 0 := by
  rw [nE, nE, mul_mul_mul_comm, ← map_mul (fE k C B _) e e', h, map_zero, mul_zero]

lemma inr_mul_inr' {M : Type u} [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M]
    [IsCentralScalar R₀ M] (m m' : M) : (inr m : TrivSqZeroExt R₀ M) * inr m' = 0 :=
  inr_mul_inr R₀ m m'

lemma sq_one (a : Γ(C, U ⊓ V)) : nE k U V a (inr 1 : B₁ k) * nE k U V a (inr 1 : B₁ k) = 0 :=
  nE_mul_nE (k := k) C (B := B₁ k) a a (inr_mul_inr R₀ (1 : R₀) (1 : R₀))

lemma sq_two (a a' : Γ(C, U ⊓ V)) :
    (nE k U V a (inr (1, 0) : B₂ k) + nE k U V a' (inr (0, 1) : B₂ k)) *
      (nE k U V a (inr (1, 0) : B₂ k) + nE k U V a' (inr (0, 1) : B₂ k)) = 0 := by
  have h1 := nE_mul_nE (k := k) C (B := B₂ k) a a (inr_mul_inr R₀ ((1, 0) : R₀ × R₀) (1, 0))
  have h2 := nE_mul_nE (k := k) C (B := B₂ k) a a' (inr_mul_inr R₀ ((1, 0) : R₀ × R₀) (0, 1))
  have h3 := nE_mul_nE (k := k) C (B := B₂ k) a' a (inr_mul_inr R₀ ((0, 1) : R₀ × R₀) (1, 0))
  have h4 := nE_mul_nE (k := k) C (B := B₂ k) a' a' (inr_mul_inr R₀ ((0, 1) : R₀ × R₀) (0, 1))
  linear_combination h1 + h2 + h3 + h4

variable (U V)

/-- `c₁ a = [𝒪(1 + a ε)]` on `C_{k[ε]}`. -/
def c₁ (a : Γ(C, U ⊓ V)) : (CT k C (B₁ k)).Pic := twK k C (B₁ k) U V hUV _ (sq_one C a)

/-- `c₂ a a' = [𝒪(1 + a ε₁ + a' ε₂)]` on `C_{k[ε₁, ε₂]}`. -/
def c₂ (a a' : Γ(C, U ⊓ V)) : (CT k C (B₂ k)).Pic := twK k C (B₂ k) U V hUV _ (sq_two C a a')

variable {U V}

lemma bc_nE {B B' : Type u} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B']
    (φ : B →ₐ[R₀] B') (a : Γ(C, U ⊓ V)) (e : B) (h) :
    (bc φ).appLE (pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V) (pB k C B' ⁻¹ᵁ U ⊓ pB k C B' ⁻¹ᵁ V) h
      (nE k U V a e) =
      nE k U V a (φ e) := by
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (bc_fA φ _ _ _ a) (bc_fE φ _ e))

/-! ### Naturality -/

variable (k) in
/-- The first projection `k[ε₁, ε₂] → k[ε]`. -/
abbrev prFst : B₂ k →ₐ[R₀] B₁ k := TrivSqZeroExt.map (LinearMap.fst R₀ R₀ R₀)

variable (k) in
/-- The second projection `k[ε₁, ε₂] → k[ε]`. -/
abbrev prSnd : B₂ k →ₐ[R₀] B₁ k := TrivSqZeroExt.map (LinearMap.snd R₀ R₀ R₀)

variable (k) in
/-- The sum `k[ε₁, ε₂] → k[ε]`, `ε₁, ε₂ ↦ ε`. -/
abbrev prSum : B₂ k →ₐ[R₀] B₁ k :=
  TrivSqZeroExt.map (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀)

variable (k) in
/-- The scaling `ε ↦ r ε`. -/
abbrev scal (r : R₀) : B₁ k →ₐ[R₀] B₁ k := TrivSqZeroExt.map (r • LinearMap.id)

lemma nE_zero {B : Type u} [CommRing B] [Algebra R₀ B] (a : Γ(C, U ⊓ V)) :
    nE k U V a (0 : B) = 0 := by
  rw [nE, map_zero, mul_zero]

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₂_fst (a a' : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (prFst k)) (c₂ C U V hUV a a') = c₁ C U V hUV a := by
  unfold c₁ c₂
  apply map_twK
  rw [map_add, bc_nE C (prFst k) a (inr (1, 0) : B₂ k),
    bc_nE C (prFst k) a' (inr (0, 1) : B₂ k)]
  simp [nE_zero]

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₂_snd (a a' : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (prSnd k)) (c₂ C U V hUV a a') = c₁ C U V hUV a' := by
  unfold c₁ c₂
  apply map_twK
  rw [map_add, bc_nE C (prSnd k) a (inr (1, 0) : B₂ k),
    bc_nE C (prSnd k) a' (inr (0, 1) : B₂ k)]
  simp [nE_zero]

lemma nE_add (a a' : Γ(C, U ⊓ V)) {B : Type u} [CommRing B] [Algebra R₀ B] (e : B) :
    nE k U V (a + a') e = nE k U V a e + nE k U V a' e := by
  rw [nE, nE, nE, map_add, add_mul]

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₂_add (a a' : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (prSum k)) (c₂ C U V hUV a a') = c₁ C U V hUV (a + a') := by
  unfold c₁ c₂
  apply map_twK
  rw [map_add, bc_nE C (prSum k) a (inr (1, 0) : B₂ k),
    bc_nE C (prSum k) a' (inr (0, 1) : B₂ k), nE_add]
  simp

lemma nE_algebraMap_mul {B : Type u} [CommRing B] [Algebra R₀ B] (r : R₀) (a : Γ(C, U ⊓ V))
    (e : B) : nE k U V a (algebraMap R₀ B r * e) =
      nE k U V ((C ↘ Sk).appLE ⊤ (U ⊓ V) (by simp) r * a) e := by
  have hE := fE_algebraMap (k := k) (C := C) (B := B) (O := U ⊓ V)
    (O' := pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V) le_rfl r
  rw [nE, nE, map_mul, hE, map_mul]
  ring

lemma nE_smul (r : R₀) (a : Γ(C, U ⊓ V)) :
    nE k U V a (inr r : B₁ k) = nE k U V (r • a) (inr 1 : B₁ k) := by
  have e : (inr r : B₁ k) = algebraMap R₀ (B₁ k) r * inr 1 := by
    rw [algebraMap_eq_inl, inl_mul_inr, smul_eq_mul, mul_one]
  have h3 : r • a = (C ↘ Sk).appLE ⊤ (U ⊓ V) (by simp) r * a := by
    rw [Algebra.smul_def, algebraMap_sections]
  exact (congrArg (nE k U V a) e).trans ((nE_algebraMap_mul C r a _).trans
    (congrArg (fun x ↦ nE k U V x (inr 1 : B₁ k)) h3.symm))

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₁_smul (r : R₀) (a : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (scal k r)) (c₁ C U V hUV a) = c₁ C U V hUV (r • a) := by
  unfold c₁
  apply map_twK
  rw [bc_nE C (scal k r) a (inr 1 : B₁ k), ← nE_smul]
  simp

/-! ### The kernel -/

variable (k) in
/-- The augmentation `R₀[M] → R₀`. -/
abbrev augM (M : Type u) [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M] :
    TrivSqZeroExt R₀ M →ₐ[R₀] R₀ :=
  TrivSqZeroExt.fstHom R₀ R₀ M

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₁_aug (a : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (augM k R₀)) (c₁ C U V hUV a) = 0 := by
  rw [← twK_zero (C := C) (B := R₀) U V hUV]
  unfold c₁
  apply map_twK
  rw [bc_nE C (augM k R₀) a (inr 1 : B₁ k)]
  simp [nE_zero]

set_option maxHeartbeats 1000000 in
-- unifying the base changes of the twists over `R₀[M]` is expensive
lemma map_c₂_aug (a a' : Γ(C, U ⊓ V)) :
    Scheme.Pic.map (bc (augM k (R₀ × R₀))) (c₂ C U V hUV a a') = 0 := by
  rw [← twK_zero (C := C) (B := R₀) U V hUV]
  unfold c₂
  apply map_twK
  rw [map_add, bc_nE C (augM k (R₀ × R₀)) a (inr (1, 0) : B₂ k),
    bc_nE C (augM k (R₀ × R₀)) a' (inr (0, 1) : B₂ k)]
  simp [nE_zero]

end CurvesJacobian.PicTangent
