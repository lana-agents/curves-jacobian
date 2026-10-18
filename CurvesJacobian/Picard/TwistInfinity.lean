/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwistCech

/-!
# Serre vanishing for twists by a divisor at infinity (input to Stacks, Lemma 44.6.5, Tag 0B9Y)

Let `Y` be a scheme over `S` with affine opens `U`, `V` (and affine `U ∩ V`), `σ ∈ Γ(Y, V)` with
`D(σ) = U ∩ V`, and `M` an invertible sheaf whose Čech `H¹` for `(U, V)` is a finite
`Γ(S)`-module. Let `N n` (`n ∈ ℕ`) be invertible sheaves with global sections `s n` which are a
basis on `U` and `σⁿ` times a basis on `V` (on a curve `X → ℙ¹`: `𝒪(n · ∞)` with its section
`x₀ⁿ`). Then for `n ≫ 0` the twist `M ⊗ N n` has Čech `H¹ = 0` and a nonzero Čech `H⁰`
(`CurvesJacobian.Cech.exists_twist_H1_eq_zero`).

This is the first step of the proof of Stacks, Lemma 44.6.5 (Tag 0B9Y) ("twisting by a high power
of an ample invertible sheaf kills `H¹` and creates sections"), proved on the chart Čech complex:
every class in `H¹(M)` is represented on `U ∩ V = D(σ)` by `q/σᵐ` with `q` a section on `V`, and
becomes a coboundary in `M ⊗ N n` for `n ≥ m`, because the twisting map on `V` has image in
`σⁿ Γ(M ⊗ N n, V)` and is bijective on `U` and `U ∩ V`.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Function
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian.Cech

variable {S Y : Scheme.{u}} [Y.Over S]

/-- Multiplication by `r ∈ Γ(Y, Z)` on `Γ(P, Z)`, as a `Γ(S)`-linear endomorphism. -/
def smulLin (P : Y.Modules) {Z : Y.Opens} (r : Γ(Y, Z)) : Module.End Γ(S, ⊤) Γ(P, Z) where
  toFun m := r • m
  map_add' := smul_add r
  map_smul' a m := by
    rw [RingHom.id_apply, smul_sections_def, smul_sections_def, smul_smul, smul_smul, mul_comm]

lemma smulLin_apply (P : Y.Modules) {Z : Y.Opens} (r : Γ(Y, Z)) (m : Γ(P, Z)) :
    smulLin (S := S) P r m = r • m := rfl

lemma smulLin_pow (P : Y.Modules) {Z : Y.Opens} (r : Γ(Y, Z)) (n : ℕ) :
    smulLin (S := S) P r ^ n = smulLin P (r ^ n) := by
  induction n with
  | zero => ext m; simp [smulLin_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    ext m
    simp [smulLin_apply, pow_succ, mul_smul]

lemma resModLin_smulLin (P : Y.Modules) {Z Z' : Y.Opens} (h : Z' ≤ Z) (r : Γ(Y, Z)) :
    resModLin S P h ∘ₗ smulLin P r = smulLin P (Y.presheaf.map (homOfLE h).op r) ∘ₗ
      resModLin S P h := by
  ext m
  exact Scheme.Modules.map_smul P (homOfLE h) r m

lemma twistLin_smulLin (M N : Y.Modules) (s : Γ(N, ⊤)) {Z : Y.Opens} (r : Γ(Y, Z)) :
    twistLin M N s Z ∘ₗ smulLin M r = smulLin (M ⊗ N) r ∘ₗ twistLin (S := S) M N s Z := by
  ext m
  exact tmulSection_smul_left r m _

variable {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hUV : IsAffineOpen (U ⊓ V)) {σ : Γ(Y, V)} (hb : Y.basicOpen σ = U ⊓ V)

/-- Every section over `D = D(σ)` becomes a restriction from `V` after multiplication by a
power of `σ`. -/
lemma exists_pow_smul_mem_range (hV : IsAffineOpen V) (P : Y.Modules) [P.IsInvertible]
    {D : Y.Opens} (hD : D ≤ V) (hb : Y.basicOpen σ = D) (c : Γ(P, D)) :
    ∃ m : ℕ, ((smulLin (S := S) P (Y.presheaf.map (homOfLE hD).op σ)) ^ m) c ∈
        LinearMap.range (resModLin S P hD) := by
  subst hb
  haveI := isQuasicoherent_of_isInvertible P
  haveI := P.isLocalizedModule_resBasicOpen hV σ
  obtain ⟨⟨q, ⟨_, m, rfl⟩⟩, hq⟩ := IsLocalizedModule.surj (Submonoid.powers σ)
    (P.resBasicOpen σ) c
  refine ⟨m, q, ?_⟩
  rw [smulLin_pow, smulLin_apply, ← map_pow]
  change P.resBasicOpen σ q = _
  exact hq.symm.trans (smul_basicOpen_def P σ (σ ^ m) c)

/-- The content ideal of a basis is the unit ideal, so twisting by a section which is a basis
on `Z` is bijective on `Z`. -/
lemma bijective_twistLin_of_isBasisOn {Z : Y.Opens} (hZ : IsAffineOpen Z) (M N : Y.Modules)
    [M.IsInvertible] [N.IsInvertible] (s : Γ(N, ⊤))
    (hs : N.IsBasisOn Z (N.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op s)) :
    Bijective (twistLin (S := S) M N s Z) := by
  have hbij := ModulesGlue.bijective_smul_of_isBasisOn hs
  refine ⟨injective_twistLin M N s hZ hbij.1, fun y ↦ ?_⟩
  have : y ∈ LinearMap.range (twistLin (S := S) M N s Z) := by
    rw [mem_range_twistLin_iff M N s hZ, contentIdeal_eq_top_of_bijective hbij, Submodule.top_smul]
    exact Submodule.mem_top
  exact this

include hU hV hUV hb in
/-- **Serre vanishing for twists at infinity** (proof of Stacks, Lemma 44.6.5, Tag 0B9Y). -/
theorem exists_twist_H1_eq_zero (M : Y.Modules) [M.IsInvertible]
    [Module.Finite Γ(S, ⊤) (cechModH1 S M U V)] {u : Γ(M, U)} (hu : u ≠ 0)
    (N : ℕ → Y.Modules) [∀ n, (N n).IsInvertible] (s : ∀ n, Γ(N n, ⊤))
    (hsU : ∀ n, (N n).IsBasisOn U ((N n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s n)))
    (hsV : ∀ n, ∃ b : Γ(N n, V), (N n).IsBasisOn V b ∧
      (N n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s n) = σ ^ n • b) :
    ∃ n, Subsingleton (cechModH1 S (M ⊗ N n) U V) ∧
      ∃ x ∈ cechModH0 S (M ⊗ N n) U V, x ≠ 0 := by
  classical
  let σW : Γ(Y, U ⊓ V) := Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ
  have hσW : IsUnit σW := by
    have := isUnit_res_basicOpen (X := Y) (U := V) σ
    have e : Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ =
        Y.presheaf.map (homOfLE hb.ge).op (Y.presheaf.map (homOfLE (Y.basicOpen_le σ)).op σ) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    change IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ)
    rw [e]
    exact this.map _
  -- generators of `H¹(M)`
  obtain ⟨T, hT⟩ := TwoCech.exists_finset_span_sup_eq_top
    (resModLin S M (inf_le_left : U ⊓ V ≤ U)) (resModLin S M (inf_le_right : U ⊓ V ≤ V))
  choose m hm using fun c : Γ(M, U ⊓ V) ↦
    exists_pow_smul_mem_range (S := S) hV M (inf_le_right : U ⊓ V ≤ V) hb c
  let n := T.sup m + m (resModLin S M (inf_le_left : U ⊓ V ≤ U) u)
  refine ⟨n, ?_⟩
  -- the twisting maps
  let α := twistLin (S := S) M (N n) (s n) U
  let β := twistLin (S := S) M (N n) (s n) V
  let γ := twistLin (S := S) M (N n) (s n) (U ⊓ V)
  have hαb : Bijective α := bijective_twistLin_of_isBasisOn hU M (N n) (s n) (hsU n)
  have hγb : Bijective γ := by
    refine bijective_twistLin_of_isBasisOn hUV M (N n) (s n) ?_
    have := Scheme.PresheafOfModules.IsBasisOn.restrict (hsU n) (inf_le_left : U ⊓ V ≤ U)
    have heq : (N n).presheaf.map (homOfLE (le_top : U ⊓ V ≤ ⊤)).op (s n) =
        Scheme.PresheafOfModules.res ((toPresheafOfModules Y).obj (N n))
          (inf_le_left : U ⊓ V ≤ U) ((N n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s n)) := by
      change _ = (N n).presheaf.map _ ((N n).presheaf.map _ (s n))
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [heq]
    exact this
  have hf := twistLin_comp_res (S := S) M (N n) (s n) (inf_le_left : U ⊓ V ≤ U)
  have hg := twistLin_comp_res (S := S) M (N n) (s n) (inf_le_right : U ⊓ V ≤ V)
  have hβn : ∀ q, β q ∈ LinearMap.range (smulLin (S := S) (M ⊗ N n) σ ^ n) := by
    intro q
    obtain ⟨b, hbV, hsb⟩ := hsV n
    have hmem := (mem_range_twistLin_iff (S := S) M (N n) (s n) hV (β q)).mp ⟨q, rfl⟩
    rw [hsb, contentIdeal_smul_of_bijective (ModulesGlue.bijective_smul_of_isBasisOn hbV),
      Submodule.ideal_span_singleton_smul] at hmem
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    exact ⟨y, by rw [smulLin_pow, smulLin_apply]; exact hy⟩
  have hkill : ∀ c : Γ(M, U ⊓ V), m c ≤ n →
      γ c ∈ LinearMap.range (resModLin S (M ⊗ N n) (inf_le_right : U ⊓ V ≤ V)) :=
    fun c hc ↦ TwoCech.mem_range_of_pow_smul_mem_range hg
      (smulLin (S := S) M σ) (smulLin (S := S) M σW) (smulLin (S := S) (M ⊗ N n) σ)
      (smulLin (S := S) (M ⊗ N n) σW)
      (resModLin_smulLin (S := S) M inf_le_right σ)
      (resModLin_smulLin (S := S) (M ⊗ N n) inf_le_right σ)
      (twistLin_smulLin (S := S) M (N n) (s n) σW)
      (fun a a' h ↦ hσW.smul_left_cancel.mp (by simpa only [smulLin_apply] using h))
      hβn hc (hm c)
  have hgen : ∀ c ∈ (T : Set Γ(M, U ⊓ V)),
      γ c ∈ LinearMap.range (resModLin S (M ⊗ N n) (inf_le_right : U ⊓ V ≤ V)) := by
    intro c hc
    refine hkill c ?_
    have h1 : m c ≤ T.sup m := Finset.le_sup (f := m) (Finset.mem_coe.mp hc)
    exact h1.trans (Nat.le_add_right _ _)
  have hsub : Subsingleton (TwoCech.H1 (resModLin S (M ⊗ N n) (inf_le_left : U ⊓ V ≤ U))
      (resModLin S (M ⊗ N n) (inf_le_right : U ⊓ V ≤ V))) :=
    TwoCech.subsingleton_H1_of_gens (f := resModLin S M (inf_le_left : U ⊓ V ≤ U))
      (g := resModLin S M (inf_le_right : U ⊓ V ≤ V)) (α := α) (β := β) (γ := γ) hf hg hγb.2
      (T : Set Γ(M, U ⊓ V)) hT hgen
  refine ⟨hsub, ?_⟩
  have hle : m (resModLin S M (inf_le_left : U ⊓ V ≤ U) u) ≤ n := Nat.le_add_left _ _
  obtain ⟨q', hq'⟩ := hkill (resModLin S M (inf_le_left : U ⊓ V ≤ U) u) hle
  exact TwoCech.exists_ne_zero_H0 (f := resModLin S M (inf_le_left : U ⊓ V ≤ U))
    (g' := resModLin S (M ⊗ N n) (inf_le_right : U ⊓ V ≤ V)) (α := α) (γ := γ) hf hαb.1 hu hq'

end CurvesJacobian.Cech
