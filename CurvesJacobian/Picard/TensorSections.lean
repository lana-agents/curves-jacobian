/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ZeroSchemeDegree
import CurvesJacobian.Picard.ContentIdeal

/-!
# Sections of tensor products of invertible sheaves over affine opens

Let `A`, `B` be invertible sheaves on a scheme `X` and `U ⊆ X` an affine open. Then

* `Scheme.Modules.tensorSectionsEquiv`: `Γ(A, U) ⊗_{Γ(X, U)} Γ(B, U) ≃ Γ(A ⊗ B, U)`,
  `a ⊗ b ↦ a ⊗ b` (`tmulSection`); sections of a tensor product of quasi-coherent modules over
  an affine open (Stacks, Lemma 26.7.3 (Tag 01I9) with Lemma 17.16.6 (Tag 01CE), here for
  invertible modules). The proof is local on `Γ(X, U)`, on the basic opens where both `A` and
  `B` have a basis, via the local bijectivity criterion `CurvesJacobian.bijective_of_local`.

As a consequence, for a section `s ∈ Γ(B, U)` the twisting map
`Γ(A, U) → Γ(A ⊗ B, U)`, `a ↦ a ⊗ s` (`Scheme.Modules.twistSec`) is injective when `s` is a
nonzerodivisor (`injective_twistSec`) and has image `c(s) · Γ(A ⊗ B, U)`, where `c(s)` is the
content ideal of `s` (`range_twistSec`). For `s` the canonical section of `𝒪(D)` these are the
maps `Γ(A, U) → Γ(A(D), U)` with image `I_D(U) · Γ(A(D), U)` used to twist line bundles by
divisors in Stacks, Lemma 44.6.5 (Tag 0B9Y).
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace TensorProduct Pointwise

universe u

noncomputable section

namespace CurvesJacobian

section Local

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **A local criterion for bijectivity.** Let `θ : M → N` be `A`-linear and `s ⊆ A` generate
the unit ideal. If for each `f ∈ s` some `m₀ ∈ M` generates `M` after inverting `f`, while
`θ m₀` is a basis of `N` after inverting `f`, then `θ` is bijective. -/
theorem bijective_of_local (θ : M →ₗ[A] N) (s : Set A) (hs : Ideal.span s = ⊤) (m₀ : A → M)
    (hM : ∀ f ∈ s, ∀ m : M, ∃ (i : ℕ) (c : A), f ^ i • m = c • m₀ f)
    (hN : ∀ f ∈ s, ∀ n : N, ∃ (i : ℕ) (c : A), f ^ i • n = c • θ (m₀ f))
    (hN' : ∀ f ∈ s, ∀ c : A, c • θ (m₀ f) = 0 → ∃ k : ℕ, f ^ k * c = 0) :
    Function.Bijective θ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    let I : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A M x)
    have hI : I = ⊤ := by
      refine ideal_eq_top_of_pow_mem (A' := A) s hs I fun f hf ↦ ?_
      obtain ⟨i, c, hc⟩ := hM f hf x
      have h0 : c • θ (m₀ f) = 0 := by
        rw [← map_smul, ← hc, map_smul, hx, smul_zero]
      obtain ⟨k, hk⟩ := hN' f hf c h0
      refine ⟨k + i, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Algebra.algebraMap_self,
        RingHom.id_apply, pow_add, mul_smul, hc, smul_smul, hk, zero_smul]
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  · intro n
    let I : Ideal A := (LinearMap.range θ).comap (LinearMap.toSpanSingleton A N n)
    have hI : I = ⊤ := by
      refine ideal_eq_top_of_pow_mem (A' := A) s hs I fun f hf ↦ ?_
      obtain ⟨i, c, hc⟩ := hN f hf n
      refine ⟨i, ?_⟩
      rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hc]
      exact ⟨c • m₀ f, map_smul _ _ _⟩
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1

end Local

section Twist

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- `m ↦ m ⊗ s`. -/
def tmulRight (s : N) : M →ₗ[R] M ⊗[R] N := (TensorProduct.mk R M N).flip s

@[simp] lemma tmulRight_apply (s : N) (m : M) : tmulRight (R := R) s m = m ⊗ₜ s := rfl

/-- If `M` is flat and `s` is a nonzerodivisor, `m ↦ m ⊗ s` is injective. -/
lemma injective_tmulRight [Module.Flat R M] {s : N}
    (hs : Function.Injective fun r : R ↦ r • s) :
    Function.Injective (tmulRight (R := R) (M := M) s) := by
  have : tmulRight (R := R) (M := M) s =
      LinearMap.lTensor M (LinearMap.toSpanSingleton R N s) ∘ₗ
        (TensorProduct.rid R M).symm.toLinearMap := by
    ext m
    simp
  rw [this]
  exact (Module.Flat.lTensor_preserves_injective_linearMap _ hs).comp
    (TensorProduct.rid R M).symm.injective

/-- For `N` invertible, the image of `m ↦ m ⊗ s` is `c(s) · (M ⊗ N)`. -/
lemma range_tmulRight [Module.Invertible R N] (s : N) :
    LinearMap.range (tmulRight (R := R) (M := M) s) =
      contentIdeal (R := R) s • (⊤ : Submodule R (M ⊗[R] N)) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    have hs : s ∈ contentIdeal (R := R) s • (⊤ : Submodule R N) := by
      rw [contentIdeal_smul_top]
      exact Submodule.mem_span_singleton_self s
    refine Submodule.smul_induction_on (p := fun n ↦ m ⊗ₜ n ∈
      contentIdeal (R := R) s • (⊤ : Submodule R (M ⊗[R] N))) hs ?_ ?_
    · intro r hr n _
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  · rw [Submodule.smul_le]
    rintro _ ⟨μ, rfl⟩ y -
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero]; exact zero_mem _
    | tmul m n =>
      refine ⟨μ n • m, ?_⟩
      change (μ n • m) ⊗ₜ s = (Module.Dual.eval R N s μ) • (m ⊗ₜ n)
      rw [Module.Dual.eval_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Invertible.apply_smul_eq μ n s, ← TensorProduct.smul_tmul]
    | add y z hy hz => rw [smul_add]; exact add_mem hy hz

end Twist

end CurvesJacobian

namespace AlgebraicGeometry.Scheme.Modules

open CurvesJacobian

variable {X : Scheme.{u}}

section TensorSections

variable (A B : X.Modules) (U : X.Opens)

/-- `Γ(A, U) ⊗_{Γ(X, U)} Γ(B, U) → Γ(A ⊗ B, U)`, `a ⊗ b ↦ a ⊗ b`. -/
def tensorSections : Γ(A, U) ⊗[Γ(X, U)] Γ(B, U) →ₗ[Γ(X, U)] Γ(A ⊗ B, U) :=
  TensorProduct.lift (LinearMap.mk₂ Γ(X, U) tmulSection tmulSection_add_left
    (fun c a b ↦ tmulSection_smul_left c a b) tmulSection_add_right
    (fun c a b ↦ tmulSection_smul_right c a b))

variable {A B U}

@[simp] lemma tensorSections_tmul (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSections A B U (a ⊗ₜ b) = tmulSection a b := rfl

/-- Restricting a basis on `D(f)` to `D(f g)`. -/
lemma isBasisOn_resBasicOpen_mul {M : X.Modules} {f g : Γ(X, U)} {m : Γ(M, U)}
    (hb : M.IsBasisOn (X.basicOpen f) (M.resBasicOpen f m)) :
    M.IsBasisOn (X.basicOpen (f * g)) (M.resBasicOpen (f * g) m) := by
  have hle : X.basicOpen (f * g) ≤ X.basicOpen f := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have h1 := Scheme.PresheafOfModules.IsBasisOn.restrict hb hle
  have heq : M.resBasicOpen (f * g) m = Scheme.PresheafOfModules.res
      ((toPresheafOfModules X).obj M) hle (M.resBasicOpen f m) := by
    rw [resBasicOpen_apply, resBasicOpen_apply]
    change _ = M.presheaf.map (homOfLE hle).op (M.presheaf.map _ m)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [heq]
  exact h1

lemma isBasisOn_resBasicOpen_mul' {M : X.Modules} {f g : Γ(X, U)} {m : Γ(M, U)}
    (hb : M.IsBasisOn (X.basicOpen g) (M.resBasicOpen g m)) :
    M.IsBasisOn (X.basicOpen (f * g)) (M.resBasicOpen (f * g) m) := by
  rw [mul_comm]
  exact isBasisOn_resBasicOpen_mul hb

variable [A.IsInvertible] [B.IsInvertible]

/-- **Sections of a tensor product of invertible sheaves over an affine open.** -/
theorem bijective_tensorSections (hU : IsAffineOpen U) :
    Function.Bijective (tensorSections A B U) := by
  classical
  haveI := isQuasicoherent_of_isInvertible A
  haveI := isQuasicoherent_of_isInvertible B
  haveI := isQuasicoherent_of_isInvertible (A ⊗ B)
  let s : Set Γ(X, U) := A.trivSet U * B.trivSet U
  have hs : Ideal.span s = ⊤ := by
    rw [← Ideal.span_mul_span', span_trivSet_eq_top A hU, span_trivSet_eq_top B hU,
      Ideal.top_mul]
  -- for `h = f g ∈ s`, sections `a h`, `b h` which are bases on `D(h)`
  have hdec : ∀ h ∈ s, ∃ f ∈ A.trivSet U, ∃ g ∈ B.trivSet U, f * g = h := fun h hh ↦ by
    obtain ⟨f, hf, g, hg, rfl⟩ := Set.mem_mul.mp hh
    exact ⟨f, hf, g, hg, rfl⟩
  have hab : ∀ h ∈ s, ∃ (a : Γ(A, U)) (b : Γ(B, U)),
      A.IsBasisOn (X.basicOpen h) (A.resBasicOpen h a) ∧
        B.IsBasisOn (X.basicOpen h) (B.resBasicOpen h b) := fun h hh ↦ by
    obtain ⟨f, ⟨a, ha⟩, g, ⟨b, hb⟩, rfl⟩ := hdec h hh
    exact ⟨a, b, isBasisOn_resBasicOpen_mul ha, isBasisOn_resBasicOpen_mul' hb⟩
  let a₀ : Γ(X, U) → Γ(A, U) := fun h ↦ if hh : h ∈ s then (hab h hh).choose else 0
  let b₀ : Γ(X, U) → Γ(B, U) := fun h ↦
    if hh : h ∈ s then (hab h hh).choose_spec.choose else 0
  have ha₀ : ∀ h ∈ s, A.IsBasisOn (X.basicOpen h) (A.resBasicOpen h (a₀ h)) := fun h hh ↦ by
    simpa [a₀, hh] using (hab h hh).choose_spec.choose_spec.1
  have hb₀ : ∀ h ∈ s, B.IsBasisOn (X.basicOpen h) (B.resBasicOpen h (b₀ h)) := fun h hh ↦ by
    simpa [b₀, hh] using (hab h hh).choose_spec.choose_spec.2
  have hθ : ∀ h ∈ s, (A ⊗ B).IsBasisOn (X.basicOpen h)
      ((A ⊗ B).resBasicOpen h (tensorSections A B U (a₀ h ⊗ₜ b₀ h))) := fun h hh ↦ by
    rw [tensorSections_tmul, resBasicOpen_apply, tmulSection_res]
    exact isBasisOn_tmulSection (ha₀ h hh) (hb₀ h hh)
  refine bijective_of_local (tensorSections A B U) s hs (fun h ↦ a₀ h ⊗ₜ b₀ h)
    (fun h hh y ↦ ?_) (fun h hh n ↦ ?_) (fun h hh c hc ↦ ?_)
  · induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a b =>
      obtain ⟨i, c, hc⟩ := exists_pow_smul_eq_smul_of_isBasisOn hU h (a₀ h) (ha₀ h hh) a
      obtain ⟨j, d, hd⟩ := exists_pow_smul_eq_smul_of_isBasisOn hU h (b₀ h) (hb₀ h hh) b
      refine ⟨i + j, c * d, ?_⟩
      rw [pow_add, mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', hc, hd,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    | add y z hy hz =>
      obtain ⟨i, a, ha⟩ := hy
      obtain ⟨j, b, hb⟩ := hz
      refine ⟨i + j, h ^ j * a + h ^ i * b, ?_⟩
      have e1 : h ^ (i + j) • y = h ^ j • (a • (a₀ h ⊗ₜ b₀ h)) := by
        rw [pow_add, mul_comm, mul_smul, ha]
      have e2 : h ^ (i + j) • z = h ^ i • (b • (a₀ h ⊗ₜ b₀ h)) := by
        rw [pow_add, mul_smul, hb]
      rw [smul_add, e1, e2, smul_smul, smul_smul, add_smul]
  · exact exists_pow_smul_eq_smul_of_isBasisOn hU h _ (hθ h hh) n
  · exact exists_pow_mul_eq_zero_of_isBasisOn hU h _ (hθ h hh) c hc

/-- `Γ(A, U) ⊗_{Γ(X, U)} Γ(B, U) ≃ Γ(A ⊗ B, U)` for invertible `A`, `B` and affine `U`. -/
def tensorSectionsEquiv (hU : IsAffineOpen U) :
    Γ(A, U) ⊗[Γ(X, U)] Γ(B, U) ≃ₗ[Γ(X, U)] Γ(A ⊗ B, U) :=
  LinearEquiv.ofBijective _ (bijective_tensorSections hU)

end TensorSections

end AlgebraicGeometry.Scheme.Modules
