/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.TwoCech
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Twisting two-set Čech complexes (algebra for Stacks, Lemma 44.6.5, Tag 0B9Y)

Let `D = (f : P → R ← Q : g)` and `D' = (f' : P' → R' ← Q' : g')` be two-set Čech data, i.e.
two-term complexes `d = f - g : P × Q → R` with `H⁰ = ker d` and `H¹ = coker d`
(`TwoCech.H0`, `TwoCech.H1`). This file contains the linear algebra of the two twisting steps in
the proof of Stacks, Lemma 44.6.5 (Tag 0B9Y), for the Čech complexes of line bundles on the two
charts `U`, `V` (with overlap `W`) of a curve over a field `F`.

**Removing a point** (`TwoCech.subsingleton_H1_of_removePoint`,
`TwoCech.finrank_H0_of_removePoint`). Let `α, β, γ : D' → D` be injective maps of Čech data
(the maps `Γ(L(-x)) → Γ(L)` on the charts), and `ε : R → E` a map to a vector space of dimension
`1` (evaluation at the point `x ∈ W`) such that `im α = ker (ε ∘ f)`, `im β = ker (ε ∘ g)` and
`ε ∘ γ = 0`. If some `h ∈ H⁰(D)` does not vanish at `x` (`ε (f h₁) ≠ 0`), then `H¹(D) = 0`
implies `H¹(D') = 0`, and `dim H⁰(D') = dim H⁰(D) - 1`. This is the exact sequence
`0 → L(-x) → L → L|_x → 0` of the proof of Tag 0B9Y.

**Twisting by a divisor at infinity** (`TwoCech.mem_range_of_pow_smul_mem_range`,
`TwoCech.subsingleton_H1_of_gens`, `TwoCech.exists_ne_zero_H0`). Let `α, β, γ : D → D'` be a map
of Čech data (the maps `Γ(L) → Γ(L(n·∞))`), where `σ` acts on `Q, R, Q', R'` compatibly, `σ` is
injective on `R'` and the image of `β` is contained in `σⁿ Q'` (the divisor `n·∞` is cut out by
`σⁿ` on `V` and disjoint from `W`). Then every `c ∈ R` with `σᵐ c ∈ g(Q)`, `m ≤ n`, satisfies
`γ c ∈ g'(Q')`. When `γ` is surjective this kills `H¹(D')` as soon as it kills classes
generating `H¹(D)` (Serre vanishing for the twists of a line bundle by a divisor at infinity).
-/

open Function LinearMap

namespace TwoCech

section Field

variable {F : Type*} [Field F]
variable {P Q R P' Q' R' E : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]
  [AddCommGroup R] [Module F R] [AddCommGroup P'] [Module F P'] [AddCommGroup Q'] [Module F Q']
  [AddCommGroup R'] [Module F R'] [AddCommGroup E] [Module F E]
  {f : P →ₗ[F] R} {g : Q →ₗ[F] R} {f' : P' →ₗ[F] R'} {g' : Q' →ₗ[F] R'}
  (α : P' →ₗ[F] P) (β : Q' →ₗ[F] Q) (γ : R' →ₗ[F] R)
  (hf : f ∘ₗ α = γ ∘ₗ f') (hg : g ∘ₗ β = γ ∘ₗ g') (ε : R →ₗ[F] E)

section RemovePoint

variable {α β γ ε}

include hf hg in
/-- **Removing a point preserves `H¹ = 0`** (proof of Stacks, Lemma 44.6.5, Tag 0B9Y). -/
theorem subsingleton_H1_of_removePoint (hα : range α = ker (ε ∘ₗ f))
    (hβ : range β = ker (ε ∘ₗ g)) (hγ : ∀ c, ε (γ c) = 0) (hγi : Injective γ)
    (hE : ∀ e₁ e₂ : E, e₁ ≠ 0 → ∃ μ : F, e₂ = μ • e₁)
    {h : P × Q} (hh : h ∈ H0 f g) (hh0 : ε (f h.1) ≠ 0) (h1 : Subsingleton (H1 f g)) :
    Subsingleton (H1 f' g') := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h1 ⊢
  intro c'
  obtain ⟨⟨a, b⟩, hab⟩ := h1 (γ c')
  rw [d_apply] at hab
  have hh' : f h.1 = g h.2 := mem_H0.mp hh
  have hεab : ε (f a) = ε (g b) := by
    have := hγ c'
    rw [← hab, map_sub, sub_eq_zero] at this
    exact this
  obtain ⟨μ, hμ⟩ := hE _ (ε (f a)) hh0
  have ha' : f (a - μ • h.1) ∈ ker ε := by
    rw [LinearMap.mem_ker, map_sub, map_smul, map_sub, map_smul, hμ, sub_self]
  have hb' : g (b - μ • h.2) ∈ ker ε := by
    rw [LinearMap.mem_ker, map_sub, map_smul, map_sub, map_smul, ← hh', ← hεab, hμ, sub_self]
  obtain ⟨a'', ha''⟩ : a - μ • h.1 ∈ range α := by rw [hα]; exact ha'
  obtain ⟨b'', hb''⟩ : b - μ • h.2 ∈ range β := by rw [hβ]; exact hb'
  refine ⟨(a'', b''), hγi ?_⟩
  rw [d_apply, map_sub, ← LinearMap.comp_apply γ f', ← hf, ← LinearMap.comp_apply γ g', ← hg,
    LinearMap.comp_apply, LinearMap.comp_apply, ha'', hb'', ← hab, map_sub, map_sub, map_smul,
    map_smul, hh']
  abel

include hf hg in
/-- The image of `H⁰(D') → H⁰(D)` is the kernel of `h ↦ ε (f h₁)`. -/
theorem range_mapH0_of_removePoint (hα : range α = ker (ε ∘ₗ f))
    (hβ : range β = ker (ε ∘ₗ g)) (hγi : Injective γ) :
    range (mapH0 α β γ hf hg) =
      ker (ε ∘ₗ f ∘ₗ LinearMap.fst F P Q ∘ₗ (H0 f g).subtype) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change ε (f (α x.1.1)) = 0
    have : α x.1.1 ∈ range α := ⟨_, rfl⟩
    rw [hα] at this
    exact this
  · rintro ⟨⟨a, b⟩, hab⟩ hx
    have hab' : f a = g b := mem_H0.mp hab
    have ha : a ∈ range α := by rw [hα]; exact hx
    have hb : b ∈ range β := by
      rw [hβ, LinearMap.mem_ker, LinearMap.comp_apply, ← hab']
      exact hx
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    refine ⟨⟨(a', b'), mem_H0.mpr (hγi ?_)⟩, rfl⟩
    rw [← LinearMap.comp_apply γ f', ← hf, ← LinearMap.comp_apply γ g', ← hg,
      LinearMap.comp_apply, LinearMap.comp_apply, hab']

include hf hg in
/-- **Removing a point lowers `h⁰` by one** (proof of Stacks, Lemma 44.6.5, Tag 0B9Y). -/
theorem finrank_H0_of_removePoint [FiniteDimensional F (H0 f g)] (hαi : Injective α)
    (hβi : Injective β) (hα : range α = ker (ε ∘ₗ f)) (hβ : range β = ker (ε ∘ₗ g))
    (hγi : Injective γ) (hE : ∀ e₁ e₂ : E, e₁ ≠ 0 → ∃ μ : F, e₂ = μ • e₁)
    {h : P × Q} (hh : h ∈ H0 f g) (hh0 : ε (f h.1) ≠ 0) :
    Module.finrank F (H0 f' g') + 1 = Module.finrank F (H0 f g) := by
  have hE1 : Module.finrank F E = 1 :=
    (finrank_eq_one_iff_of_nonzero' _ hh0).mpr fun w ↦
      (hE _ w hh0).imp fun μ hμ ↦ hμ.symm
  set lam := ε ∘ₗ f ∘ₗ LinearMap.fst F P Q ∘ₗ (H0 f g).subtype
  have hsurj : Surjective lam := by
    intro e
    obtain ⟨μ, hμ⟩ := hE _ e hh0
    exact ⟨μ • ⟨h, hh⟩, by simp [lam, hμ]⟩
  have hinj := mapH0_injective α β γ hf hg hαi hβi
  haveI : FiniteDimensional F (H0 f' g') :=
    Module.Finite.of_injective (mapH0 α β γ hf hg) hinj
  have h1 := LinearMap.finrank_range_add_finrank_ker lam
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hE1,
    ← range_mapH0_of_removePoint hf hg hα hβ hγi, LinearMap.finrank_range_of_inj hinj] at h1
  omega

end RemovePoint

end Field

section Infinity

variable {A : Type*} [CommRing A]
variable {P Q R P' Q' R' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R] [AddCommGroup P'] [Module A P'] [AddCommGroup Q'] [Module A Q']
  [AddCommGroup R'] [Module A R']
  {f : P →ₗ[A] R} {g : Q →ₗ[A] R} {f' : P' →ₗ[A] R'} {g' : Q' →ₗ[A] R'}
  {α : P →ₗ[A] P'} {β : Q →ₗ[A] Q'} {γ : R →ₗ[A] R'}

/-- **Twisting by a divisor at infinity kills a class** (Serre vanishing on the charts). Let
`σ` act on `Q, R, Q', R'` compatibly with `g, g', β, γ`, injectively on `R'`, and let the image
of `β` lie in `σⁿ Q'`. If `σᵐ c ∈ g(Q)` with `m ≤ n`, then `γ c ∈ g'(Q')`. -/
theorem mem_range_of_pow_smul_mem_range (hg : g' ∘ₗ β = γ ∘ₗ g)
    (sQ : Module.End A Q) (sR : Module.End A R) (sQ' : Module.End A Q') (sR' : Module.End A R')
    (hgs : g ∘ₗ sQ = sR ∘ₗ g) (hg's : g' ∘ₗ sQ' = sR' ∘ₗ g') (hγs : γ ∘ₗ sR = sR' ∘ₗ γ)
    (hsR' : Injective sR') {n : ℕ} (hβn : ∀ q, β q ∈ range (sQ' ^ n))
    {c : R} {m : ℕ} (hm : m ≤ n) (hc : (sR ^ m) c ∈ range g) : γ c ∈ range g' := by
  obtain ⟨b, hb⟩ := hc
  obtain ⟨q', hq'⟩ := hβn ((sQ ^ (n - m)) b)
  refine ⟨q', ?_⟩
  have P1 : ∀ j : ℕ, g' ∘ₗ (sQ' ^ j) = (sR' ^ j) ∘ₗ g' := fun j ↦
    (Module.End.commute_pow_left_of_commute hg's.symm j).symm
  have P2 : ∀ j : ℕ, γ ∘ₗ (sR ^ j) = (sR' ^ j) ∘ₗ γ := fun j ↦
    (Module.End.commute_pow_left_of_commute hγs.symm j).symm
  have P3 : ∀ j : ℕ, g ∘ₗ (sQ ^ j) = (sR ^ j) ∘ₗ g := fun j ↦
    (Module.End.commute_pow_left_of_commute hgs.symm j).symm
  have hinj : Injective (sR' ^ n) := by
    rw [Module.End.coe_pow]
    exact hsR'.iterate n
  apply hinj
  have e1 : (sR' ^ n) (g' q') = g' ((sQ' ^ n) q') := (LinearMap.congr_fun (P1 n) q').symm
  have e2 : (sR' ^ n) (γ c) = γ ((sR ^ n) c) := (LinearMap.congr_fun (P2 n) c).symm
  have e3 : (sR ^ n) c = g ((sQ ^ (n - m)) b) := by
    have : sR ^ n = sR ^ (n - m) * sR ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
    rw [this, Module.End.mul_apply, ← hb]
    exact (LinearMap.congr_fun (P3 (n - m)) b).symm
  rw [e1, e2, e3, hq', ← LinearMap.comp_apply g', hg, LinearMap.comp_apply]

/-- If `γ` is surjective and the images of classes generating `H¹(D)` lie in `g'(Q')`, then
`H¹(D') = 0`. -/
theorem subsingleton_H1_of_gens (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g)
    (hγ : Surjective γ) (S : Set R) (hS : Submodule.span A S ⊔ range (d f g) = ⊤)
    (hSg : ∀ c ∈ S, γ c ∈ range g') : Subsingleton (H1 f' g') := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  intro r'
  obtain ⟨r, rfl⟩ := hγ r'
  have hr : r ∈ Submodule.span A S ⊔ range (d f g) := hS ▸ Submodule.mem_top
  have hle : Submodule.span A S ⊔ range (d f g) ≤ (range (d f' g')).comap γ := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro c hc
      obtain ⟨q', hq'⟩ := hSg c hc
      exact ⟨(0, -q'), by rw [d_apply, map_zero, map_neg, zero_sub, neg_neg, hq']⟩
    · rintro _ ⟨⟨p, q⟩, rfl⟩
      refine ⟨(α p, β q), ?_⟩
      rw [d_apply, d_apply, map_sub, ← LinearMap.comp_apply f', hf, ← LinearMap.comp_apply g',
        hg, LinearMap.comp_apply, LinearMap.comp_apply]
  exact hle hr

/-- A nonzero element of `P` whose image lies in `g'(Q')` after twisting gives a nonzero element
of `H⁰(D')`. -/
theorem exists_ne_zero_H0 (hf : f' ∘ₗ α = γ ∘ₗ f) (hα : Injective α) {u : P} (hu : u ≠ 0)
    {q' : Q'} (hq' : g' q' = γ (f u)) : ∃ x ∈ H0 f' g', x ≠ 0 := by
  refine ⟨(α u, q'), mem_H0.mpr ?_, ?_⟩
  · rw [hq', ← LinearMap.comp_apply f', hf, LinearMap.comp_apply]
  · intro h
    exact hu (hα (by rw [map_zero]; exact congrArg Prod.fst h))

/-- Classes generating a finite `H¹`. -/
theorem exists_finset_span_sup_eq_top (f : P →ₗ[A] R) (g : Q →ₗ[A] R)
    [Module.Finite A (H1 f g)] :
    ∃ S : Finset R, Submodule.span A (S : Set R) ⊔ range (d f g) = ⊤ := by
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := H1 f g)
  classical
  choose lift hlift using fun t : H1 f g ↦ Submodule.Quotient.mk_surjective _ t
  refine ⟨T.image lift, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← hT]
  congr 1
  ext t
  simp [hlift]

end Infinity

end TwoCech
