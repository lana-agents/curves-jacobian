/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Étaleness from bijectivity on tangent vectors

Let `k` be a ring and `A → B` a map of `k`-algebras with `B` smooth over `k` and `A` of finite
type over `k`. If for every maximal ideal `m` of `B` the restriction of derivations
`Der_k(B, B/m) → Der_k(A, B/m)` is bijective, then `A → B` is étale
(`CurvesJacobian.etale_of_bijective_compAlgebraMap`).

Proof. The map `u : B ⊗_A Ω_{A/k} → Ω_{B/k}` is bijective: `Hom_B(-, B/m)` of its cokernel and of
its kernel vanish for all maximal `m` (`Ω_{B/k}` is projective, so the kernel is a direct summand
of the finitely generated `B ⊗_A Ω_{A/k}`), and a finitely generated module with no nonzero maps
to the residue fields at maximal ideals is zero (`CurvesJacobian.subsingleton_of_forall_maximal`,
Nakayama via `Module.support_quotient`). Then the Jacobi–Zariski sequence
`H₁(L_{B/k}) → H₁(L_{B/A}) → B ⊗_A Ω_{A/k} → Ω_{B/k} → Ω_{B/A} → 0` (Stacks, Tag 00S2) gives
`H₁(L_{B/A}) = 0` and `Ω_{B/A} = 0`, i.e. `A → B` is formally étale, and it is of finite
presentation since `B` is of finite presentation over `k`.
-/

open TensorProduct

universe u

namespace CurvesJacobian

/-- **A finitely generated module with no nonzero maps to the residue fields at maximal ideals
is zero.** -/
lemma subsingleton_of_forall_maximal {B Q : Type*} [CommRing B] [AddCommGroup Q] [Module B Q]
    [Module.Finite B Q]
    (h : ∀ (m : Ideal B) [m.IsMaximal] (f : Q →ₗ[B] B ⧸ m), f = 0) : Subsingleton Q := by
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  have hann : Module.annihilator B Q ≠ ⊤ := fun h1 ↦
    (not_subsingleton_iff_nontrivial.mpr hQ) (Module.annihilator_eq_top_iff.mp h1)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
  have hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∈
      Module.support B (Q ⧸ (m • ⊤ : Submodule B Q)) := by
    rw [Module.support_quotient]
    exact ⟨Module.mem_support_iff_of_finite.mpr hle, by
      rw [PrimeSpectrum.mem_zeroLocus]⟩
  have hnt : Nontrivial (Q ⧸ (m • ⊤ : Submodule B Q)) := by
    by_contra h'
    rw [not_nontrivial_iff_subsingleton] at h'
    rw [Module.support_eq_empty] at hmem
    exact hmem
  letI := Ideal.Quotient.field m
  obtain ⟨v, hv⟩ := exists_ne (0 : Q ⧸ (m • ⊤ : Submodule B Q))
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (B ⧸ m) (Q ⧸ (m • ⊤ : Submodule B Q)), φ v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff (B ⧸ m) v).mp hc)
  obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective _ v
  have h0 := h m ((φ.restrictScalars B).comp (Submodule.mkQ _))
  exact hφ (LinearMap.congr_fun h0 q)

section Etale

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

omit [Algebra A B] in
private lemma eq_zero_of_compDer {m : Ideal B} (f : Ω[B⁄k] →ₗ[B] B ⧸ m)
    (hf : f.compDer (KaehlerDifferential.D k B) = 0) : f = 0 :=
  Derivation.liftKaehlerDifferential_unique _ _ (by rw [hf]; ext; simp)

variable (k A B) in
/-- **Bijectivity of `B ⊗_A Ω_{A/k} → Ω_{B/k}` from bijectivity on derivations to residue
fields.** -/
theorem bijective_mapBaseChange_of_bijective_compAlgebraMap [Algebra.FormallySmooth k B]
    [Module.Finite B Ω[B⁄k]] [Module.Finite B (B ⊗[A] Ω[A⁄k])]
    (h : ∀ (m : Ideal B) [m.IsMaximal],
      Function.Bijective (fun D : Derivation k B (B ⧸ m) ↦ D.compAlgebraMap A)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange k A B) := by
  set u := KaehlerDifferential.mapBaseChange k A B
  -- surjectivity
  have hsurj : Function.Surjective u := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine subsingleton_of_forall_maximal (B := B) ?_
    intro m _ f
    set g : Ω[B⁄k] →ₗ[B] B ⧸ m := f.comp (LinearMap.range u).mkQ
    have hgu : g.comp u = 0 := LinearMap.ext fun x ↦ by
      change f ((LinearMap.range u).mkQ (u x)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self u x), map_zero]
    have hD : (g.compDer (KaehlerDifferential.D k B)).compAlgebraMap A =
        (0 : Derivation k B (B ⧸ m)).compAlgebraMap A := by
      ext a
      have := LinearMap.congr_fun hgu (1 ⊗ₜ KaehlerDifferential.D k A a)
      simpa [u, KaehlerDifferential.mapBaseChange_tmul] using this
    have hg : g = 0 := eq_zero_of_compDer g ((h m).1 hD)
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (LinearMap.range u).mkQ_surjective x
    exact LinearMap.congr_fun hg y
  refine ⟨?_, hsurj⟩
  -- injectivity: `u` splits since `Ω_{B/k}` is projective
  obtain ⟨s, hs⟩ := Module.projective_lifting_property u LinearMap.id hsurj
  set K := LinearMap.ker u
  let p : B ⊗[A] Ω[A⁄k] →ₗ[B] K :=
    LinearMap.codRestrict K (LinearMap.id - s.comp u) (fun x ↦ by
      change u (x - s (u x)) = 0
      rw [map_sub, ← LinearMap.comp_apply u s, hs, LinearMap.id_apply, sub_self])
  have hp : Function.Surjective p := fun y ↦ ⟨y, by
    apply Subtype.ext
    change (y : B ⊗[A] Ω[A⁄k]) - s (u y) = y
    rw [y.2, map_zero, sub_zero]⟩
  haveI : Module.Finite B K := Module.Finite.of_surjective (R := B) p hp
  have hK : Subsingleton K := by
    refine subsingleton_of_forall_maximal (B := B) ?_
    intro m _ f
    set g : B ⊗[A] Ω[A⁄k] →ₗ[B] B ⧸ m := f.comp p
    -- the derivation of `A` corresponding to `g`
    let DA : Derivation k A (B ⧸ m) :=
      ((g.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄k] 1)).compDer
        (KaehlerDifferential.D k A)
    obtain ⟨DB, hDB⟩ := (h m).2 DA
    set hB : Ω[B⁄k] →ₗ[B] B ⧸ m := DB.liftKaehlerDifferential
    have hhu : hB.comp u = g := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b ω
      have e1 : (b ⊗ₜ ω : B ⊗[A] Ω[A⁄k]) = b • (1 ⊗ₜ ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, map_smul, map_smul]
      congr 1
      have e2 : ((hB.comp u).restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄k] 1) =
          (g.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄k] 1) := by
        apply Derivation.liftKaehlerDifferential_unique
        ext a
        have := congrArg (fun D : Derivation k A (B ⧸ m) ↦ D a) hDB
        simp only [Derivation.compAlgebraMap_apply] at this
        simp [u, hB, KaehlerDifferential.mapBaseChange_tmul, this, DA]
      exact LinearMap.congr_fun e2 ω
    have hgs : g.comp s = 0 := LinearMap.ext fun x ↦ by
      have : p (s x) = 0 := Subtype.ext (by
        change s x - s (u (s x)) = 0
        rw [← LinearMap.comp_apply u s, hs, LinearMap.id_apply, sub_self])
      change f (p (s x)) = 0
      rw [this, map_zero]
    have hB0 : hB = 0 := by
      rw [← hhu, LinearMap.comp_assoc, hs, LinearMap.comp_id] at hgs
      exact hgs
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hp y
    change g x = 0
    rw [← hhu, hB0, LinearMap.zero_comp, LinearMap.zero_apply]
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.eq_bot_iff _).mpr fun x hx ↦
    congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 0)

variable (k A B) in
/-- **Étaleness from bijectivity on derivations to residue fields.** If `B` is smooth over `k`,
`A` is of finite type over `k`, and `Der_k(B, B/m) → Der_k(A, B/m)` is bijective for every
maximal ideal `m` of `B`, then `B` is étale over `A`. -/
theorem etale_of_bijective_compAlgebraMap [Algebra.Smooth k B] [Algebra.FiniteType k A]
    (h : ∀ (m : Ideal B) [m.IsMaximal],
      Function.Bijective (fun D : Derivation k B (B ⧸ m) ↦ D.compAlgebraMap A)) :
    Algebra.Etale A B := by
  have hu := bijective_mapBaseChange_of_bijective_compAlgebraMap k A B h
  haveI : Subsingleton Ω[B⁄A] := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective k A B x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective k A B y
    obtain ⟨x', rfl⟩ := hu.2 x
    obtain ⟨y', rfl⟩ := hu.2 y
    rw [(KaehlerDifferential.exact_mapBaseChange_map k A B).apply_apply_eq_zero,
      (KaehlerDifferential.exact_mapBaseChange_map k A B).apply_apply_eq_zero]
  haveI : Subsingleton (Algebra.H1Cotangent A B) := by
    refine ⟨fun x y ↦ ?_⟩
    have hδ : ∀ z, Algebra.H1Cotangent.δ k A B z = 0 := fun z ↦
      hu.1 ((Algebra.H1Cotangent.exact_δ_mapBaseChange k A B).apply_apply_eq_zero z |>.trans
        (map_zero _).symm)
    obtain ⟨x', hx'⟩ := (Algebra.H1Cotangent.exact_map_δ k A B x).mp (hδ x)
    obtain ⟨y', hy'⟩ := (Algebra.H1Cotangent.exact_map_δ k A B y).mp (hδ y)
    rw [← hx', ← hy', Subsingleton.elim x' y']
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k A B
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end Etale

/-! ### Tangent vectors as lifts to `κ[ε]` -/

section Lift

open TrivSqZeroExt

variable {k B κ : Type u} [CommRing k] [CommRing B] [Algebra k B] [CommRing κ] [Algebra k κ]
  [Algebra B κ] [IsScalarTower k B κ]

/-- The lift `b ↦ b + D(b) ε : B → κ[ε]` of `B → κ` given by a derivation `D`. -/
def derLift (D : Derivation k B κ) : B →ₐ[k] TrivSqZeroExt κ κ where
  toFun b := inl (algebraMap B κ b) + inr (D b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [Derivation.leibniz, snd_mul, snd_add, snd_inl, snd_inr, fst_add, fst_inl,
        fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Algebra.smul_def,
        add_zero, zero_add, map_mul]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm]
  commutes' r := by
    rw [algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply, D.map_algebraMap, add_eq_left]
    exact inr_zero κ

@[simp] lemma fst_derLift (D : Derivation k B κ) (b : B) :
    (derLift D b).fst = algebraMap B κ b := by simp [derLift]

@[simp] lemma snd_derLift (D : Derivation k B κ) (b : B) : (derLift D b).snd = D b := by
  simp [derLift]

lemma derLift_injective : Function.Injective (derLift (k := k) (B := B) (κ := κ)) :=
  fun _ _ h ↦ Derivation.ext fun b ↦ by
    simpa using congrArg (fun ψ : B →ₐ[k] TrivSqZeroExt κ κ ↦ (ψ b).snd) h

/-- Every lift of `B → κ` to `κ[ε]` comes from a derivation. -/
lemma exists_derLift_eq (ψ : B →ₐ[k] TrivSqZeroExt κ κ) (hψ : ∀ b, (ψ b).fst = algebraMap B κ b) :
    ∃ D : Derivation k B κ, derLift D = ψ := by
  refine ⟨{ toFun := fun b ↦ (ψ b).snd
            map_add' := fun a b ↦ by simp
            map_smul' := fun r b ↦ by
              rw [map_smul, snd_smul]
              rfl
            map_one_eq_zero' := by simp
            leibniz' := fun a b ↦ by
              simp only [map_mul, snd_mul, hψ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
                MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
              ring }, ?_⟩
  ext b
  · simp [hψ]
  · simp

variable {A : Type u} [CommRing A] [Algebra k A] [Algebra A B] [IsScalarTower k A B]
  [Algebra A κ] [IsScalarTower A B κ] [IsScalarTower k A κ]

lemma derLift_comp (D : Derivation k B κ) :
    (derLift D).comp (IsScalarTower.toAlgHom k A B) = derLift (D.compAlgebraMap A) := by
  ext a
  · simp [IsScalarTower.algebraMap_apply A B κ a]
  · simp

end Lift

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

variable (k A B) in
/-- **Étaleness from bijectivity on tangent vectors.** If `B` is smooth over `k`, `A` is of
finite type over `k`, and for every maximal ideal `m` of `B` composing with `A → B` is a
bijection from the lifts `B → (B/m)[ε]` of `B → B/m` to the lifts `A → (B/m)[ε]` of
`A → B/m`, then `B` is étale over `A`. -/
theorem etale_of_bijective_lift [Algebra.Smooth k B] [Algebra.FiniteType k A]
    (h : ∀ (m : Ideal B) [m.IsMaximal],
      (∀ ψ ψ' : B →ₐ[k] TrivSqZeroExt (B ⧸ m) (B ⧸ m),
        (∀ b, (ψ b).fst = Ideal.Quotient.mk m b) → (∀ b, (ψ' b).fst = Ideal.Quotient.mk m b) →
        ψ.comp (IsScalarTower.toAlgHom k A B) = ψ'.comp (IsScalarTower.toAlgHom k A B) →
        ψ = ψ') ∧
      ∀ ψ' : A →ₐ[k] TrivSqZeroExt (B ⧸ m) (B ⧸ m),
        (∀ a, (ψ' a).fst = Ideal.Quotient.mk m (algebraMap A B a)) →
        ∃ ψ : B →ₐ[k] TrivSqZeroExt (B ⧸ m) (B ⧸ m),
          (∀ b, (ψ b).fst = Ideal.Quotient.mk m b) ∧
          ψ.comp (IsScalarTower.toAlgHom k A B) = ψ') :
    Algebra.Etale A B := by
  refine etale_of_bijective_compAlgebraMap k A B fun m _ ↦ ⟨fun D D' hDD ↦ ?_, fun DA ↦ ?_⟩
  · apply derLift_injective (k := k)
    refine (h m).1 _ _ (fun b ↦ fst_derLift _ b) (fun b ↦ fst_derLift _ b) ?_
    simp only at hDD
    rw [derLift_comp, derLift_comp, hDD]
  · obtain ⟨ψ, hψ, hψc⟩ := (h m).2 (derLift DA) (fun a ↦
      (fst_derLift DA a).trans (IsScalarTower.algebraMap_apply A B (B ⧸ m) a))
    obtain ⟨D, rfl⟩ := exists_derLift_eq (k := k) (B := B) (κ := B ⧸ m) ψ
      (fun b ↦ (hψ b).trans (Ideal.Quotient.algebraMap_eq m ▸ rfl))
    refine ⟨D, derLift_injective (k := k) ?_⟩
    simp only
    rw [← derLift_comp, hψc]

end CurvesJacobian
