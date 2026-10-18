/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisAlgebra
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Ring.Action.End

/-!
# Galois descent of algebra homomorphisms

Let `L / k` be a finite Galois extension with group `G`, `A` an `L`-algebra with a semilinear
`G`-action `ρ`, `R` a `k`-algebra and `B = L ⊗_k R` (given abstractly by
`Algebra.IsPushout k L R B`) with a semilinear `G`-action `σ` fixing `R` (on `L ⊗_k R` this is
`g ⊗ id`, but `σ` may be any such action, which is then automatically `g ⊗ id`).

* `CurvesJacobian.GaloisDescent.mem_fixedAlg_pushout_iff`: `B^G = R`.
* `CurvesJacobian.GaloisDescent.algebraMap_pushout_injective`: `R ⟶ B` is injective.
* **`CurvesJacobian.GaloisDescent.equivariantHomEquiv`**: `G`-equivariant `L`-algebra maps
  `A ⟶ B` correspond to `k`-algebra maps `A^G ⟶ R` (restriction to the invariants).
* `CurvesJacobian.GaloisDescent.exists_comap_eq_of_comap_eq`: `G` acts transitively on the
  primes of `B` above a given prime of `R` (the fibres of `Spec B ⟶ Spec R` are `G`-orbits).
-/

open TensorProduct

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

section Pushout

variable (R B : Type*) [CommRing R] [Algebra k R] [CommRing B] [Algebra L B] [Algebra k B]
  [IsScalarTower k L B] [Algebra R B] [IsScalarTower k R B] [Algebra.IsPushout k L R B]
  (σ : Gal(L/k) →* RingAut B) (hσ : ∀ g l, σ g (algebraMap L B l) = algebraMap L B (g l))
  (hσR : ∀ g r, σ g (algebraMap R B r) = algebraMap R B r)

omit [FiniteDimensional k L] [IsGalois k L] in
include hσ hσR in
/-- Under `L ⊗_k R ≃ B`, the action `σ` is `g ⊗ id`. -/
lemma pushoutEquiv_tensorAction (g : Gal(L/k)) (z : L ⊗[k] R) :
    Algebra.IsPushout.equiv k L R B (tensorAction R g z) =
      σ g (Algebra.IsPushout.equiv k L R B z) := by
  induction z with
  | zero => simp
  | tmul l r =>
    rw [tensorAction_tmul, Algebra.IsPushout.equiv_tmul, Algebra.IsPushout.equiv_tmul, map_mul,
      hσ, hσR]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

omit [FiniteDimensional k L] [IsGalois k L] in
lemma pushoutEquiv_one_tmul (r : R) :
    Algebra.IsPushout.equiv k L R B (1 ⊗ₜ r) = algebraMap R B r := by
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

variable (k L) in
include k L in
omit [FiniteDimensional k L] [IsGalois k L] in
/-- `R ⟶ L ⊗_k R` is injective. -/
lemma algebraMap_pushout_injective : Function.Injective (algebraMap R B) := by
  intro r r' h
  rw [← pushoutEquiv_one_tmul (k := k) (L := L) R B,
    ← pushoutEquiv_one_tmul (k := k) (L := L) R B] at h
  exact Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective
    ((Algebra.IsPushout.equiv k L R B).injective h)

include hσR in
/-- **The invariants of `B = L ⊗_k R` are `R`.** -/
theorem mem_fixedAlg_pushout_iff (b : B) :
    b ∈ fixedAlg σ hσ ↔ ∃ r : R, algebraMap R B r = b := by
  constructor
  · intro hb
    obtain ⟨z, rfl⟩ := (Algebra.IsPushout.equiv k L R B).surjective b
    have hz : z ∈ fixedAlg (tensorAction R) (tensorAction_algebraMap R) := fun g ↦
      (Algebra.IsPushout.equiv k L R B).injective (by
        rw [pushoutEquiv_tensorAction R B σ hσ hσR, hb g])
    obtain ⟨r, rfl⟩ := (mem_fixedAlg_tensor_iff R z).mp hz
    exact ⟨r, (pushoutEquiv_one_tmul R B r).symm⟩
  · rintro ⟨r, rfl⟩ g
    exact hσR g r

variable {A : Type*} [CommRing A] [Algebra L A] [Algebra k A] [IsScalarTower k L A]
  (ρ : Gal(L/k) →* RingAut A) (hρ : ∀ g l, ρ g (algebraMap L A l) = algebraMap L A (g l))

/-- The `G`-equivariant `L`-algebra maps `A ⟶ B`. -/
def EquivariantHom : Type _ := {φ : A →ₐ[L] B // ∀ g a, φ (ρ g a) = σ g (φ a)}

variable {R B σ ρ}

include hσ hσR in
lemma exists_algebraMap_eq (φ : EquivariantHom B σ ρ) (β : fixedAlg ρ hρ) :
    ∃ r : R, algebraMap R B r = φ.1 β :=
  (mem_fixedAlg_pushout_iff R B σ hσ hσR _).mp fun g ↦ by rw [← φ.2, β.2 g]

include hσ hσR in
/-- The restriction `A^G ⟶ R` of an equivariant map `A ⟶ B`. -/
def restrictInv (φ : EquivariantHom B σ ρ) : fixedAlg ρ hρ →ₐ[k] R where
  toFun β := (exists_algebraMap_eq hσ hσR hρ φ β).choose
  map_one' := algebraMap_pushout_injective k L R B (by
    rw [(exists_algebraMap_eq hσ hσR hρ φ 1).choose_spec, map_one, OneMemClass.coe_one, map_one])
  map_mul' β β' := algebraMap_pushout_injective k L R B (by
    rw [(exists_algebraMap_eq hσ hσR hρ φ _).choose_spec, map_mul,
      (exists_algebraMap_eq hσ hσR hρ φ _).choose_spec,
      (exists_algebraMap_eq hσ hσR hρ φ _).choose_spec, MulMemClass.coe_mul, map_mul])
  map_zero' := algebraMap_pushout_injective k L R B (by
    rw [(exists_algebraMap_eq hσ hσR hρ φ 0).choose_spec, map_zero, ZeroMemClass.coe_zero,
      map_zero])
  map_add' β β' := algebraMap_pushout_injective k L R B (by
    rw [(exists_algebraMap_eq hσ hσR hρ φ _).choose_spec, map_add,
      (exists_algebraMap_eq hσ hσR hρ φ _).choose_spec,
      (exists_algebraMap_eq hσ hσR hρ φ _).choose_spec, AddMemClass.coe_add, map_add])
  commutes' c := algebraMap_pushout_injective k L R B (by
    rw [(exists_algebraMap_eq hσ hσR hρ φ _).choose_spec, ← IsScalarTower.algebraMap_apply,
      Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply k L A, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply])

include hσ hσR in
lemma algebraMap_restrictInv (φ : EquivariantHom B σ ρ) (β : fixedAlg ρ hρ) :
    algebraMap R B (restrictInv hσ hσR hρ φ β) = φ.1 β :=
  (exists_algebraMap_eq hσ hσR hρ φ β).choose_spec

variable (B) in
/-- The `L`-linear extension `A ≃ L ⊗_k A^G ⟶ B` of a `k`-algebra map `χ : A^G ⟶ R`. -/
def extendInv (χ : fixedAlg ρ hρ →ₐ[k] R) : A →ₐ[L] B :=
  (Algebra.TensorProduct.lift (Algebra.ofId L B) ((IsScalarTower.toAlgHom k R B).comp χ)
    fun _ _ ↦ Commute.all _ _).comp (descentEquiv ρ hρ).symm.toAlgHom

omit [FiniteDimensional k L] [IsGalois k L] [Algebra.IsPushout k L R B] in
lemma lift_tmul_aux (χ : fixedAlg ρ hρ →ₐ[k] R) (l : L) (β : fixedAlg ρ hρ) :
    Algebra.TensorProduct.lift (Algebra.ofId L B) ((IsScalarTower.toAlgHom k R B).comp χ)
      (fun _ _ ↦ Commute.all _ _) (l ⊗ₜ β) = l • algebraMap R B (χ β) := by
  rw [Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

omit [Algebra.IsPushout k L R B] in
lemma extendInv_smul (χ : fixedAlg ρ hρ →ₐ[k] R) (l : L) (β : fixedAlg ρ hρ) :
    extendInv B hρ χ (l • (β : A)) = l • algebraMap R B (χ β) := by
  rw [extendInv, AlgHom.comp_apply,
    show l • (β : A) = descentEquiv ρ hρ (l ⊗ₜ β) from (descentEquiv_tmul ρ hρ l β).symm]
  change Algebra.TensorProduct.lift _ _ _ ((descentEquiv ρ hρ).symm _) = _
  rw [AlgEquiv.symm_apply_apply, lift_tmul_aux]

omit [Algebra.IsPushout k L R B] in
lemma extendInv_coe (χ : fixedAlg ρ hρ →ₐ[k] R) (β : fixedAlg ρ hρ) :
    extendInv B hρ χ (β : A) = algebraMap R B (χ β) := by
  simpa using extendInv_smul (B := B) hρ χ 1 β

omit [Algebra.IsPushout k L R B] in
include hσ hσR in
lemma extendInv_equivariant (χ : fixedAlg ρ hρ →ₐ[k] R) (g : Gal(L/k)) (a : A) :
    extendInv B hρ χ (ρ g a) = σ g (extendInv B hρ χ a) := by
  obtain ⟨z, rfl⟩ := (descentEquiv ρ hρ).surjective a
  induction z with
  | zero => simp
  | tmul l β =>
    rw [descentEquiv_tmul, map_smul' ρ hρ, β.2 g, extendInv_smul, extendInv_smul,
      Algebra.smul_def, Algebra.smul_def, map_mul, hσ, hσR]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', map_add, map_add]

omit [Algebra k B] [IsScalarTower k L B] [Algebra R B] [IsScalarTower k R B]
  [Algebra.IsPushout k L R B] in
/-- `L`-algebra maps out of `A = L · A^G` agree once they agree on `A^G`. -/
lemma fixedAlg_ext {φ ψ : A →ₐ[L] B}
    (h : ∀ β : fixedAlg ρ hρ, φ β = ψ β) : φ = ψ := by
  ext a
  obtain ⟨z, rfl⟩ := (descentEquiv ρ hρ).surjective a
  induction z with
  | zero => simp
  | tmul l β => rw [descentEquiv_tmul, map_smul, map_smul, h]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- **Speiser for base change**: if `χ : A^G ⟶ R` is bijective, so is its extension
`A ≅ L ⊗_k A^G ⟶ L ⊗_k R ≅ B`. -/
theorem bijective_extendInv (χ : fixedAlg ρ hρ →ₐ[k] R) (hχ : Function.Bijective χ) :
    Function.Bijective (extendInv B hρ χ) := by
  let e : L ⊗[k] fixedAlg ρ hρ ≃ₐ[L] B := (Algebra.TensorProduct.congr AlgEquiv.refl
    (AlgEquiv.ofBijective χ hχ)).trans (Algebra.IsPushout.equiv k L R B)
  have h : extendInv B hρ χ = e.toAlgHom.comp (descentEquiv ρ hρ).symm.toAlgHom := by
    refine fixedAlg_ext hρ fun β ↦ ?_
    have hb : (β : A) = descentEquiv ρ hρ (1 ⊗ₜ β) := by rw [descentEquiv_tmul, one_smul]
    rw [extendInv_coe, AlgHom.comp_apply]
    change _ = e ((descentEquiv ρ hρ).symm (β : A))
    rw [hb, AlgEquiv.symm_apply_apply]
    change _ = Algebra.IsPushout.equiv k L R B
      (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective χ hχ) (1 ⊗ₜ β))
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    exact (pushoutEquiv_one_tmul R B _).symm
  rw [h]
  exact e.bijective.comp (descentEquiv ρ hρ).symm.bijective

/-- **Galois descent of algebra maps**: `G`-equivariant `L`-algebra maps `A ⟶ L ⊗_k R`
correspond to `k`-algebra maps `A^G ⟶ R`. -/
def equivariantHomEquiv : EquivariantHom B σ ρ ≃ (fixedAlg ρ hρ →ₐ[k] R) where
  toFun φ := restrictInv hσ hσR hρ φ
  invFun χ := ⟨extendInv B hρ χ, extendInv_equivariant hσ hσR hρ χ⟩
  left_inv φ := by
    refine Subtype.ext (fixedAlg_ext hρ fun β ↦ ?_)
    rw [extendInv_coe, algebraMap_restrictInv]
  right_inv χ := by
    ext β
    apply algebraMap_pushout_injective k L R B
    rw [algebraMap_restrictInv]
    exact extendInv_coe hρ χ β

include hσ hσR in
/-- **The fibres of `Spec (L ⊗_k R) ⟶ Spec R` are `G`-orbits**: two primes of `B` above the same
prime of `R` are conjugate under `σ`. -/
theorem exists_comap_eq_of_comap_eq (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (algebraMap R B) = Q.comap (algebraMap R B)) :
    ∃ g : Gal(L/k), Q = P.comap ((σ g : B ≃+* B) : B →+* B) := by
  letI : MulSemiringAction Gal(L/k) B := MulSemiringAction.compHom B σ
  have hsm (g : Gal(L/k)) (b : B) : g • b = σ g b := rfl
  haveI : Algebra.IsInvariant R B Gal(L/k) := ⟨fun b hb ↦
    (mem_fixedAlg_pushout_iff R B σ hσ hσR b).mp fun g ↦ (hsm g b).symm.trans (hb g)⟩
  haveI : SMulCommClass Gal(L/k) R B := ⟨fun g r b ↦ by
    rw [hsm, hsm, Algebra.smul_def, Algebra.smul_def, map_mul, hσR]⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R B Gal(L/k) P Q h
  refine ⟨g⁻¹, hg.trans ?_⟩
  rw [Ideal.pointwise_smul_eq_comap]
  congr 1
  ext b
  rfl

end Pushout

end CurvesJacobian.GaloisDescent
