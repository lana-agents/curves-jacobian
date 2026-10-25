/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinNaturality
import LocalClassFieldTheory.Reciprocity.ArtinInertia
import Pi1.Profinite.Slim
import Pi1.FundamentalGroup.Point

/-!
# The absolute Galois group of a `p`-adic field is slim

For a finite extension `K` of `ℚ_p` and an algebraic closure `Ω` of `K`, the absolute Galois
group `G_K = Gal(Ω/K)` is **slim**: every element commuting with an open subgroup is trivial
(`CurvesJacobian.LocAn.isSlim_galoisGroup_padic`). Hence so is `G_K = π₁ᵉᵗ(Spec K)`
(`CurvesJacobian.LocAn.isSlim_Gk_padic`), whose centre is trivial
(`CurvesJacobian.LocAn.center_Gk_padic`), the `p`-adic analogue of
`CurvesJacobian.Cusp.isSlim_galoisGroup_numberField` and `CurvesJacobian.Cusp.isSlim_Gk`.

This is the slimness portion of [AbsTopI] Theorem 1.7 (ii) ("If `k` is an MLF ..., then `G_k` ...
is elastic and slim"; [AbsTopI] = `Topics in Absolute Anabelian Geometry I.txt`). Ported from
iut `Iut/Frobenioid/PAdicSlim.lean` (`Iut.Frobenioid.PAdicGalois.isSlimGroup`).

Proof (local class field theory): let `m` commute with an open subgroup `U`, and `x ∈ Ω`. Choose
a finite Galois `M/K` containing `x` with `Gal(Ω/M) ⊆ U`. Then `m(M) = M`, and for `a ∈ M^×`,
naturality of the Artin map (`PadicField.artin_naturality`) and `m ρ = ρ m` for lifts
`ρ ∈ Gal(Ω/M)` of `artin_M(a)` give `artin_M(m a) = artin_M(a)`; the Artin map is injective
(`PadicField.artin_injective`), so `m a = a`. Hence `m` fixes `x`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale IntermediateField
  Pi1.Profinite

universe u

noncomputable section

namespace CurvesJacobian.LocAn

section Slim

variable (p : ℕ) [hp : Fact p.Prime] {K Ω : Type*} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
  [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω]

include hp in
/-- `m ∈ Gal(Ω/K)` fixes a finite Galois `M/K` pointwise if it commutes with `Gal(Ω/M)`. -/
theorem padic_fixes_of_commute [Algebra.IsAlgebraic K Ω] (M : IntermediateField K Ω)
    [FiniteDimensional K M] [Normal K M] (m : Ω ≃ₐ[K] Ω)
    (hm : ∀ v ∈ M.fixingSubgroup, m * v = v * m) (a : M) :
    m (a : Ω) = a := by
  haveI : FiniteDimensional ℚ_[p] M := Module.Finite.trans K M
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  haveI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  have hmM : ∀ y : Ω, y ∈ M → m y ∈ M := fun y hy ↦ by
    rw [show m y = ((m.restrictNormal M ⟨y, hy⟩ : M) : Ω) from
      (AlgEquiv.restrictNormal_commutes m M ⟨y, hy⟩).symm]
    exact SetLike.coe_mem _
  have hmM' : ∀ y : Ω, y ∈ M → m.symm y ∈ M := fun y hy ↦ by
    rw [show m.symm y = ((m.symm.restrictNormal M ⟨y, hy⟩ : M) : Ω) from
      (AlgEquiv.restrictNormal_commutes m.symm M ⟨y, hy⟩).symm]
    exact SetLike.coe_mem _
  -- `τ = m|_M : M ≃ M` over `ℚ_p`
  let τ : M ≃ₐ[ℚ_[p]] M :=
    { toFun := fun y ↦ ⟨m y, hmM y y.2⟩
      invFun := fun y ↦ ⟨m.symm y, hmM' y y.2⟩
      left_inv := fun y ↦ Subtype.ext (m.symm_apply_apply y)
      right_inv := fun y ↦ Subtype.ext (m.apply_symm_apply y)
      map_mul' := fun x y ↦ Subtype.ext (map_mul m (x : Ω) y)
      map_add' := fun x y ↦ Subtype.ext (map_add m (x : Ω) y)
      commutes' := fun c ↦ Subtype.ext (by
        change m (algebraMap ℚ_[p] Ω c) = algebraMap ℚ_[p] Ω c
        exact (m.restrictScalars ℚ_[p]).commutes c) }
  let σ : Ω ≃+* Ω := m.toRingEquiv
  have hσ : ∀ c : M, σ (algebraMap M Ω c) = algebraMap M Ω (τ c) := fun _ ↦ rfl
  by_cases ha : (a : Ω) = 0
  · rw [ha, map_zero]
  let u : Mˣ := Units.mk0 ⟨a, a.2⟩ (fun h ↦ ha (congrArg Subtype.val h))
  -- the Artin images of `u` and `τ u` agree
  have key : PadicField.artin p M Ω (Units.map (τ : M →* M) u) = PadicField.artin p M Ω u := by
    ext y
    obtain ⟨y₀, rfl⟩ := (PadicField.maxAbelianRingEquiv τ σ hσ).surjective y
    rw [PadicField.artin_naturality (p := p) τ σ hσ u y₀]
    -- lift `artin u` to `ρ ∈ Gal(Ω/M)`
    let ρ : Ω ≃ₐ[M] Ω := (PadicField.artin p M Ω u).liftNormal Ω
    have hρ : ∀ z : PadicField.maxAbelian M Ω, ρ (z : Ω) = (PadicField.artin p M Ω u z : Ω) :=
      fun z ↦ AlgEquiv.liftNormal_commutes _ Ω z
    let ρK : Ω ≃ₐ[K] Ω := ρ.restrictScalars K
    have hρK : ρK ∈ M.fixingSubgroup := fun z ↦ ρ.commutes (⟨(z : Ω), z.2⟩ : M)
    have h1 := congrArg (fun g : Ω ≃ₐ[K] Ω ↦ g (y₀ : Ω)) (hm ρK hρK)
    simp only [AlgEquiv.mul_apply] at h1
    change σ (PadicField.artin p M Ω u y₀ : Ω) =
      (PadicField.artin p M Ω u (PadicField.maxAbelianRingEquiv τ σ hσ y₀) : Ω)
    rw [← hρ, ← hρ, PadicField.coe_maxAbelianRingEquiv]
    exact h1
  have hu := PadicField.artin_injective (p := p) (Ω := Ω) key
  exact congrArg (fun w : Mˣ ↦ ((w : M) : Ω)) hu

include hp in
omit [IsAlgClosed Ω] in
/-- The slimness of `Gal(Ω/K)`, for `Ω` an algebraic closure of `K` with a compatible
`ℚ_p`-algebra structure. -/
theorem isSlim_galoisGroup_padic_of_isScalarTower [IsAlgClosure K Ω] :
    IsSlim (Ω ≃ₐ[K] Ω) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  intro U m hm
  obtain ⟨F, hF, hFn, hFU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K Ω U).mp
    (U.isOpen.mem_nhds U.one_mem)
  ext x
  -- a finite Galois `M ⊇ F(x)`
  let L0 : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  haveI : FiniteDimensional K L0 := IntermediateField.finiteDimensional_sup _ _
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L0 Ω
  haveI : FiniteDimensional K M := normalClosure.is_finiteDimensional K L0 Ω
  haveI : Normal K M := normalClosure.normal K L0 Ω
  have hL0 : L0 ≤ M := L0.le_normalClosure
  have hxM : x ∈ M := hL0 (le_sup_right (a := F) (mem_adjoin_simple_self K x))
  have hV : ∀ v ∈ M.fixingSubgroup, m * v = v * m := fun v hv ↦
    hm v (hFU (fixingSubgroup_antitone (le_sup_left.trans hL0) hv))
  exact padic_fixes_of_commute p M m hV ⟨x, hxM⟩

end Slim

/-- **The absolute Galois group of a `p`-adic field is slim** ([AbsTopI] Theorem 1.7 (ii)): for
a finite extension `K/ℚ_p` and an algebraic closure `Ω` of `K`, an element of `Gal(Ω/K)`
commuting with an open subgroup is trivial. -/
theorem isSlim_galoisGroup_padic (p : ℕ) [Fact p.Prime] (K Ω : Type*) [Field K]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    IsSlim (Ω ≃ₐ[K] Ω) := by
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp (algebraMap ℚ_[p] K)).toAlgebra
  haveI : IsScalarTower ℚ_[p] K Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact isSlim_galoisGroup_padic_of_isScalarTower p

section Gk

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [Algebra.IsAlgebraic K Ω]

omit [FiniteDimensional ℚ_[p] K] in
include p in
/-- A separably closed algebraic extension `Ω` of a `p`-adic field `K` is an algebraic closure
of `K` (`char K = 0`). -/
lemma isAlgClosure_padic : IsAlgClosure K Ω := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  exact ⟨inferInstance, inferInstance⟩

omit [FiniteDimensional ℚ_[p] K] in
include p in
/-- `Ω/K` is Galois. -/
lemma isGalois_padic : IsGalois K Ω := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI := isAlgClosure_padic p (K := K) Ω
  exact ⟨⟩

include p in
/-- **`G_K = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)` is slim** for a finite extension `K/ℚ_p`. -/
theorem isSlim_Gk_padic : IsSlim π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
  haveI := isAlgClosure_padic p (K := K) Ω
  haveI := isGalois_padic p (K := K) Ω
  let e : (Ω ≃ₐ[K] Ω) ≃ₜ* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    { mulEquivAutFiber K Ω with
      continuous_toFun := (isHomeomorph_mulEquivAutFiber K Ω).continuous
      continuous_invFun := (isHomeomorph_mulEquivAutFiber K Ω).homeomorph.symm.continuous }
  exact (isSlim_galoisGroup_padic p K Ω).of_continuousMulEquiv e

include p in
/-- **`G_K` has trivial centre** for a finite extension `K/ℚ_p` (the hypothesis `hcen` of
`CurvesJacobian.Cusp.isPathOverBase_of_isOverGk`). -/
theorem center_Gk_padic :
    Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) = ⊥ :=
  (isSlim_Gk_padic p (K := K) Ω).center_eq_bot

end Gk

end CurvesJacobian.LocAn
