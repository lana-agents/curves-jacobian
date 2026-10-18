/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Belyi.Converse.PathConnected

/-!
# Tensor products with an extension in which the base field is algebraically closed

Let `K ⊆ L` be fields of characteristic zero such that `K` is algebraically closed in `L`, i.e.
every element of `L` algebraic over `K` lies in `K`. Then:

* `CurvesJacobian.isDomain_tensorProduct_of_isAlgClosedIn`: `F ⊗[K] L` is a domain for every
  field extension `F / K`;
* `CurvesJacobian.isDomain_tensorProduct_of_injective`: more generally `F ⊗[K] A` is a domain
  for every `K`-algebra `A` admitting an injective `K`-algebra map `A → L` (e.g. a domain with
  fraction field `L`).

## Proof

1. (`irreducible_map_of_isAlgClosedIn`) An irreducible monic `f ∈ K[X]` stays irreducible in
   `L[X]`: the coefficients of a monic factor `g ∈ L[X]` of `f` are integral over `K`
   (Mathlib's `Polynomial.isIntegral_coeff_of_dvd`, Stacks Tag 00H6 (1)), hence lie in `K`,
   so `g` comes from a monic factor of `f` in `K[X]`.
2. (`isDomain_tensorProduct_of_finiteDimensional`) For `E / K` finite, write `E = K(α)`
   (primitive element theorem, characteristic zero) and embed `E` into `Ω = L̄`. The map
   `L ⊗[K] E → Ω` is `L`-linear, its image contains `L(α)` of `L`-dimension
   `deg (minpoly L α) = deg (minpoly K α) = [E : K] = dim_L (L ⊗[K] E)` by step 1, so it is
   injective and `E ⊗[K] L` is a domain.
3. (`isDomain_tensorProduct_of_isAlgebraic`) For `R / K` algebraic, every element of
   `R ⊗[K] L` comes from `E ⊗[K] L` for a finite subextension `E`, and these maps are
   injective (flatness over a field); hence `R ⊗[K] L` is a domain.
4. For general `F`, let `Ω = F̄` and `K̄ ⊆ Ω` the algebraic closure of `K` in `Ω`. Then
   `F ⊗[K] L ↪ Ω ⊗[K] L ≅ Ω ⊗[K̄] (K̄ ⊗[K] L)`; here `K̄ ⊗[K] L` is a domain by step 3, and
   `Ω ⊗[K̄] D` is a domain for every domain `D` over the algebraically closed field `K̄`
   (reduce as in step 3 to finitely generated `K̄`-subalgebras of `Ω` and apply
   `Belyi.Converse.isDomain_tensorProduct_of_isAlgClosed`).
-/

open scoped TensorProduct
open Polynomial

namespace CurvesJacobian

section Generic

variable {k : Type*} [Field k]

/-- Over a field, the tensor product of injective algebra maps is injective. -/
lemma tensorProduct_map_injective {R R' B B' : Type*} [CommRing R] [Algebra k R] [CommRing R']
    [Algebra k R'] [CommRing B] [Algebra k B] [CommRing B'] [Algebra k B']
    (f : R →ₐ[k] R') (g : B →ₐ[k] B') (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (Algebra.TensorProduct.map f g) :=
  TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

variable {R B : Type*} [CommRing R] [Algebra k R] [CommRing B] [Algebra k B]

/-- Every element of `R ⊗[k] B` comes from `A ⊗[k] B` for every subalgebra `A ⊆ R` containing
a suitable finite set. -/
lemma exists_finset_forall_mem_range_tensor (x : R ⊗[k] B) :
    ∃ s : Finset R, ∀ A : Subalgebra k R, (s : Set R) ⊆ A →
      x ∈ Set.range (Algebra.TensorProduct.map A.val (AlgHom.id k B)) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun A _ ↦ ⟨0, map_zero _⟩⟩
  | tmul r b => exact ⟨{r}, fun A hA ↦ ⟨⟨r, hA (by simp)⟩ ⊗ₜ b, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun A hA ↦ ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at hA
    obtain ⟨x', hx'⟩ := hs A hA.1
    obtain ⟨y', hy'⟩ := ht A hA.2
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

/-- `R ⊗[k] B` is a domain as soon as every finite subset of `R` lies in a subalgebra `A`
with `A ⊗[k] B` a domain. -/
theorem isDomain_tensorProduct_of_forall_finset [Nontrivial (R ⊗[k] B)]
    (h : ∀ s : Finset R, ∃ A : Subalgebra k R, (s : Set R) ⊆ A ∧ IsDomain (A ⊗[k] B)) :
    IsDomain (R ⊗[k] B) := by
  classical
  suffices NoZeroDivisors (R ⊗[k] B) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy ↦ ?_⟩
  obtain ⟨s, hs⟩ := exists_finset_forall_mem_range_tensor (B := B) x
  obtain ⟨t, ht⟩ := exists_finset_forall_mem_range_tensor (B := B) y
  obtain ⟨A, hA, hdom⟩ := h (s ∪ t)
  rw [Finset.coe_union, Set.union_subset_iff] at hA
  obtain ⟨x', rfl⟩ := hs A hA.1
  obtain ⟨y', rfl⟩ := ht A hA.2
  have hinj := tensorProduct_map_injective A.val (AlgHom.id k B) Subtype.val_injective
    Function.injective_id
  rw [← map_mul, ← map_zero (Algebra.TensorProduct.map A.val (AlgHom.id k B))] at hxy
  rcases mul_eq_zero.mp (hinj hxy) with h | h
  · exact .inl (by rw [h, map_zero])
  · exact .inr (by rw [h, map_zero])

end Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `K` is algebraically closed in `L`, an irreducible monic polynomial over `K` stays
irreducible over `L`. -/
theorem irreducible_map_of_isAlgClosedIn
    (hK : ∀ x : L, IsAlgebraic K x → x ∈ (algebraMap K L).range)
    {f : K[X]} (hf : Irreducible f) (hm : f.Monic) :
    Irreducible (f.map (algebraMap K L)) := by
  have hmL : (f.map (algebraMap K L)).Monic := hm.map _
  rw [hmL.irreducible_iff_natDegree]
  refine ⟨fun h1 ↦ hf.not_isUnit ?_, fun g h hg hh hgh ↦ ?_⟩
  · have : f = 1 := by
      apply Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective
      rw [h1, Polynomial.map_one]
    rw [this]
    exact isUnit_one
  · have hgl : g ∈ Polynomial.lifts (algebraMap K L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact hK _ (Polynomial.isIntegral_coeff_of_dvd f g hm hg ⟨h, hgh.symm⟩ n).isAlgebraic
    obtain ⟨g0, hg0, -, hg0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hgl hg
    have hdvd : g0 ∣ f := by
      rw [← Polynomial.map_dvd_map (algebraMap K L) (algebraMap K L).injective hg0m, hg0]
      exact ⟨h, hgh.symm⟩
    obtain ⟨h0, rfl⟩ := hdvd
    rcases hf.isUnit_or_isUnit rfl with hu | hu
    · left
      rw [← hg0, Polynomial.natDegree_map]
      exact Polynomial.natDegree_eq_zero_of_isUnit hu
    · right
      have h01 : h0 = 1 := (hg0m.of_mul_monic_left hm).isUnit_iff.mp hu
      subst h01
      have := hg.natDegree_mul hh
      rw [hgh, mul_one, hg0] at this
      omega

/-- If `K` (of characteristic zero) is algebraically closed in `L`, then `E ⊗[K] L` is a domain
for every finite extension `E / K`. -/
theorem isDomain_tensorProduct_of_finiteDimensional [CharZero K]
    (hK : ∀ x : L, IsAlgebraic K x → x ∈ (algebraMap K L).range)
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E] :
    IsDomain (E ⊗[K] L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  let ι : E →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  let φ : L ⊗[K] E →ₐ[L] AlgebraicClosure L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι fun _ _ ↦ .all _ _
  have hαint : IsIntegral K α := .of_finite K α
  have hmin : minpoly L (ι α) = (minpoly K α).map (algebraMap K L) := by
    refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ((minpoly.monic hαint).map _)).symm
    · exact irreducible_map_of_isAlgClosedIn hK (minpoly.irreducible hαint)
        (minpoly.monic hαint)
    · rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval,
        map_zero]
  have hfinE : Module.finrank K E = (minpoly K α).natDegree := by
    rw [← IntermediateField.adjoin.finrank hαint, hα, IntermediateField.finrank_top']
  have hθint : IsIntegral L (ι α) := (hαint.map ι).tower_top
  have hfinA : Module.finrank L (IntermediateField.adjoin L {ι α}) =
      (minpoly K α).natDegree := by
    rw [IntermediateField.adjoin.finrank hθint, hmin, Polynomial.natDegree_map]
  have hle : (IntermediateField.adjoin L {ι α}).toSubalgebra ≤ φ.range := by
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨1 ⊗ₜ α, by simp [φ]⟩
  have hinj : Function.Injective φ := by
    have hrank := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    have h1 : Module.finrank L (L ⊗[K] E) = (minpoly K α).natDegree := by
      rw [Module.finrank_baseChange, hfinE]
    have h2 : (minpoly K α).natDegree ≤
        Module.finrank L (LinearMap.range φ.toLinearMap) := by
      rw [← hfinA]
      exact Submodule.finrank_mono (R := L)
        (s := Subalgebra.toSubmodule (IntermediateField.adjoin L {ι α}).toSubalgebra)
        (t := LinearMap.range φ.toLinearMap) (fun x hx ↦ hle hx)
    have h3 := LinearMap.finrank_range_le φ.toLinearMap
    have h4 : Module.finrank L (LinearMap.ker φ.toLinearMap) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp h4)
  haveI : IsDomain (L ⊗[K] E) := hinj.isDomain φ
  exact (Algebra.TensorProduct.comm K E L).toMulEquiv.isDomain

/-- If `K` (of characteristic zero) is algebraically closed in `L`, then `R ⊗[K] L` is a domain
for every algebraic field extension `R / K`. -/
theorem isDomain_tensorProduct_of_isAlgebraic [CharZero K]
    (hK : ∀ x : L, IsAlgebraic K x → x ∈ (algebraMap K L).range)
    (R : Type*) [Field R] [Algebra K R] [Algebra.IsAlgebraic K R] :
    IsDomain (R ⊗[K] L) := by
  haveI : Nontrivial (R ⊗[K] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K R L
      (algebraMap K R).injective (algebraMap K L).injective
  refine isDomain_tensorProduct_of_forall_finset fun s ↦ ?_
  let E := IntermediateField.adjoin K (s : Set R)
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  exact ⟨E.toSubalgebra, IntermediateField.subset_adjoin _ _,
    isDomain_tensorProduct_of_finiteDimensional hK E⟩

/-- **Base change of an extension in which the base field is algebraically closed.** If `K` is a
field of characteristic zero which is algebraically closed in the field `L`, then `F ⊗[K] L` is
a domain for every field extension `F / K`. -/
theorem isDomain_tensorProduct_of_isAlgClosedIn [CharZero K]
    (hK : ∀ x : L, IsAlgebraic K x → x ∈ (algebraMap K L).range)
    (F : Type*) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] L) := by
  let Ω := AlgebraicClosure F
  let Kb := algebraicClosure K Ω
  haveI : IsAlgClosed Kb := IsAlgClosure.isAlgClosed K
  haveI : IsDomain (Kb ⊗[K] L) := isDomain_tensorProduct_of_isAlgebraic hK Kb
  haveI : IsDomain (Ω ⊗[Kb] (Kb ⊗[K] L)) := by
    haveI : Nontrivial (Ω ⊗[Kb] (Kb ⊗[K] L)) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain Kb Ω _
        (algebraMap Kb Ω).injective (algebraMap Kb (Kb ⊗[K] L)).injective
    refine isDomain_tensorProduct_of_forall_finset fun s ↦
      ⟨Algebra.adjoin Kb (s : Set Ω), Algebra.subset_adjoin, ?_⟩
    haveI : Algebra.FiniteType Kb (Algebra.adjoin Kb (s : Set Ω)) :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
    exact Belyi.Converse.isDomain_tensorProduct_of_isAlgClosed
  haveI : IsDomain (Ω ⊗[K] L) :=
    (Algebra.TensorProduct.cancelBaseChange K Kb Kb Ω L).symm.toMulEquiv.isDomain
  exact (tensorProduct_map_injective (IsScalarTower.toAlgHom K F Ω) (AlgHom.id K L)
    (algebraMap F Ω).injective Function.injective_id).isDomain _

/-- **Corollary.** If `K` (of characteristic zero) is algebraically closed in the field `L` and
`A` is a `K`-algebra with an injective `K`-algebra map `A → L` (e.g. a domain with fraction
field `L`), then `F ⊗[K] A` is a domain for every field extension `F / K`. -/
theorem isDomain_tensorProduct_of_injective [CharZero K]
    (hK : ∀ x : L, IsAlgebraic K x → x ∈ (algebraMap K L).range)
    (F : Type*) [Field F] [Algebra K F] {A : Type*} [CommRing A] [Algebra K A]
    (g : A →ₐ[K] L) (hg : Function.Injective g) :
    IsDomain (F ⊗[K] A) := by
  haveI := isDomain_tensorProduct_of_isAlgClosedIn hK F
  exact (tensorProduct_map_injective (AlgHom.id K F) g Function.injective_id hg).isDomain _

end CurvesJacobian
