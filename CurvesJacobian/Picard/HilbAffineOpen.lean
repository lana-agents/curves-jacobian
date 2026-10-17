/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbAffineData
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# The subfunctors `F_W` of the affine Hilbert functor are open and cover

This continues the affine case of the representability of the Hilbert scheme of points (Stacks,
Lemma 44.2.5, Tag 0B99), at the level of rings. For a ring `A`, the `A`-points of `Hilb^d` of
`𝔸^I` are the ideals `J ⊆ A[x_i]` such that `A[x_i]/J` is a finite projective `A`-module of
constant rank `d` (`IsHilbIdeal`); for the comparison with closed subschemes of `𝔸^I_A` finite
locally free of degree `d` over `Spec A` see the scheme-theoretic files.

* `tensorQuotEquiv`: base change, `A' ⊗_A A[x]/J ≃ A'[x]/J A'[x]`; hence `IsHilbIdeal.map`.
* `bijective_of_surjective_of_rankAtStalk`: a surjection `A^d → Q` onto a finite projective module
  of constant rank `d` is bijective.
* For monomials `w : Fin d → (I →₀ ℕ)` let `obstr w J` be the annihilator of the cokernel of
  `A^d → A[x]/J`, `e_l ↦ w_l`. **Openness** (`hasMonomialBasis_map_iff`): the extension of `J` to
  `A'[x]` has `w` as a basis iff `obstr w J` generates the unit ideal of `A'`, i.e. iff
  `Spec A' → Spec A` lands in the open `D(obstr w J)`.
* **Covering** (`iSup_obstr_eq_top`): the opens `D(obstr w J)` cover `Spec A` (at a prime `p`
  choose `d` monomials whose images form a basis of the `d`-dimensional `κ(p)`-vector space
  `κ(p) ⊗ A[x]/J`; Nakayama).
-/

open MvPolynomial TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.HilbAffine

variable {A : Type u} [CommRing A] {I : Type u} {d : ℕ}

section Rank

variable {Q : Type*} [AddCommGroup Q] [Module A Q]

lemma nontrivial_of_primeSpectrum (p : PrimeSpectrum A) : Nontrivial A := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact p.2.ne_top (Subsingleton.elim _ _)

/-- A surjection `A^d → Q` onto a finite projective module of constant rank `d` is bijective. -/
lemma bijective_of_surjective_of_rankAtStalk [Module.Finite A Q] [Module.Projective A Q]
    (hQ : ∀ p, Module.rankAtStalk (R := A) Q p = d) (f : (Fin d → A) →ₗ[A] Q)
    (hf : Function.Surjective f) : Function.Bijective f := by
  refine ⟨?_, hf⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ y, f (s y) = y := fun y ↦ LinearMap.congr_fun hs y
  let r : (Fin d → A) →ₗ[A] LinearMap.ker f :=
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ f) fun x ↦ by
      simp [LinearMap.mem_ker, hfs]
  have hr : ∀ k : LinearMap.ker f, r k = k := fun k ↦ by
    ext1
    simp [r, LinearMap.mem_ker.mp k.2]
  haveI : Module.Finite A (LinearMap.ker f) :=
    Module.Finite.of_surjective r fun k ↦ ⟨k, hr k⟩
  haveI : Module.Projective A (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext hr)
  let e : (Fin d → A) ≃ₗ[A] LinearMap.ker f × Q :=
    LinearEquiv.ofLinear (r.prod f) ((LinearMap.ker f).subtype.coprod s)
      (by
        refine LinearMap.ext fun y ↦ Prod.ext ?_ ?_
        · ext1
          simp [r, LinearMap.mem_ker.mp y.1.2, hfs]
        · simp [LinearMap.mem_ker.mp y.1.2, hfs])
      (LinearMap.ext fun x ↦ by simp [r])
  have hrank := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod] at hrank
  have h0 : Module.rankAtStalk (R := A) (LinearMap.ker f) = 0 := by
    funext p
    have h := congrFun hrank p
    haveI := nontrivial_of_primeSpectrum p
    have hd : Module.rankAtStalk (R := A) (Fin d → A) p = d := by
      rw [Module.rankAtStalk_eq_finrank_of_free]
      simp
    rw [Pi.add_apply, hQ p, hd] at h
    simp only [Pi.zero_apply]
    omega
  haveI := Module.rankAtStalk_eq_zero_iff_subsingleton.mp h0
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

end Rank

/-- The `A`-points of `Hilb^d` of `𝔸^I` (Stacks, Tag 0B99): ideals `J ⊆ A[x_i]` such that
`A[x_i]/J` is a finite projective `A`-module of constant rank `d`. -/
def IsHilbIdeal (d : ℕ) (J : Ideal (MvPolynomial I A)) : Prop :=
  Module.Finite A (MvPolynomial I A ⧸ J) ∧ Module.Projective A (MvPolynomial I A ⧸ J) ∧
    ∀ p, Module.rankAtStalk (R := A) (MvPolynomial I A ⧸ J) p = d

section Span

variable (w : Fin d → I →₀ ℕ) (J : Ideal (MvPolynomial I A))

/-- The submodule of `A[x]/J` spanned by the images of the monomials `w l`. -/
def wSpan : Submodule A (MvPolynomial I A ⧸ J) :=
  Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk J (monomial (w l) 1))

/-- The annihilator of the cokernel of `A^d → A[x]/J`, `e_l ↦ w_l`: the open subscheme
`D(obstr w J) ⊆ Spec A` is the locus where `w` is a basis (`hasMonomialBasis_map_iff`). -/
def obstr : Ideal A := Module.annihilator A ((MvPolynomial I A ⧸ J) ⧸ wSpan w J)

lemma wSpan_eq_top_iff : wSpan w J = ⊤ ↔ obstr w J = ⊤ := by
  rw [obstr, Module.annihilator_eq_top_iff, Submodule.Quotient.subsingleton_iff]

variable {w J}

lemma wSpan_eq_top_of_hasMonomialBasis (h : HasMonomialBasis w J) : wSpan w J = ⊤ := by
  obtain ⟨b, hb⟩ := h
  rw [wSpan, ← b.span_eq]
  congr 1
  ext x
  simp [hb]

lemma hasMonomialBasis_of_wSpan_eq_top (hJ : IsHilbIdeal d J) (h : wSpan w J = ⊤) :
    HasMonomialBasis w J := by
  obtain ⟨_, _, hrk⟩ := hJ
  let f := Fintype.linearCombination A fun l ↦ Ideal.Quotient.mk J (monomial (w l) 1)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact h
  have hb := bijective_of_surjective_of_rankAtStalk hrk f hf
  refine ⟨(Pi.basisFun A (Fin d)).map (LinearEquiv.ofBijective f hb), fun l ↦ ?_⟩
  simp [f, Fintype.linearCombination_apply_single]

lemma hasMonomialBasis_iff (hJ : IsHilbIdeal d J) : HasMonomialBasis w J ↔ obstr w J = ⊤ :=
  ⟨fun h ↦ (wSpan_eq_top_iff w J).mp (wSpan_eq_top_of_hasMonomialBasis h),
    fun h ↦ hasMonomialBasis_of_wSpan_eq_top hJ ((wSpan_eq_top_iff w J).mpr h)⟩

end Span

section BaseChange

variable (A' : Type u) [CommRing A'] [Algebra A A'] (J : Ideal (MvPolynomial I A))

/-- The extension `J A'[x_i]` of `J` along `A → A'`. -/
abbrev extIdeal : Ideal (MvPolynomial I A') := J.map (MvPolynomial.map (algebraMap A A'))

/-- The map `A[x]/J → A'[x]/J A'[x]`. -/
def quotMap : (MvPolynomial I A ⧸ J) →ₐ[A] (MvPolynomial I A' ⧸ extIdeal A' J) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId A A'))
    (Ideal.le_comap_map (f := MvPolynomial.map (algebraMap A A')))

lemma quotMap_mk (p : MvPolynomial I A) :
    quotMap A' J (Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A A') p) := rfl

lemma aeval_tmul_map (p : MvPolynomial I A) :
    aeval (fun i ↦ (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J (X i))
      (MvPolynomial.map (algebraMap A A') p) = (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J p := by
  rw [MvPolynomial.aeval_map_algebraMap]
  have : (aeval fun i ↦ (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J (X i)) =
      (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ A J) :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  rw [this]
  rfl

/-- The inverse of `tensorQuotEquiv`. -/
def quotToTensor : (MvPolynomial I A' ⧸ extIdeal A' J) →ₐ[A'] A' ⊗[A] (MvPolynomial I A ⧸ J) :=
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J (X i)) fun a ha ↦ by
    have hle : extIdeal A' J ≤
        RingHom.ker (aeval fun i ↦ (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J (X i)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, aeval_tmul_map,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]
    exact hle ha

/-- Base change for quotients of polynomial rings: `A' ⊗_A A[x]/J ≃ A'[x]/J A'[x]`. -/
def tensorQuotEquiv :
    A' ⊗[A] (MvPolynomial I A ⧸ J) ≃ₐ[A'] (MvPolynomial I A' ⧸ extIdeal A' J) :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId A' _) (quotMap A' J) fun _ _ ↦ Commute.all _ _)
    (quotToTensor A' J)
    (by
      apply Ideal.Quotient.algHom_ext
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp [quotToTensor, quotMap_mk])
    (by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext p
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one,
          one_mul, quotMap_mk, AlgHom.coe_id, id_eq]
        exact aeval_tmul_map A' J p)

lemma tensorQuotEquiv_tmul (x : MvPolynomial I A ⧸ J) :
    tensorQuotEquiv A' J ((1 : A') ⊗ₜ[A] x) = quotMap A' J x := by
  simp [tensorQuotEquiv]

lemma isBaseChange_quotMap :
    IsBaseChange A' ((quotMap A' J).toLinearMap) :=
  IsBaseChange.of_equiv (tensorQuotEquiv A' J).toLinearEquiv fun x ↦ tensorQuotEquiv_tmul A' J x

variable {A' J}

lemma IsHilbIdeal.map (hJ : IsHilbIdeal d J) : IsHilbIdeal d (extIdeal A' J) := by
  obtain ⟨_, _, hrk⟩ := hJ
  let e := (tensorQuotEquiv A' J).toLinearEquiv
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_isBaseChange (isBaseChange_quotMap A' J), hrk]

end BaseChange

section Open

variable {w : Fin d → I →₀ ℕ} {J : Ideal (MvPolynomial I A)}

lemma subsingleton_tensor_right {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : Subsingleton (M ⊗[R] N) := by
  have h : ∀ z : M ⊗[R] N, z = 0 := fun z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ by rw [h x, h y]⟩

/-- If the elements `1 ⊗ q_l` span `B ⊗ Q` over `B`, then `B ⊗ (Q / span q) = 0`. -/
lemma subsingleton_tensor_quotient {B Q : Type*} [CommRing B] [Algebra A B] [AddCommGroup Q]
    [Module A Q] {ι : Type*} (q : ι → Q)
    (h : Submodule.span B (Set.range fun l ↦ (1 : B) ⊗ₜ[A] q l) = ⊤) :
    Subsingleton (B ⊗[A] (Q ⧸ Submodule.span A (Set.range q))) := by
  let π := (Submodule.span A (Set.range q)).mkQ.baseChange B
  have hle : Submodule.span B (Set.range fun l ↦ (1 : B) ⊗ₜ[A] q l) ≤ LinearMap.ker π := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (Set.mem_range_self l)),
      tmul_zero]
  rw [h, top_le_iff, LinearMap.ker_eq_top] at hle
  have hsurj : Function.Surjective π := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective B (Submodule.mkQ_surjective _)
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj x
  obtain ⟨y, rfl⟩ := hsurj y
  rw [hle]
  rfl

/-- If `κ(q) ⊗_A M = 0` for a prime `q` of an `A`-algebra `A'`, then `κ(p) ⊗_A M = 0` for the
prime `p` of `A` below `q` (`κ(p) → κ(q)` is faithfully flat). -/
lemma subsingleton_residueField_comap (A' : Type u) [CommRing A'] [Algebra A A'] {M : Type*}
    [AddCommGroup M] [Module A M] (q : Ideal A') [q.IsPrime]
    (h : Subsingleton (q.ResidueField ⊗[A] M)) :
    Subsingleton ((q.comap (algebraMap A A')).ResidueField ⊗[A] M) := by
  let φ := Ideal.ResidueField.mapₐ (q.comap (algebraMap A A')) q (Algebra.ofId A A') rfl
  letI : Algebra (q.comap (algebraMap A A')).ResidueField q.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A (q.comap (algebraMap A A')).ResidueField q.ResidueField :=
    IsScalarTower.of_algHom φ
  by_contra hn
  rw [not_subsingleton_iff_nontrivial] at hn
  haveI := Module.FaithfullyFlat.lTensor_nontrivial (q.comap (algebraMap A A')).ResidueField
    q.ResidueField ((q.comap (algebraMap A A')).ResidueField ⊗[A] M)
  exact not_subsingleton _ ((AlgebraTensorModule.cancelBaseChange A
    (q.comap (algebraMap A A')).ResidueField q.ResidueField q.ResidueField M).toEquiv.subsingleton)

variable (A' : Type u) [CommRing A'] [Algebra A A']

lemma smul_mem_wSpan {a : A} (ha : a ∈ obstr w J) (x : MvPolynomial I A ⧸ J) :
    a • x ∈ wSpan w J := by
  have := (Module.mem_annihilator.mp ha) (Submodule.mkQ _ x)
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

lemma map_wSpan_le : (wSpan w J).map (quotMap A' J).toLinearMap ≤
    (wSpan w (extIdeal A' J)).restrictScalars A := by
  rw [wSpan, Submodule.map_span_le]
  rintro _ ⟨l, rfl⟩
  exact Submodule.subset_span ⟨l, by simp [quotMap_mk]⟩

lemma obstr_map_le : (obstr w J).map (algebraMap A A') ≤ obstr w (extIdeal A' J) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, obstr, Module.mem_annihilator]
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have h3 := map_wSpan_le A' (Submodule.mem_map_of_mem
      (smul_mem_wSpan ha (Ideal.Quotient.mk J (monomial m 1))))
    have e : algebraMap A A' a • Ideal.Quotient.mk (extIdeal A' J) (monomial m c) =
        c • (quotMap A' J).toLinearMap (a • Ideal.Quotient.mk J (monomial m 1)) := by
      rw [LinearMap.map_smul, AlgHom.toLinearMap_apply, quotMap_mk, MvPolynomial.map_monomial,
        map_one]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap,
        ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_mul,
        ← map_mul]
      congr 1
      simp only [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, C_mul_monomial]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ c h3
  | add p q hp hq =>
    rw [map_add, smul_add]
    exact add_mem hp hq

/-- **`F_W` is open in `Hilb^d`** (affine case of Stacks, Tag 0B99): for `J ∈ Hilb^d(A)` and an
`A`-algebra `A'`, the monomials `w` form a basis of `A'[x]/J A'[x]` iff `Spec A' → Spec A` lands
in the open `D(obstr w J)`. -/
theorem hasMonomialBasis_map_iff (hJ : IsHilbIdeal d J) :
    HasMonomialBasis w (extIdeal A' J) ↔ (obstr w J).map (algebraMap A A') = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hJ.1
    let p : PrimeSpectrum A := ⟨q.comap (algebraMap A A'), inferInstance⟩
    have hp : p ∈ Module.support A ((MvPolynomial I A ⧸ J) ⧸ wSpan w J) := by
      rw [Module.mem_support_iff_of_finite]
      exact Ideal.map_le_iff_le_comap.mp hle
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
    let e := (tensorQuotEquiv A' J).toLinearEquiv
    let v : Fin d → A' ⊗[A] (MvPolynomial I A ⧸ J) :=
      fun l ↦ (1 : A') ⊗ₜ[A] Ideal.Quotient.mk J (monomial (w l) 1)
    have h1 : (Submodule.span A' (Set.range v)).map e.toLinearMap = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp, ← wSpan_eq_top_of_hasMonomialBasis h, wSpan]
      congr 1
      ext x
      simp [v, e, tensorQuotEquiv_tmul, quotMap_mk]
    have hspan : Submodule.span A' (Set.range v) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := (h1.ge (Submodule.mem_top (x := e x)))
      rwa [e.injective hyx] at hy
    haveI : Subsingleton (A' ⊗[A] ((MvPolynomial I A ⧸ J) ⧸ wSpan w J)) :=
      subsingleton_tensor_quotient (B := A') _ hspan
    haveI := subsingleton_tensor_right (M := q.ResidueField) (R := A')
      (N := A' ⊗[A] ((MvPolynomial I A ⧸ J) ⧸ wSpan w J))
    haveI : Subsingleton (q.ResidueField ⊗[A] ((MvPolynomial I A ⧸ J) ⧸ wSpan w J)) :=
      (AlgebraTensorModule.cancelBaseChange A A' q.ResidueField q.ResidueField
        ((MvPolynomial I A ⧸ J) ⧸ wSpan w J)).toEquiv.symm.subsingleton
    exact not_subsingleton _ (subsingleton_residueField_comap A' q this)
  · intro h
    apply hasMonomialBasis_of_wSpan_eq_top hJ.map
    rw [wSpan_eq_top_iff, eq_top_iff, ← h]
    exact obstr_map_le A'

variable {A'}

/-- At every prime `p` of `A`, some `d` monomials form a basis of `A[x]/J` near `p`. -/
theorem exists_not_obstr_le (hJ : IsHilbIdeal d J) (p : PrimeSpectrum A) :
    ∃ w : Fin d → I →₀ ℕ, ¬ obstr w J ≤ p.asIdeal := by
  obtain ⟨hfin, hproj, hrk⟩ := hJ
  let K := p.asIdeal.ResidueField
  let v : (I →₀ ℕ) → K ⊗[A] (MvPolynomial I A ⧸ J) :=
    fun m ↦ (1 : K) ⊗ₜ[A] Ideal.Quotient.mk J (monomial m 1)
  have h1 : ∀ x : MvPolynomial I A ⧸ J, (1 : K) ⊗ₜ[A] x ∈ Submodule.span K (Set.range v) := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using MvPolynomial.induction_on' with
    | monomial m c =>
      have : Ideal.Quotient.mk J (monomial m c) = c • Ideal.Quotient.mk J (monomial m 1) := by
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
          MvPolynomial.algebraMap_eq, C_mul_monomial, mul_one]
      rw [this, tmul_smul]
      exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨m, rfl⟩)
    | add p q hp hq =>
      rw [map_add, tmul_add]
      exact add_mem hp hq
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[A] x = k • ((1 : K) ⊗ₜ[A] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ k (h1 x)
    | add x y hx hy => exact add_mem hx hy
  obtain ⟨κ, a, -, hspan', hli⟩ := exists_linearIndependent' K v
  rw [hspan] at hspan'
  let b := Module.Basis.mk hli hspan'.ge
  haveI : Module.Finite K (K ⊗[A] (MvPolynomial I A ⧸ J)) := Module.Finite.base_change A K _
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by
    have := Module.rankAtStalk_eq (R := A) (M := MvPolynomial I A ⧸ J) p
    rw [hrk p] at this
    rw [← Module.finrank_eq_card_basis b, this]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, fun hle ↦ ?_⟩
  have hp : p ∈ Module.support A ((MvPolynomial I A ⧸ J) ⧸ wSpan (a ∘ e.symm) J) :=
    Module.mem_support_iff_of_finite.mpr hle
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have hspan'' : Submodule.span K (Set.range fun l ↦
      (1 : K) ⊗ₜ[A] Ideal.Quotient.mk J (monomial ((a ∘ e.symm) l) 1)) = ⊤ := by
    rw [← hspan']
    congr 1
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨e.symm l, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, by simp [v]⟩
  exact @not_subsingleton _ hp (subsingleton_tensor_quotient (B := K) _ hspan'' :
    Subsingleton (K ⊗[A] ((MvPolynomial I A ⧸ J) ⧸ wSpan (a ∘ e.symm) J)))

/-- **The `F_W` cover `Hilb^d`** (affine case of Stacks, Tag 0B99): the opens `D(obstr w J)`
cover `Spec A`. -/
theorem iSup_obstr_eq_top (hJ : IsHilbIdeal d J) : ⨆ w : Fin d → I →₀ ℕ, obstr w J = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨w, hw⟩ := exists_not_obstr_le hJ ⟨m, hm.isPrime⟩
  exact hw ((le_iSup (fun w ↦ obstr w J) w).trans hle)

end Open

end CurvesJacobian.HilbAffine
