/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbAffineOpen
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The rings representing `F_W` for a presented affine scheme over a base ring

For a base ring `R`, an ideal `K ⊆ R[x_i]` (so `X = Spec R[x_i]/K`) and monomials `w`, the
subfunctor `F_W ⊆ Hilb^d_{X/R}` (Stacks, Lemma 44.2.5, Tag 0B99) is represented by
`Spec (univRingK K w)`, where `univRingK K w` is the quotient of `R ⊗ univRing I d w` by the entries
of `k(X) v` for `k ∈ K`. This is the closed condition `K A[x] ⊆ J` inside `F_W` used in Stacks,
Lemma 44.2.3 (Tag 0B97), for the closed immersion `X ⊆ 𝔸^I_R`.

* `univRingKHomEquiv φ`: ring maps `univRingK K w → A` restricting to `φ : R → A` are the matrix
  data `M` over `A` (`MatData`) with `k(M.X) M.v = 0` for `k ∈ K`, i.e. with `K A[x] ⊆ J_M`
  (`map_le_kerIdeal_iff`); natural in `A` (`univRingKHomEquiv_comp`).
* `isHilbIdeal_of_hasMonomialBasis`: points of `F_W` are points of `Hilb^d`.
-/

open MvPolynomial TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.HilbAffine

variable {I : Type u} {d : ℕ}

lemma isHilbIdeal_of_hasMonomialBasis {A : Type u} [CommRing A] {w : Fin d → I →₀ ℕ}
    {J : Ideal (MvPolynomial I A)} (h : HasMonomialBasis w J) : IsHilbIdeal d J := by
  obtain ⟨b, -⟩ := h
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  refine ⟨inferInstance, inferInstance, fun p ↦ ?_⟩
  haveI := nontrivial_of_primeSpectrum p
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rfl

section Univ

variable {R : Type u} [CommRing R] (K : Ideal (MvPolynomial I R)) (w : Fin d → I →₀ ℕ)

variable (R I d) in
/-- The generic matrices over `R`. -/
def genMatR (i : I) : Matrix (Fin d) (Fin d) (MvPolynomial (UnivVar I d) R) :=
  fun a b ↦ MvPolynomial.X (Sum.inl (i, a, b))

variable (R I d) in
/-- The generic vector over `R`. -/
def genVecR : Fin d → MvPolynomial (UnivVar I d) R := fun a ↦ MvPolynomial.X (Sum.inr ⟨a⟩)

variable (R I d) in
/-- The entries of the commutators of the generic matrices over `R`. -/
def commIdealR : Ideal (MvPolynomial (UnivVar I d) R) :=
  Ideal.span {x | ∃ i j a b,
    x = (genMatR I d R i * genMatR I d R j - genMatR I d R j * genMatR I d R i) a b}

variable (R I d) in
/-- Pairwise commuting generic matrices and a generic vector over `R`. -/
abbrev CommRingR₀ : Type u := MvPolynomial (UnivVar I d) R ⧸ commIdealR I d R

variable (R I d) in
/-- The generic matrices over `CommRingR₀`. -/
def genMatR₀ (i : I) : Matrix (Fin d) (Fin d) (CommRingR₀ I d R) :=
  (genMatR I d R i).map (Ideal.Quotient.mk _)

lemma genMatR₀_comm (i j : I) :
    genMatR₀ I d R i * genMatR₀ I d R j = genMatR₀ I d R j * genMatR₀ I d R i := by
  rw [genMatR₀, genMatR₀, ← Matrix.map_mul, ← Matrix.map_mul, ← sub_eq_zero,
    ← Matrix.map_sub _ (map_sub _)]
  ext a b
  rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, j, a, b, rfl⟩

variable (R I d) in
/-- The generic vector over `CommRingR₀`. -/
def genVecR₀ : Fin d → CommRingR₀ I d R := fun a ↦ Ideal.Quotient.mk _ (genVecR I d R a)

/-- The relations `w_l(X) v = e_l` and `k(X) v = 0` for `k ∈ K`. -/
def relIdealR : Ideal (CommRingR₀ I d R) :=
  Ideal.span ({x | ∃ l a, x = evalVec (genMatR₀ I d R) genMatR₀_comm (genVecR₀ I d R)
      (monomial (w l) 1) a - (Pi.single l 1 : Fin d → CommRingR₀ I d R) a} ∪
    {x | ∃ k ∈ K, ∃ a, x = evalVec (genMatR₀ I d R) genMatR₀_comm (genVecR₀ I d R)
      (MvPolynomial.map (algebraMap R (CommRingR₀ I d R)) k) a})

/-- The ring representing `F_W` for `X = Spec R[x_i]/K` over `Spec R`. -/
abbrev univRingK : Type u := CommRingR₀ I d R ⧸ relIdealR K w

variable {A : Type u} [CommRing A]

/-- The closed condition `K A[x] ⊆ J_M` on matrix data, for `φ : R → A`. -/
def KCond (φ : R →+* A) (M : MatData A w) : Prop :=
  ∀ k ∈ K, evalVec M.X M.comm M.v (MvPolynomial.map φ k) = 0

lemma map_le_kerIdeal_iff (φ : R →+* A) (M : MatData A w) :
    K.map (MvPolynomial.map φ) ≤ kerIdeal M.X M.comm M.v ↔ KCond K w φ M := by
  rw [Ideal.map_le_iff_le_comap]
  exact ⟨fun h k hk ↦ h hk, fun h k hk ↦ h k hk⟩

lemma evalVec_genR₀_map (f₀ : CommRingR₀ I d R →+* A) (p : MvPolynomial I (CommRingR₀ I d R)) :
    evalVec (fun i ↦ (genMatR₀ I d R i).map f₀) (map_comm f₀ _ genMatR₀_comm)
      (f₀ ∘ genVecR₀ I d R) (MvPolynomial.map f₀ p) =
      f₀ ∘ evalVec (genMatR₀ I d R) genMatR₀_comm (genVecR₀ I d R) p := by
  funext a
  rw [evalVec_apply, Function.comp_apply, evalVec_apply, RingHom.map_mulVec,
    ← evalMat_map f₀ _ genMatR₀_comm]

/-- Ring maps out of `CommRingR₀` give commuting matrices and a vector; `relIdealR` is in the
kernel iff these are matrix data satisfying `K`. -/
lemma relIdealR_le_ker_iff (f₀ : CommRingR₀ I d R →+* A) :
    relIdealR K w ≤ RingHom.ker f₀ ↔
      (∀ l, (evalMat (fun i ↦ (genMatR₀ I d R i).map f₀) (map_comm f₀ _ genMatR₀_comm)
        (monomial (w l) 1)).mulVec (f₀ ∘ genVecR₀ I d R) = Pi.single l 1) ∧
      ∀ k ∈ K, evalVec (fun i ↦ (genMatR₀ I d R i).map f₀) (map_comm f₀ _ genMatR₀_comm)
        (f₀ ∘ genVecR₀ I d R) (MvPolynomial.map (f₀.comp (algebraMap R _)) k) = 0 := by
  have hmon : ∀ l, (evalMat (fun i ↦ (genMatR₀ I d R i).map f₀) (map_comm f₀ _ genMatR₀_comm)
      (monomial (w l) 1)).mulVec (f₀ ∘ genVecR₀ I d R) = f₀ ∘ evalVec (genMatR₀ I d R)
        genMatR₀_comm (genVecR₀ I d R) (monomial (w l) 1) := fun l ↦ by
    rw [← evalVec_genR₀_map, MvPolynomial.map_monomial, map_one f₀]
    rfl
  have hK : ∀ k : MvPolynomial I R, evalVec (fun i ↦ (genMatR₀ I d R i).map f₀)
      (map_comm f₀ _ genMatR₀_comm) (f₀ ∘ genVecR₀ I d R)
        (MvPolynomial.map (f₀.comp (algebraMap R _)) k) = f₀ ∘ evalVec (genMatR₀ I d R)
          genMatR₀_comm (genVecR₀ I d R) (MvPolynomial.map (algebraMap R _) k) := fun k ↦ by
    rw [← evalVec_genR₀_map, MvPolynomial.map_map]
  rw [relIdealR, Ideal.span_le, Set.union_subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l ↦ funext fun a ↦ ?_, fun k hk ↦ funext fun a ↦ ?_⟩
    · have := h1 ⟨l, a, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero] at this
      rw [hmon, Function.comp_apply, this, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    · have := h2 ⟨k, hk, a, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker] at this
      rw [hK, Function.comp_apply, this, Pi.zero_apply]
  · rintro ⟨h1, h2⟩
    constructor
    · rintro _ ⟨l, a, rfl⟩
      have := congrFun (h1 l) a
      rw [hmon, Function.comp_apply] at this
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, this, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    · rintro _ ⟨k, hk, a, rfl⟩
      have := congrFun (h2 k hk) a
      rw [hK, Function.comp_apply] at this
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact this

/-- The matrix data of a ring map out of `univRingK K w`. -/
def matOfHom (f : univRingK K w →+* A) : MatData A w where
  X i := (genMatR₀ I d R i).map (f.comp (Ideal.Quotient.mk _))
  v := f.comp (Ideal.Quotient.mk _) ∘ genVecR₀ I d R
  comm := map_comm _ _ genMatR₀_comm
  eval_eq := ((relIdealR_le_ker_iff K w _).mp fun x hx ↦ by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      map_zero]).1

lemma kCond_matOfHom (f : univRingK K w →+* A) :
    KCond K w (f.comp (algebraMap R _)) (matOfHom K w f) :=
  ((relIdealR_le_ker_iff K w _).mp fun x hx ↦ by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      map_zero]).2

/-- **`F_W` of `Spec R[x]/K` is represented by `Spec (univRingK K w)`** (Stacks, Tags 0B99 and
0B97, matrix description): ring maps `univRingK K w → A` restricting to `φ` on `R` are the
matrix data over `A` satisfying the relations `K`. -/
def univRingKHomEquiv (φ : R →+* A) :
    {f : univRingK K w →+* A // f.comp (algebraMap R _) = φ} ≃
      {M : MatData A w // KCond K w φ M} where
  toFun f := ⟨matOfHom K w f.1, by
    obtain ⟨f, rfl⟩ := f
    exact kCond_matOfHom K w f⟩
  invFun M :=
    let ψ : MvPolynomial (UnivVar I d) R →+* A :=
      eval₂Hom φ (Sum.elim (fun t ↦ M.1.X t.1 t.2.1 t.2.2) (fun a ↦ M.1.v a.down))
    have hc : commIdealR I d R ≤ RingHom.ker ψ := by
      have hψ : ∀ i, (genMatR I d R i).map ψ = M.1.X i := fun i ↦ by
        ext a b; simp [genMatR, ψ]
      rw [commIdealR, Ideal.span_le]
      rintro _ ⟨i, j, a, b, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, ← Matrix.map_apply (f := ψ),
        Matrix.map_sub _ (map_sub ψ), Matrix.map_mul, Matrix.map_mul, hψ, hψ, M.1.comm, sub_self,
        Matrix.zero_apply]
    let ψ₀ : CommRingR₀ I d R →+* A := Ideal.Quotient.lift _ ψ hc
    have hX : (fun i ↦ (genMatR₀ I d R i).map ψ₀) = M.1.X := funext fun i ↦ by
      ext a b; simp [genMatR₀, genMatR, ψ₀, ψ]
    have hv : ψ₀ ∘ genVecR₀ I d R = M.1.v := funext fun a ↦ by
      simp [genVecR₀, genVecR, ψ₀, ψ]
    have hφ : ψ₀.comp (algebraMap R _) = φ := RingHom.ext fun r ↦ by
      change ψ (C r) = φ r
      simp [ψ]
    have he : relIdealR K w ≤ RingHom.ker ψ₀ := by
      rw [relIdealR_le_ker_iff]
      refine ⟨fun l ↦ ?_, fun k hk ↦ ?_⟩
      · rw [evalMat_congr _ _ hX M.1.comm, hv]
        exact M.1.eval_eq l
      · have key : ∀ (X' : I → Matrix (Fin d) (Fin d) A) (hX' : ∀ i j, X' i * X' j = X' j * X' i)
            (v' : Fin d → A) (p : MvPolynomial I A), X' = M.1.X → v' = M.1.v →
            evalVec X' hX' v' p = evalVec M.1.X M.1.comm M.1.v p := by
          rintro _ _ _ _ rfl rfl
          rfl
        rw [hφ, key _ _ _ _ hX hv]
        exact M.2 k hk
    ⟨Ideal.Quotient.lift _ ψ₀ he, by
      rw [← hφ]
      rfl⟩
  left_inv f := by
    obtain ⟨f, hf⟩ := f
    ext1
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) ?_
    · simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, eval₂Hom_C]
      rw [← hf]
      rfl
    · rintro (⟨i, a, b⟩ | ⟨a⟩) <;> simp [matOfHom, genMatR₀, genMatR, genVecR₀, genVecR]
  right_inv M := by
    ext1
    ext1
    · funext i
      ext a b
      simp [matOfHom, genMatR₀, genMatR]
    · funext a
      simp [matOfHom, genVecR₀, genVecR]

end Univ

end CurvesJacobian.HilbAffine
