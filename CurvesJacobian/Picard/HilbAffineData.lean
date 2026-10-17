/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Quotients of polynomial rings with a prescribed monomial basis

This is the algebraic core of the affine case of the representability of the Hilbert scheme of
points (Stacks, Lemma 44.2.5, Tag 0B99). Fix a set of variables `I`, `d : ℕ` and monomials
`w : Fin d → (I →₀ ℕ)`. For a commutative ring `A`, Stacks considers the subfunctor `F_W` of
`Hilb^d` of ideals `J ⊆ A[x_i]` such that the images of the monomials `w l` form an `A`-basis of
`A[x_i]/J` (`HasMonomialBasis`).

Instead of the structure constants used in Stacks, we describe such an ideal by linear algebra
(`monomialBasisEquiv`): the multiplications by the variables `x_i` in the basis `w`, which are
pairwise commuting matrices `X i`, together with the coordinate vector `v` of `1`, subject to
`w_l(X) v = e_l` (`MatData`). Conversely `(X, v)` gives back `J = {p | p(X) v = 0}`. Both
descriptions are given by polynomial equations in the entries of `X i` and `v`, which is what
makes `F_W` representable by an affine scheme: `MatData A w` is in natural bijection with ring
maps `U → A` out of an explicit finitely presented ring `U = univRing I d w`
(`univRingHomEquiv`; `U` is a quotient of `ℤ[X_{i,a,b}, v_a]` by the entries of the commutators
`[X_i, X_j]` and of `w_l(X) v - e_l`).
-/

open MvPolynomial

universe u

noncomputable section

namespace CurvesJacobian.HilbAffine

variable {A : Type u} [CommRing A] {I : Type u} {d : ℕ}

/-- The `A`-points of the subfunctor `F_W` of `Hilb^d` of `𝔸^I` (Stacks, Tag 0B99): ideals
`J ⊆ A[x_i]` such that the monomials `w l` form an `A`-basis of `A[x_i]/J`. -/
def HasMonomialBasis (w : Fin d → I →₀ ℕ) (J : Ideal (MvPolynomial I A)) : Prop :=
  ∃ b : Module.Basis (Fin d) A (MvPolynomial I A ⧸ J),
    ∀ l, b l = Ideal.Quotient.mk J (monomial (w l) 1)

section Eval

variable (X : I → Matrix (Fin d) (Fin d) A) (hX : ∀ i j, X i * X j = X j * X i)

open scoped IsMulCommutative in
/-- Evaluation of polynomials at a family of pairwise commuting matrices. -/
def evalMat : MvPolynomial I A →ₐ[A] Matrix (Fin d) (Fin d) A :=
  haveI : IsMulCommutative (Algebra.adjoin A (Set.range X)) :=
    Algebra.isMulCommutative_adjoin A (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hX i j)
  (Algebra.adjoin A (Set.range X)).val.comp
    (aeval fun i ↦ (⟨X i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin A (Set.range X)))

lemma evalMat_congr {X' : I → Matrix (Fin d) (Fin d) A} (h : X = X')
    (hX' : ∀ i j, X' i * X' j = X' j * X' i) : evalMat X hX = evalMat X' hX' := by
  subst h; rfl

@[simp]
lemma evalMat_X (i : I) : evalMat X hX (MvPolynomial.X i) = X i := by
  simp [evalMat]

lemma evalMat_comm (p q : MvPolynomial I A) :
    evalMat X hX p * evalMat X hX q = evalMat X hX q * evalMat X hX p := by
  rw [← map_mul, mul_comm, map_mul]

lemma evalMat_C_mulVec (a : A) (v : Fin d → A) :
    (evalMat X hX (C a)).mulVec v = a • v := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- `p ↦ p(X) v`, as an `A`-linear map. -/
def evalVec (v : Fin d → A) : MvPolynomial I A →ₗ[A] (Fin d → A) where
  toFun p := (evalMat X hX p).mulVec v
  map_add' p q := by simp only [map_add, Matrix.add_mulVec]
  map_smul' a p := by simp only [map_smul, Matrix.smul_mulVec, RingHom.id_apply]

lemma evalVec_apply (v : Fin d → A) (p : MvPolynomial I A) :
    evalVec X hX v p = (evalMat X hX p).mulVec v := rfl

lemma evalVec_mul (v : Fin d → A) (p q : MvPolynomial I A) :
    evalVec X hX v (p * q) = (evalMat X hX p).mulVec (evalVec X hX v q) := by
  simp only [evalVec_apply, map_mul, Matrix.mulVec_mulVec]

/-- The ideal `{p | p(X) v = 0}`. -/
def kerIdeal (v : Fin d → A) : Ideal (MvPolynomial I A) where
  carrier := {p | evalVec X hX v p = 0}
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq, map_add] at hp hq ⊢
    rw [hp, hq, add_zero]
  zero_mem' := by simp
  smul_mem' c p hp := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hp ⊢
    rw [evalVec_mul, hp, Matrix.mulVec_zero]

lemma mem_kerIdeal (v : Fin d → A) (p : MvPolynomial I A) :
    p ∈ kerIdeal X hX v ↔ evalVec X hX v p = 0 := Iff.rfl

end Eval

section Equiv

variable (w : Fin d → I →₀ ℕ)

variable (A) in
/-- The matrix description of `F_W`: pairwise commuting matrices `X i` and a vector `v` with
`w_l(X) v = e_l` for all `l`. -/
structure MatData where
  /-- the matrices of multiplication by the variables -/
  X : I → Matrix (Fin d) (Fin d) A
  /-- the coordinates of `1` -/
  v : Fin d → A
  comm : ∀ i j, X i * X j = X j * X i
  eval_eq : ∀ l, (evalMat X comm (monomial (w l) 1)).mulVec v = Pi.single l 1

@[ext]
lemma MatData.ext {M N : MatData A w} (hX : M.X = N.X) (hv : M.v = N.v) : M = N := by
  cases M; cases N; cases hX; cases hv; rfl

variable {w}

section FromMat

variable {X : I → Matrix (Fin d) (Fin d) A} (hX : ∀ i j, X i * X j = X j * X i)
  {v : Fin d → A} (hw : ∀ l, (evalMat X hX (monomial (w l) 1)).mulVec v = Pi.single l 1)

include hw in
lemma evalVec_surjective : Function.Surjective (evalVec X hX v) := by
  intro y
  refine ⟨∑ l, y l • monomial (w l) 1, ?_⟩
  rw [map_sum]
  simp only [map_smul, evalVec_apply, hw]
  ext m
  simp [Finset.sum_apply, Pi.single_apply]

/-- The quotient by `{p | p(X) v = 0}` is `A^d`, via `p ↦ p(X) v`. -/
def quotEquiv : (MvPolynomial I A ⧸ kerIdeal X hX v) ≃ₗ[A] (Fin d → A) :=
  (Submodule.Quotient.restrictScalarsEquiv A (kerIdeal X hX v)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (Submodule.ext fun _ ↦ Iff.rfl) ≪≫ₗ
    (evalVec X hX v).quotKerEquivOfSurjective (evalVec_surjective hX hw)

lemma quotEquiv_mk (p : MvPolynomial I A) :
    quotEquiv hX hw (Ideal.Quotient.mk _ p) = evalVec X hX v p := rfl

/-- The basis of `A[x]/J` coming from `(X, v)`. -/
def basisOfMat : Module.Basis (Fin d) A (MvPolynomial I A ⧸ kerIdeal X hX v) :=
  (Pi.basisFun A (Fin d)).map (quotEquiv hX hw).symm

lemma basisOfMat_apply (l : Fin d) :
    basisOfMat hX hw l = Ideal.Quotient.mk _ (monomial (w l) 1) := by
  rw [basisOfMat, Module.Basis.map_apply, LinearEquiv.symm_apply_eq, quotEquiv_mk,
    evalVec_apply, hw, Pi.basisFun_apply]

include hw in
lemma hasMonomialBasis_kerIdeal : HasMonomialBasis w (kerIdeal X hX v) :=
  ⟨basisOfMat hX hw, basisOfMat_apply hX hw⟩

end FromMat

section FromBasis

variable {J : Ideal (MvPolynomial I A)} (b : Module.Basis (Fin d) A (MvPolynomial I A ⧸ J))

/-- Multiplication by `x_i` on `A[x]/J`, in the basis `b`. -/
def mulMat (i : I) : Matrix (Fin d) (Fin d) A :=
  LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ
    LinearMap.mulLeft A (Ideal.Quotient.mk J (MvPolynomial.X i)) ∘ₗ b.equivFun.symm.toLinearMap)

lemma mulMat_mulVec (i : I) (y : Fin d → A) :
    (mulMat b i).mulVec y =
      b.equivFun (Ideal.Quotient.mk J (MvPolynomial.X i) * b.equivFun.symm y) := by
  rw [mulMat, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

lemma mulMat_comm (i j : I) : mulMat b i * mulMat b j = mulMat b j * mulMat b i := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y ↦ ?_
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, mulMat_mulVec,
    LinearEquiv.symm_apply_apply]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (MvPolynomial.X i)]

/-- `p(X) v = coordinates of p mod J`, for the matrices of multiplication by the variables. -/
lemma evalMat_mulMat_mulVec (p : MvPolynomial I A) :
    (evalMat (mulMat b) (mulMat_comm b) p).mulVec (b.equivFun 1) =
      b.equivFun (Ideal.Quotient.mk J p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [evalMat_C_mulVec, ← map_smul, Algebra.smul_def, mul_one]
    rfl
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, evalMat_comm, ← Matrix.mulVec_mulVec, hp, evalMat_X, mulMat_mulVec,
      LinearEquiv.symm_apply_apply, ← map_mul, mul_comm (MvPolynomial.X i)]

include b in
lemma mulMat_eval_eq (hb : ∀ l, b l = Ideal.Quotient.mk J (monomial (w l) 1)) (l : Fin d) :
    (evalMat (mulMat b) (mulMat_comm b) (monomial (w l) 1)).mulVec (b.equivFun 1) =
      Pi.single l 1 := by
  classical
  rw [evalMat_mulMat_mulVec, ← hb]
  ext m
  rw [Module.Basis.equivFun_self, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

lemma kerIdeal_mulMat : kerIdeal (mulMat b) (mulMat_comm b) (b.equivFun 1) = J := by
  ext p
  rw [mem_kerIdeal, evalVec_apply, evalMat_mulMat_mulVec, LinearEquiv.map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

end FromBasis

/-- **The matrix description of `F_W`** (affine case of Stacks, Tag 0B99): ideals `J ⊆ A[x_i]`
with the monomials `w` as a basis of `A[x_i]/J` correspond to pairs `(X, v)` of commuting
matrices and a vector with `w_l(X) v = e_l`. -/
def monomialBasisEquiv :
    {J : Ideal (MvPolynomial I A) // HasMonomialBasis w J} ≃ MatData A w where
  toFun J := ⟨mulMat J.2.choose, J.2.choose.equivFun 1, mulMat_comm _,
    mulMat_eval_eq _ J.2.choose_spec⟩
  invFun M := ⟨kerIdeal M.X M.comm M.v, hasMonomialBasis_kerIdeal M.comm M.eval_eq⟩
  left_inv J := Subtype.ext (kerIdeal_mulMat J.2.choose)
  right_inv := by
    rintro ⟨X, v, hX, hw⟩
    set b := (hasMonomialBasis_kerIdeal hX hw).choose
    have hb : b = basisOfMat hX hw :=
      Module.Basis.eq_of_apply_eq fun l ↦
        ((hasMonomialBasis_kerIdeal hX hw).choose_spec l).trans (basisOfMat_apply hX hw l).symm
    have hequiv : b.equivFun = quotEquiv hX hw := by
      rw [hb, basisOfMat, Module.Basis.map_equivFun, Pi.basisFun_equivFun]
      ext y
      simp
    ext1
    · funext i
      change mulMat b i = X i
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun y ↦ ?_
      obtain ⟨p, rfl⟩ := (quotEquiv hX hw).surjective y
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulMat_mulVec, hequiv,
        LinearEquiv.symm_apply_apply, ← map_mul, quotEquiv_mk, quotEquiv_mk, evalVec_mul,
        evalMat_X]
    · change b.equivFun 1 = v
      rw [hequiv, ← map_one (Ideal.Quotient.mk _), quotEquiv_mk, evalVec_apply, map_one,
        Matrix.one_mulVec]

end Equiv

section Map

variable {B : Type u} [CommRing B] (φ : B →+* A) (X : I → Matrix (Fin d) (Fin d) B)
  (hX : ∀ i j, X i * X j = X j * X i)

include hX in
lemma map_comm : ∀ i j, (X i).map φ * (X j).map φ = (X j).map φ * (X i).map φ := by
  intro i j
  rw [← Matrix.map_mul, hX, Matrix.map_mul]

/-- Evaluation at commuting matrices commutes with ring homomorphisms. -/
lemma evalMat_map (p : MvPolynomial I B) :
    evalMat (fun i ↦ (X i).map φ) (map_comm φ X hX) (MvPolynomial.map φ p) =
      (evalMat X hX p).map φ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    ext a' b'
    simp only [Matrix.algebraMap_matrix_apply, Matrix.map_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    split_ifs <;> simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, Matrix.map_add _ (map_add φ)]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, evalMat_X, hp, map_mul, evalMat_X, Matrix.map_mul]

end Map

section Universal

variable (I d)

/-- The variables of the universal ring: matrix entries `X_{i,a,b}` and vector entries `v_a`. -/
abbrev UnivVar : Type u := (I × Fin d × Fin d) ⊕ ULift.{u} (Fin d)

/-- The generic matrices. -/
def genMat (i : I) : Matrix (Fin d) (Fin d) (MvPolynomial (UnivVar I d) ℤ) :=
  fun a b ↦ MvPolynomial.X (Sum.inl (i, a, b))

/-- The generic vector. -/
def genVec : Fin d → MvPolynomial (UnivVar I d) ℤ := fun a ↦ MvPolynomial.X (Sum.inr ⟨a⟩)

/-- The ideal generated by the entries of the commutators of the generic matrices. -/
def commIdeal : Ideal (MvPolynomial (UnivVar I d) ℤ) :=
  Ideal.span {x | ∃ i j a b, x = (genMat I d i * genMat I d j - genMat I d j * genMat I d i) a b}

/-- The ring of pairwise commuting generic matrices and a generic vector. -/
abbrev CommRing₀ : Type u := MvPolynomial (UnivVar I d) ℤ ⧸ commIdeal I d

/-- The generic matrices over `CommRing₀`, which commute. -/
def genMat₀ (i : I) : Matrix (Fin d) (Fin d) (CommRing₀ I d) :=
  (genMat I d i).map (Ideal.Quotient.mk _)

lemma genMat₀_comm (i j : I) : genMat₀ I d i * genMat₀ I d j = genMat₀ I d j * genMat₀ I d i := by
  rw [genMat₀, genMat₀, ← Matrix.map_mul, ← Matrix.map_mul, ← sub_eq_zero,
    ← Matrix.map_sub _ (map_sub _)]
  ext a b
  rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, j, a, b, rfl⟩

/-- The generic vector over `CommRing₀`. -/
def genVec₀ : Fin d → CommRing₀ I d := fun a ↦ Ideal.Quotient.mk _ (genVec I d a)

/-- The relations `w_l(X) v = e_l`. -/
def evalIdeal (w : Fin d → I →₀ ℕ) : Ideal (CommRing₀ I d) :=
  Ideal.span {x | ∃ l a, x = (evalMat (genMat₀ I d) (genMat₀_comm I d)
    (monomial (w l) 1)).mulVec (genVec₀ I d) a - (Pi.single l 1 : Fin d → CommRing₀ I d) a}

/-- The ring representing `F_W` (Stacks, Tag 0B99, in the matrix description). -/
abbrev univRing (w : Fin d → I →₀ ℕ) : Type u := CommRing₀ I d ⧸ evalIdeal I d w

variable {I d}

lemma map_genMat (ψ : MvPolynomial (UnivVar I d) ℤ →+* A) (i : I) :
    (genMat I d i).map ψ = fun a b ↦ ψ (MvPolynomial.X (Sum.inl (i, a, b))) := rfl

/-- **Representability of the matrix description of `F_W`**: ring maps out of `univRing I d w`
are the matrix data of `F_W` (affine case of Stacks, Tag 0B99). -/
def univRingHomEquiv (w : Fin d → I →₀ ℕ) : (univRing I d w →+* A) ≃ MatData A w where
  toFun f :=
    let φ : CommRing₀ I d →+* A := f.comp (Ideal.Quotient.mk _)
    { X := fun i ↦ (genMat₀ I d i).map φ
      v := fun a ↦ φ (genVec₀ I d a)
      comm := map_comm φ _ (genMat₀_comm I d)
      eval_eq := fun l ↦ by
        ext a
        have h0 : (evalMat (genMat₀ I d) (genMat₀_comm I d)
            (monomial (w l) 1)).mulVec (genVec₀ I d) a -
              (Pi.single l 1 : Fin d → CommRing₀ I d) a ∈ evalIdeal I d w :=
          Ideal.subset_span ⟨l, a, rfl⟩
        have h1 := congrArg f ((Ideal.Quotient.eq_zero_iff_mem).mpr h0)
        rw [map_zero, map_sub, map_sub, sub_eq_zero] at h1
        have h2 := RingHom.map_mulVec φ (evalMat (genMat₀ I d) (genMat₀_comm I d)
          (monomial (w l) 1)) (genVec₀ I d) a
        rw [← evalMat_map φ _ (genMat₀_comm I d), MvPolynomial.map_monomial, map_one φ] at h2
        refine h2.symm.trans ?_
        change f (Ideal.Quotient.mk _ _) = _
        rw [h1, Pi.single_apply, Pi.single_apply]
        split_ifs <;> simp }
  invFun M :=
    let ψ : MvPolynomial (UnivVar I d) ℤ →+* A :=
      eval₂Hom (Int.castRingHom A) (Sum.elim (fun t ↦ M.X t.1 t.2.1 t.2.2) (fun a ↦ M.v a.down))
    have hψ : ∀ i, (genMat I d i).map ψ = M.X i := fun i ↦ by
      ext a b; simp [genMat, ψ]
    have hc : commIdeal I d ≤ RingHom.ker ψ := by
      rw [commIdeal, Ideal.span_le]
      rintro _ ⟨i, j, a, b, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, ← Matrix.map_apply (f := ψ),
        Matrix.map_sub _ (map_sub ψ),
        Matrix.map_mul, Matrix.map_mul, hψ, hψ, M.comm, sub_self, Matrix.zero_apply]
    let ψ₀ : CommRing₀ I d →+* A := Ideal.Quotient.lift _ ψ hc
    have hψ₀ : ∀ i, (genMat₀ I d i).map ψ₀ = M.X i := fun i ↦ by
      rw [genMat₀, Matrix.map_map]
      exact hψ i
    have hv₀ : ψ₀ ∘ genVec₀ I d = M.v := by
      funext a; simp [ψ₀, genVec₀, genVec, ψ]
    have he : evalIdeal I d w ≤ RingHom.ker ψ₀ := by
      rw [evalIdeal, Ideal.span_le]
      rintro _ ⟨l, a, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, RingHom.map_mulVec,
        ← evalMat_map ψ₀ _ (genMat₀_comm I d), MvPolynomial.map_monomial, map_one ψ₀, hv₀]
      rw [evalMat_congr _ _ (funext hψ₀) M.comm, M.eval_eq, sub_eq_zero, Pi.single_apply,
        Pi.single_apply]
      split_ifs <;> simp
    Ideal.Quotient.lift _ ψ₀ he
  left_inv f := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rintro (⟨i, a, b⟩ | ⟨a⟩) <;> simp [genMat₀, genMat, genVec₀, genVec]
  right_inv M := by
    ext1
    · funext i
      ext a b
      simp [genMat₀, genMat]
    · funext a
      simp [genVec₀, genVec]

end Universal

end CurvesJacobian.HilbAffine
