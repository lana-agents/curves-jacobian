/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineBranch

/-!
# Branches at a cusp with a polynomial coordinate relation

A generalisation of `CurvesJacobian.Cusp.CuspBranch` (which is hard-wired to the three cusps
`0, 1, ∞` of `ℙ¹ ∖ {0, 1, ∞}`): the relation between the coordinate `T` of the base and the local
coordinate `s` at the cusp is `T · Q(s) = P(s)` for two polynomials `P, Q ∈ K[X]`
(`CurvesJacobian.Cusp.PBranch`). For the cusps of `ℙ¹ ∖ (S ∪ {∞})`
(`CurvesJacobian.Cusp.cuspP`, `CurvesJacobian.Cusp.cuspQ`): `T = a + s` at a finite cusp `a`
(`P = a + X`, `Q = 1`) and `T s = 1` at `∞` (`P = 1`, `Q = X`).
-/

open CategoryTheory AlgebraicGeometry Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **A branch with coordinate relation `T · Q(s) = P(s)`** of `q : Y ⟶ Spec R`, `T ∈ R`: a finite
type `K`-algebra `A`, étale over `K[s]`, with a `K`-point `pt` at `s = 0`, and a morphism
`m : Spec A[1/s] ⟶ Y` over `Spec R` for `θ : R → A[1/s]` with `θ(T) Q(s) = P(s)`. -/
structure PBranch (K : Type u) [Field K] {R : Type u} [CommRing R] [Algebra K R] (T : R)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (P Q : K[X]) : Type (u + 1) where
  /-- The étale neighbourhood of the point over the cusp. -/
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  [finiteType : Algebra.FiniteType K A]
  /-- The local coordinate. -/
  s : A
  etale : (MvPolynomial.aeval (R := K) fun _ : Fin 1 ↦ s).toRingHom.Etale
  /-- The point over the cusp. -/
  pt : A →ₐ[K] K
  pt_s : pt s = 0
  /-- `R → A[1/s]`. -/
  θ : R →ₐ[K] Localization.Away s
  rel : θ T * aeval (algebraMap A (Localization.Away s) s) Q =
    aeval (algebraMap A (Localization.Away s) s) P
  /-- The branch, a morphism to `Y` over `Spec R`. -/
  m : Spec (.of (Localization.Away s)) ⟶ Y
  hm : m ≫ q = Spec.map (CommRingCat.ofHom θ.toRingHom)

attribute [instance] PBranch.commRing PBranch.algebra PBranch.finiteType

variable {K : Type u} [Field K]

/-- The numerator of the coordinate relation at a cusp of `ℙ¹ ∖ (S ∪ {∞})`: `a + X` at the finite
cusp `a`, `1` at `∞` (`none`). -/
def cuspP : Option K → K[X]
  | some a => C a + X
  | none => 1

/-- The denominator of the coordinate relation at a cusp of `ℙ¹ ∖ (S ∪ {∞})`: `1` at a finite
cusp, `X` at `∞` (`none`). -/
def cuspQ : Option K → K[X]
  | some _ => 1
  | none => X

@[simp] lemma cuspP_some (a : K) : cuspP (some a) = C a + X := rfl
@[simp] lemma cuspP_none : cuspP (none : Option K) = 1 := rfl
@[simp] lemma cuspQ_some (a : K) : cuspQ (some a) = (1 : K[X]) := rfl
@[simp] lemma cuspQ_none : cuspQ (none : Option K) = X := rfl

/-- The relation `T · Q(s) = P(s)` at the cusp `c` is `T = a + s` resp. `T s = 1`. -/
lemma cuspRel_iff {A : Type*} [CommRing A] [Algebra K A] (c : Option K) (T s : A) :
    T * aeval s (cuspQ c) = aeval s (cuspP c) ↔
      (match c with
        | some a => T = algebraMap K A a + s
        | none => T * s = 1) := by
  cases c with
  | none => simp
  | some a => simp

/-- The cusp relations under a field extension. -/
lemma map_cuspP {Ω : Type*} [Field Ω] [Algebra K Ω] (c : Option K) :
    (cuspP c).map (algebraMap K Ω) = cuspP (c.map (algebraMap K Ω)) := by
  cases c <;> simp

lemma map_cuspQ {Ω : Type*} [Field Ω] [Algebra K Ω] (c : Option K) :
    (cuspQ c).map (algebraMap K Ω) = cuspQ (c.map (algebraMap K Ω)) := by
  cases c <;> simp

end CurvesJacobian.Cusp
