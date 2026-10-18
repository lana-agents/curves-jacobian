/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ChartMatrix
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Base change of matrix data of two-chart Čech complexes

* `CurvesJacobian.ChartMatrix.isBaseChange_of_retract`: base change commutes with retracts: if
  `j : M₀ → M` is a base change along `A₀ → A` intertwining idempotents `i₀ r₀` and `i r`, then
  the induced map of the retracts `F₀ → F` is a base change.
* `MatData.mapBC`: matrix data over `A₀`-algebras `S₀` transported along base change maps
  `S₀ → S` (`S = A ⊗_{A₀} S₀`), and `MatData.hasPerfectModel_mapBC`: a perfect model of the
  Čech data over `A₀` gives one of the transported data over `A` (the fixed vectors of an
  idempotent matrix commute with base change).
-/

open TensorProduct LinearMap Matrix

universe u

namespace CurvesJacobian.ChartMatrix

section Retract

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {M₀ F₀ M F : Type u} [AddCommGroup M₀] [Module A₀ M₀] [AddCommGroup F₀] [Module A₀ F₀]
  [AddCommGroup M] [Module A₀ M] [Module A M] [IsScalarTower A₀ A M]
  [AddCommGroup F] [Module A₀ F] [Module A F] [IsScalarTower A₀ A F]
  {j : M₀ →ₗ[A₀] M} (hj : IsBaseChange A j)
  (i₀ : F₀ →ₗ[A₀] M₀) (r₀ : M₀ →ₗ[A₀] F₀) (hr₀ : r₀ ∘ₗ i₀ = LinearMap.id)
  (i : F →ₗ[A] M) (r : M →ₗ[A] F) (hr : r ∘ₗ i = LinearMap.id)
  (j' : F₀ →ₗ[A₀] F) (hj' : ∀ x, i (j' x) = j (i₀ x))
  (hjr : ∀ m, j (i₀ (r₀ m)) = i (r (j m)))

omit [Module A₀ F] [IsScalarTower A₀ A F] in
include hjr in
lemma equiv_comp_baseChange (x : A ⊗[A₀] M₀) :
    hj.equiv ((i₀ ∘ₗ r₀).baseChange A x) = i (r (hj.equiv x)) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul,
      LinearMap.comp_apply, hjr, map_smul, map_smul]

include hj hr₀ hr hj' hjr in
/-- **Base change commutes with retracts.** -/
theorem isBaseChange_of_retract : IsBaseChange A j' := by
  have hr₀' : ∀ x, r₀ (i₀ x) = x := fun x ↦ LinearMap.congr_fun hr₀ x
  have hr' : ∀ x, r (i x) = x := fun x ↦ LinearMap.congr_fun hr x
  let Fwd : A ⊗[A₀] F₀ →ₗ[A] F := r ∘ₗ hj.equiv.toLinearMap ∘ₗ i₀.baseChange A
  let Bwd : F →ₗ[A] A ⊗[A₀] F₀ := r₀.baseChange A ∘ₗ hj.equiv.symm.toLinearMap ∘ₗ i
  have h1 : Fwd ∘ₗ Bwd = LinearMap.id := by
    refine LinearMap.ext fun y ↦ ?_
    change r (hj.equiv (i₀.baseChange A (r₀.baseChange A (hj.equiv.symm (i y))))) = y
    rw [← LinearMap.comp_apply (i₀.baseChange A), ← LinearMap.baseChange_comp,
      equiv_comp_baseChange hj i₀ r₀ i r hjr, LinearEquiv.apply_symm_apply, hr', hr']
  have h2 : Bwd ∘ₗ Fwd = LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    change r₀.baseChange A (hj.equiv.symm (i (r (hj.equiv (i₀.baseChange A x))))) = x
    rw [← equiv_comp_baseChange hj i₀ r₀ i r hjr, LinearEquiv.symm_apply_apply]
    have key : r₀ ∘ₗ ((i₀ ∘ₗ r₀) ∘ₗ i₀) = LinearMap.id :=
      LinearMap.ext fun y ↦ by simp only [LinearMap.comp_apply, hr₀', LinearMap.id_apply]
    rw [← LinearMap.comp_apply ((i₀ ∘ₗ r₀).baseChange A) (i₀.baseChange A),
      ← LinearMap.baseChange_comp, ← LinearMap.comp_apply (r₀.baseChange A),
      ← LinearMap.baseChange_comp, key, LinearMap.baseChange_id, LinearMap.id_apply]
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinear Fwd Bwd h1 h2) fun x ↦ ?_
  change r (hj.equiv (i₀.baseChange A (1 ⊗ₜ x))) = j' x
  rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, ← hj', hr']

end Retract

lemma map_mul_hom {S S' F : Type*} [CommRing S] [CommRing S'] [FunLike F S S']
    [RingHomClass F S S'] (f : F) {a b c : ℕ} (M : Matrix (Fin a) (Fin b) S)
    (N : Matrix (Fin b) (Fin c) S) : (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := (f : S →+* S'))

section FixBC

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {S₀ S : Type u} [CommRing S₀] [CommRing S] [Algebra A₀ S₀] [Algebra A S] [Algebra A₀ S]
  [IsScalarTower A₀ A S] {n : ℕ}

/-- `v ↦ ι ∘ v` on fixed vectors. -/
def fixMap (e₀ : Matrix (Fin n) (Fin n) S₀) (ι : S₀ →ₐ[A₀] S) :
    fixSub e₀ →ₗ[A₀] fixSub (e₀.map ι) where
  toFun v := ⟨ι ∘ v.1, by
    rw [mem_fixSub]
    have := map_mulVec_comp (ι : S₀ →+* S) e₀ v.1
    rw [show ((ι : S₀ →+* S) : S₀ → S) = ι from rfl] at this
    rw [this, mem_fixSub.mp v.2]⟩
  map_add' x y := Subtype.ext <| funext fun i ↦ by simp
  map_smul' a x := Subtype.ext <| funext fun i ↦ by simp

@[simp]
lemma fixMap_apply (e₀ : Matrix (Fin n) (Fin n) S₀) (ι : S₀ →ₐ[A₀] S) (v : fixSub e₀) :
    (fixMap e₀ ι v : Fin n → S) = ι ∘ v.1 := rfl

/-- The inclusion of fixed vectors, linear over a subring of scalars. -/
def fixIncl {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (e : Matrix (Fin n) (Fin n) T) : fixSub e →ₗ[R] (Fin n → T) where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection `v ↦ e v` onto the fixed vectors of an idempotent. -/
def fixProj {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (e : Matrix (Fin n) (Fin n) T) (he : e * e = e) : (Fin n → T) →ₗ[R] fixSub e where
  toFun v := ⟨e *ᵥ v, by rw [mem_fixSub, Matrix.mulVec_mulVec, he]⟩
  map_add' x y := Subtype.ext (Matrix.mulVec_add e x y)
  map_smul' a x := Subtype.ext (Matrix.mulVec_smul e a x)

lemma fixProj_fixIncl {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (e : Matrix (Fin n) (Fin n) T) (he : e * e = e) :
    fixProj (R := R) e he ∘ₗ fixIncl e = LinearMap.id :=
  LinearMap.ext fun v ↦ Subtype.ext (show e *ᵥ v.1 = v.1 from mem_fixSub.mp v.2)

/-- **Fixed vectors of an idempotent matrix commute with base change.** -/
theorem isBaseChange_fixMap (e₀ : Matrix (Fin n) (Fin n) S₀) (he₀ : e₀ * e₀ = e₀)
    (ι : S₀ →ₐ[A₀] S) (b : IsBaseChange A ι.toLinearMap) : IsBaseChange A (fixMap e₀ ι) := by
  have he : e₀.map ι * e₀.map ι = e₀.map ι := by
    rw [← map_mul_hom, he₀]
  refine isBaseChange_of_retract (b.finitePow (Fin n)) (fixIncl e₀) (fixProj e₀ he₀)
    (fixProj_fixIncl e₀ he₀) (fixIncl (e₀.map ι)) (fixProj (e₀.map ι) he)
    (fixProj_fixIncl _ he) (fixMap e₀ ι) (fun _ ↦ rfl) fun m ↦ ?_
  change ι ∘ (e₀ *ᵥ m) = e₀.map ι *ᵥ (ι ∘ m)
  have := map_mulVec_comp (ι : S₀ →+* S) e₀ m
  rw [show ((ι : S₀ →+* S) : S₀ → S) = ι from rfl] at this
  exact this.symm

end FixBC

namespace MatData

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {S₀U S₀V S₀W SU SV SW : Type u} [CommRing S₀U] [CommRing S₀V] [CommRing S₀W]
  [CommRing SU] [CommRing SV] [CommRing SW]
  [Algebra A₀ S₀U] [Algebra A₀ S₀V] [Algebra A₀ S₀W] [Algebra A SU] [Algebra A SV] [Algebra A SW]
  [Algebra A₀ SU] [Algebra A₀ SV] [Algebra A₀ SW]
  [IsScalarTower A₀ A SU] [IsScalarTower A₀ A SV] [IsScalarTower A₀ A SW]
  {t₀U : S₀U →ₐ[A₀] S₀W} {t₀V : S₀V →ₐ[A₀] S₀W} {tU : SU →ₐ[A] SW} {tV : SV →ₐ[A] SW}
  (D₀ : MatData t₀U t₀V) (ιU : S₀U →ₐ[A₀] SU) (ιV : S₀V →ₐ[A₀] SV) (ιW : S₀W →ₐ[A₀] SW)
  (cU : ∀ x, ιW (t₀U x) = tU (ιU x)) (cV : ∀ x, ιW (t₀V x) = tV (ιV x))

lemma map_map_of_comm {S S₁ S₂ T : Type u} [CommRing S] [CommRing S₁] [CommRing S₂]
    [CommRing T] {a b : ℕ} (M : Matrix (Fin a) (Fin b) S) (f₁ : S →+* S₁) (g₁ : S₁ →+* T)
    (f₂ : S →+* S₂) (g₂ : S₂ →+* T) (h : ∀ x, g₁ (f₁ x) = g₂ (f₂ x)) :
    (M.map f₁).map g₁ = (M.map f₂).map g₂ := by
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  exact funext h

include cU cV in
/-- **Base change of matrix data** along `S₀ → S`. -/
def mapBC : MatData tU tV where
  n := D₀.n
  m := D₀.m
  eU := D₀.eU.map ιU
  eV := D₀.eV.map ιV
  Φ := D₀.Φ.map ιW
  Ψ := D₀.Ψ.map ιW
  eU_mul := by rw [← map_mul_hom, D₀.eU_mul]
  eV_mul := by rw [← map_mul_hom, D₀.eV_mul]
  Φ_Ψ := by
    rw [← map_mul_hom, D₀.Φ_Ψ]
    exact map_map_of_comm D₀.eU (t₀U : S₀U →+* S₀W) (ιW : S₀W →+* SW) (ιU : S₀U →+* SU)
      (tU : SU →+* SW) cU
  Ψ_Φ := by
    rw [← map_mul_hom, D₀.Ψ_Φ]
    exact map_map_of_comm D₀.eV (t₀V : S₀V →+* S₀W) (ιW : S₀W →+* SW) (ιV : S₀V →+* SV)
      (tV : SV →+* SW) cV
  eU_Φ := by
    have := map_map_of_comm D₀.eU (t₀U : S₀U →+* S₀W) (ιW : S₀W →+* SW) (ιU : S₀U →+* SU)
      (tU : SU →+* SW) cU
    change (D₀.eU.map ιU).map tU * D₀.Φ.map ιW = D₀.Φ.map ιW
    rw [← show (D₀.eU.map t₀U).map ιW = (D₀.eU.map ιU).map tU from this,
      ← map_mul_hom, D₀.eU_Φ]
  Φ_eV := by
    have := map_map_of_comm D₀.eV (t₀V : S₀V →+* S₀W) (ιW : S₀W →+* SW) (ιV : S₀V →+* SV)
      (tV : SV →+* SW) cV
    change D₀.Φ.map ιW * (D₀.eV.map ιV).map tV = D₀.Φ.map ιW
    rw [← show (D₀.eV.map t₀V).map ιW = (D₀.eV.map ιV).map tV from this,
      ← map_mul_hom, D₀.Φ_eV]

/-- **A perfect model over `A₀` gives one after base change** of the matrix data to `A`. -/
theorem hasPerfectModel_mapBC (bU : IsBaseChange A ιU.toLinearMap)
    (bV : IsBaseChange A ιV.toLinearMap) (bW : IsBaseChange A ιW.toLinearMap)
    (H : D₀.HasPerfectModel) : (D₀.mapBC ιU ιV ιW cU cV).HasPerfectModel := by
  have H' := TwoTerm.HasPerfectModel.baseChange (A := A) H
  have hW : (D₀.eU.map ιU).map tU = (D₀.eU.map t₀U).map ιW :=
    (map_map_of_comm D₀.eU (t₀U : S₀U →+* S₀W) (ιW : S₀W →+* SW) (ιU : S₀U →+* SU)
      (tU : SU →+* SW) cU).symm
  have heW : D₀.eU.map t₀U * D₀.eU.map t₀U = D₀.eU.map t₀U := by
    rw [← map_mul_hom, D₀.eU_mul]
  have bU' := isBaseChange_fixMap D₀.eU D₀.eU_mul ιU bU
  have bV' := isBaseChange_fixMap D₀.eV D₀.eV_mul ιV bV
  have bW' := isBaseChange_fixMap (D₀.eU.map t₀U) heW ιW bW
  let γ := bW'.equiv ≪≫ₗ (LinearEquiv.ofEq _ _ (congrArg fixSub hW.symm)).restrictScalars A
  refine H'.of_equiv bU'.equiv bV'.equiv γ ?_ ?_
  · refine LinearMap.ext fun x ↦ ?_
    induction x with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
    | tmul a v =>
      change (D₀.mapBC ιU ιV ιW cU cV).fU (bU'.equiv (a ⊗ₜ v)) =
        (LinearEquiv.ofEq _ _ (congrArg fixSub hW.symm)).restrictScalars A
          (bW'.equiv (a ⊗ₜ D₀.fU v))
      rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      apply Subtype.ext
      change tU ∘ (a • (ιU ∘ v.1)) = a • (ιW ∘ (t₀U ∘ v.1))
      rw [comp_smul]
      congr 1
      exact funext fun i ↦ (cU _).symm
  · refine LinearMap.ext fun x ↦ ?_
    induction x with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
    | tmul a v =>
      change (D₀.mapBC ιU ιV ιW cU cV).fV (bV'.equiv (a ⊗ₜ v)) =
        (LinearEquiv.ofEq _ _ (congrArg fixSub hW.symm)).restrictScalars A
          (bW'.equiv (a ⊗ₜ D₀.fV v))
      rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      apply Subtype.ext
      change D₀.Φ.map ιW *ᵥ (tV ∘ (a • (ιV ∘ v.1))) = a • (ιW ∘ (D₀.Φ *ᵥ (t₀V ∘ v.1)))
      rw [comp_smul, Matrix.mulVec_smul]
      congr 1
      have e : tV ∘ (ιV ∘ v.1) = ιW ∘ (t₀V ∘ v.1) := funext fun i ↦ (cV _).symm
      have := map_mulVec_comp (ιW : S₀W →+* SW) D₀.Φ (t₀V ∘ v.1)
      rw [show ((ιW : S₀W →+* SW) : S₀W → SW) = ιW from rfl] at this
      rw [e, this]

end MatData

end CurvesJacobian.ChartMatrix
