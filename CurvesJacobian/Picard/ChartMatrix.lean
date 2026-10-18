/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PerfectModel
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.Projective

/-!
# Matrix presentations of two-chart Čech data

Let `S_U → S_W ← S_V` be `A`-algebra maps (think: functions on two affine opens `U`, `V` and on
`U ∩ V`). A finite projective module on each chart is the image of an idempotent matrix, and
the gluing over `U ∩ V` is a pair of matrices `Φ`, `Ψ`. `CurvesJacobian.ChartMatrix.MatData`
records such data, and `MatData.fU`, `MatData.fV` its two-set Čech data (as `A`-modules):
`{v ∈ S_U^n | e_U v = v} → {w ∈ S_W^n | e_U w = w} ← {v ∈ S_V^m | e_V v = v}`.

* `MatData.map`: transport along compatible `A`-algebra maps (used for base change of the
  coefficients, the step of Noetherian approximation);
* `MatData.hasPerfectModel_of_map`: along isomorphisms the Čech data do not change;
* `ChartMatrix.exists_matData`: Čech data `P_U → P_W ← P_V` with `P_U`, `P_V` finite projective
  over `S_U`, `S_V` and `P_W` the localization of `P_U` at `τ ∈ S_U` and of `P_V` at `σ ∈ S_V`
  (with `S_W` the corresponding localization of `S_U` and of `S_V`) are isomorphic to the Čech
  data of some `MatData`; in particular perfect models transfer back.

This is the bookkeeping needed for Noetherian approximation of invertible sheaves on curves
(cf. the reduction to the Noetherian case in Stacks, Lemma 36.30.1, Tag 0A1H): the finitely many
matrix entries are defined over a finitely generated subring.
-/

open TensorProduct LinearMap Matrix

universe u

namespace CurvesJacobian.ChartMatrix

section Fix

variable {S : Type u} [CommRing S] {n : ℕ}

/-- The vectors fixed by a square matrix `e` (for `e` idempotent: its image). -/
abbrev fixSub (e : Matrix (Fin n) (Fin n) S) : Submodule S (Fin n → S) :=
  LinearMap.eqLocus e.mulVecLin LinearMap.id

lemma mem_fixSub {e : Matrix (Fin n) (Fin n) S} {v : Fin n → S} :
    v ∈ fixSub e ↔ e *ᵥ v = v := Iff.rfl

lemma map_mulVec_comp {S' : Type u} [CommRing S'] (f : S →+* S') {m : ℕ}
    (M : Matrix (Fin n) (Fin m) S) (v : Fin m → S) : M.map f *ᵥ (f ∘ v) = f ∘ (M *ᵥ v) :=
  funext fun i ↦ (RingHom.map_mulVec f M v i).symm

end Fix

variable {A : Type u} [CommRing A] {SU SV SW : Type u} [CommRing SU] [CommRing SV] [CommRing SW]
  [Algebra A SU] [Algebra A SV] [Algebra A SW]

variable (iU : SU →ₐ[A] SW) (iV : SV →ₐ[A] SW) in
/-- **Matrix data** of a pair of finite projective modules on two charts glued over the
overlap: idempotents `e_U`, `e_V` and mutually inverse gluing matrices `Φ`, `Ψ` over `S_W`. -/
structure MatData where
  /-- rank of the free module on `U` -/
  n : ℕ
  /-- rank of the free module on `V` -/
  m : ℕ
  /-- idempotent on `S_U^n` -/
  eU : Matrix (Fin n) (Fin n) SU
  /-- idempotent on `S_V^m` -/
  eV : Matrix (Fin m) (Fin m) SV
  /-- gluing `V → U` over `S_W` -/
  Φ : Matrix (Fin n) (Fin m) SW
  /-- gluing `U → V` over `S_W` -/
  Ψ : Matrix (Fin m) (Fin n) SW
  eU_mul : eU * eU = eU
  eV_mul : eV * eV = eV
  Φ_Ψ : Φ * Ψ = eU.map iU
  Ψ_Φ : Ψ * Φ = eV.map iV
  eU_Φ : eU.map iU * Φ = Φ
  Φ_eV : Φ * eV.map iV = Φ

namespace MatData

variable {iU : SU →ₐ[A] SW} {iV : SV →ₐ[A] SW} (D : MatData iU iV)

/-- Sections over `U`. -/
abbrev PU : Submodule SU (Fin D.n → SU) := fixSub D.eU
/-- Sections over `V`. -/
abbrev PV : Submodule SV (Fin D.m → SV) := fixSub D.eV
/-- Sections over `U ∩ V`. -/
abbrev PW : Submodule SW (Fin D.n → SW) := fixSub (D.eU.map iU)

lemma comp_smul {S S' : Type u} [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S']
    (h : S →ₐ[A] S') {k : ℕ} (a : A) (v : Fin k → S) : h ∘ (a • v) = a • (h ∘ v) :=
  funext fun i ↦ by simp

/-- Restriction from `U` to `U ∩ V`. -/
def fU : D.PU →ₗ[A] D.PW where
  toFun v := ⟨iU ∘ v.1, by
    rw [mem_fixSub]
    have := map_mulVec_comp iU.toRingHom D.eU v.1
    rw [show (iU.toRingHom : SU → SW) = iU from rfl] at this
    rw [this, mem_fixSub.mp v.2]⟩
  map_add' x y := Subtype.ext <| funext fun i ↦ by simp
  map_smul' a x := Subtype.ext <| comp_smul iU a x.1

/-- Restriction from `V` to `U ∩ V`, followed by the gluing `Φ`. -/
def fV : D.PV →ₗ[A] D.PW where
  toFun v := ⟨D.Φ *ᵥ (iV ∘ v.1), by rw [mem_fixSub, Matrix.mulVec_mulVec, D.eU_Φ]⟩
  map_add' x y := Subtype.ext <| by
    simp only [Submodule.coe_add]
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := Subtype.ext <| by
    change D.Φ *ᵥ (iV ∘ (a • x.1)) = a • (D.Φ *ᵥ (iV ∘ x.1))
    rw [comp_smul iV a x.1, Matrix.mulVec_smul]

/-- `MatData` has a perfect model if its two-set Čech data do. -/
abbrev HasPerfectModel : Prop := TwoTerm.HasPerfectModel D.fU D.fV

section Map

variable {SU' SV' SW' : Type u} [CommRing SU'] [CommRing SV'] [CommRing SW']
  [Algebra A SU'] [Algebra A SV'] [Algebra A SW'] {iU' : SU' →ₐ[A] SW'} {iV' : SV' →ₐ[A] SW'}
  (hU : SU →ₐ[A] SU') (hV : SV →ₐ[A] SV') (hW : SW →ₐ[A] SW')
  (cU : iU'.comp hU = hW.comp iU) (cV : iV'.comp hV = hW.comp iV)

lemma map_map_eq {S S₁ S₂ T : Type u} [CommRing S] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra A S] [Algebra A S₁] [Algebra A S₂] [Algebra A T] {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) S) (f₁ : S →ₐ[A] S₁) (g₁ : S₁ →ₐ[A] T) (f₂ : S →ₐ[A] S₂)
    (g₂ : S₂ →ₐ[A] T) (h : g₁.comp f₁ = g₂.comp f₂) :
    (M.map f₁).map g₁ = (M.map f₂).map g₂ := by
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  exact congrArg DFunLike.coe h

lemma map_mul_alg {S S' : Type u} [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S']
    (h : S →ₐ[A] S') {a b c : ℕ} (M : Matrix (Fin a) (Fin b) S) (N : Matrix (Fin b) (Fin c) S) :
    (M * N).map h = M.map h * N.map h :=
  Matrix.map_mul (f := h.toRingHom)

include cU cV in
/-- **Transport of matrix data** along compatible `A`-algebra maps. -/
def map : MatData iU' iV' where
  n := D.n
  m := D.m
  eU := D.eU.map hU
  eV := D.eV.map hV
  Φ := D.Φ.map hW
  Ψ := D.Ψ.map hW
  eU_mul := by rw [← map_mul_alg, D.eU_mul]
  eV_mul := by rw [← map_mul_alg, D.eV_mul]
  Φ_Ψ := by rw [← map_mul_alg, D.Φ_Ψ, map_map_eq _ _ _ _ _ cU]
  Ψ_Φ := by rw [← map_mul_alg, D.Ψ_Φ, map_map_eq _ _ _ _ _ cV]
  eU_Φ := by rw [map_map_eq _ _ _ _ _ cU, ← map_mul_alg, D.eU_Φ]
  Φ_eV := by rw [map_map_eq _ _ _ _ _ cV, ← map_mul_alg, D.Φ_eV]

end Map

end MatData

section FixEquiv

variable {S S' : Type u} [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S'] {n : ℕ}

/-- Fixed vectors of `e` and of its image under an `A`-algebra isomorphism. -/
def fixSubMapEquiv (e : Matrix (Fin n) (Fin n) S) (h : S ≃ₐ[A] S') :
    fixSub e ≃ₗ[A] fixSub (e.map (h : S →ₐ[A] S')) where
  toFun v := ⟨h ∘ v.1, by
    rw [mem_fixSub]
    have := map_mulVec_comp (h : S →+* S') e v.1
    rw [show ((h : S →+* S') : S → S') = h from rfl] at this
    change e.map h *ᵥ (h ∘ v.1) = h ∘ v.1
    rw [this, mem_fixSub.mp v.2]⟩
  invFun w := ⟨h.symm ∘ w.1, by
    rw [mem_fixSub]
    have := map_mulVec_comp (h.symm : S' →+* S) (e.map (h : S →ₐ[A] S')) w.1
    rw [show ((h.symm : S' →+* S) : S' → S) = h.symm from rfl, Matrix.map_map,
      show (h.symm ∘ (h : S →ₐ[A] S') : S → S) = id from funext h.symm_apply_apply,
      Matrix.map_id] at this
    rw [this, mem_fixSub.mp w.2]⟩
  left_inv v := Subtype.ext <| funext fun i ↦ h.symm_apply_apply _
  right_inv w := Subtype.ext <| funext fun i ↦ h.apply_symm_apply _
  map_add' x y := Subtype.ext <| funext fun i ↦ by
    change h (x.1 i + y.1 i) = h (x.1 i) + h (y.1 i)
    exact map_add _ _ _
  map_smul' a x := Subtype.ext <| funext fun i ↦ by
    change h (a • x.1 i) = a • h (x.1 i)
    exact map_smul _ _ _

@[simp]
lemma fixSubMapEquiv_apply (e : Matrix (Fin n) (Fin n) S) (h : S ≃ₐ[A] S') (v : fixSub e) :
    (fixSubMapEquiv e h v : Fin n → S') = h ∘ v.1 := rfl

end FixEquiv

namespace MatData

variable {iU : SU →ₐ[A] SW} {iV : SV →ₐ[A] SW} (D : MatData iU iV)
  {SU' SV' SW' : Type u} [CommRing SU'] [CommRing SV'] [CommRing SW']
  [Algebra A SU'] [Algebra A SV'] [Algebra A SW'] {iU' : SU' →ₐ[A] SW'} {iV' : SV' →ₐ[A] SW'}
  (hU : SU ≃ₐ[A] SU') (hV : SV ≃ₐ[A] SV') (hW : SW ≃ₐ[A] SW')
  (cU : iU'.comp (hU : SU →ₐ[A] SU') = (hW : SW →ₐ[A] SW').comp iU)
  (cV : iV'.comp (hV : SV →ₐ[A] SV') = (hW : SW →ₐ[A] SW').comp iV)

/-- **Transport along isomorphisms** does not change the existence of a perfect model. -/
theorem hasPerfectModel_of_map
    (H : (D.map (hU : SU →ₐ[A] SU') (hV : SV →ₐ[A] SV') (hW : SW →ₐ[A] SW') cU
      cV).HasPerfectModel) :
    D.HasPerfectModel := by
  have hE : fixSub ((D.eU.map (hU : SU →ₐ[A] SU')).map iU') =
      fixSub ((D.eU.map iU).map (hW : SW →ₐ[A] SW')) := by
    rw [map_map_eq _ _ _ _ _ cU]
  let α : (D.map (hU : SU →ₐ[A] SU') (hV : SV →ₐ[A] SV') (hW : SW →ₐ[A] SW') cU cV).PU ≃ₗ[A]
      D.PU := (fixSubMapEquiv D.eU hU).symm
  let β : (D.map (hU : SU →ₐ[A] SU') (hV : SV →ₐ[A] SV') (hW : SW →ₐ[A] SW') cU cV).PV ≃ₗ[A]
      D.PV := (fixSubMapEquiv D.eV hV).symm
  let γ : (D.map (hU : SU →ₐ[A] SU') (hV : SV →ₐ[A] SV') (hW : SW →ₐ[A] SW') cU cV).PW ≃ₗ[A]
      D.PW := (LinearEquiv.ofEq _ _ hE).restrictScalars A ≪≫ₗ
        (fixSubMapEquiv (D.eU.map iU) hW).symm
  refine H.of_equiv α β γ ?_ ?_
  · refine LinearMap.ext fun v ↦ Subtype.ext ?_
    obtain ⟨v, rfl⟩ := (fixSubMapEquiv D.eU hU).surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
    simp only [α]
    erw [(fixSubMapEquiv D.eU hU).symm_apply_apply v]
    change iU ∘ v.1 = hW.symm ∘ (iU' ∘ (hU ∘ v.1))
    funext i
    have := congrArg (fun φ : SU →ₐ[A] SW' ↦ φ (v.1 i)) cU
    simp only [AlgHom.comp_apply] at this
    exact ((congrArg hW.symm this).trans (hW.symm_apply_apply _)).symm
  · refine LinearMap.ext fun v ↦ Subtype.ext ?_
    obtain ⟨v, rfl⟩ := (fixSubMapEquiv D.eV hV).surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
    simp only [β]
    erw [(fixSubMapEquiv D.eV hV).symm_apply_apply v]
    change D.Φ *ᵥ (iV ∘ v.1) = hW.symm ∘ ((D.Φ.map hW) *ᵥ (iV' ∘ (hV ∘ v.1)))
    have e : iV' ∘ (hV ∘ v.1) = hW ∘ (iV ∘ v.1) := by
      funext i
      have := congrArg (fun φ : SV →ₐ[A] SW' ↦ φ (v.1 i)) cV
      simpa using this
    have := map_mulVec_comp (hW : SW →+* SW') D.Φ (iV ∘ v.1)
    rw [show ((hW : SW →+* SW') : SW → SW') = hW from rfl] at this
    rw [e, this]
    funext i
    simp

end MatData

/-! ### Existence of matrix presentations -/

section Exists

variable {iU : SU →ₐ[A] SW} {iV : SV →ₐ[A] SW}
  {PU PV PW : Type u} [AddCommGroup PU] [Module SU PU] [Module A PU] [IsScalarTower A SU PU]
  [AddCommGroup PV] [Module SV PV] [Module A PV] [IsScalarTower A SV PV]
  [AddCommGroup PW] [Module SW PW] [Module A PW] [IsScalarTower A SW PW]

omit [IsScalarTower A SW PW] in
/-- A localization of modules `ρ : P → P_W` at `τ`, in elementary form, gives a base change
`P_W = S_W ⊗ P` if `S_W` is the localization of `S` at `τ`. -/
lemma isBaseChange_of_loc {S : Type u} [CommRing S] [Algebra A S] {P : Type u} [AddCommGroup P]
    [Module S P] [Module A P] (i : S →ₐ[A] SW) (τ : S)
    (hloc : letI := i.toRingHom.toAlgebra; IsLocalization.Away τ SW)
    (ρ : P →ₗ[A] PW) (hρ : ∀ (s : S) (p : P), ρ (s • p) = i s • ρ p)
    (hsurj : ∀ z : PW, ∃ (p : P) (k : ℕ), i τ ^ k • z = ρ p)
    (hker : ∀ p : P, ρ p = 0 → ∃ k : ℕ, τ ^ k • p = 0) :
    letI := i.toRingHom.toAlgebra
    letI : Module S PW := Module.compHom PW i.toRingHom
    ∃ (_ : IsScalarTower S SW PW) (ρ' : P →ₗ[S] PW), (∀ p, ρ' p = ρ p) ∧ IsBaseChange SW ρ' := by
  letI := i.toRingHom.toAlgebra
  letI : Module S PW := Module.compHom PW i.toRingHom
  haveI : IsScalarTower S SW PW := ⟨fun s w p ↦ mul_smul (i s) w p⟩
  let ρ' : P →ₗ[S] PW := { toFun := ρ, map_add' := ρ.map_add, map_smul' := hρ }
  refine ⟨inferInstance, ρ', fun _ ↦ rfl, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers τ) ρ' := by
    refine ⟨fun x ↦ ?_, fun z ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
    · obtain ⟨u, hu⟩ := IsLocalization.map_units SW x
      rw [Module.End.isUnit_iff]
      have key : ∀ p : PW, (algebraMap S (Module.End S PW) x) p = (u : SW) • p := fun p ↦ by
        rw [Module.algebraMap_end_apply, hu]; rfl
      refine ⟨fun p q hpq ↦ ?_, fun p ↦ ⟨(↑u⁻¹ : SW) • p, ?_⟩⟩
      · rw [key, key] at hpq
        have := congrArg (fun w ↦ (↑u⁻¹ : SW) • w) hpq
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · rw [key, smul_smul, Units.mul_inv, one_smul]
    · obtain ⟨p, k, hk⟩ := hsurj z
      refine ⟨(p, ⟨τ ^ k, k, rfl⟩), ?_⟩
      change i (τ ^ k) • z = ρ p
      rw [map_pow]
      exact hk
    · have : ρ (x₁ - x₂) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
      obtain ⟨k, hk⟩ := hker _ this
      exact ⟨⟨τ ^ k, k, rfl⟩, by rw [smul_sub] at hk; exact sub_eq_zero.mp hk⟩
  exact IsLocalizedModule.isBaseChange (Submonoid.powers τ) SW ρ'

variable [Module.Finite SU PU] [Module.Projective SU PU] [Module.Finite SV PV]
  [Module.Projective SV PV]

/-- **Matrix presentation of two-chart Čech data** (bookkeeping for Noetherian approximation):
if `P_U`, `P_V` are finite projective over `S_U`, `S_V`, and `ρ_U : P_U → P_W`, `ρ_V : P_V → P_W`
are localizations at `τ ∈ S_U`, `σ ∈ S_V` (in elementary form), with `S_W` the corresponding
localization of `S_U` and of `S_V`, then the Čech data `(ρ_U, ρ_V)` are isomorphic to those of
some `MatData`; in particular a perfect model of the latter gives one of `(ρ_U, ρ_V)`. -/
theorem exists_matData (τ : SU) (σ : SV)
    (hlocU : letI := iU.toRingHom.toAlgebra; IsLocalization.Away τ SW)
    (hlocV : letI := iV.toRingHom.toAlgebra; IsLocalization.Away σ SW)
    (ρU : PU →ₗ[A] PW) (hρU : ∀ (s : SU) (p : PU), ρU (s • p) = iU s • ρU p)
    (hsurjU : ∀ z : PW, ∃ (p : PU) (k : ℕ), iU τ ^ k • z = ρU p)
    (hkerU : ∀ p : PU, ρU p = 0 → ∃ k : ℕ, τ ^ k • p = 0)
    (ρV : PV →ₗ[A] PW) (hρV : ∀ (s : SV) (p : PV), ρV (s • p) = iV s • ρV p)
    (hsurjV : ∀ z : PW, ∃ (p : PV) (k : ℕ), iV σ ^ k • z = ρV p)
    (hkerV : ∀ p : PV, ρV p = 0 → ∃ k : ℕ, σ ^ k • p = 0) :
    ∃ D : MatData iU iV, D.HasPerfectModel → TwoTerm.HasPerfectModel ρU ρV := by
  classical
  letI := iU.toRingHom.toAlgebra
  letI := iV.toRingHom.toAlgebra
  letI : Module SU PW := Module.compHom PW iU.toRingHom
  letI : Module SV PW := Module.compHom PW iV.toRingHom
  obtain ⟨_, ρU', hρU', bcU⟩ := isBaseChange_of_loc iU τ hlocU ρU hρU hsurjU hkerU
  obtain ⟨_, ρV', hρV', bcV⟩ := isBaseChange_of_loc iV σ hlocV ρV hρV hsurjV hkerV
  obtain ⟨n, πU, hπU⟩ := Module.Finite.exists_fin' SU PU
  obtain ⟨sU, hsU⟩ := Module.projective_lifting_property πU LinearMap.id hπU
  obtain ⟨m, πV, hπV⟩ := Module.Finite.exists_fin' SV PV
  obtain ⟨sV, hsV⟩ := Module.projective_lifting_property πV LinearMap.id hπV
  have hsU' : ∀ p, πU (sU p) = p := fun p ↦ LinearMap.congr_fun hsU p
  have hsV' : ∀ p, πV (sV p) = p := fun p ↦ LinearMap.congr_fun hsV p
  -- the `W`-side sections and generators
  let sW : PW →ₗ[SW] (Fin n → SW) := bcU.lift ((Algebra.linearMap SU SW).compLeft (Fin n) ∘ₗ sU)
  let sW' : PW →ₗ[SW] (Fin m → SW) := bcV.lift ((Algebra.linearMap SV SW).compLeft (Fin m) ∘ₗ sV)
  have hsW : ∀ p, sW (ρU p) = iU ∘ sU p := fun p ↦ by
    rw [← hρU' p]
    exact bcU.lift_eq _ p
  have hsW' : ∀ p, sW' (ρV p) = iV ∘ sV p := fun p ↦ by
    rw [← hρV' p]
    exact bcV.lift_eq _ p
  let πW : (Fin n → SW) →ₗ[SW] PW :=
    Fintype.linearCombination SW (fun j ↦ ρU (πU (Pi.single j 1)))
  let πW' : (Fin m → SW) →ₗ[SW] PW :=
    Fintype.linearCombination SW (fun j ↦ ρV (πV (Pi.single j 1)))
  have hπW : ∀ v : Fin n → SU, πW (iU ∘ v) = ρU (πU v) := fun v ↦ by
    conv_rhs => rw [pi_eq_sum_univ' v, map_sum, map_sum]
    simp only [πW, Fintype.linearCombination_apply, map_smul, hρU, Function.comp_apply]
  have hπW' : ∀ v : Fin m → SV, πW' (iV ∘ v) = ρV (πV v) := fun v ↦ by
    conv_rhs => rw [pi_eq_sum_univ' v, map_sum, map_sum]
    simp only [πW', Fintype.linearCombination_apply, map_smul, hρV, Function.comp_apply]
  have hπs : πW ∘ₗ sW = LinearMap.id := bcU.algHom_ext _ _ fun p ↦ by
    change πW (sW (ρU' p)) = ρU' p
    rw [hρU', hsW, hπW, hsU']
  have hπs' : πW' ∘ₗ sW' = LinearMap.id := bcV.algHom_ext _ _ fun p ↦ by
    change πW' (sW' (ρV' p)) = ρV' p
    rw [hρV', hsW', hπW', hsV']
  have hπs1 : ∀ z, πW (sW z) = z := fun z ↦ LinearMap.congr_fun hπs z
  have hπs1' : ∀ z, πW' (sW' z) = z := fun z ↦ LinearMap.congr_fun hπs' z
  -- the matrices
  set eU := LinearMap.toMatrix' (sU ∘ₗ πU) with heU
  set eV := LinearMap.toMatrix' (sV ∘ₗ πV) with heV
  have heUW : eU.map iU = LinearMap.toMatrix' (sW ∘ₗ πW) := by
    ext i j
    simp only [Matrix.map_apply, heU, LinearMap.toMatrix'_apply, LinearMap.coe_comp,
      Function.comp_apply, πW, Fintype.linearCombination_apply_single, one_smul, hsW]
  have heVW : eV.map iV = LinearMap.toMatrix' (sW' ∘ₗ πW') := by
    ext i j
    simp only [Matrix.map_apply, heV, LinearMap.toMatrix'_apply, LinearMap.coe_comp,
      Function.comp_apply, πW', Fintype.linearCombination_apply_single, one_smul, hsW']
  let D : MatData iU iV :=
    { n := n, m := m, eU := eU, eV := eV
      Φ := LinearMap.toMatrix' (sW ∘ₗ πW')
      Ψ := LinearMap.toMatrix' (sW' ∘ₗ πW)
      eU_mul := by
        rw [heU, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hsU']
      eV_mul := by
        rw [heV, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hsV']
      Φ_Ψ := by
        rw [heUW, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hπs1']
      Ψ_Φ := by
        rw [heVW, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hπs1]
      eU_Φ := by
        rw [heUW, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hπs1]
      Φ_eV := by
        rw [heVW, ← LinearMap.toMatrix'_comp]
        congr 1
        exact LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, hπs1'] }
  refine ⟨D, fun H ↦ ?_⟩
  -- the isomorphism of Čech data
  have memU : ∀ p, sU p ∈ D.PU := fun p ↦ by
    rw [mem_fixSub]
    change LinearMap.toMatrix' (sU ∘ₗ πU) *ᵥ sU p = sU p
    rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, hsU']
  have memV : ∀ p, sV p ∈ D.PV := fun p ↦ by
    rw [mem_fixSub]
    change LinearMap.toMatrix' (sV ∘ₗ πV) *ᵥ sV p = sV p
    rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, hsV']
  have memW : ∀ z, sW z ∈ D.PW := fun z ↦ by
    rw [mem_fixSub]
    change eU.map iU *ᵥ sW z = sW z
    rw [heUW, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, hπs1]
  let α : PU ≃ₗ[A] D.PU :=
    { toFun := fun p ↦ ⟨sU p, memU p⟩
      invFun := fun v ↦ πU v.1
      left_inv := hsU'
      right_inv := fun v ↦ Subtype.ext <| by
        have := mem_fixSub.mp v.2
        change sU (πU v.1) = v.1
        rw [← LinearMap.comp_apply, ← LinearMap.toMatrix'_mulVec]
        exact this
      map_add' := fun x y ↦ Subtype.ext (map_add sU x y)
      map_smul' := fun a x ↦ Subtype.ext (sU.map_smul_of_tower a x) }
  let β : PV ≃ₗ[A] D.PV :=
    { toFun := fun p ↦ ⟨sV p, memV p⟩
      invFun := fun v ↦ πV v.1
      left_inv := hsV'
      right_inv := fun v ↦ Subtype.ext <| by
        have := mem_fixSub.mp v.2
        change sV (πV v.1) = v.1
        rw [← LinearMap.comp_apply, ← LinearMap.toMatrix'_mulVec]
        exact this
      map_add' := fun x y ↦ Subtype.ext (map_add sV x y)
      map_smul' := fun a x ↦ Subtype.ext (sV.map_smul_of_tower a x) }
  let γ : PW ≃ₗ[A] D.PW :=
    { toFun := fun z ↦ ⟨sW z, memW z⟩
      invFun := fun v ↦ πW v.1
      left_inv := hπs1
      right_inv := fun v ↦ Subtype.ext <| by
        have := mem_fixSub.mp v.2
        change sW (πW v.1) = v.1
        change eU.map iU *ᵥ v.1 = v.1 at this
        rw [heUW, LinearMap.toMatrix'_mulVec] at this
        exact this
      map_add' := fun x y ↦ Subtype.ext (map_add sW x y)
      map_smul' := fun a x ↦ Subtype.ext (sW.map_smul_of_tower a x) }
  have hf : D.fU ∘ₗ (α : PU →ₗ[A] D.PU) = (γ : PW →ₗ[A] D.PW) ∘ₗ ρU :=
    LinearMap.ext fun p ↦ Subtype.ext (hsW p).symm
  have hg : D.fV ∘ₗ (β : PV →ₗ[A] D.PV) = (γ : PW →ₗ[A] D.PW) ∘ₗ ρV := by
    refine LinearMap.ext fun p ↦ Subtype.ext ?_
    change LinearMap.toMatrix' (sW ∘ₗ πW') *ᵥ (iV ∘ sV p) = sW (ρV p)
    rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, hπW', hsV']
  exact H.of_equiv α.symm β.symm γ.symm (TwoCech.symm_comp_eq α γ hf)
    (TwoCech.symm_comp_eq β γ hg)

end Exists

end CurvesJacobian.ChartMatrix
