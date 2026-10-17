/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbGlue
import CurvesJacobian.Picard.Hilb

/-!
# The Hilbert scheme of points of a curve (Stacks, Tags 0B9A, 0B9C, 0B9I)

Let `C` be a curve over a perfect field `k` (`Belyi.IsCurveOver k C`: smooth of relative
dimension 1, proper, geometrically integral). We show that the Hilbert functor
`Hilb^d_{C/k}` is representable (`isRepresentable_hilbSch_curve`), by Stacks, Proposition
44.2.6 (Tag 0B9A, `CurvesJacobian.isRepresentable_hilbSch`): `C → Spec k` is proper, hence
separated, and every finite set of points of `C` lies in an affine open
(`exists_isAffineOpen_superset`, from `exists_affine_chart_flat`).

We call the representing scheme `hilbCurve k C d` (the scheme `Hilb^d_{C/k}`, which equals the
symmetric power `C^{(d)}`), with structure morphism `hilbCurveHom k C d : hilbCurve k C d ⟶ Spec k`
and universal point `hilbCurveUniv k C d`. Its `T`-points are relative effective Cartier divisors
of degree `d` on `C ×_k T / T` (`hilbCurveEquiv`, combining the representability with
Stacks, Section 44.3, Tag 0B9C, `hilbEquivRelEffCartier`). In particular, for a field extension
`k'/k`, the `k'`-points of `Hilb^d_{C/k}` are the effective Cartier divisors of degree `d` on
`C_{k'}` (part of Stacks, Proposition 44.3.6, Tag 0B9I).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Belyi

universe u

noncomputable section

namespace CurvesJacobian

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]

local notation "Sk" => Spec (CommRingCat.of k)

variable (k)
include k

/-- Every finite set of points of a curve lies in an affine open. -/
theorem IsCurveOver.exists_isAffineOpen_superset {E : Set C} (hE : E.Finite) :
    ∃ U : C.Opens, IsAffineOpen U ∧ E ⊆ U := by
  have := IsCurveOver.isIntegral k C
  obtain ⟨U, hU, -, hEU, -⟩ := exists_affine_chart_flat k C hE.toFinset
  exact ⟨U, hU, fun x hx ↦ hEU x (hE.mem_toFinset.2 hx)⟩

/-- **Stacks, Proposition 44.2.6 (Tag 0B9A)** for a curve: `Hilb^d_{C/k}` is representable. -/
theorem isRepresentable_hilbSch_curve (d : ℕ) : (hilbSch (C ↘ Sk) d).IsRepresentable :=
  isRepresentable_hilbSch fun _ _ hE _ ↦ IsCurveOver.exists_isAffineOpen_superset k C hE

instance (d : ℕ) : (hilbSch (C ↘ Sk) d).IsRepresentable := isRepresentable_hilbSch_curve k C d

/-- The Hilbert scheme of `d` points `Hilb^d_{C/k}` of a curve `C`. -/
def hilbCurve (d : ℕ) : Scheme.{u} := (hilbSch (C ↘ Sk) d).reprX

/-- The universal point of `Hilb^d_{C/k}`. -/
def hilbCurveUniv (d : ℕ) : (hilbSch (C ↘ Sk) d).obj (op (hilbCurve k C d)) :=
  (hilbSch (C ↘ Sk) d).reprx

/-- The structure morphism `Hilb^d_{C/k} ⟶ Spec k`. -/
def hilbCurveHom (d : ℕ) : hilbCurve k C d ⟶ Sk := (hilbCurveUniv k C d).1

/-- Morphisms to `Hilb^d_{C/k}` are `T`-points of the Hilbert functor. -/
def hilbCurveHomEquiv (d : ℕ) (T : Scheme.{u}) :
    (T ⟶ hilbCurve k C d) ≃ (hilbSch (C ↘ Sk) d).obj (op T) :=
  ((hilbSch (C ↘ Sk) d).reprW.app (op T)).toEquiv

lemma hilbCurveHomEquiv_apply (d : ℕ) {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) :
    hilbCurveHomEquiv k C d T a = (hilbSch (C ↘ Sk) d).map a.op (hilbCurveUniv k C d) :=
  (hilbSch (C ↘ Sk) d).reprW_hom_app _ _

lemma hilbCurveHomEquiv_fst (d : ℕ) {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) :
    (hilbCurveHomEquiv k C d T a).1 = a ≫ hilbCurveHom k C d := by
  rw [hilbCurveHomEquiv_apply]
  rfl

/-- **`T`-points of `Hilb^d_{C/k}`**: a morphism `T ⟶ Hilb^d_{C/k}` is the same as a morphism
`g : T ⟶ Spec k` together with a relative effective Cartier divisor of degree `d` on
`C ×_k T / T` (Stacks, Tags 0B9A and 0B9C). -/
def hilbCurveEquiv (d : ℕ) (T : Scheme.{u}) :
    (T ⟶ hilbCurve k C d) ≃ Σ g : T ⟶ Sk,
      {D : RelEffCartier (pullback.snd (C ↘ Sk) g) // ∀ t, D.degree t = d} :=
  (hilbCurveHomEquiv k C d T).trans
    (Equiv.sigmaCongrRight fun g ↦ hilbEquivRelEffCartier d C (Over.mk g))

lemma hilbCurveEquiv_fst (d : ℕ) {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) :
    (hilbCurveEquiv k C d T a).1 = a ≫ hilbCurveHom k C d :=
  hilbCurveHomEquiv_fst k C d a

end CurvesJacobian
