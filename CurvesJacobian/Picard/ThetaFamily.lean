/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Poincare
import CurvesJacobian.Picard.PicDegreeDivisor
import CurvesJacobian.Picard.PicFFieldExt

/-!
# The theta family `P ⊗ 𝒪((g − 1)(σ × J_L))` on `C × J_L` (JAC J2)

For a curve `C/k` with a rational point `σ` and its Jacobian `J_L` with Poincaré bundle `P`:

* `CurvesJacobian.chiCurve_add_zsmul_divisor`: twisting by `n` times a divisor of degree `1`
  raises `χ` by `n` (over a field);
* `CurvesJacobian.sigmaDivJ`: the divisor `σ × J_L` on `C × J_L`, of degree `1`
  (`degree_sigmaDivJ`);
* `CurvesJacobian.thetaFamily`: a line bundle on `C × J_L` of class `[P] + (g − 1) [σ × J_L]`;
* **`CurvesJacobian.chiCurve_thetaFamily`**: its restriction to every fibre has Euler
  characteristic `0` (`P_t` has degree `0`, so `χ(P_t) = 1 − g`).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Belyi

section Twist

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

/-- **Twisting by multiples of a degree one divisor**: on `C ×_k T`, `Γ(T)` a field, for a
relative effective Cartier divisor `D` of degree `1`, `χ(z + n [𝒪(D)]) = χ(z) + n`. -/
theorem chiCurve_add_zsmul_divisor (hF : IsField Γ(T, ⊤))
    (z : (pullback (C ↘ Sk) (T ↘ Sk)).Pic)
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) (hD : D.degree = 1) (n : ℤ) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (z + n • D.picClass)) =
      chiCurve π (T ↘ Sk) (Scheme.Pic.rep z) + n := by
  obtain ⟨t⟩ := nonempty_of_isField hF
  have step : ∀ w : (pullback (C ↘ Sk) (T ↘ Sk)).Pic,
      chiCurve π (T ↘ Sk) (Scheme.Pic.rep (w + D.picClass)) =
        chiCurve π (T ↘ Sk) (Scheme.Pic.rep w) + 1 := fun w ↦ by
    have := chiCurve_add_divisor π hF (Scheme.Pic.rep w) D t
    simpa only [Scheme.Pic.mk_rep, hD, Pi.one_apply, Nat.cast_one] using this
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have e : z + ((n : ℤ) + 1) • D.picClass = z + (n : ℤ) • D.picClass + D.picClass := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, step, ih]
    ring
  | pred n ih =>
    have e : z + (-(n : ℤ) - 1) • D.picClass + D.picClass = z + (-(n : ℤ)) • D.picClass := by
      rw [sub_smul, one_smul]
      abel
    have := step (z + (-(n : ℤ) - 1) • D.picClass)
    rw [e, ih] at this
    linarith

end Twist

section Curve

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "Sk" => Spec (CommRingCat.of k)

/-- **The divisor `σ × J_L`** on `C ×_k J_L`: the image of the section `σ_{J_L}`. -/
def sigmaDivJ : RelEffCartier (pullback.snd (C ↘ Sk) (jacDk C σ hσ Ω).hom) :=
  RelEffCartier.ofSection C _ (secT (C ↘ Sk) σ hσ _) (secT_snd _ σ hσ _)

/-- `σ × J_L` has degree `1` over `J_L`. -/
lemma degree_sigmaDivJ : (sigmaDivJ C σ hσ Ω).degree = 1 :=
  RelEffCartier.degree_ofSection _ _ _ _

/-- The class `[P] + (g − 1) [σ × J_L]` of the theta family. -/
def thetaClass : (pullback (C ↘ Sk) (jacDk C σ hσ Ω).hom).Pic :=
  Scheme.Pic.mk (poincare C σ hσ Ω).L + ((genusNat k C : ℤ) - 1) • (sigmaDivJ C σ hσ Ω).picClass

/-- **The theta family** `P ⊗ 𝒪((g − 1)(σ × J_L))` on `C ×_k J_L`. -/
def thetaFamily : (pullback (C ↘ Sk) (jacDk C σ hσ Ω).hom).Modules :=
  Scheme.Pic.rep (thetaClass C σ hσ Ω)

instance : (thetaFamily C σ hσ Ω).IsInvertible :=
  inferInstanceAs (Scheme.Pic.rep (thetaClass C σ hσ Ω)).IsInvertible

lemma mk_thetaFamily : Scheme.Pic.mk (thetaFamily C σ hσ Ω) = thetaClass C σ hσ Ω :=
  Scheme.Pic.mk_rep _

/-- `χ(L_t)` only depends on the class of `L`: `χ(b^* L) = χ(rep (b^* [L]))`. -/
lemma chiCurve_pullback_eq_rep {T' : Scheme.{u}} (g' : T' ⟶ Sk) {Y : Scheme.{u}}
    (b : pullback (C ↘ Sk) g' ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    chiCurve (curveToP1 k C) g' ((Scheme.Modules.pullback b).obj L) =
      chiCurve (curveToP1 k C) g' (Scheme.Pic.rep (Scheme.Pic.map b (Scheme.Pic.mk L))) := by
  rw [Scheme.Pic.map_mk]
  exact (chiCurve_congr _ g' (Scheme.Pic.rep_mk _).some).symm

/-- **The theta family has Euler characteristic `0` on every fibre**: for every affine `T'`
with `Γ(T')` a field and `h : T' ⟶ J_L`, `χ((1 × h)^* Θ) = 0`. -/
theorem chiCurve_thetaFamily_of_isField {T' : Scheme.{u}} [IsAffine T'] (hF : IsField Γ(T', ⊤))
    (h : T' ⟶ (jacDk C σ hσ Ω).left) :
    chiCurve (curveToP1 k C) (h ≫ (jacDk C σ hσ Ω).hom)
      ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h (jacDk C σ hσ Ω).hom _ rfl)).obj
        (thetaFamily C σ hσ Ω)) = 0 := by
  -- `χ(P_t) = 1 − g`, since the universal class lies in `Pic⁰`
  have hmem : picDeg σ hσ (curveToP1 k C) 0 (jacDk C σ hσ Ω).left
      ⟨(jacDk C σ hσ Ω).hom, univClass C σ hσ Ω⟩ :=
    ((jacDRepresentableBy C σ hσ Ω).homEquiv (𝟙 (jacD C σ hσ Ω))).2
  have h0 := hmem T' hF h
  rw [chiPoint_map] at h0
  have hP : Scheme.Pic.mk (poincare C σ hσ Ω).L = (univClass C σ hσ Ω).1 :=
    congrArg Subtype.val (poincare_cls C σ hσ Ω)
  have h0' : chiCurve (curveToP1 k C) (h ≫ (jacDk C σ hσ Ω).hom)
      (Scheme.Pic.rep (Scheme.Pic.map (bcMap (C ↘ Sk) h (jacDk C σ hσ Ω).hom _ rfl)
        (Scheme.Pic.mk (poincare C σ hσ Ω).L))) = 1 - genusNat k C := by
    rw [hP, ← Scheme.Pic.mk_rep (univClass C σ hσ Ω).1, ← chiCurve_pullback_eq_rep, h0]
    ring
  -- the pullback of `σ × J_L` is `σ × T'`
  have hx : ((jacDk C σ hσ Ω).hom ≫ σ) ≫ (C ↘ Sk) = (jacDk C σ hσ Ω).hom := by
    rw [Category.assoc, hσ, Category.comp_id]
  have hD : Scheme.Pic.map (bcMap (C ↘ Sk) h (jacDk C σ hσ Ω).hom _ rfl)
      (sigmaDivJ C σ hσ Ω).picClass = _ :=
    map_picClass_ptSec C (jacDk C σ hσ Ω).hom ((jacDk C σ hσ Ω).hom ≫ σ) hx h _ rfl
  rw [chiCurve_pullback_eq_rep, mk_thetaFamily, thetaClass, map_add, map_zsmul, hD]
  letI : T'.Over Sk := ⟨h ≫ (jacDk C σ hσ Ω).hom⟩
  have key : ∀ (z : (pullback (C ↘ Sk) (h ≫ (jacDk C σ hσ Ω).hom)).Pic)
      (D : RelEffCartier (pullback.snd (C ↘ Sk) (h ≫ (jacDk C σ hσ Ω).hom))), D.degree = 1 →
      chiCurve (curveToP1 k C) (h ≫ (jacDk C σ hσ Ω).hom)
        (Scheme.Pic.rep (z + ((genusNat k C : ℤ) - 1) • D.picClass)) =
        chiCurve (curveToP1 k C) (h ≫ (jacDk C σ hσ Ω).hom) (Scheme.Pic.rep z) +
          ((genusNat k C : ℤ) - 1) := fun z D hD ↦
    chiCurve_add_zsmul_divisor (curveToP1 k C) (T := T') hF z D hD _
  rw [key _ _ (RelEffCartier.degree_ofSection _ _ _ _), h0']
  ring

/-- **The theta family has Euler characteristic `0` on every fibre** `C_{κ(x)}`,
`x ∈ J_L`. -/
theorem chiCurve_thetaFamily (x : (jacDk C σ hσ Ω).left) :
    chiCurve (curveToP1 k C)
      ((jacDk C σ hσ Ω).left.fromSpecResidueField x ≫ (jacDk C σ hσ Ω).hom)
      ((Scheme.Modules.pullback (bcMap (C ↘ Sk) ((jacDk C σ hσ Ω).left.fromSpecResidueField x)
        (jacDk C σ hσ Ω).hom _ rfl)).obj (thetaFamily C σ hσ Ω)) = 0 :=
  chiCurve_thetaFamily_of_isField C σ hσ Ω (isField_residueField x) _

end Curve

end CurvesJacobian
