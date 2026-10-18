/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDegreeAdd
import CurvesJacobian.Picard.AbelMap

/-!
# Points of `Pic^d` over a field are Abel classes for `d ≥ g`

Let `C` be a curve of genus `g` over a perfect field `k` with a rational point `σ`, and `T` an
affine `k`-scheme whose ring of global sections is a field.

* `CurvesJacobian.exists_relEffCartier_of_chiCurve_pos`: an invertible sheaf `L` on `C_T` with
  `χ(L) > 0` has a nonzero global section, hence is `𝒪(D)` for a relative effective Cartier
  divisor `D` (its zero scheme, `exists_relEffCartier_of_ne_zero`).
* **`CurvesJacobian.exists_abelClass_eq_of_isField`**: for `d ≥ g` every `T`-point of
  `Pic^d_{C/k,σ}` is the Abel class of a relative effective Cartier divisor on `C_T`, since its
  Euler characteristic is `d + 1 − g > 0`. This is the surjectivity of the Abel map
  `Hilb^d → Pic^d` on field valued points (Stacks, Lemma 44.6.7, Tag 0BA0, uses it for
  `d ≥ 2g − 1`), an input for the properness of `Pic^d`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

/-- **Sheaves with positive Euler characteristic over a field are effective.** -/
theorem exists_relEffCartier_of_chiCurve_pos {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Sk)
    (hF : IsField Γ(T, ⊤)) (L : (pullback (C ↘ Sk) g).Modules) [L.IsInvertible]
    (h : 0 < chiCurve π g L) :
    ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) g), D.picClass = Scheme.Pic.mk L := by
  letI : T.Over Sk := ⟨g⟩
  haveI : Nontrivial Γ(T, ⊤) := ⟨hF.exists_pair_ne⟩
  haveI : (show (pullback (C ↘ Sk) (T ↘ Sk)).Modules from L).IsInvertible := by assumption
  have h0 : 0 < Module.finrank Γ(T, ⊤) (cechModH0 T L
      ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) := by
    unfold chiCurve at h
    omega
  obtain ⟨x, hx⟩ : ∃ x : cechModH0 T L
      ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1), x ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    haveI : Subsingleton (cechModH0 T L
        ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
        ((pullback.fst (C ↘ Sk) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) :=
      ⟨fun a b ↦ (hne a).trans (hne b).symm⟩
    rw [Module.finrank_zero_of_subsingleton] at h0
    exact lt_irrefl 0 h0
  let e := globalSectionsEquivH0 T L (chartOf_sup π (T ↘ Sk))
  refine exists_relEffCartier_of_ne_zero π hF L (e.symm x) ?_
  intro h1
  apply hx
  rw [← e.apply_symm_apply x, h1]
  exact e.map_zero

variable (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- **For `d ≥ g`, field valued points of `Pic^d` are Abel classes.** -/
theorem exists_abelClass_eq_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤))
    (d : ℤ) (hd : (genusNat k C : ℤ) ≤ d) (x : (sigmaG G).obj (op T))
    (hx : picDeg σ hσ π d T x) :
    ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) x.1),
      abelClass (C ↘ Sk) σ hσ D = (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1) := by
  have hχ := hx T hF (𝟙 T)
  have hid : (sigmaG G).map (𝟙 T).op x = x := by
    rw [op_id, Functor.map_id_apply]
  rw [hid] at hχ
  have hpos : 0 < chiCurve π x.1
      (Scheme.Pic.rep (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1).1) := by
    have h1 : chiPoint σ hσ π x = d + 1 - genusNat k C := hχ
    unfold chiPoint at h1
    omega
  obtain ⟨D, hD⟩ := exists_relEffCartier_of_chiCurve_pos π x.1 hF _ hpos
  have hmem : Scheme.Pic.map (secT (C ↘ Sk) σ hσ x.1)
      (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1).1 = 0 := (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1).2
  refine ⟨D, Subtype.ext ?_⟩
  rw [coe_abelClass, hD, Scheme.Pic.mk_rep, hmem, map_zero, sub_zero]

end CurvesJacobian
