/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.AbelInjLocal
import CurvesJacobian.Picard.AbelMap
import CurvesJacobian.Picard.PicFSub
import CurvesJacobian.Picard.PicLocTriv
import CurvesJacobian.Picard.IdealSheafGlue
import CurvesJacobian.Picard.PicSigmaSheaf

/-!
# Injectivity of the Abel map on the open subfunctor `F` (Stacks, Lemma 44.6.4, Tag 0B9X)

Let `C` be a curve over a perfect field `k` with a rational point `σ` and a finite
`π : C → ℙ¹_k`, and `T` affine. If two relative effective Cartier divisors `D`, `D'` of the same
degree on `C ×_k T` have the same Abel class `𝒪(D) ⊗ f^*σ^*𝒪(D)^{-1}` in `Pic_{C/k,σ}(T)`,
and this class lies in the open subfunctor `F` (`picF`, Stacks, Lemma 44.6.2, Tag 0B9V), then
`D = D'` (`CurvesJacobian.eq_of_abelClass_eq`).

Locally on `T`, the classes `σ^*𝒪(D)`, `σ^*(𝒪(D) - 𝒪(D'))` die and `H⁰` becomes cyclic
(`exists_opens_map_eq_zero`, `exists_basicOpen_H0_cyclic`), so `𝒪(D_U) ≅ 𝒪(D'_U)` with cyclic
`H⁰`, and `RelEffCartier.eq_of_picClass_eq` applies; ideal sheaves are determined locally
(`IdealSheafData.ext_of_comap_eq`).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

section Restr

variable [PerfectField k] [IsCurveOver k C]

/-- The base change of a divisor of degree `d` along `h : T' ⟶ T`. -/
def restrDiv {T T' : Scheme.{u}} {g : T ⟶ Sk} {d : ℕ}
    (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) (hD : ∀ t, D.degree t = d) (h : T' ⟶ T) :
    {E : RelEffCartier (pullback.snd (C ↘ Sk) (h ≫ g)) // ∀ t, E.degree t = d} :=
  hilbEquivRelEffCartier d C (Over.mk (h ≫ g))
    (((hilbEquivRelEffCartier d C (Over.mk g)).symm ⟨D, hD⟩).pullback
      (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g))

lemma restrDiv_ideal {T T' : Scheme.{u}} {g : T ⟶ Sk} {d : ℕ}
    (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) (hD : ∀ t, D.degree t = d) (h : T' ⟶ T) :
    (restrDiv D hD h).1.ideal = D.ideal.comap (bcMap (C ↘ Sk) h g (h ≫ g) rfl) :=
  rfl

end Restr

/-- Isomorphic modules have isomorphic chart `H⁰`. -/
def chartH0Congr {T : Scheme.{u}} (g : T ⟶ Sk) {M M' : (pullback (C ↘ Sk) g).Modules}
    (e : M ≅ M') : chartH0 π g M ≃ₗ[Γ(T, ⊤)] chartH0 π g M' :=
  TwoCech.equivH0 _ _ _ (sectionsIso_res (S := T) e inf_le_left)
    (sectionsIso_res (S := T) e inf_le_right)

variable [PerfectField k] [IsCurveOver k C] [IsFinite π]

/-- The Picard class of the pullback of a representative. -/
lemma mk_pullback_rep {X Y : Scheme.{u}} (φ : X ⟶ Y) (x : Y.Pic) :
    Scheme.Pic.mk ((Scheme.Modules.pullback φ).obj (Scheme.Pic.rep x)) = Scheme.Pic.map φ x :=
  rfl

/-- **Injectivity of the Abel map on `F`** (Stacks, Lemma 44.6.4, Tag 0B9X). -/
theorem eq_of_abelClass_eq {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Sk) {d : ℕ}
    (D D' : RelEffCartier (pullback.snd (C ↘ Sk) g)) (hD : ∀ t, D.degree t = d)
    (hD' : ∀ t, D'.degree t = d)
    (habel : abelClass (C ↘ Sk) σ hσ D = abelClass (C ↘ Sk) σ hσ D')
    (hF : picF σ hσ π T ⟨g, abelClass (C ↘ Sk) σ hσ D'⟩) : D = D' := by
  refine RelEffCartier.ext_ideal ?_
  set δ := D.picClass - D'.picClass
  have hδ : δ = Scheme.Pic.map (pullback.snd (C ↘ Sk) g)
      (Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) δ) := by
    have := congrArg Subtype.val habel
    rw [coe_abelClass, coe_abelClass] at this
    simp only [δ, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub] at this
    exact this
  -- the `F`-condition on `T` itself
  have hFC : FCond π g (Scheme.Pic.rep
      (abelClass (C ↘ Sk) σ hσ D' : picSigmaGrp (C ↘ Sk) σ hσ g).1) := by
    have := hF T (𝟙 T)
    rwa [op_id, Functor.map_id_apply] at this
  letI : T.Over Sk := ⟨g⟩
  have key : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      D.ideal.comap (bcMap (C ↘ Sk) U.ι g (U.ι ≫ g) rfl) =
        D'.ideal.comap (bcMap (C ↘ Sk) U.ι g (U.ι ≫ g) rfl) := by
    intro t
    obtain ⟨V₁, htV₁, hV₁⟩ := Scheme.Pic.exists_opens_map_eq_zero
      (Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) δ) t
    obtain ⟨V₂, htV₂, hV₂⟩ := Scheme.Pic.exists_opens_map_eq_zero
      (Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) D'.picClass) t
    haveI : Scheme.Modules.IsInvertible (X := pullback (C ↘ Sk) (T ↘ Sk)) (Scheme.Pic.rep
        (abelClass (C ↘ Sk) σ hσ D' : picSigmaGrp (C ↘ Sk) σ hσ g).1) :=
      inferInstanceAs (Scheme.Pic.rep
        (abelClass (C ↘ Sk) σ hσ D' : picSigmaGrp (C ↘ Sk) σ hσ g).1).IsInvertible
    obtain ⟨r, htr, hcyc⟩ := exists_basicOpen_H0_cyclic π (T := T) (Scheme.Pic.rep
      (abelClass (C ↘ Sk) σ hσ D' : picSigmaGrp (C ↘ Sk) σ hσ g).1) hFC t
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, htU₀, hU₀le⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (show t ∈ (V₁ ⊓ V₂ ⊓ T.basicOpen r : T.Opens) from ⟨⟨htV₁, htV₂⟩, htr⟩)
      (V₁ ⊓ V₂ ⊓ T.basicOpen r).2
    let U : T.Opens := U₀
    haveI : IsAffine U := hU₀
    have hrange : Set.range U.ι ⊆ (V₁ ⊓ V₂ ⊓ T.basicOpen r : T.Opens) := by
      rintro _ ⟨u, rfl⟩
      exact hU₀le u.2
    refine ⟨U, htU₀, ?_⟩
    let φ := bcMap (C ↘ Sk) U.ι g (U.ι ≫ g) rfl
    let E := restrDiv D hD U.ι
    let E' := restrDiv D' hD' U.ι
    have hE := RelEffCartier.map_picClass_of_ideal_eq D E.1 φ (restrDiv_ideal D hD U.ι)
    have hE' := RelEffCartier.map_picClass_of_ideal_eq D' E'.1 φ (restrDiv_ideal D' hD' U.ι)
    -- `Pic.map φ ∘ Pic.map f = Pic.map f_U ∘ Pic.map U.ι`
    have hφf : ∀ n : T.Pic, Scheme.Pic.map φ (Scheme.Pic.map (pullback.snd (C ↘ Sk) g) n) =
        Scheme.Pic.map (pullback.snd (C ↘ Sk) (U.ι ≫ g)) (Scheme.Pic.map U.ι n) := fun n ↦ by
      rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← AddMonoidHom.comp_apply,
        ← Scheme.Pic.map_comp, bcMap_snd]
    have hpic : E.1.picClass = E'.1.picClass := by
      rw [← hE, ← hE', ← sub_eq_zero, ← map_sub]
      change Scheme.Pic.map φ δ = 0
      rw [hδ, hφf, hV₁ U.ι (hrange.trans fun _ h ↦ h.1.1), map_zero]
    -- the representative of the Abel class of `D'` restricts to `𝒪(D'_U)`
    letI : U.toScheme.Over T := ⟨U.ι⟩
    obtain ⟨s, hs⟩ := hcyc U (hrange.trans fun _ h ↦ h.2)
    have hiso : Scheme.Pic.mk ((Scheme.Modules.pullback φ).obj (Scheme.Pic.rep
        (abelClass (C ↘ Sk) σ hσ D' : picSigmaGrp (C ↘ Sk) σ hσ g).1)) =
        Scheme.Pic.mk E'.1.lineBundle := by
      rw [mk_pullback_rep, coe_abelClass, map_sub, hφf, hV₂ U.ι (hrange.trans fun _ h ↦ h.1.2),
        map_zero, sub_zero, hE']
      rfl
    obtain ⟨e⟩ := Scheme.Pic.mk_eq_mk_iff.mp hiso
    have := RelEffCartier.eq_of_picClass_eq π (U.ι ≫ g) E.1 E'.1 hpic
      (chartH0Congr π (U.ι ≫ g) e s) (span_singleton_equiv_eq_top _ hs)
    exact congrArg RelEffCartier.ideal this
  choose U htU hU using key
  exact Scheme.IdealSheafData.ext_of_comap_eq
    (fun t ↦ bcMap (C ↘ Sk) (U t).ι g ((U t).ι ≫ g) rfl)
    (fun y ↦ ⟨pullback.snd (C ↘ Sk) g y, by
      rw [← Scheme.Hom.coe_opensRange, opensRange_bcMap, Scheme.Opens.opensRange_ι]
      exact htU (pullback.snd (C ↘ Sk) g y)⟩) hU

end CurvesJacobian
