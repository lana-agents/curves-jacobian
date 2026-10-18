/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.BelyiCoverEtale
import CurvesJacobian.Cusp.BelyiCover

/-!
# `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}` for the open `ℙ¹ ∖ {0, 1, ∞}` of the curve `ℙ¹`

`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia` is stated for a curve `X` with an open
`U ≅ Spec k[t, 1/(t(t-1))]` compatibly with the geometric generic points. For `X = ℙ¹_k` and
`U = ℙ¹ ∖ {0, 1, ∞}` both are constructed here: the chart is the restriction of `𝟙 : ℙ¹ ⟶ ℙ¹`
over the punctured line (`CurvesJacobian.Cusp.cuspCover`, an isomorphism), and the generic
points match as soon as `eL` sends the coordinate function of `ℙ¹` to `t`
(`CurvesJacobian.Cusp.genericL_cuspCover`).

Main result: `CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_P1`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve
open Pi1.Orbifold

noncomputable section

namespace CurvesJacobian.Cusp

variable (k : Type) [Field k]

/-- `𝟙 : ℙ¹ ⟶ ℙ¹`. -/
abbrev idP1 : P1 k ⟶ P1 k := 𝟙 (P1 k)

instance nonempty_cuspOpen_id : Nonempty (cuspOpen (idP1 k)) := by
  refine ⟨⟨genericPoint (P1 k), ?_⟩⟩
  change (idP1 k).base (genericPoint (P1 k)) ∈ (puncturedι k).opensRange
  rw [opensRange_puncturedι]
  exact Belyi.genericPoint_mem_puncturedLine k

lemma id_base_genericPoint_ne_infty :
    (idP1 k).base (genericPoint (P1 k)) ≠ P1.infty k :=
  fun h ↦ P1.infty_ne_genericPoint k h.symm

instance isIso_cuspCover_id : IsIso (cuspCover (idP1 k)) := by
  unfold cuspCover
  infer_instance

lemma lineGen_congr {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {s s' : Ω}
    (hs : Transcendental k s) (hs' : Transcendental k s') (h : s = s') :
    lineGen hs = lineGen hs' := by
  subst h
  rfl

variable {k} {Ω : Type} [IsAlgClosed k] [CharZero k] [Countable k] [Field Ω] [Algebra k Ω]
  [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  (eL : (P1 k).functionField ≃+* D.L) (hH : D.H ≤ D.HL)

/-- **`π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}` with `cuspInertia` at the cusps ↦ conjugates of `Iⱼ`**, for
the open `ℙ¹ ∖ {0, 1, ∞}` of the curve `ℙ¹_k` (`k` countable algebraically closed of
characteristic `0`), Galois data `D` with `L = k(t)` (every automorphism of `Ω / k(t)` lies in
`H`) and `eL : K(ℙ¹) ≃ L` sending the coordinate function to `t`. -/
theorem exists_continuousMulEquiv_cuspInertia_P1
    (hk : ∀ c : k, ((eL (algebraMap k (P1 k).functionField c) : D.L) : Ω) = algebraMap k Ω c)
    (hτ : ((eL (coordFun (idP1 k) (id_base_genericPoint_ne_infty k)) : D.L) : Ω) = t)
    (hHtop : ∀ σ : Ω ≃ₐ[K₀ k t] Ω, σ ∈ D.H) :
    ∃ Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D (P1 k) eL (cuspOpen (idP1 k))) ≃ₜ*
        Pi1.ProfiniteSurfaceGroup 0 3,
      ∀ (j : Fin 3) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
        W.valuation (cuspCoord j t) < 1 →
          ∃ σ, (cuspInertia D (P1 k) eL hH (cuspOpen (idP1 k)) W).map
            ((Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D (P1 k) eL (cuspOpen (idP1 k))) →*
              Pi1.ProfiniteSurfaceGroup 0 3).comp (MulAut.conj σ).toMonoidHom) =
            Pi1.SurfaceGroup.inertia j := by
  have hη := id_base_genericPoint_ne_infty k
  have hfk : idP1 k ≫ (P1 k ↘ Spec (CommRingCat.of k)) = P1 k ↘ Spec (CommRingCat.of k) :=
    Category.id_comp _
  have ht : Transcendental k (belyiT D eL (idP1 k) hη) := by
    change Transcendental k ((eL (coordFun (idP1 k) hη) : D.L) : Ω)
    rw [hτ]
    exact D.transcendental
  have he := genericL_cuspCover D eL (idP1 k) hη hk hfk ht
  rw [lineGen_congr ht D.transcendental hτ] at he
  exact exists_continuousMulEquiv_cuspInertia eL hH D.transcendental hHtop
    (cuspOpen (idP1 k)) (asIso (cuspCover (idP1 k))) he

end CurvesJacobian.Cusp
