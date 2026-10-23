/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticChainFill
import CurvesJacobian.Cusp.FillCover
import CurvesJacobian.Cusp.BelyiCuspSpec

/-!
# Elliptic cuspidalisation candidates are geometric (MR8.7, round 29)

[AbsTopII] Corollary 3.3 (iii)(a) (`Topics in Absolute Anabelian Geometry II.txt` l.4481–4491):
an elliptic-type `Π`-chain with a terminal isomorphism to the trivial chain produces
`Π_U ↠ Π_D ↩ Π_V ↪ Π` and the cuspidalisation candidate `Π_U ×_{Π_D} Π_V ↠ Π_V ↪ Π`
(`EllCandidate.toCuspCandidate`). For the arithmetic fundamental group `Π_X ↠ G_K` of an affine
hyperbolic curve over a number field, assuming the rel-isom-DGC over number fields:

* **`PiChain.IsEllipticType.isGeomCandidate₂`**: if `Δ` of `Π_U = Π_3` is torsion-free, the
  candidate is geometric (`IsGeomCandidate₂`): `Π_Z ↠ Π_{Z'} ↪ Π_X` for a filling `Z ⊆ Z'` of a
  hyperbolic curve over a number field and a finite étale `q : Z' ⟶ X` over `Spec K`.

Proof: the run of the chain is a filling `Y ⊆ Y'` (`IsEllipticType.exists_candidate_fill_toG`);
the open subgroup `ε⁻¹(Π_V) ⊆ Π_{Y'}` gives a finite étale cover `Z' → Y'` with the filling
`Z = Z' ×_{Y'} Y ⊆ Z'` (`exists_fill_cover`), so `Π_U ×_{Π_D} Π_V ≅ Π_Z` and `Π_V ≅ Π_{Z'}`
(`EllCandidate.exists_fibre_equiv`); `Π_{Z'} ≅ Π_V ↪ Π_X` is induced by a finite étale map by the
rel-isom-DGC (`exists_isConjInduced_cover_of_range'`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace Belyi.Anabelian.EllCandidate

open CurvesJacobian.Cusp

variable {E : CuspidalExt.{u}} (x : EllCandidate E)

/-- **The fibre product of a surjection with an open subgroup, realised by maps of groups.**
Let `ι : P_Y ≅ Π_U` and `ε : P_{Y'} ≅ Π_D` identify `Π_U ↠ Π_D` with `f_Y : P_Y → P_{Y'}`, and let
`κ : P_Z ↪ P_Y`, `ε_Z : P_{Z'} ↪ P_{Y'}` have images `f_Y⁻¹(O)` and `O = ε⁻¹(Π_V)`, compatibly
with `f_Z : P_Z → P_{Z'}`. Then `P_Z ≅ Π_U ×_{Π_D} Π_V` and `P_{Z'} ≅ Π_V` compatibly with the
projections. -/
theorem exists_fibre_equiv {PY PY' PZ PZ' : Type*} [Group PY] [Group PY'] [Group PZ]
    [TopologicalSpace PZ] [IsTopologicalGroup PZ] [CompactSpace PZ] [Group PZ']
    [TopologicalSpace PZ'] [IsTopologicalGroup PZ'] [CompactSpace PZ'] [TopologicalSpace PY]
    [TopologicalSpace PY'] (ι : PY ≃ₜ* x.PiU) (ε : PY' ≃ₜ* x.PiD) (fY : PY →* PY')
    (hι : ∀ σ, x.surj (ι σ) = ε (fY σ)) (κ : PZ →ₜ* PY) (hκ : Function.Injective κ)
    (hκr : ∀ y, (∃ σ, κ σ = y) ↔ ∃ v, x.incl v = ε (fY y))
    (εZ : PZ' →ₜ* PY') (hεZ : Function.Injective εZ)
    (hεZr : ∀ w, (∃ τ, εZ τ = w) ↔ ∃ v, x.incl v = ε w)
    (fZ : PZ →ₜ* PZ') (hf : ∀ σ, fY (κ σ) = εZ (fZ σ)) :
    ∃ (ιg : PZ ≃ₜ* x.fibre) (εg : PZ' ≃ₜ* x.PiV),
      (∀ σ, x.fibreProj (ιg σ) = εg (fZ σ)) ∧ ∀ τ, x.incl (εg τ) = ε (εZ τ) := by
  have hmem : ∀ τ, ((ContinuousMonoidHom.toContinuousMonoidHom ε).comp εZ) τ ∈
      Set.range x.incl := fun τ ↦ by
    obtain ⟨v, hv⟩ := (hεZr (εZ τ)).1 ⟨τ, rfl⟩
    exact ⟨v, hv⟩
  let εg₀ : PZ' →ₜ* x.PiV := liftInj₂ x.incl x.incl_injective _ hmem
  have hεg₀ : ∀ τ, x.incl (εg₀ τ) = ε (εZ τ) := liftInj₂_spec x.incl x.incl_injective _ hmem
  have hbij : Function.Bijective εg₀ := by
    refine ⟨fun a b hab ↦ hεZ (ε.injective ?_), fun v ↦ ?_⟩
    · rw [← hεg₀, ← hεg₀, hab]
    · obtain ⟨τ, hτ⟩ := (hεZr (ε.symm (x.incl v))).2 ⟨v, (ε.apply_symm_apply _).symm⟩
      refine ⟨τ, x.incl_injective ?_⟩
      rw [hεg₀, hτ, ε.apply_symm_apply]
  let εg := continuousMulEquivOfBijective εg₀ hbij
  have hεg : ∀ τ, x.incl (εg τ) = ε (εZ τ) := hεg₀
  have hpt : ∀ σ, x.surj (ι (κ σ)) = x.incl (εg (fZ σ)) := fun σ ↦ by
    rw [hι, hf, hεg]
  let ιg₀ : PZ →ₜ* x.fibre :=
    { toFun := fun σ ↦ ⟨(ι (κ σ), εg (fZ σ)), hpt σ⟩
      map_one' := Subtype.ext (Prod.ext (by simp only [map_one]; rfl) (by simp only [map_one]; rfl))
      map_mul' := fun a b ↦ Subtype.ext (Prod.ext (by simp only [map_mul]; rfl)
        (by simp only [map_mul]; rfl))
      continuous_toFun := continuous_induced_rng.2 (Continuous.prodMk
        (ι.continuous.comp κ.continuous) (εg.continuous.comp fZ.continuous)) }
  have hι₀ : ∀ σ, x.fibreFst (ιg₀ σ) = ι (κ σ) := fun _ ↦ rfl
  have hbij' : Function.Bijective ιg₀ := by
    refine ⟨fun a b hab ↦ ?_, fun p ↦ ?_⟩
    · have h1 := congrArg x.fibreFst hab
      rw [hι₀, hι₀] at h1
      exact hκ (ι.injective h1)
    · obtain ⟨⟨u, v⟩, hp⟩ := p
      have hu : x.surj u = x.incl v := hp
      obtain ⟨σ, hσ⟩ := (hκr (ι.symm u)).2 ⟨v, by rw [hu.symm, ← hι, ι.apply_symm_apply]⟩
      refine ⟨σ, Subtype.ext (Prod.ext ?_ ?_)⟩
      · change ι (κ σ) = u
        rw [hσ, ι.apply_symm_apply]
      · change εg (fZ σ) = v
        refine x.incl_injective ?_
        rw [← hpt, hσ, ι.apply_symm_apply, hu]
  exact ⟨continuousMulEquivOfBijective ιg₀ hbij', εg, fun _ ↦ rfl, hεg⟩

end Belyi.Anabelian.EllCandidate

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **An elliptic candidate whose surjection is a filling of curves is geometric.** Let
`x = (Π_U ↠ Π_D ↩ Π_V ↪ Π_X)` with `Π_U ↠ Π_D` identified (`ι`, `ε`) with the filling
`Π_Y ↠ Π_{Y'}` of a curve over a number field `M ⊇ K`, `ε` over `res : G_M → G_K` up to
conjugation for some `toGD : Π_D → G_K` with `pr ∘ emb = conj ∘ toGD ∘ incl`. Then the candidate
`Π_U ×_{Π_D} Π_V ↠ Π_V ↪ Π_X` is geometric (rel-isom-DGC over number fields). -/
theorem _root_.Belyi.Anabelian.EllCandidate.isGeomCandidate₂_of_fill
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (x : EllCandidate (arithmeticExt Ω CX hcX)) {M : Type u} [Field M] [NumberField M]
    [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω] [FiniteDimensional K M]
    [Algebra.IsAlgebraic M Ω] (Y : HypCurve M) (hY : (Y.U : Set Y.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) ≃ₜ* x.PiU)
    {U' : Y.Xbar.Opens} (h : Y.U ≤ U') (hc' : (U' : Set Y.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral M Y.Xbar
      2 < 2 * Anabelian.curveGenus M Y.Xbar + cuspDegree M Y.Xbar U')
    (ε : π₁ᵉᵗ(basePoint Ω (fillCurve Y h hyp) hc' ≫ baseChangeSpec M Ω Γ(Y.Xbar, U')) ≃ₜ*
      x.PiD)
    (hε : ∀ σ, x.surj (ι σ) = ε (fillPiHom Ω Y hY h hc' hyp σ))
    (toGD : x.PiD →* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (g₀ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hg₀ : ∀ τ, toGD (ε τ) = g₀ * resGal K Ω M (projGk Ω (fillCurve Y h hyp) hc' τ) * g₀⁻¹)
    (g : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hg : ∀ v, projGk Ω CX hcX (x.emb v) = g * toGD (x.incl v) * g⁻¹) :
    IsGeomCandidate₂ Ω CX hcX x.toCuspCandidate := by
  let O : Subgroup π₁ᵉᵗ(basePoint Ω (fillCurve Y h hyp) hc' ≫ baseChangeSpec M Ω Γ(Y.Xbar, U')) :=
    (x.incl : x.PiV →* x.PiD).range.comap (ε : _ →* x.PiD)
  have hOm : ∀ w, w ∈ O ↔ ∃ v, x.incl v = ε w := fun w ↦ Iff.rfl
  have hO : IsOpen (O : Set π₁ᵉᵗ(basePoint Ω (fillCurve Y h hyp) hc' ≫
      baseChangeSpec M Ω Γ(Y.Xbar, U'))) :=
    x.isOpen_range_incl.preimage ε.continuous
  obtain ⟨M₁, _, _, _, _, _, _, _, Z, hZ, UZ, hZU, hcZ, hypZ, κ, εZ, hκ, hκr, hεZ, hεZr, hfill,
    g₂, hg₂⟩ := exists_fill_cover Ω Y hY h hc' hyp O hO
  have hκr' : ∀ y, (∃ σ, κ σ = y) ↔ ∃ v, x.incl v = ε (fillPiHom Ω Y hY h hc' hyp y) := by
    intro y
    have e := congrArg (y ∈ ·) hκr
    simp only [MonoidHom.mem_range, Subgroup.mem_comap, eq_iff_iff] at e
    exact e.trans (hOm _)
  have hεZr' : ∀ w, (∃ τ, εZ τ = w) ↔ ∃ v, x.incl v = ε w := by
    intro w
    have e := congrArg (w ∈ ·) hεZr
    simp only [MonoidHom.mem_range, eq_iff_iff] at e
    exact e.trans (hOm _)
  obtain ⟨ιg, εg, hproj, hincl⟩ := x.exists_fibre_equiv ι ε
    (fillPiHom Ω Y hY h hc' hyp).toMonoidHom hε κ hκ hκr' εZ hεZ hεZr'
    (fillPiHom Ω Z hZ hZU hcZ hypZ) hfill
  letI : Algebra K M₁ := ((algebraMap M M₁).comp (algebraMap K M)).toAlgebra
  haveI : IsScalarTower K M M₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower K M₁ Ω := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap K Ω a = algebraMap M₁ Ω (algebraMap M M₁ (algebraMap K M a))
    rw [← IsScalarTower.algebraMap_apply M M₁ Ω, ← IsScalarTower.algebraMap_apply K M Ω]
  haveI : FiniteDimensional K M₁ := Module.Finite.trans M M₁
  haveI := isIntegral_specSections CX hcX
  have hOX : IsOpen (x.emb.toMonoidHom.range : Set (arithmeticExt Ω CX hcX).Pi) :=
    x.isOpen_range_emb
  obtain ⟨Yc, p, hp, ζ, hζ, hconn, hrange⟩ := exists_isFiniteEtale_range_eq_of_open
    (basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) ⟨_, hOX⟩
  have hres : ∀ s, resGal K Ω M (resGal M Ω M₁ s) = resGal K Ω M₁ s :=
    resGal_galoisMap M M₁
  have hf : ∀ τ, projGk Ω CX hcX (x.emb (εg τ)) = (g * g₀ * resGal K Ω M g₂) *
      resGal K Ω M₁ (projGk Ω (fillCurve Z hZU hypZ) hcZ τ) * (g * g₀ * resGal K Ω M g₂)⁻¹ := by
    intro τ
    rw [hg, hincl, hg₀, hg₂, map_mul, map_mul, map_inv, hres]
    group
  have hrange' : (fundamentalGroupMap p hζ).toMonoidHom.range = x.emb.toMonoidHom.range := hrange
  obtain ⟨q, hq, hIC, hK⟩ := exists_isConjInduced_cover_of_range' (fillCurve Z hZU hypZ) hcZ
    (hDGC M₁) εg x.emb x.emb_injective p ζ hζ hrange' _ hf
  exact ⟨M₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Z, hZ, ιg, UZ, hZU, hcZ, hypZ, εg, hproj, q, hq, hIC, hK⟩

variable {c : PiChain (arithmeticExt Ω CX hcX)} {n : ℕ}

/-- **[AbsTopII] Cor 3.3 (iii)(a), soundness: elliptic cuspidalisation candidates are
geometric.** For an elliptic-type chain of `Π_X ↠ G_K` with a terminal isomorphism to the trivial
chain and torsion-free `Δ_U` (`U = Π_3`), the candidate `Π_U ×_{Π_D} Π_V ↠ Π_V ↪ Π_X` is
`Π_Z ↠ Π_{Z'} ↪ Π_X` for a filling `Z ⊆ Z'` of a hyperbolic curve over a number field and a finite
étale `q : Z' ⟶ X` over `Spec K` (assuming the rel-isom-DGC over number fields). -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.isGeomCandidate₂ (hc : c.IsEllipticType n)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (htf : IsTorsionFreeSubgroup (c.objN 3 (by have := hc.len_eq; omega)).Delta) :
    IsGeomCandidate₂ Ω CX hcX (PiChain.ellipticCandidate hc t).toCuspCandidate := by
  have hlen := hc.len_eq
  obtain ⟨D, hD, U', h, hc', hyp, ε, hε, g₀, hg₀⟩ := hc.exists_candidate_fill_toG t hDGC htf
  obtain ⟨g, hg⟩ : ∃ g : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))), ∀ y,
      (arithmeticExt Ω CX hcX).pr (PiChain.ellipticEmb hc t y) =
        g * toGk (c.objN (n + 4) (by omega)) y * g⁻¹ := PiChain.exists_pr_ellipticEmb hc t
  have hg' : ∀ v, projGk Ω CX hcX ((PiChain.ellipticCandidate hc t).emb v) =
      g * toGk (c.objN (n + 3) (by omega)) ((PiChain.ellipticCandidate hc t).incl v) * g⁻¹ :=
    fun v ↦ (hg v).trans (congrArg (fun z ↦ g * z * g⁻¹)
      (ChainObj.toG_apply_of_compat (PiChain.compat_ellipticIncl hc) v).symm)
  exact (PiChain.ellipticCandidate hc t).isGeomCandidate₂_of_fill hDGC D.Y D.hY
    (continuousMulEquivOfBijective D.ι ⟨D.inj, hD⟩) h hc' hyp ε hε _ g₀ hg₀ g hg'

end CurvesJacobian.Cusp
