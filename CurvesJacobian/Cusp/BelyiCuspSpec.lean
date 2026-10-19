/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelCuspIndep
import CurvesJacobian.Cusp.Cor38Exists
import CurvesJacobian.Cusp.Cor38Elliptic
import CurvesJacobian.Cusp.CandidateCover

/-!
# The Belyi cuspidalisation `belyiCusp` of `Π_X` (MR8, round 28)

`belyiCusp E` (belyi, `Belyi/Anabelian/BelyiChain.lean`) is the set of all candidates
`Π_U ↠ Π_V ↪ Π` produced by Belyi-type `Π`-chains with a terminal isomorphism to the trivial
chain; it is defined from the cuspidal extension `E` alone. For `E = (Π_X ↠ G_K)` the arithmetic
fundamental group of an affine hyperbolic curve `X` over a number field `K` of strictly Belyi type
with a Galois cover `V → X` (`S : GaloisBelyiInput CX M`), we show
(**`CurvesJacobian.Cusp.belyiCusp_spec`**, [AbsTopII] Cor 3.7 (a), (b),
`Topics in Absolute Anabelian Geometry II.txt` l.4735–4775, and Cor 3.8, l.4794–4842):

* (a) **soundness** (`belyiCusp_sound`): every candidate is geometric (`IsGeomCandidate₂`): it is
  `Π_Y ↠ Π_{Y'} ↪ Π_X` for a filling `Y = (X̄_Y, U_Y) ⊆ Y' = (X̄_Y, U')` of a hyperbolic curve over
  a number field `M' ⊇ K` and a finite étale `q : Spec Γ(U') ⟶ Spec Γ(X)` over `Spec K`;
* (b) **completeness** (`belyiCusp_complete`): for every nonempty open `U_X ⊆ X` some candidate
  has normal `Π_V ⊆ Π_X`, the lifting property of automorphisms of `Π_V` to `Π_U`, and
  `Π_U ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation;
* (c) **functoriality**: `belyiCusp` is transported along isomorphisms `Π_X ≅ E'` of cuspidal
  extensions (`belyiCusp_transport`), and every isomorphism `Π_X ≅ Π_{X₂}` lifts to the
  cuspidalisations (`cor38_exists`), uniquely up to inner automorphisms from the kernel
  (`cor38_unique`).

The only input is the rel-isom-DGC over all number fields (`hDGC`); (a) uses it also through the
model independence of cusps (`modelCuspIndep₂`, ModelCuspIndep.lean).
`belyiCusp_spec_oncePunctured` is the case `X = E ∖ {O}` with `K`-rational `E[2]`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (CX : HypCurve K)
  (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **A geometric cuspidalisation candidate** of `Π_X`: `Π_U ↠ Π_V ↪ Π_X` is
`Π_Y ↠ Π_{Y'} ↪ Π_X` for a hyperbolic curve `Y = (X̄_Y, U_Y)` over a number field `M' ⊇ K`
(`ι : Π_Y ≅ Π_U`), a filling `U_Y ⊆ U'` (`ε : Π_{Y'} ≅ Π_V`, `Π_U ↠ Π_V` is `fillPiHom`), and a
finite étale `q : Spec Γ(U') ⟶ Spec Γ(X)` over `Spec K` inducing `Π_{Y'} ≅ Π_V ↪ Π_X` up to a
change of base point. -/
def IsGeomCandidate₂ (x : CuspCandidate (arithmeticExt Ω CX hcX)) : Prop :=
  ∃ (M' : Type u) (_ : Field M') (_ : NumberField M') (_ : Algebra K M') (_ : Algebra M' Ω)
    (_ : IsScalarTower K M' Ω) (_ : FiniteDimensional K M') (_ : Algebra.IsAlgebraic M' Ω)
    (Y : HypCurve M') (hY : (Y.U : Set Y.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M' Ω Γ(Y.Xbar, Y.U)) ≃ₜ* x.PiU)
    (U' : Y.Xbar.Opens) (h : Y.U ≤ U') (hc' : (U' : Set Y.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral M' Y.Xbar
      2 < 2 * Anabelian.curveGenus M' Y.Xbar + cuspDegree M' Y.Xbar U')
    (ε : π₁ᵉᵗ(basePoint Ω (fillCurve Y h hyp) hc' ≫ baseChangeSpec M' Ω Γ(Y.Xbar, U')) ≃ₜ*
      x.PiV),
    (∀ σ, x.surj (ι σ) = ε (fillPiHom Ω Y hY h hc' hyp σ)) ∧
    ∃ (q : Spec Γ(Y.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U)) (_ : IsFiniteEtale q),
      IsConjInduced q (fun τ ↦ x.emb (ε τ) :
        π₁ᵉᵗ(basePoint Ω (fillCurve Y h hyp) hc' ≫ baseChangeSpec M' Ω Γ(Y.Xbar, U')) →
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))) ∧
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
        Spec.map (CommRingCat.ofHom (algebraMap M' Γ(Y.Xbar, U'))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K M'))

/-- **[AbsTopII] Cor 3.7 (a), soundness of `belyiCusp`**: every Belyi cuspidalisation candidate
of `Π_X` is geometric. The only input is the rel-isom-DGC over number fields (`hDGC`). -/
theorem belyiCusp_sound (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {x : CuspCandidate (arithmeticExt Ω CX hcX)}
    (hx : x ∈ belyiCusp (arithmeticExt Ω CX hcX)) : IsGeomCandidate₂ Ω CX hcX x := by
  obtain ⟨c, l, r, hc, t, m, hm, rfl⟩ := hx
  obtain ⟨D, hD, U', h, hc', hyp, ε, hε, q, hqfe, hq, hqK⟩ :=
    hc.exists_cover_fill' t hDGC m hm
  exact ⟨D.M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, D.Y, D.hY, continuousMulEquivOfBijective D.ι ⟨D.inj, hD⟩,
    U', h, hc', hyp, ε, hε, q, hqfe, hq, hqK⟩

variable {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω]
  [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]

/-- **[AbsTopII] Cor 3.7 (a), (b), completeness of `belyiCusp`**: for a strictly Belyi input with
Galois `V → X` and every nonempty open `U_X ⊆ X`, some Belyi candidate `Π_U ↠ Π_V ↪ Π_X` has normal
`Π_V`, lifts automorphisms of `Π_V` induced by `Π_X` to `Π_U`, and `Π_U ≅ Π_V ×_{Π_X} Π_{U_X}`
over `Π_X` up to conjugation by some `k`, with automorphisms of `Π_V ×_{Π_X} Π_{U_X}` over `Π_X`
inner from `ker(Π_{U_X} ↠ Π_X)`. -/
theorem belyiCusp_complete (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (S : GaloisBelyiInput CX M) (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hne : (UX : Set CX.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω CX hcX) ≅
      fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)) :
    ∃ x ∈ belyiCusp (arithmeticExt Ω CX hcX),
      x.emb.toMonoidHom.range.Normal ∧
      (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
        (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
          ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u)) ∧
      ∃ (k : (arithmeticExt Ω CX hcX).Pi)
        (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀)),
        (∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
        ∀ β : x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀) ≃ₜ*
            x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀),
          (∀ z, cor38Fill Ω CX hcX UX hUX hne α₀ (β z) = cor38Fill Ω CX hcX UX hUX hne α₀ z) →
          ∃ n : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi,
            cor38Fill Ω CX hcX UX hUX hne α₀ n = 1 ∧
              ∀ z, (β z : (arithmeticExt Ω (subCurve CX UX hUX hne)
                (compl_nonempty_of_le hUX hcX)).Pi) = n * z * n⁻¹ := by
  obtain ⟨c, l, r, hc, t, -, m, hm, hN, hL, H⟩ :=
    exists_belyiChain_cor38₂ Ω CX hcX UX hUX hne α₀ hDGC S
  exact ⟨PiChain.belyiCandidate hc t m hm, ⟨c, l, r, hc, t, m, hm, rfl⟩, hN, hL, H⟩

/-- **`belyiCusp` of `Π_X`** ([AbsTopII] Cor 3.7 (a), (b), Cor 3.8): for `X` of strictly Belyi
type with a Galois cover `V → X` (`S`), assuming the rel-isom-DGC over number fields (`hDGC`):
(a) every candidate in `belyiCusp (Π_X)` is geometric, `Π_Y ↠ Π_{Y'} ↪ Π_X`;
(b) for every nonempty open `U_X ⊆ X` some candidate recovers `Π_V ×_{Π_X} Π_{U_X} ↠ Π_V` (normal
`Π_V`, lifting property, `Π_U ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation);
(c) `belyiCusp` is functorial in isomorphisms `Π_X ≅ E'` of cuspidal extensions;
(d) every isomorphism `Φ : Π_X ≅ Π_{X₂}` to an affine hyperbolic curve over a number field lifts
to `φ_U : Π_{U_X} ≅ Π_{U_{X₂}}` for some nonempty open `U_{X₂} ⊆ X₂` (Cor 3.8, existence);
(e) such lifts are unique up to inner automorphisms from `ker(Π_{U_X} ↠ Π_X)` (Cor 3.8,
uniqueness). -/
theorem belyiCusp_spec (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (S : GaloisBelyiInput CX M) :
    (∀ x ∈ belyiCusp (arithmeticExt Ω CX hcX), IsGeomCandidate₂ Ω CX hcX x) ∧
    (∀ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω CX hcX) ≅
        fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)),
      ∃ x ∈ belyiCusp (arithmeticExt Ω CX hcX),
        x.emb.toMonoidHom.range.Normal ∧
        (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
          (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
            ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u)) ∧
        ∃ (k : (arithmeticExt Ω CX hcX).Pi)
          (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀)),
          ∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
    (∀ {E' : CuspidalExt.{u + 1}} (Φ : (arithmeticExt Ω CX hcX).Iso E'),
      ∀ x ∈ belyiCusp (arithmeticExt Ω CX hcX), x.transport Φ ∈ belyiCusp E') ∧
    (∀ {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
      [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] (CX₂ : HypCurve K₂)
      (hcX₂ : (CX₂.U : Set CX₂.Xbar)ᶜ.Nonempty)
      (Φ : (arithmeticExt Ω CX hcX).Iso (arithmeticExt Ω₂ CX₂ hcX₂))
      (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω CX hcX) ≅
        fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)),
      ∃ (UX₂ : CX₂.Xbar.Opens) (hUX₂ : UX₂ ≤ CX₂.U) (hne₂ : (UX₂ : Set CX₂.Xbar).Nonempty),
        ∀ α₂ : fiber (basePoint Ω₂ CX₂ hcX₂) ≅
            fiber (fillPoint Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)
              hUX₂),
          ∃ φU : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ≃ₜ*
              (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)).Pi,
            ∀ e, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (φU e) =
              Φ.pi (cor38Fill Ω CX hcX UX hUX hne α₀ e)) ∧
    (∀ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω CX hcX) ≅
        fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))
      {P : Type u} [Group P] [TopologicalSpace P]
      (φ₁ φ₂ : P ≃ₜ* (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi),
      (∀ p, cor38Fill Ω CX hcX UX hUX hne α₀ (φ₂ p) = cor38Fill Ω CX hcX UX hUX hne α₀ (φ₁ p)) →
      ∃ n ∈ (cor38Fill Ω CX hcX UX hUX hne α₀).ker, ∀ p, φ₂ p = n * φ₁ p * n⁻¹) := by
  refine ⟨fun x hx ↦ belyiCusp_sound Ω CX hcX hDGC hx, fun UX hUX hne α₀ ↦ ?_,
    fun Φ x hx ↦ belyiCusp_transport Φ hx, ?_, ?_⟩
  · obtain ⟨x, hx, hN, hL, k, J, hJ, -⟩ := belyiCusp_complete Ω CX hcX hDGC S UX hUX hne α₀
    exact ⟨x, hx, hN, hL, k, J, hJ⟩
  · intro K₂ _ _ Ω₂ _ _ _ _ _ CX₂ hcX₂ Φ UX hUX hne α₀
    exact cor38_exists hDGC Ω Ω₂ CX hcX S CX₂ hcX₂ Φ UX hUX hne α₀
  · intro UX hUX hne α₀ P _ _ φ₁ φ₂ hφ
    exact cor38_unique Ω CX hcX UX hUX hne α₀ (hDGC K) φ₁ φ₂ hφ

/-- **`belyiCusp_spec` for `X = E ∖ {O}`** with `K`-rational `E[2]` (`hE`; IUT I Def 3.1 (b)
assumes the `2·3`-torsion rational), via its Galois Belyi input `nonempty_galoisBelyiInput`. -/
theorem belyiCusp_spec_oncePunctured
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {E : WeierstrassCurve K} [E.IsElliptic] (hE : E.Ψ₂Sq.Splits) :
    (∀ x ∈ belyiCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
      IsGeomCandidate₂ Ω (hypCurveX E) (compl_XE_nonempty E) x) ∧
    (∀ (UX : (hypCurveX E).Xbar.Opens) (hUX : UX ≤ (hypCurveX E).U)
      (hne : (UX : Set (hypCurveX E).Xbar).Nonempty)
      (α₀ : fiber (basePoint Ω (hypCurveX E) (compl_XE_nonempty E)) ≅
        fiber (fillPoint Ω (subCurve (hypCurveX E) UX hUX hne)
          (compl_nonempty_of_le hUX (compl_XE_nonempty E)) hUX)),
      ∃ x ∈ belyiCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
        x.emb.toMonoidHom.range.Normal ∧
        (∀ (B : x.PiV ≃ₜ* x.PiV)
            (g : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi),
          (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
            ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u)) ∧
        ∃ (k : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi)
          (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap
            (cor38Fill Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne α₀)),
          ∀ u, cor38Fill Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne α₀ (J u) =
            k * x.emb (x.surj u) * k⁻¹) ∧
    (∀ {E' : CuspidalExt.{u + 1}}
      (Φ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Iso E'),
      ∀ x ∈ belyiCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
        x.transport Φ ∈ belyiCusp E') := by
  haveI : CharZero K := inferInstance
  obtain ⟨S⟩ := nonempty_galoisBelyiInput E hE
  obtain ⟨h1, h2, h3, -⟩ := belyiCusp_spec (M := K) Ω (hypCurveX E) (compl_XE_nonempty E) hDGC S
  exact ⟨h1, h2, h3⟩

end CurvesJacobian.Cusp
