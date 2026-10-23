/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticChainE
import CurvesJacobian.Cusp.EllipticSound

/-!
# Elliptic cuspidalisation of `E ∖ {O}` (MR8.7, round 29)

[AbsTopII] Example 3.2 and Corollary 3.3 (iii)(a)
(`Topics in Absolute Anabelian Geometry II.txt` l.4326–4400, l.4481–4491) for IUT's once-punctured
elliptic curve `X = E ∖ {O}` over a number field `K` with `K`-rational `E[2]` and `N = 2`
(the critical points of IUT I Rem 3.1.7 are the `2`-torsion points).

**`ellipticCusp_spec_oncePunctured`**, assuming the rel-isom-DGC over number fields:
* (a) **soundness**: every elliptic candidate of `Π_X` coming from a chain with torsion-free `Δ_U`
  is geometric (`PiChain.IsEllipticType.isGeomCandidate₂`);
* (b) **existence**: some elliptic candidate `Π_U ↠ Π_D ↩ Π_V ↪ Π_X` is, up to continuous
  isomorphisms, the filling `Π_{E ∖ E[2]} ↠ Π_{E ∖ {O}}` with `Π_V = Π_D = Π_X`
  (`exists_ellipticCandidate_oncePunctured`, chain of `EllipticData`);
* (c) **functoriality**: `ellipticCusp` is transported along isomorphisms of cuspidal extensions
  (`ellipticCusp_transport`).
The decomposition groups of the `2`-torsion points are then the images of cuspidal decomposition
groups ([AbsTopII] Cor 3.3 (iii)(c); `exists_map_fillMap_commensurator`, ArithDecomp.lean).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Cor 3.3 (iii)(a) for `X = E ∖ {O}`, `N = 2`** (`E[2]` rational): soundness of
the elliptic candidates (torsion-free `Δ_U`), existence of the elliptic candidate realising
`Π_{E ∖ E[2]} ↠ Π_{E ∖ {O}}`, and functoriality of `ellipticCusp`. -/
theorem ellipticCusp_spec_oncePunctured
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (E : WeierstrassCurve K) [E.IsElliptic] (hE : E.Ψ₂Sq.Splits) :
    (∀ (c : PiChain (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E))) (n : ℕ)
      (hc : c.IsEllipticType n) (t : c.TerminalIso (PiChain.trivial _))
      (_ : IsTorsionFreeSubgroup (c.objN 3 (by have := hc.len_eq; omega)).Delta),
      IsGeomCandidate₂ Ω (hypCurveX E) (compl_XE_nonempty E)
        (PiChain.ellipticCandidate hc t).toCuspCandidate) ∧
    (∃ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
      ∃ (eU : x.PiU ≃ₜ* π₁ᵉᵗ(basePoint Ω (hypCurveV E) (compl_VE_nonempty₂ E) ≫
          baseChangeSpec K Ω Γ(curveE E, VE E)))
        (eD : x.PiD ≃ₜ* π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveV E) (VE_le_XE E)
          (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
            baseChangeSpec K Ω Γ(curveE E, XE E)))
        (eV : x.PiV ≃ₜ* (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi)
        (ψ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveV E) (VE_le_XE E)
            (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
              baseChangeSpec K Ω Γ(curveE E, XE E))),
        (∀ u, eD (x.surj u) = fillPiHom Ω (hypCurveV E) (compl_VE_nonempty₂ E) (VE_le_XE E)
          (compl_XE_nonempty E) (hyperbolic_of_le E (VE_le_XE E) le_rfl) (eU u)) ∧
        (∀ v, eD (x.incl v) = ψ (eV v)) ∧ ∀ v, x.emb v = eV v) ∧
    (∀ {E' : CuspidalExt.{u + 1}}
      (Φ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Iso E'),
      ∀ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
        x.transport Φ ∈ ellipticCusp E') :=
  ⟨fun _ _ hc t htf ↦ hc.isGeomCandidate₂ t hDGC htf,
    exists_ellipticCandidate_oncePunctured Ω E hE, fun Φ _ hx ↦ ellipticCusp_transport Φ hx⟩

end CurvesJacobian.Cusp
