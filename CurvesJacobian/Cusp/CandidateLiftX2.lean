/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CandidateCover
import CurvesJacobian.Cusp.CandidateDescent
import CurvesJacobian.Cusp.GaloisOfNormal
import CurvesJacobian.Cusp.FillAutUnique

/-!
# Deck transformations of a geometric candidate lift to `Π_U` (MR8, round 28, step (N2))

Let `x = (Π_U ↠ Π_V ↪ Π_X)` be a cuspidalisation candidate which is geometric in the sense of
`PiChain.IsBelyiType.exists_cover_fill`: `Π_U ≅ Π_Y`, `Π_V ≅ Π_{Y'}` for a filling `Y ⊆ Y'`, with
`Π_U ↠ Π_V` the filling map and `Π_V ↪ Π_X` induced (up to a change of base point) by a finite
étale `q : Y' ⟶ X`. If the candidate has the **lifting property** (every automorphism `B` of
`Π_V` with `emb ∘ B = conj(g) ∘ emb` for some `g ∈ Π_X` lifts along `Π_U ↠ Π_V`), then every
automorphism of `Π_{Y'}` induced by a deck transformation of `q` lifts along
`fillPiHom : Π_Y ↠ Π_{Y'}` (**`CurvesJacobian.Cusp.hlift_of_lifts`**): this is the hypothesis
`hlift` of `CurvesJacobian.Cusp.exists_descent_of_lift`. If `emb` has normal image, `q` is
Galois (**`CurvesJacobian.Cusp.isGalois_of_isConjInduced_normal`**).

Both properties are stable under transport of candidates along isomorphisms of cuspidal
extensions (`CuspCandidate.lifts_transport`, `CuspCandidate.normal_range_emb_transport`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section Transport

variable {PU PV P P' : Type*} [Group PU] [Group PV] [Group P] [Group P'] [TopologicalSpace PU]
  [TopologicalSpace PV]

/-- The lifting property passes along an isomorphism of the ambient group. -/
lemma lifts_of_mulEquiv (surj : PU →* PV) (emb : PV →* P) (Φ : P ≃* P')
    (hL : ∀ (B : PV ≃ₜ* PV) (g : P), (∀ v, emb (B v) = g * emb v * g⁻¹) →
      ∃ ψ : PU ≃ₜ* PU, ∀ u, surj (ψ u) = B (surj u))
    (B : PV ≃ₜ* PV) (g : P') (hB : ∀ v, Φ (emb (B v)) = g * Φ (emb v) * g⁻¹) :
    ∃ ψ : PU ≃ₜ* PU, ∀ u, surj (ψ u) = B (surj u) :=
  hL B (Φ.symm g) fun v ↦ Φ.injective (by rw [hB, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply])

end Transport

section Generic

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω]
  [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}
  {C : HypCurve M} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty} {U' : C.Xbar.Opens}
  {h : C.U ≤ U'} {hc' : (U' : Set C.Xbar)ᶜ.Nonempty}
  {hyp : haveI := IsCurveOver.isIntegral M C.Xbar
      2 < 2 * Anabelian.curveGenus M C.Xbar + cuspDegree M C.Xbar U'}
  {PU PV : Type*} [Group PU] [Group PV] [TopologicalSpace PU] [TopologicalSpace PV]
  [IsTopologicalGroup PU] [T2Space PU]

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] [NumberField M]
  [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω] [IsTopologicalGroup PU] [T2Space PU] in
/-- A deck transformation `σ'` of `q` and an automorphism `A` it induces give
`emb ∘ ε ∘ A = conj(g) ∘ emb ∘ ε`. -/
lemma exists_conj_of_deck {X' Y' : Scheme.{u}} {q : Y' ⟶ X'} {y : Spec (.of Ω) ⟶ Y'}
    {x : Spec (.of Ω) ⟶ X'} {φ : π₁ᵉᵗ(y) → π₁ᵉᵗ(x)} (hq : IsConjInduced q φ)
    (σ' : Y' ≅ Y') (hσ' : σ'.hom ≫ q = q) (A : π₁ᵉᵗ(y) → π₁ᵉᵗ(y))
    (hA : IsConjInduced σ'.hom A) : ∃ g : π₁ᵉᵗ(x), ∀ τ, φ (A τ) = g * φ τ * g⁻¹ :=
  ((hA.comp hq).congr_hom hσ').exists_conj_eq hq

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Algebra K M] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω] [IsTopologicalGroup PU] in
/-- **Lifting deck transformations** (the hypothesis `hlift` of `exists_descent_of_lift`) from
the lifting property of a geometric candidate `Π_U ↠ Π_V ↪ Π_X`. -/
theorem hlift_of_lifts
    (surj : PU →* PV) (emb : PV →* π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))
    (hL : ∀ (B : PV ≃ₜ* PV) (g : π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))),
      (∀ v, emb (B v) = g * emb v * g⁻¹) → ∃ ψ : PU ≃ₜ* PU, ∀ u, surj (ψ u) = B (surj u))
    (ι : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) →ₜ* PU)
    (hι : Function.Bijective ι)
    (ε : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ≃ₜ* PV)
    (hε : ∀ σ, surj (ι σ) = ε (fillPiHom Ω C hc h hc' hyp σ))
    (q : Spec Γ(C.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U))
    (hq : IsConjInduced q (fun τ ↦ emb (ε τ) :
      π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) →
        π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) :
    ∀ (σ' : Spec Γ(C.Xbar, U') ≅ Spec Γ(C.Xbar, U')), σ'.hom ≫ q = q →
      ∀ (A : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ≃ₜ*
        π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U'))),
        IsConjInduced σ'.hom A →
        ∃ ψ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ*
          π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)),
          ∀ s, fillPiHom Ω C hc h hc' hyp (ψ s) = A (fillPiHom Ω C hc h hc' hyp s) := by
  intro σ' hσ' A hA
  obtain ⟨g, hg⟩ := exists_conj_of_deck hq σ' hσ' A hA
  let B : PV ≃ₜ* PV := ε.symm.trans (A.trans ε)
  have hB : ∀ v, emb (B v) = g * emb v * g⁻¹ := fun v ↦ by
    have := hg (ε.symm v)
    rwa [ContinuousMulEquiv.apply_symm_apply] at this
  obtain ⟨ψ', hψ'⟩ := hL B g hB
  let ιe := continuousMulEquivOfBijective ι hι
  refine ⟨ιe.trans (ψ'.trans ιe.symm), fun s ↦ ε.injective ?_⟩
  have e1 : ι (ιe.symm (ψ' (ι s))) = ψ' (ι s) := ιe.apply_symm_apply _
  change ε (fillPiHom Ω C hc h hc' hyp (ιe.symm (ψ' (ι s)))) = _
  rw [← hε, e1, hψ', hε]
  change ε (A (ε.symm (ε _))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

omit [NumberField K] [Algebra K M] [IsScalarTower K M Ω] [IsTopologicalGroup PU] [T2Space PU] in
include hyp in
/-- **Uniqueness hypothesis of the extension lemma from a geometric model**: if
`H = N.comap f ⊆ E` is identified with `Π_C` (`J`) so that `f ∘ J` is
`conj(k) ∘ e ∘ fillPiHom` for an injective `e`, then (by the DGC over `M`) every continuous
automorphism `β` of `H` with `f ∘ β = f` is conjugation by an element of `ker f`. -/
theorem exists_conj_of_model_fill (hDGC : RelIsomDGC M) {E P : Type*} [Group E] [Group P]
    [TopologicalSpace E] {f : E →* P} {N : Subgroup P}
    (J : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ* N.comap f)
    (e : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) →* P)
    (he : Function.Injective e) (k : P)
    (hJ : ∀ y, f (J y) = k * e (fillPiHom Ω C hc h hc' hyp y) * k⁻¹)
    (β : N.comap f ≃ₜ* N.comap f) (hβ : ∀ x, f (β x) = f x) :
    ∃ n : E, f n = 1 ∧ ∀ x, (β x : E) = n * x * n⁻¹ := by
  let β' := J.trans (β.trans J.symm)
  have hfill : ∀ σ, fillMap Ω C hc h (β' σ) = 1 * fillMap Ω C hc h σ * 1⁻¹ := fun σ ↦ by
    rw [one_mul, inv_one, mul_one]
    have e1 : f (J (β' σ)) = f (J σ) := by
      change f (J (J.symm (β (J σ)))) = _
      rw [ContinuousMulEquiv.apply_symm_apply, hβ]
    rw [hJ, hJ] at e1
    have e2 := congrArg (fillTransport Ω C hc h hc' hyp)
      (he (mul_left_cancel (mul_right_cancel e1)))
    rwa [fillTransport_fillPiHom, fillTransport_fillPiHom] at e2
  obtain ⟨n', hn', hβ'⟩ := exists_eq_conj_of_fillMap Ω C hc h hc' hyp hDGC β' 1 hfill
  refine ⟨J n', ?_, fun x ↦ ?_⟩
  · rw [hJ]
    have e3 : fillPiHom Ω C hc h hc' hyp n' = 1 := (fillTransport Ω C hc h hc' hyp).injective
      ((fillTransport_fillPiHom Ω C hc h hc' hyp n').trans (hn'.trans (map_one _).symm))
    rw [e3, map_one, mul_one, mul_inv_cancel]
  · have e4 : ((J (β' (J.symm x)) : N.comap f) : E) =
        ((J (n' * J.symm x * n'⁻¹) : N.comap f) : E) := by rw [hβ' (J.symm x)]
    have e5 : J (β' (J.symm x)) = β x := by
      change J (J.symm (β (J (J.symm x)))) = _
      rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
    rw [e5, map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at e4
    exact e4

end Generic

section CandTransport

variable {E E' : CuspidalExt.{u}} (Φ : E.Iso E') {c : PiChain E} {l r : ℕ}

/-- **The candidates of a transported Belyi chain are the transported candidates.** -/
theorem PiChain.belyiCandidate_transport (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial E)) (m : ℕ) (hm : m ≤ r) :
    PiChain.belyiCandidate (hc.transport (Φ := Φ)) t.transportTrivial m hm =
      (PiChain.belyiCandidate hc t m hm).transport Φ := by
  simp only [PiChain.belyiCandidate, CuspCandidate.transport]
  congr 1
  · ext y
    simp only [ContinuousMonoidHom.comp_toFun]
    rw [PiChain.runHom_transport]
    rfl
  · ext y
    have hq := DFunLike.congr_fun (ElemOp.quotHom_transport (Φ := Φ)
      (c.opN (l + r + 3) (by have := hc.len_eq; omega)) hc.2.2.2.2.2.2) y
    simp only [PiChain.belyiEmb, ContinuousMonoidHom.comp_toFun]
    erw [hq, PiChain.objCongr_transport]
    rfl

/-- The image of the embedding of a transported candidate is normal if it was. -/
theorem CuspCandidate.normal_range_emb_transport (x : CuspCandidate E)
    (hN : x.emb.toMonoidHom.range.Normal) : (x.transport Φ).emb.toMonoidHom.range.Normal := by
  have e : (x.transport Φ).emb.toMonoidHom.range =
      x.emb.toMonoidHom.range.map Φ.pi.toMulEquiv.toMonoidHom := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨x.emb v, ⟨v, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  rw [e]
  exact Subgroup.Normal.map hN _ Φ.pi.surjective

end CandTransport

section Galois

variable {X' Y' : Scheme.{u}} [ConnectedSpace X'] [ConnectedSpace Y'] {Ω : Type u} [Field Ω]
  [IsSepClosed Ω]

/-- **A finite étale `q` inducing a map with normal image is Galois.** -/
theorem isGalois_of_isConjInduced_normal {q : Y' ⟶ X'} [IsFiniteEtale q]
    {y : Spec (.of Ω) ⟶ Y'} {x : Spec (.of Ω) ⟶ X'} {PV : Type*} [Group PV]
    (ε : π₁ᵉᵗ(y) →* PV) (hε : Function.Surjective ε) (emb : PV →* π₁ᵉᵗ(x))
    (hN : emb.range.Normal) (hq : IsConjInduced q (fun τ ↦ emb (ε τ))) :
    IsGalois (coverObj q) := by
  obtain ⟨γ, hγ⟩ := hq
  have hγ' : ∀ τ, (autContinuousMulEquivOfIso γ).symm (emb (ε τ)) = fundamentalGroupMap q rfl τ :=
    fun τ ↦ by
      have e := hγ τ
      change emb (ε τ) = _ at e
      rw [e, ContinuousMulEquiv.symm_apply_apply]
  refine isGalois_coverObj_of_normal_range y rfl ?_
  have e : (fundamentalGroupMap q rfl).toMonoidHom.range =
      emb.range.map (autContinuousMulEquivOfIso γ).symm.toMulEquiv.toMonoidHom := by
    ext z
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨emb (ε τ), ⟨ε τ, rfl⟩, hγ' τ⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      obtain ⟨τ, rfl⟩ := hε v
      exact ⟨τ, (hγ' τ).symm⟩
  rw [e]
  exact Subgroup.Normal.map hN _ (autContinuousMulEquivOfIso γ).symm.surjective

end Galois

end CurvesJacobian.Cusp
