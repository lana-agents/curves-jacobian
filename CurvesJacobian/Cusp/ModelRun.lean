/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelChain

/-!
# The candidate of a Belyi-type chain is a filling of curves (MR8, round 26, step (2))

For a Belyi-type chain `c` of `Π_X ↠ G_K` with a terminal isomorphism, every object of the final
run `Π_U = Π_{l+3+(r-m)} ⇝ … ⇝ Π_V` of `•`'s has torsion-free `Δ`, hence a **full** geometric model
(`PiChain.IsBelyiType.exists_full_geomModel`). Starting from a full model `(Y, ι : Π_Y ≅ Π_U)` the
operations `•` of the run are fillings of single cusps of `Y` (`GeomModel.exists_fill_of_decusp`,
`GeomModel.decusp`; a full model stays full), so (`PiChain.IsBelyiType.exists_candidate_fill`):

  the surjection `Π_U ↠ Π_V` of the candidate `belyiCandidate hc t m hm` is, up to the
  isomorphisms `ι : Π_Y ≅ Π_U` and `ε : Π_{Y'} ≅ Π_V`, the canonical map `fillPiHom : Π_Y ↠ Π_{Y'}`
  of the filling `Y = (X̄, U_Y) ⊆ Y' = (X̄, U')` of one curve over a number field `M`,

assuming the rel-isom-DGC over number fields and that `Π_V` has an infinite cusp image (`hV`, see
`ChainObj.HasInfCusp`).

* `ChainObj.Compat.comp`, `PiChain.compat_runHom`: the composite of a run of `•`'s is compatible
  with the rigidifying homomorphisms.
* `GeomModel.ofFill`: from a full model `D` of `A`, a surjection `f : A ↠ B` compatible with the
  rigidifying homomorphisms and an isomorphism `ι' : Π_{(X̄_Y, U')} ≅ B` such that `ι'⁻¹ ∘ f ∘ ι` is
  induced by `Spec Γ(U_Y) ⟶ Spec Γ(U')`, the full model `((X̄_Y, U'), ι')` of `B`.
* `ElemOp.exists_full_fill`: a `•` from a full model is the filling of a single cusp.
* `PiChain.exists_run_fill`: the same for a run of `•`'s (by induction, `IsConjInduced.comp`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace Belyi.Anabelian

variable {E : CuspidalExt.{u}}

/-- **Composition of compatible homomorphisms.** -/
theorem ChainObj.Compat.comp {A B C : ChainObj E} {f : A.grp →ₜ* B.grp} {g : B.grp →ₜ* C.grp}
    (hf : Compat A B f) (hg : Compat B C g) : Compat A C (g.comp f) := by
  obtain ⟨H₁, hA, hB, h₁⟩ := hf
  obtain ⟨H₂, hB', hC, h₂⟩ := hg
  refine ⟨H₁ ⊓ H₂, fun x hx ↦ hA hx.1, fun x hx ↦ hC hx.2, fun h hh ↦ ?_⟩
  change g (f (A.rho ⟨h, hA hh.1⟩)) = C.rho ⟨h, hC hh.2⟩
  rw [h₁ h hh.1]
  exact h₂ h hh.2

/-- The operation homomorphism of a `•` is compatible with the rigidifying homomorphisms. -/
theorem ElemOp.compat_decuspHom {A B : ChainObj E} :
    ∀ (o : ElemOp A B) (h : o.kind = .decusp), ChainObj.Compat A B (o.decuspHom h)
  | .decusp _ _ _ _ _ _ compat, _ => compat
  | .cover .., h => absurd h (by simp [ElemOp.kind])
  | .quot .., h => absurd h (by simp [ElemOp.kind])
  | .deorb .., h => absurd h (by simp [ElemOp.kind])

/-- **The composite of a run of `•`'s is compatible with the rigidifying homomorphisms.** -/
theorem PiChain.compat_runHom (c : PiChain E) (i : ℕ) : ∀ (r : ℕ) (h : i + r ≤ c.len)
    (hrun : c.IsDecuspRun i r h), ChainObj.Compat _ _ (c.runHom i r h hrun)
  | 0, _, _ => ⟨_, le_rfl, le_rfl, fun _ _ ↦ rfl⟩
  | r + 1, h, hrun => (c.compat_runHom i r (by omega) fun s hs ↦ hrun s (by omega)).comp
      (ElemOp.compat_decuspHom _ _)

/-- The identification `Π_a = Π_b` (`PiChain.objCongr`) is compatible with the rigidifying
homomorphisms. -/
theorem PiChain.compat_objCongr (c : PiChain E) {a b : ℕ} (hab : a = b) (ha : a ≤ c.len)
    (hb : b ≤ c.len) : ChainObj.Compat _ _
      (ContinuousMonoidHom.toContinuousMonoidHom (c.objCongr hab ha hb)) := by
  subst hab
  exact ⟨_, le_rfl, le_rfl, fun _ _ ↦ rfl⟩

/-- The operation homomorphism of a `⋎` is compatible with the rigidifying homomorphisms. -/
theorem ElemOp.compat_quotHom {A B : ChainObj E} :
    ∀ (o : ElemOp A B) (h : o.kind = .quot), ChainObj.Compat A B (o.quotHom h)
  | .quot _ _ _ compat, _ => compat
  | .cover .., h => absurd h (by simp [ElemOp.kind])
  | .decusp .., h => absurd h (by simp [ElemOp.kind])
  | .deorb .., h => absurd h (by simp [ElemOp.kind])

/-- **The embedding `Π_V ↪ Π` of a Belyi-type chain lies over `G` up to conjugation.** -/
theorem PiChain.exists_pr_belyiEmb {c : PiChain E} {l r : ℕ} (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial E)) :
    ∃ g : E.G, ∀ y, E.pr (PiChain.belyiEmb hc t y) =
      g * (c.objN (l + r + 3) (by have := hc.len_eq; omega)).toG y * g⁻¹ := by
  have hlen := hc.len_eq
  obtain ⟨g, hg⟩ := t.over
  refine ⟨g, fun y ↦ ?_⟩
  have h1 := ChainObj.toG_apply_of_compat (ElemOp.compat_quotHom
    (c.opN (l + r + 3) (by omega)) hc.2.2.2.2.2.2) y
  have h2 := ChainObj.toG_apply_of_compat (c.compat_objCongr (a := l + r + 3 + 1) (b := c.len)
    (by omega) (by omega) le_rfl) ((c.opN (l + r + 3) (by omega)).quotHom hc.2.2.2.2.2.2 y)
  have h3 := hg (c.objCongr (a := l + r + 3 + 1) (b := c.len) (by omega) (by omega) le_rfl
    ((c.opN (l + r + 3) (by omega)).quotHom hc.2.2.2.2.2.2 y))
  exact h3.trans (congrArg (fun z ↦ g * z * g⁻¹) (h2.trans h1))

end Belyi.Anabelian

namespace CurvesJacobian.Cusp

open Belyi.Anabelian.ChainObj

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

namespace GeomModel

variable {A B : ChainObj (arithmeticExt Ω CX hcX)} (D : GeomModel Ω CX hcX A)
  (hfull : Function.Surjective D.ι) (f : A.grp →ₜ* B.grp) (hf : ChainObj.Compat A B f)
  {U' : D.Y.Xbar.Opens} (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
    2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
  (ι' : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
    baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* B.grp)
  (hrel : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg D.M h).toRingHom))
    (fun σ ↦ ι'.symm (f (D.ι σ))))

/-- `ψ = ι'⁻¹ ∘ f ∘ ι : Π_Y → Π_{Y'}`. -/
def fillPsi : D.Pi →* π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
    baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) :=
  ι'.symm.toMulEquiv.toMonoidHom.comp ((f : A.grp →* B.grp).comp (D.ι : D.Pi →* A.grp))

lemma fillPsi_apply (σ : D.Pi) : D.fillPsi f h hc' hyp ι' σ = ι'.symm (f (D.ι σ)) := rfl

include hrel in
lemma fillPsi_surjective : Function.Surjective (D.fillPsi f h hc' hyp ι') :=
  surjective_of_conjInduced_fill Ω D.Y D.hY h hc' hyp hrel

include hf hrel in
/-- `ι'` lies over `res : G_M → G_K` up to conjugation. -/
theorem exists_toGk_ofFill : ∃ g₀ : π₁ᵉᵗ(sK), ∀ τ,
    toGk B (ι' τ) = g₀ * resGal K Ω D.M (projGk Ω (fillCurve D.Y h hyp) hc' τ) * g₀⁻¹ := by
  have hF : Spec.map (CommRingCat.ofHom (resAlg D.M h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, U'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K D.M)) =
      Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, D.Y.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K D.M)) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (specMap_resAlg_structure _ _))
  obtain ⟨c, hc⟩ := exists_resGal_projGk_conj_of_conjInduced Ω (K := K) (K₁ := D.M) (K₂ := D.M)
    (C₁ := D.Y) (C₂ := fillCurve D.Y h hyp) D.hY hc' _ hF hrel
  refine ⟨D.g₀ * c⁻¹, fun τ ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := D.fillPsi_surjective f h hc' hyp ι' hrel τ
  have h1 : toGk B (ι' (D.fillPsi f h hc' hyp ι' γ)) = toGk A (D.ι γ) := by
    rw [fillPsi_apply, ContinuousMulEquiv.apply_symm_apply]
    exact ChainObj.toG_apply_of_compat hf (D.ι γ)
  refine (h1.trans (D.toG_ι γ)).trans ?_
  exact Eq.trans (by group) (congrArg (fun z ↦ (D.g₀ * c⁻¹) * z * (D.g₀ * c⁻¹)⁻¹) (hc γ).symm)

include hfull in
/-- `ι'⁻¹(f(S)) = ψ(ι⁻¹(S))` for a full model. -/
lemma comap_ofFill_map (S : Subgroup A.grp) :
    (S.map (f : A.grp →* B.grp)).comap ι'.toMulEquiv.toMonoidHom =
      (S.comap (D.ι : D.Pi →* A.grp)).map (D.fillPsi f h hc' hyp ι') := by
  ext y
  constructor
  · rintro ⟨s, hs, hsy⟩
    obtain ⟨σ, rfl⟩ := hfull s
    refine ⟨σ, hs, ?_⟩
    change ι'.symm (f (D.ι σ)) = y
    have hsy' : f (D.ι σ) = ι' y := hsy
    rw [hsy', ContinuousMulEquiv.symm_apply_apply]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨D.ι σ, hσ, ?_⟩
    change f (D.ι σ) = ι' (ι'.symm (f (D.ι σ)))
    rw [ContinuousMulEquiv.apply_symm_apply]

include hfull hf hrel in
/-- Cusp compatibility of `ι'`. -/
theorem ofFill_cusp : ∀ I ∈ (arithmeticExt Ω CX hcX).cusps,
    ((B.image I).comap ι'.toMulEquiv.toMonoidHom).Commensurable ⊥ ∨
      ∃ J ∈ arithCusps Ω (fillCurve D.Y h hyp) hc',
        ((B.image I).comap ι'.toMulEquiv.toMonoidHom).Commensurable J := by
  intro I hI
  haveI : Nonempty (baseChangeOpen D.M Ω U') :=
    (nonempty_baseChangeOpen D.M Ω (D.Y.nonempty.mono h)).to_subtype
  have h1 := (hf.image_commensurable I).comap' ι'.toMulEquiv.toMonoidHom
  rw [D.comap_ofFill_map hfull f h hc' hyp ι'] at h1
  rcases D.cusp I hI with hb | ⟨J, hJ, hc⟩
  · left
    have h2 := hb.map' (D.fillPsi f h hc' hyp ι')
    rw [Subgroup.map_bot] at h2
    exact h1.trans h2
  · rcases le_ker_or_map_mem_arithCusps_of_conjInduced_fill Ω D.Y D.hY h hc' hyp
        (D.fillPsi f h hc' hyp ι') hrel hJ with hk | hm
    · left
      have h2 := hc.map' (D.fillPsi f h hc' hyp ι')
      have hb : J.map (D.fillPsi f h hc' hyp ι') = ⊥ :=
        eq_bot_iff.2 fun x hx ↦ by
          obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
          exact Subgroup.mem_bot.2 (hk hz)
      exact h1.trans (hb ▸ h2)
    · exact Or.inr ⟨_, hm, h1.trans (hc.map' _)⟩

lemma _root_.CurvesJacobian.Cusp.range_cme {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q]
    [TopologicalSpace Q] (e : P ≃ₜ* Q) :
    Set.range (ContinuousMonoidHom.toContinuousMonoidHom e : P →ₜ* Q) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ ⟨e.symm x, e.apply_symm_apply x⟩

lemma _root_.CurvesJacobian.Cusp.isOpen_range_cme {P Q : Type*} [Group P] [TopologicalSpace P]
    [Group Q] [TopologicalSpace Q] (e : P ≃ₜ* Q) :
    IsOpen (Set.range (ContinuousMonoidHom.toContinuousMonoidHom e : P →ₜ* Q)) := by
  rw [range_cme]
  exact isOpen_univ

lemma _root_.CurvesJacobian.Cusp.mem_normalizer_range_cme {P Q : Type*} [Group P]
    [TopologicalSpace P] [Group Q] [TopologicalSpace Q] (e : P ≃ₜ* Q) (q : Q) :
    q ∈ Subgroup.normalizer
      (Set.range (ContinuousMonoidHom.toContinuousMonoidHom e : P →ₜ* Q)) := by
  rw [range_cme]
  exact Subgroup.mem_set_normalizer_iff.2 fun _ ↦ by simp

/-- **The full model `((X̄_Y, U'), ι')` of `B`.** -/
def ofFill : GeomModel Ω CX hcX B where
  M := D.M
  Y := fillCurve D.Y h hyp
  hY := hc'
  ι := ContinuousMonoidHom.toContinuousMonoidHom ι'
  inj := ι'.injective
  isOpen_range := isOpen_range_cme ι'
  normal := fun _ _ ↦ mem_normalizer_range_cme ι' _
  toG_eq := D.exists_toGk_ofFill f hf h hc' hyp ι' hrel
  cusp := D.ofFill_cusp hfull f hf h hc' hyp ι' hrel

lemma ofFill_ι (τ) : (D.ofFill hfull f hf h hc' hyp ι' hrel).ι τ = ι' τ := rfl

end GeomModel

/-- **A `•` from a full model is the filling of a single cusp**: for a full model `D` of `A` and an
operation `o : A ⇝ B` of type `•` (with an infinite cusp image in `B`) there are a filling
`U' ⊇ U_Y` and `ι' : Π_{(X̄_Y, U')} ≅ B` with `ι' ∘ fillPiHom = φ ∘ ι`. -/
theorem _root_.Belyi.Anabelian.ElemOp.exists_full_fill {A B : ChainObj (arithmeticExt Ω CX hcX)}
    (o : ElemOp A B) (ho : o.kind = .decusp) (D : GeomModel Ω CX hcX A)
    (hfull : Function.Surjective D.ι)
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) (hB : B.HasInfCusp) :
    ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
      (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
        2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
      (ι' : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
        baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* B.grp),
      ∀ τ, ι' (fillPiHom Ω D.Y D.hY h hc' hyp τ) = o.decuspHom ho (D.ι τ) := by
  match o, ho with
  | .decusp φ surj C cusp tf ker compat, _ =>
    obtain ⟨J, hJΔ, hCJ, hJn, hJo, -⟩ := id tf
    have hJr : J ≤ (D.ι : D.Pi →* A.grp).range := fun x _ ↦ hfull x
    have hKP : (φ : A.grp →* B.grp).ker ≤ (D.ι : D.Pi →* A.grp).range := fun x _ ↦ hfull x
    obtain ⟨U', h, hc', hyp, hkerf⟩ := D.exists_fill_of_decusp hDGC φ surj cusp tf ker compat
      hB hJΔ hCJ hJn hJo hJr
    have hbij : Function.Bijective (D.dcIota φ h hc' hyp hkerf) := by
      refine ⟨D.dcIota_injective φ h hc' hyp hkerf, fun b ↦ ?_⟩
      have hb : b ∈ Set.range (D.dcIota φ h hc' hyp hkerf) := by
        rw [GeomModel.range_dcIota]
        obtain ⟨a, rfl⟩ := surj b
        obtain ⟨σ, rfl⟩ := hfull a
        exact ⟨D.ι σ, ⟨σ, rfl⟩, rfl⟩
      exact hb
    exact ⟨U', h, hc', hyp, continuousMulEquivOfBijective _ hbij,
      fun τ ↦ D.dcIota_dcFill φ h hc' hyp hkerf τ⟩
  | .cover .., h => exact absurd h (by simp [ElemOp.kind])
  | .quot .., h => exact absurd h (by simp [ElemOp.kind])
  | .deorb .., h => exact absurd h (by simp [ElemOp.kind])

/-- `fillPiHom` is bijective if nothing is filled. -/
lemma GeomModel.fillPiHom_bijective_self {A : ChainObj (arithmeticExt Ω CX hcX)}
    (D : GeomModel Ω CX hcX A) :
    Function.Bijective (fillPiHom Ω D.Y D.hY le_rfl D.hY D.Y.hyperbolic) := by
  have h1 := ContinuousMulEquiv.bijective (autContinuousMulEquivOfIso
    (fiberIsoMap (baseChangeSpec D.M Ω Γ(D.Y.Xbar, D.Y.U)) rfl rfl
      (fillAlpha Ω D.Y D.hY le_rfl D.hY D.Y.hyperbolic)).symm)
  have h2 := fillMap_bijective_of_eq Ω D.Y D.hY le_rfl rfl
  exact h1.comp h2

/-- **A run of `•`'s from a full model is a filling**: for a full model `D` of `Π_i` and a run
`Π_i ⇝ … ⇝ Π_{i+m}` of `•`'s whose targets have infinite cusp images there are a filling
`U' ⊇ U_Y` and `ι' : Π_{(X̄_Y, U')} ≅ Π_{i+m}` such that `ι'⁻¹ ∘ run ∘ ι` is induced by
`Spec Γ(U_Y) ⟶ Spec Γ(U')`. -/
theorem _root_.Belyi.Anabelian.PiChain.exists_run_fill (c : PiChain (arithmeticExt Ω CX hcX))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) (i : ℕ) (hi : i ≤ c.len)
    (D : GeomModel Ω CX hcX (c.objN i hi)) (hfull : Function.Surjective D.ι) :
    ∀ (m : ℕ) (hm : i + m ≤ c.len) (hrun : c.IsDecuspRun i m hm)
      (_ : ∀ s (hs : s < m), (c.objN (i + s + 1) (by omega)).HasInfCusp),
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ι' : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (c.objN (i + m) hm).grp),
        IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg D.M h).toRingHom))
          (fun σ ↦ ι'.symm (c.runHom i m hm hrun (D.ι σ)))
  | 0, hm, hrun, _ => by
    let eF := continuousMulEquivOfBijective _ D.fillPiHom_bijective_self
    let eι := continuousMulEquivOfBijective D.ι ⟨D.inj, hfull⟩
    refine ⟨D.Y.U, le_rfl, D.hY, D.Y.hyperbolic, eF.symm.trans eι, ?_⟩
    refine (isConjInduced_fillPiHom Ω D.Y D.hY le_rfl D.hY D.Y.hyperbolic).congr_fun fun σ ↦ ?_
    change (eF.symm.trans eι).symm (D.ι σ) = eF σ
    rw [ContinuousMulEquiv.symm_trans_apply, ContinuousMulEquiv.symm_symm]
    congr 1
    exact eι.symm_apply_apply σ
  | m + 1, hm, hrun, hinf => by
    obtain ⟨U', h, hc', hyp, ι', hrel⟩ := c.exists_run_fill hDGC i hi D hfull m (by omega)
      (fun s hs ↦ hrun s (by omega)) (fun s hs ↦ hinf s (by omega))
    obtain ⟨U'', h', hc'', hyp'', ι'', hι''⟩ := (c.opN (i + m) (by omega)).exists_full_fill
      (hrun m (by omega)) (D.ofFill hfull _ (c.compat_runHom i m (by omega)
        fun s hs ↦ hrun s (by omega)) h hc' hyp ι' hrel) ι'.surjective hDGC (hinf m (by omega))
    have hψ := isConjInduced_fillPiHom Ω (fillCurve D.Y h hyp) hc' h' hc'' hyp''
    refine ⟨U'', h.trans h', hc'', hyp'', ι'', ?_⟩
    refine ((hrel.comp hψ).congr_hom (specMap_resAlg_comp D.Y h h')).congr_fun fun σ ↦ ?_
    have hι2 : ∀ τ, ι'' (fillPiHom Ω (fillCurve D.Y h hyp) hc' h' hc'' hyp'' τ) =
        (c.opN (i + m) (by omega)).decuspHom (hrun m (by omega)) (ι' τ) := hι''
    have h4 := ι'.apply_symm_apply
      (c.runHom i m (by omega) (fun s hs ↦ hrun s (by omega)) (D.ι σ))
    have h3 := (hι2 _).trans
      (congrArg ((c.opN (i + m) (by omega)).decuspHom (hrun m (by omega))) h4)
    exact (ContinuousMulEquiv.symm_apply_eq ι'').2 h3.symm

variable {c : PiChain (arithmeticExt Ω CX hcX)} {l r : ℕ}

/-- **[AbsTopII] Cor 3.7 (a), the candidate is a filling of curves** (MR8 round 26, step (2)):
for a Belyi-type chain with a terminal isomorphism to the trivial chain whose object `Π_V` has an
infinite cusp image, and `m ≤ r`, there are a full geometric model `(Y, ι : Π_Y ≅ Π_U)` of
`Π_U = Π_{l+3+(r-m)}`, a filling `U_Y ⊆ U'` and `ε : Π_{(X̄_Y, U')} ≅ Π_V` such that the surjection
`Π_U ↠ Π_V` of the candidate is `ε ∘ fillPiHom ∘ ι⁻¹`. -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.exists_candidate_fill (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (m : ℕ) (hm : m ≤ r) :
    ∃ D : GeomModel Ω CX hcX (c.objN (l + 3 + (r - m)) (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiV),
        ∀ σ, (PiChain.belyiCandidate hc t m hm).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ) := by
  have hlen := hc.len_eq
  have h3 := PiChain.IsBelyiType.exists_full_geomModel hc t hDGC hV (l + 3 + (r - m)) (by omega)
    (by omega)
  obtain ⟨D, hD⟩ := h3
  have hinf : ∀ s (hs : s < m), (c.objN (l + 3 + (r - m) + s + 1) (by omega)).HasInfCusp :=
    fun s _ ↦ hc.hasInfCusp hV _
  have h4 := c.exists_run_fill hDGC (l + 3 + (r - m)) (by omega) D hD m (by omega)
    (hc.isDecuspRun m hm) hinf
  obtain ⟨U', h, hc', hyp, ι', hrel⟩ := h4
  have hF := isConjInduced_fillPiHom Ω D.Y D.hY h hc' hyp
  have h5 := IsConjInduced.exists_conj_eq hrel hF
  obtain ⟨u, hu⟩ := h5
  refine ⟨D, hD, U', h, hc', hyp, ((conjCMEquiv u).trans ι').trans
    (c.objCongr (a := l + 3 + (r - m) + m) (b := l + r + 3) (by omega) (by omega) (by omega)),
    fun σ ↦ ?_⟩
  have e : ι' (u * fillPiHom Ω D.Y D.hY h hc' hyp σ * u⁻¹) =
      c.runHom (l + 3 + (r - m)) m (by omega) (hc.isDecuspRun m hm) (D.ι σ) :=
    (congrArg ι' (hu σ)).symm.trans (ι'.apply_symm_apply _)
  exact congrArg (c.objCongr (a := l + 3 + (r - m) + m) (b := l + r + 3) (by omega) (by omega)
    (by omega)) e.symm

/-- **The candidate is a filling of curves, with the projections to `G_K`**: as
`PiChain.IsBelyiType.exists_candidate_fill`, and moreover `ε : Π_{(X̄_Y, U')} ≅ Π_V` lies over
`res : G_M → G_K` up to conjugation. -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.exists_candidate_fill_toG
    (hc : c.IsBelyiType l r) (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (m : ℕ) (hm : m ≤ r) :
    ∃ D : GeomModel Ω CX hcX (c.objN (l + 3 + (r - m)) (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiV),
        (∀ σ, (PiChain.belyiCandidate hc t m hm).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ)) ∧
        ∃ g₀ : π₁ᵉᵗ(sK), ∀ τ, toGk (c.objN (l + r + 3) (by have := hc.len_eq; omega)) (ε τ) =
          g₀ * resGal K Ω D.M (projGk Ω (fillCurve D.Y h hyp) hc' τ) * g₀⁻¹ := by
  have hlen := hc.len_eq
  have h1 := hc.exists_candidate_fill t hDGC hV m hm
  obtain ⟨D, hD, U', h, hc', hyp, ε, hε⟩ := h1
  have hf : ChainObj.Compat (c.objN (l + 3 + (r - m)) (by omega)) (c.objN (l + r + 3) (by omega))
      (PiChain.belyiCandidate hc t m hm).surj :=
    (c.compat_runHom (l + 3 + (r - m)) m (by omega) (hc.isDecuspRun m hm)).comp
      (c.compat_objCongr (a := l + 3 + (r - m) + m) (b := l + r + 3) (by omega) (by omega)
        (by omega))
  have hrel : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg D.M h).toRingHom))
      (fun σ ↦ ε.symm ((PiChain.belyiCandidate hc t m hm).surj (D.ι σ))) :=
    (isConjInduced_fillPiHom Ω D.Y D.hY h hc' hyp).congr_fun fun σ ↦
      (congrArg ε.symm (hε σ)).trans (ε.symm_apply_apply _)
  have hG := D.exists_toGk_ofFill _ hf h hc' hyp ε hrel
  exact ⟨D, hD, U', h, hc', hyp, ε, hε, hG⟩

end CurvesJacobian.Cusp
