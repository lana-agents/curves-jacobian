/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelFaithful
import CurvesJacobian.Cusp.QuotConj
import CurvesJacobian.Cusp.QuotientCurve

/-!
# Enlarging a geometric model: the setup (MR8 option (Q), step (Q-a))

Let `D` be a geometric model of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`), with the
rel-isom-DGC over its field of definition, and `P' ≤ N_A(ι(Π_Y))` a subgroup with
`ι(Π_Y) ≤ P'` of finite index. Put `R = Γ(U_Y)`, a `K`-algebra. We fix:

* `GeomModel.enlT`: a `t ∈ R` invariant under `autRing g`, `g ∈ P'`, transcendental over `K`,
  with `R` finite over `K[t]`, and `GeomModel.enlH`: `h ≠ 0` with `K[X]_h → R_h` étale;
* `GeomModel.enlG`: the finite group `G = autRing(P') ≤ Aut_K(R)` and `GeomModel.enlRho`
  (`G ↪ Aut_K(R)`);
* the punctured line `L = GeomModel.enlL` and its base point `η'` (`GeomModel.enlEta`), the
  finite étale cover `V = Spec R_{h'} ⟶ Spec Γ(L)` (`GeomModel.enlCover`), the action
  `GeomModel.enlCoverAut` of `G` on it, a point `a` of `V` over `η'` (`GeomModel.enlPt`);
* `E₁ = π₁ᵉᵗ(W) = stab(b) ≤ π₁ᵉᵗ(L, η')` for `W = V / G` (`GeomModel.enlE₁`) with the
  surjection `p₁ : E₁ ↠ G` (`GeomModel.enlP₁`, kernel `π₁ᵉᵗ(V)`) and
  `p₂ = autRing|_{P'} : P' ↠ G` (`GeomModel.enlP₂`, kernel `ι(Π_Y) ∩ P'`);
* `j = Spec (R → R_{h'}) : V ⟶ Spec R` (`GeomModel.enlJ`), with `π₁ᵉᵗ(j)` surjective at every
  base point (`GeomModel.surjective_fundamentalGroupMap_enlJ`: `R` is integrally closed in
  `R_{h'}`), and `ψ₀ : π₁ᵉᵗ(V, a) ↠ Π_Y` (`GeomModel.enlPsi₀`, `π₁ᵉᵗ(j)` followed by a fixed change
  of base point, `GeomModel.isConjInduced_enlPsi₀`);
* **`GeomModel.enlPsi : ker p₁ →* ker p₂`**, continuous (`GeomModel.continuous_enlPsi`) and
  surjective (`GeomModel.enlPsi_surjective`), `n ↦ ι(ψ₀(τ))` for the `τ ∈ π₁ᵉᵗ(V, a)` above `n`;
* **`GeomModel.center_ker_enlP₂`**: `ker p₂` has trivial centre (slimness of chain objects).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **A normal domain is integrally closed in its localisation away from a nonzero element.** -/
lemma mem_range_of_isIntegral_away {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {r : A} (hr : r ≠ 0) {s : Localization.Away r} (hs : IsIntegral A s) :
    s ∈ Set.range (algebraMap A (Localization.Away r)) := by
  have hS : Submonoid.powers r ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  let f := Localization.mapToFractionRing (FractionRing A) (Submonoid.powers r)
    (Localization.Away r) hS
  have hf : Function.Injective f := (IsLocalization.lift_injective_iff _).2 fun x y ↦ by
    rw [(IsLocalization.injective (Localization.Away r) hS).eq_iff,
      (IsFractionRing.injective A (FractionRing A)).eq_iff]
  haveI : IsIntegrallyClosedIn A (Localization.Away r) :=
    f.isIntegrallyClosedIn hf inferInstance
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hs
  exact ⟨a, ha⟩

namespace GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC D.M) {P' : Subgroup D.Nrm}
  (hrel : D.ιNHom.range.relIndex P' ≠ 0)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### The invariant line and generic étaleness -/

/-- **The invariant coordinate `t ∈ Γ(U_Y)`** (fixed by `autRing(P')`). -/
def enlT : Γ(D.Y.Xbar, D.Y.U) := (D.exists_invariant_line hDGC hrel).choose

lemma enlT_fix : ∀ g ∈ D.autGroup hDGC P', g (D.enlT hDGC hrel) = D.enlT hDGC hrel :=
  (D.exists_invariant_line hDGC hrel).choose_spec.1

/-- `t` is fixed by `autRing g` for `g ∈ P'`. -/
lemma autRing_enlT {g : D.Nrm} (hg : g ∈ P') :
    D.autRing hDGC g (D.enlT hDGC hrel) = D.enlT hDGC hrel :=
  D.enlT_fix hDGC hrel _ (D.mem_autGroup hDGC hg)

lemma transcendental_enlT : Transcendental K (D.enlT hDGC hrel) :=
  (D.exists_invariant_line hDGC hrel).choose_spec.2.1

lemma finite_enlT : (lineHom K (D.enlT hDGC hrel)).Finite :=
  (D.exists_invariant_line hDGC hrel).choose_spec.2.2

/-- **The polynomial `h ≠ 0`** with `K[X]_h → R_h` étale (generic étaleness). -/
def enlH : K[X] :=
  (exists_etale_away (D.enlT hDGC hrel) (D.transcendental_enlT hDGC hrel)
    (D.finite_enlT hDGC hrel)).choose

lemma enlH_ne_zero : D.enlH hDGC hrel ≠ 0 :=
  (exists_etale_away (D.enlT hDGC hrel) (D.transcendental_enlT hDGC hrel)
    (D.finite_enlT hDGC hrel)).choose_spec.1

lemma enlH_etale : (Localization.awayMap (lineHom K (D.enlT hDGC hrel)) (D.enlH hDGC hrel)).Etale :=
  (exists_etale_away (D.enlT hDGC hrel) (D.transcendental_enlT hDGC hrel)
    (D.finite_enlT hDGC hrel)).choose_spec.2.1

/-! ### The finite group `G = autRing(P')` -/

/-- **The finite group `G = autRing(P') ≤ Aut_K(Γ(U_Y))`** (`GeomModel.autGroup`; the argument
`hrel` makes `Finite` an instance). -/
def enlG (_hrel : D.ιNHom.range.relIndex P' ≠ 0) :
    Subgroup (Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U)) :=
  D.autGroup hDGC P'

instance finite_enlG : Finite (D.enlG hDGC hrel) := D.finite_autGroup hDGC hrel

/-- `G ↪ Aut_K(Γ(U_Y))`. -/
def enlRho : D.enlG hDGC hrel →* (Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U)) :=
  (D.enlG hDGC hrel).subtype

lemma enlRho_injective : Function.Injective (D.enlRho hDGC hrel) := Subtype.val_injective

lemma enlRho_fix (g : D.enlG hDGC hrel) :
    D.enlRho hDGC hrel g (D.enlT hDGC hrel) = D.enlT hDGC hrel :=
  D.enlT_fix hDGC hrel _ g.2

/-! ### The punctured line, the cover `V = Spec R_{h'}` and the point `a` -/

/-- **The punctured line `L = (ℙ¹, D(X (X - 1) h))`** over `K`. -/
abbrev enlL : HypCurve K := lineCurve K (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)

lemma enlL_cusp : ((D.enlL hDGC hrel).U : Set (D.enlL hDGC hrel).Xbar)ᶜ.Nonempty :=
  lineCurve_cusp K _ _

/-- The ring `R_{h'}`, `h' = X (X - 1) h`. -/
abbrev enlRing : Type u := quotCoverRing K (D.enlT hDGC hrel) (D.enlH hDGC hrel)

/-- **The finite étale cover `V = Spec R_{h'} ⟶ Spec Γ(L)`.** -/
abbrev enlCover : Spec (.of (D.enlRing hDGC hrel)) ⟶
    Spec Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U) :=
  quotLineCover K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)

instance isFiniteEtale_enlCover : IsFiniteEtale (D.enlCover hDGC hrel) :=
  isFiniteEtale_lineCover K _ _ _ (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel)

instance connectedSpace_enlRing : ConnectedSpace (Spec (.of (D.enlRing hDGC hrel))) :=
  connectedSpace_coverRing K _ _ (D.enlH_ne_zero hDGC hrel) (D.transcendental_enlT hDGC hrel)

/-- **The action of `G` on the cover `V`**: `g ↦ Spec (ρ g⁻¹)` (`CurvesJacobian.Cusp.coverAut`). -/
abbrev enlCoverAut : D.enlG hDGC hrel →* Aut (coverObj (D.enlCover hDGC hrel)) :=
  coverAut K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
    (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)

lemma enlCoverAut_injective : Function.Injective (D.enlCoverAut hDGC hrel) :=
  coverAut_injective K _ _ _ _ _ _ _ (D.transcendental_enlT hDGC hrel)
    (D.enlRho_injective hDGC hrel)

/-- **The base point `η'` of the punctured line.** -/
abbrev enlEta : Spec (.of Ω) ⟶ Spec Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U) :=
  basePoint Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) ≫
    baseChangeSpec K Ω Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U)

lemma exists_enlPt : ∃ a : Spec (.of Ω) ⟶ Spec (.of (D.enlRing hDGC hrel)),
    a ≫ D.enlCover hDGC hrel = D.enlEta hDGC hrel := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected (fiber (D.enlEta hDGC hrel))
    (coverObj (D.enlCover hDGC hrel))
  exact ⟨(fiberObjEquivHom _ (coverObj _) x).left, w_left _⟩

/-- **A geometric point `a` of `V` over `η'`.** -/
def enlPt : Spec (.of Ω) ⟶ Spec (.of (D.enlRing hDGC hrel)) := (D.exists_enlPt hDGC hrel).choose

lemma enlPt_spec : D.enlPt hDGC hrel ≫ D.enlCover hDGC hrel = D.enlEta hDGC hrel :=
  (D.exists_enlPt hDGC hrel).choose_spec

/-! ### The extensions `p₁ : E₁ ↠ G` and `p₂ : P' ↠ G` -/

/-- **`E₁ = π₁ᵉᵗ(W) ≤ π₁ᵉᵗ(L, η')`** for the quotient `W = V / G`: the stabiliser of the image
`b` of `a` in the fibre of `W`. -/
abbrev enlE₁ : Subgroup π₁ᵉᵗ(D.enlEta hDGC hrel) :=
  quotCoverSubgroup (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) (D.enlCoverAut hDGC hrel)

/-- **`p₁ : E₁ ↠ G`** (`CurvesJacobian.Cusp.stabQuotHom`, `σ • a = ρ(p₁ σ)⁻¹ • a`). -/
def enlP₁ : D.enlE₁ hDGC hrel →* D.enlG hDGC hrel :=
  stabQuotHom (fiber (D.enlEta hDGC hrel))
    (coverPt (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel))
    (map_qMap_coverPt _ _ _) (D.enlCoverAut_injective hDGC hrel)

lemma enlP₁_surjective : Function.Surjective (D.enlP₁ hDGC hrel) :=
  surjective_stabQuotHom _ _ _ _

/-- **`ker p₁ = π₁ᵉᵗ(V, a)`** (inside `E₁`). -/
lemma ker_enlP₁ : (D.enlP₁ hDGC hrel).ker =
    (coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) :
      Subgroup π₁ᵉᵗ(D.enlEta hDGC hrel)).subgroupOf (D.enlE₁ hDGC hrel) :=
  ker_stabQuotHom _ _ _ _

lemma mem_coverSubgroup_of_mem_ker_enlP₁ {x : D.enlE₁ hDGC hrel}
    (hx : x ∈ (D.enlP₁ hDGC hrel).ker) :
    (x : π₁ᵉᵗ(D.enlEta hDGC hrel)) ∈
      coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) := by
  rw [ker_enlP₁] at hx
  exact Subgroup.mem_subgroupOf.1 hx

/-- `ker p₁` is open in `E₁`. -/
lemma isOpen_ker_enlP₁ : IsOpen ((D.enlP₁ hDGC hrel).ker : Set (D.enlE₁ hDGC hrel)) := by
  rw [ker_enlP₁]
  exact (coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
    (D.enlPt_spec hDGC hrel)).isOpen.preimage continuous_subtype_val

/-- **`p₂ = autRing|_{P'} : P' ↠ G`.** -/
def enlP₂ : P' →* D.enlG hDGC hrel := ((D.autRing hDGC).comp P'.subtype).rangeRestrict

@[simp]
lemma coe_enlP₂ (g : P') : (D.enlP₂ hDGC hrel g : Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U)) =
    D.autRing hDGC g :=
  rfl

lemma enlP₂_surjective : Function.Surjective (D.enlP₂ hDGC hrel) :=
  MonoidHom.rangeRestrict_surjective _

/-- **`ker p₂ = ι(Π_Y) ∩ P'`.** -/
lemma ker_enlP₂ : (D.enlP₂ hDGC hrel).ker = D.ιNHom.range.subgroupOf P' := by
  rw [← D.ker_autRing_comp_subtype hDGC P']
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact Subtype.ext_iff

/-! ### The map `j : V ⟶ Spec Γ(U_Y)` and `ψ₀ : π₁ᵉᵗ(V, a) ↠ Π_Y` -/

/-- **`j = Spec (Γ(U_Y) → R_{h'}) : V ⟶ Spec Γ(U_Y)`.** -/
def enlJ : Spec (.of (D.enlRing hDGC hrel)) ⟶ Spec Γ(D.Y.Xbar, D.Y.U) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel)))

instance connectedSpace_specSections_enl : ConnectedSpace (Spec Γ(D.Y.Xbar, D.Y.U)) :=
  haveI := isIntegral_specSections D.Y D.hY
  inferInstance

instance isIso_fromNormalization_enlJ : IsIso (D.enlJ hDGC hrel).fromNormalization := by
  haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
  haveI : IsIntegrallyClosed Γ(D.Y.Xbar, D.Y.U) :=
    isIntegrallyClosed_of_isAffineOpen (isAffineOpen_U D.Y D.hY)
      fun x _ ↦ IsCurveOver.isIntegrallyClosed_stalk D.M D.Y.Xbar x
  have hr : lineHom K (D.enlT hDGC hrel) (quotLinePoly K (D.enlH hDGC hrel)) ≠ 0 :=
    lineHom_ne_zero (D.transcendental_enlT hDGC hrel)
      (quotLinePoly_ne_zero K (D.enlH_ne_zero hDGC hrel))
  refine isIso_fromNormalization_specMap _ ?_ fun s hs ↦ mem_range_of_isIntegral_away hr hs
  exact IsLocalization.injective (M := Submonoid.powers
    (lineHom K (D.enlT hDGC hrel) (quotLinePoly K (D.enlH hDGC hrel)))) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr)

/-- **`π₁ᵉᵗ(j)` is surjective** (at any base point): `Γ(U_Y)` is integrally closed in `R_{h'}`. -/
theorem surjective_fundamentalGroupMap_enlJ
    {x₀ : Spec (.of Ω) ⟶ Spec (.of (D.enlRing hDGC hrel))}
    {y : Spec (.of Ω) ⟶ Spec Γ(D.Y.Xbar, D.Y.U)} (hx₀ : x₀ ≫ D.enlJ hDGC hrel = y) :
    Function.Surjective (fundamentalGroupMap (D.enlJ hDGC hrel) hx₀) :=
  fundamentalGroupMap_surjective_of_isIso_fromNormalization _ hx₀

/-- The fixed change of base point `fiber (a ≫ j) ≅ fiber (base point of Π_Y)`. -/
def enlFib : fiber (D.enlPt hDGC hrel ≫ D.enlJ hDGC hrel) ≅
    fiber (basePoint Ω D.Y D.hY ≫ baseChangeSpec D.M Ω Γ(D.Y.Xbar, D.Y.U)) :=
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`ψ₀ : π₁ᵉᵗ(V, a) → Π_Y`**: `π₁ᵉᵗ(j)` followed by the change of base point `enlFib`. -/
def enlPsi₀ : π₁ᵉᵗ(D.enlPt hDGC hrel) →ₜ* D.Pi :=
  (ContinuousMonoidHom.toContinuousMonoidHom (autContinuousMulEquivOfIso (D.enlFib hDGC hrel))).comp
    (fundamentalGroupMap (D.enlJ hDGC hrel) rfl)

lemma enlPsi₀_apply (σ : π₁ᵉᵗ(D.enlPt hDGC hrel)) :
    D.enlPsi₀ hDGC hrel σ =
      autContinuousMulEquivOfIso (D.enlFib hDGC hrel)
        (fundamentalGroupMap (D.enlJ hDGC hrel) rfl σ) :=
  rfl

/-- **`ψ₀` is induced by `j`.** -/
theorem isConjInduced_enlPsi₀ : IsConjInduced (D.enlJ hDGC hrel) (D.enlPsi₀ hDGC hrel) :=
  ⟨D.enlFib hDGC hrel, fun _ ↦ rfl⟩

/-- **`ψ₀` is surjective.** -/
theorem enlPsi₀_surjective : Function.Surjective (D.enlPsi₀ hDGC hrel) :=
  (autContinuousMulEquivOfIso (D.enlFib hDGC hrel)).surjective.comp
    (D.surjective_fundamentalGroupMap_enlJ hDGC hrel rfl)

/-! ### The map `ψ : ker p₁ → ker p₂` -/

/-- `ker p₁ ≅ π₁ᵉᵗ(V, a)`: an element of `ker p₁` as an element of `π₁ᵉᵗ(V, a)`. -/
def enlKerToV : (D.enlP₁ hDGC hrel).ker →ₜ* π₁ᵉᵗ(D.enlPt hDGC hrel) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (coverEquiv (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
    (D.enlPt_spec hDGC hrel)).symm).comp
    { toMonoidHom := (((D.enlE₁ hDGC hrel).subtype.comp (D.enlP₁ hDGC hrel).ker.subtype).codRestrict
        (coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) :
          Subgroup π₁ᵉᵗ(D.enlEta hDGC hrel))
        fun n ↦ D.mem_coverSubgroup_of_mem_ker_enlP₁ hDGC hrel n.2)
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

/-- The defining property of `enlKerToV`. -/
theorem fundamentalGroupMap_enlKerToV (n : (D.enlP₁ hDGC hrel).ker) :
    fundamentalGroupMap (D.enlCover hDGC hrel) (D.enlPt_spec hDGC hrel) (D.enlKerToV hDGC hrel n) =
      ((n : D.enlE₁ hDGC hrel) : π₁ᵉᵗ(D.enlEta hDGC hrel)) := by
  rw [← coe_coverEquiv_apply]
  exact congrArg Subtype.val ((coverEquiv (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
    (D.enlPt_spec hDGC hrel)).apply_symm_apply _)

variable (hPP' : D.ιNHom.range ≤ P')

lemma enlP₂_ιN (σ : D.Pi) : D.enlP₂ hDGC hrel ⟨D.ιN σ, hPP' ⟨σ, rfl⟩⟩ = 1 :=
  Subtype.ext (D.autRing_ι hDGC σ)

/-- `ι : Π_Y → ker p₂ = ι(Π_Y) ∩ P'`. -/
def enlIota : D.Pi →ₜ* (D.enlP₂ hDGC hrel).ker where
  toMonoidHom := (D.ιNHom.codRestrict P' fun σ ↦ hPP' ⟨σ, rfl⟩).codRestrict _
    fun σ ↦ MonoidHom.mem_ker.2 (D.enlP₂_ιN hDGC hrel hPP' σ)
  continuous_toFun := ((D.ι.continuous.subtype_mk _).subtype_mk _).subtype_mk _

@[simp]
lemma coe_enlIota (σ : D.Pi) :
    (((D.enlIota hDGC hrel hPP' σ : P') : D.Nrm) : A.grp) = D.ι σ :=
  rfl

/-- **`ψ : ker p₁ → ker p₂`**, `n ↦ ι(ψ₀(τ))` for the `τ ∈ π₁ᵉᵗ(V, a)` above `n`, as a continuous
homomorphism. -/
def enlPsiCont : (D.enlP₁ hDGC hrel).ker →ₜ* (D.enlP₂ hDGC hrel).ker :=
  (D.enlIota hDGC hrel hPP').comp ((D.enlPsi₀ hDGC hrel).comp (D.enlKerToV hDGC hrel))

/-- **`ψ : ker p₁ →* ker p₂`.** -/
def enlPsi : (D.enlP₁ hDGC hrel).ker →* (D.enlP₂ hDGC hrel).ker :=
  (D.enlPsiCont hDGC hrel hPP').toMonoidHom

lemma continuous_enlPsi : Continuous (D.enlPsi hDGC hrel hPP') :=
  (D.enlPsiCont hDGC hrel hPP').continuous

lemma coe_enlPsi (n : (D.enlP₁ hDGC hrel).ker) :
    (((D.enlPsi hDGC hrel hPP' n : P') : D.Nrm) : A.grp) =
      D.ι (D.enlPsi₀ hDGC hrel (D.enlKerToV hDGC hrel n)) :=
  rfl

/-- **`ψ` is surjective**: `ker p₂ = ι(Π_Y) ∩ P'`, `ψ₀` is surjective and `π₁ᵉᵗ(V, a)` maps onto
`ker p₁`. -/
theorem enlPsi_surjective : Function.Surjective (D.enlPsi hDGC hrel hPP') := by
  intro m
  have hm : (m : P') ∈ D.ιNHom.range.subgroupOf P' := by
    rw [← ker_enlP₂]
    exact m.2
  obtain ⟨σ, hσ⟩ := Subgroup.mem_subgroupOf.1 hm
  obtain ⟨τ, hτ⟩ := D.enlPsi₀_surjective hDGC hrel σ
  have hcov : fundamentalGroupMap (D.enlCover hDGC hrel) (D.enlPt_spec hDGC hrel) τ ∈
      (coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) :
        Subgroup π₁ᵉᵗ(D.enlEta hDGC hrel)) := by
    rw [← range_fundamentalGroupMap_eq_coverSubgroup]
    exact ⟨τ, rfl⟩
  let e : D.enlE₁ hDGC hrel :=
    ⟨_, coverSubgroup_le_quot (ρ := D.enlCoverAut hDGC hrel) (D.enlPt_spec hDGC hrel) hcov⟩
  have he : e ∈ (D.enlP₁ hDGC hrel).ker := by
    rw [ker_enlP₁]
    exact Subgroup.mem_subgroupOf.2 hcov
  refine ⟨⟨e, he⟩, ?_⟩
  have hv : D.enlKerToV hDGC hrel ⟨e, he⟩ = τ :=
    fundamentalGroupMap_injective_of_isFiniteEtale' (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
      (D.enlPt_spec hDGC hrel) (D.fundamentalGroupMap_enlKerToV hDGC hrel ⟨e, he⟩)
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  rw [coe_enlPsi, hv, hτ]
  exact congrArg Subtype.val hσ

include hPP' in
/-- **`ker p₂ = ι(Π_Y) ∩ P'` has trivial centre** (chain objects are slim:
`CurvesJacobian.Cusp.ChainObj.eq_one_of_forall_commute`). -/
theorem center_ker_enlP₂ : Subgroup.center (D.enlP₂ hDGC hrel).ker = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ ?_
  rw [Subgroup.mem_bot]
  have hz' : (((z : P') : D.Nrm) : A.grp) = 1 := by
    refine ChainObj.eq_one_of_forall_commute A (U := (D.ι : D.Pi →* A.grp).range)
      (by rw [MonoidHom.coe_range]; exact D.isOpen_range) ?_
    rintro _ ⟨σ, rfl⟩
    have h := Subgroup.mem_center_iff.1 hz (D.enlIota hDGC hrel hPP' σ)
    exact (congrArg (fun x : (D.enlP₂ hDGC hrel).ker ↦ (((x : P') : D.Nrm) : A.grp)) h).symm
  exact Subtype.ext (Subtype.ext (Subtype.ext hz'))

end GeomModel

end CurvesJacobian.Cusp
