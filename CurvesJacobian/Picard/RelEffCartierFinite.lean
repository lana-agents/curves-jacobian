/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.QuasiFiniteCriterion
import CurvesJacobian.Picard.RelEffCartierCurve
import CurvesJacobian.Picard.CurveCohomology
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Relative effective Cartier divisors on relative curves are finite locally free

Let `C` be a curve over a perfect field `k` (`Belyi.IsCurveOver`), `T` a `k`-scheme and
`X_T = C ×_k T → T`. This file proves "(2) ⇒ (3)" and, since `C` is proper, "(2) ⇒ (1)" of
Stacks, Lemma 44.3.1 (Tag 0B9D): a relative effective Cartier divisor `D ⊂ X_T` is locally
quasi-finite and of finite presentation over `T` (`RelEffCartier.locallyQuasiFinite`,
`RelEffCartier.locallyOfFinitePresentation`), hence finite, being proper
(`RelEffCartier.isFinite`, via Mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite`).
Together with `RelEffCartier.ofFiniteFlat` this gives `CurvesJacobian.relEffCartier_iff`:
a closed subscheme of `X_T` is a relative effective Cartier divisor iff it is finite, flat and
of finite presentation over `T`.

Quasi-finiteness is local: choose a finite `π : C → ℙ¹_k`; over an affine `V ⊆ T` and a chart
`W₀ = π⁻¹ D₊(x_i)` the ring `Γ(V) ⊗_k Γ(W₀)` is finite over `Γ(V)[X]`, and on a basic open where
`D` is cut out by a nonzerodivisor `g` with `Γ/g` flat over `Γ(V)`, the algebraic criterion
`QuasiFiniteCriterion.quasiFinite_quotient` applies.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Polynomial TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- A property of `D → S` induced by a ring map property can be checked on the rings
`𝒪_X(W)/I(W)` over `𝒪_S(V)` for affine opens `W` covering the support of `D`. -/
lemma IdealSheafData.prop_of_quotient {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (H : ∀ x ∈ I.support, ∃ (V : S.affineOpens) (W : X.affineOpens) (_ : x ∈ W.1)
      (e : W.1 ≤ f ⁻¹ᵁ V.1), Q ((Ideal.Quotient.mk (I.ideal W)).comp (f.appLE V.1 W.1 e).hom)) :
    P (I.subschemeι ≫ f) := by
  have hQi : RingHom.RespectsIso Q := HasRingHomProperty.isLocal_ringHomProperty P |>.respectsIso
  rw [HasRingHomProperty.iff_exists_appLE (P := P) hQ]
  intro z
  have hz : I.subschemeι z ∈ I.support := by
    change I.subschemeι z ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨V, W, hxW, e, hQW⟩ := H _ hz
  refine ⟨V, ⟨_, W.2.preimage I.subschemeι⟩, hxW, I.subschemeι.preimage_mono e, ?_⟩
  rw [I.appLE_subschemeι_comp f V W e, ← Category.assoc, CommRingCat.hom_comp,
    hQi.cancel_right_isIso, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact hQW

end Local

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  {T : Scheme.{u}} (gT : T ⟶ Spec (CommRingCat.of k))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) gT
local notation "pC" => pullback.fst (C ↘ Sk) gT
local notation "fT" => pullback.snd (C ↘ Sk) gT

open Cech Belyi

section Chart

variable {C} [PerfectField k] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)

/-- On a chart `π⁻¹ D₊(x_i)` of `C`, every function pulled back from `ℙ¹_k` is a polynomial with
coefficients in `Γ(Spec k)` in the chart coordinate. -/
lemma exists_aeval_eq_curve (i : Fin 2) (q : k[X]) :
    ∃ q' : Γ(Sk, ⊤)[X], aeval (π.app _ (ProjectiveLine.coord k i)) q' =
      π.app (ProjectiveLine.U k i) ((ProjectiveLine.chartSections k i).symm q) := by
  induction q using Polynomial.induction_on with
  | C a =>
    have hs := (IsCurveOver.bijective_structureToGlobal k C).2
    have e1 : (ProjectiveLine.chartSections k i).symm (Polynomial.C a) =
        ProjectiveLine.secMap k (ProjectiveLine.U k i) a := by
      rw [(ProjectiveLine.chartSections k i).symm_apply_eq, ProjectiveLine.chartSections_secMap]
    obtain ⟨c, hc⟩ := hs (π.app ⊤ (ProjectiveLine.structMap k a))
    refine ⟨Polynomial.C ((Scheme.ΓSpecIso _).inv c), ?_⟩
    rw [aeval_C, e1, ProjectiveLine.secMap, RingHom.comp_apply, ← app_res_apply π le_top, ← hc]
    rw [algebraMap_sections]
    rfl
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [map_add, map_add, map_add, hp', hq']⟩
  | monomial n a h =>
    obtain ⟨p', hp'⟩ := h
    refine ⟨p' * Polynomial.X, ?_⟩
    have hX : (ProjectiveLine.chartSections k i).symm Polynomial.X = ProjectiveLine.coord k i :=
      (ProjectiveLine.chartSections k i).symm_apply_eq.mpr (chartSections_coord i).symm
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, hX, map_mul, aeval_X, hp']

/-- `Γ(Spec k)[X]` acting on `Γ(C, π⁻¹ D₊(x_i))` through the chart coordinate. -/
abbrev curveChartAlgebra (i : Fin 2) : Algebra Γ(Sk, ⊤)[X] Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) :=
  (aeval (R := Γ(Sk, ⊤)) (π.app _ (ProjectiveLine.coord k i))).toRingHom.toAlgebra

attribute [local instance] curveChartAlgebra

/-- For `π` finite, `Γ(C, π⁻¹ D₊(x_i))` is finite over `Γ(Spec k)[X]`. -/
theorem finite_curveChart [IsFinite π] (i : Fin 2) :
    Module.Finite Γ(Sk, ⊤)[X] Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) := by
  set W := π ⁻¹ᵁ ProjectiveLine.U k i
  have hfin := π.finite_app (ProjectiveLine.U k i) (ProjectiveLine.isAffineOpen_U k i)
  letI := (π.app (ProjectiveLine.U k i)).hom.toAlgebra
  obtain ⟨G, hG⟩ := (show Module.Finite Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i) Γ(C, W)
    from hfin).fg_top
  refine ⟨⟨G, ?_⟩⟩
  rw [eq_top_iff]
  rintro r -
  have hr : r ∈ Submodule.span Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i)
      (G : Set Γ(C, W)) := hG ▸ Submodule.mem_top
  induction hr using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    obtain ⟨q', hq'⟩ := exists_aeval_eq_curve π i (ProjectiveLine.chartSections k i s)
    rw [RingEquiv.symm_apply_apply] at hq'
    have e : s • x = q' • x := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change π.app _ s * x = aeval _ q' * x
      rw [hq']
    rw [e]
    exact Submodule.smul_mem _ _ hx

end Chart

section Main

variable [PerfectField k] [IsCurveOver k C]

/-- The local statement: around every point of `X_T` there are affine opens `V ⊆ T` and
`W ⊆ X_T` over `V` such that `Γ(V) → Γ(W)/I_D(W)` is quasi-finite and of finite presentation. -/
theorem _root_.AlgebraicGeometry.RelEffCartier.exists_quasiFinite_finitePresentation
    (D : RelEffCartier (fT))
    (x : ↥(pullback (C ↘ Sk) gT)) :
    ∃ (V : T.affineOpens) (W : (XT).affineOpens) (_ : x ∈ W.1) (e : W.1 ≤ fT ⁻¹ᵁ V.1),
      ((Ideal.Quotient.mk (D.ideal.ideal W)).comp ((fT).appLE V.1 W.1 e).hom).QuasiFinite ∧
      ((Ideal.Quotient.mk (D.ideal.ideal W)).comp ((fT).appLE V.1 W.1 e).hom).FinitePresentation
    := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : C ⟶ ProjectiveLine.scheme k, IsFinite π :=
    IsCurveOver.exists_finite_to_P1 k C
  obtain ⟨V, hV, hsV, -⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (Opens.mem_top (fT x))
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, π (pC x) ∈ ProjectiveLine.U k i := by
    have : π (pC x) ∈ ProjectiveLine.U k 0 ⊔ ProjectiveLine.U k 1 := by
      rw [ProjectiveLine.U_sup]; trivial
    rcases this with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  set W₀ := π ⁻¹ᵁ ProjectiveLine.U k i
  have hW₀ : IsAffineOpen W₀ := (ProjectiveLine.isAffineOpen_U k i).preimage π
  set 𝒰 := pC ⁻¹ᵁ W₀ ⊓ fT ⁻¹ᵁ V
  have h𝒰 : IsAffineOpen 𝒰 := isAffineOpen_inf_preimage C gT hW₀ hV
  have hx𝒰 : x ∈ 𝒰 := ⟨hi, hsV⟩
  obtain ⟨U', g', hxU', hI', hg'⟩ := D.locally_principal x
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter h𝒰 U'.2 x ⟨hx𝒰, hxU'⟩
  set W : (XT).affineOpens := (XT).affineBasicOpen (U := ⟨𝒰, h𝒰⟩) a
  have hWb : W.1 = (XT).basicOpen b := hab
  have hWU' : W.1 ≤ U'.1 := hWb ▸ (XT).basicOpen_le b
  obtain ⟨hIW, hgW⟩ := Scheme.IdealSheafData.principal_basicOpen hI' hg' W b hWb hWU'
  set g := (XT).presheaf.map (homOfLE hWU').op g'
  have hW𝒰 : W.1 ≤ 𝒰 := (XT).basicOpen_le a
  have e : W.1 ≤ fT ⁻¹ᵁ V := hW𝒰.trans inf_le_right
  refine ⟨⟨V, hV⟩, W, hxa, e, ?_⟩
  -- the rings
  letI : Algebra Γ(T, V) Γ(XT, 𝒰) := ((fT).appLE V 𝒰 inf_le_right).hom.toAlgebra
  letI : Algebra Γ(XT, 𝒰) Γ(XT, W.1) := ((XT).presheaf.map (homOfLE hW𝒰).op).hom.toAlgebra
  letI : Algebra Γ(T, V) Γ(XT, W.1) := ((fT).appLE V W.1 e).hom.toAlgebra
  haveI : IsScalarTower Γ(T, V) Γ(XT, 𝒰) Γ(XT, W.1) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = ((fT).appLE V 𝒰 inf_le_right ≫ (XT).presheaf.map _) r
    rw [Scheme.Hom.appLE_map]
    rfl
  haveI : IsLocalization.Away a Γ(XT, W.1) := h𝒰.isLocalization_basicOpen a
  -- `Γ(𝒰) = Γ(V) ⊗_k Γ(W₀)` is finite over `Γ(V)[X]`
  letI : Algebra Γ(Sk, ⊤) Γ(T, V) := (gT.appLE ⊤ V (by simp)).hom.toAlgebra
  set r : Γ(C, W₀) := π.app _ (ProjectiveLine.coord k i)
  let e₁ := pushoutTensorEquiv (isPushout_inf_preimage C gT hW₀ hV)
  have he₁ : ∀ c : Γ(T, V), e₁ (c ⊗ₜ 1) = algebraMap Γ(T, V) Γ(XT, 𝒰) c := by
    intro c
    rw [pushoutTensorEquiv_tmul, map_one, mul_one]
    rfl
  letI : Algebra Γ(T, V)[X] Γ(XT, 𝒰) :=
    (aeval (R := Γ(T, V)) (e₁ ((1 : Γ(T, V)) ⊗ₜ r))).toRingHom.toAlgebra
  haveI : IsScalarTower Γ(T, V) Γ(T, V)[X] Γ(XT, 𝒰) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = aeval (e₁ ((1 : Γ(T, V)) ⊗ₜ r)) (algebraMap Γ(T, V) Γ(T, V)[X] c)
    rw [Polynomial.algebraMap_eq, aeval_C]
  haveI : Module.Finite Γ(T, V)[X] Γ(XT, 𝒰) := by
    have h₀ := finite_curveChart π i
    have h₁ := QuasiFiniteCriterion.finite_tensor_polynomial (k₀ := Γ(Sk, ⊤)) Γ(T, V) r h₀
    letI := (aeval (R := Γ(T, V)) ((1 : Γ(T, V)) ⊗ₜ[Γ(Sk, ⊤)] r)).toRingHom.toAlgebra
    let e₂ : Γ(T, V) ⊗[Γ(Sk, ⊤)] Γ(C, W₀) ≃ₐ[Γ(T, V)] Γ(XT, 𝒰) :=
      AlgEquiv.ofRingEquiv (f := e₁) fun c ↦ by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          he₁]
    let e₃ : Γ(T, V) ⊗[Γ(Sk, ⊤)] Γ(C, W₀) ≃ₗ[Γ(T, V)[X]] Γ(XT, 𝒰) :=
      { e₂.toLinearEquiv with
        map_smul' := fun p y ↦ by
          change e₂ (aeval _ p * y) = aeval _ p * e₂ y
          rw [map_mul, ← aeval_algHom_apply]
          rfl }
    exact Module.Finite.equiv e₃
  haveI : Algebra.FiniteType Γ(T, V) Γ(XT, W.1) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (fT) inferInstance ⟨V, hV⟩ W e
  haveI hfp : Algebra.FinitePresentation Γ(T, V) Γ(XT, W.1) :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (fT) inferInstance ⟨V, hV⟩ W e
  haveI : Module.Flat Γ(T, V) (Γ(XT, W.1) ⧸ Ideal.span {g}) := by
    have := D.ideal.flat_quotient_of_flat (hf := D.flat) (fT) ⟨V, hV⟩ W e
    rw [hIW] at this
    exact RingHom.flat_algebraMap_iff.mp this
  rw [hIW]
  refine ⟨?_, ?_⟩
  · refine RingHom.quasiFinite_algebraMap.mpr ?_
    exact QuasiFiniteCriterion.quasiFinite_quotient (A := Γ(T, V)) (B := Γ(XT, 𝒰)) (h := a)
      Γ(XT, W.1) hgW
  · refine RingHom.finitePresentation_algebraMap.mpr ?_
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)

/-- **Stacks, Lemma 44.3.1 (Tag 0B9D), "(2) ⇒ (3)"**: a relative effective Cartier divisor on
`C ×_k T` is locally quasi-finite over `T`. -/
theorem _root_.AlgebraicGeometry.RelEffCartier.locallyQuasiFinite (D : RelEffCartier (fT)) :
    LocallyQuasiFinite (D.ideal.subschemeι ≫ fT) :=
  IdealSheafData.prop_of_quotient (P := @LocallyQuasiFinite) (fT) D.ideal
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left
    fun x _ ↦ by
      obtain ⟨V, W, hx, e, h, -⟩ := D.exists_quasiFinite_finitePresentation C gT x
      exact ⟨V, W, hx, e, h⟩

/-- A relative effective Cartier divisor on `C ×_k T` is of finite presentation over `T`. -/
theorem _root_.AlgebraicGeometry.RelEffCartier.locallyOfFinitePresentation
    (D : RelEffCartier (fT)) :
    LocallyOfFinitePresentation (D.ideal.subschemeι ≫ fT) :=
  IdealSheafData.prop_of_quotient (P := @LocallyOfFinitePresentation) (fT) D.ideal
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left
    fun x _ ↦ by
      obtain ⟨V, W, hx, e, -, h⟩ := D.exists_quasiFinite_finitePresentation C gT x
      exact ⟨V, W, hx, e, h⟩

/-- **Stacks, Lemma 44.3.1 (Tag 0B9D), "(2) ⇒ (1)"** (`C` is proper over `k`): a relative
effective Cartier divisor on `C ×_k T` is finite over `T`. -/
theorem _root_.AlgebraicGeometry.RelEffCartier.isFinite (D : RelEffCartier (fT)) :
    IsFinite (D.ideal.subschemeι ≫ fT) :=
  haveI := D.locallyQuasiFinite C gT
  IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **Stacks, Lemma 44.3.1 (Tag 0B9D), (1) ⇔ (2)** for `C ×_k T → T`, `C` a curve over a perfect
field: a closed subscheme is a relative effective Cartier divisor iff it is finite, flat and of
finite presentation (i.e. finite locally free) over `T`. -/
theorem relEffCartier_iff (D : (XT).IdealSheafData) :
    (∃ E : RelEffCartier (fT), E.ideal = D) ↔ IsFinite (D.subschemeι ≫ fT) ∧
      Flat (D.subschemeι ≫ fT) ∧ LocallyOfFinitePresentation (D.subschemeι ≫ fT) := by
  constructor
  · rintro ⟨E, rfl⟩
    exact ⟨E.isFinite C gT, E.flat, E.locallyOfFinitePresentation C gT⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨RelEffCartier.ofFiniteFlat C gT D, rfl⟩

end Main

end CurvesJacobian
