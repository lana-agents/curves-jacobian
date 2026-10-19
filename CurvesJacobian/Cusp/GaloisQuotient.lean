/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Galois.Prorepresentability
import CurvesJacobian.Cusp.CoverOpen

/-!
# Quotients by finite groups in a Galois category and their fundamental groups

Let `C` be a (pre)Galois category with fibre functor `F`, `A` a connected object and
`ρ : G →* Aut A` an injective homomorphism from a finite group. By axiom (G2) the quotient
`B = A / G` exists: it is the colimit `qObj ρ` of the action diagram `SingleObj G ⥤ C`,
with `q = qMap ρ : A ⟶ B`. By (G5) `F` preserves it. We show:

* `fiberQuotEquiv`: `F.obj B ≃ (F.obj A) / G` (orbits), with `F.map q x ↦ ⟦x⟧`; the
  `Aut F`-action is compatible (`qMap_smul`, `fiberQuotEquiv_smul`);
* `isConnected_qObj`: `B` is connected;
* for `a : F.obj A` and `b = F.map q a`: `stabilizer a ≤ stabilizer b`
  (`stabilizer_le_stabilizer_quot`), `stabilizer a` is normal in `stabilizer b`
  (`normal_subgroupOf_stabilizer_quot`, `conj_mem_stabilizer`), and
  `stabilizer b ⧸ stabilizer a ≃* G` (`stabQuotEquiv`), induced by the surjective homomorphism
  `stabQuotHom : stabilizer b →* G` characterised by `σ • a = (ρ (stabQuotHom σ)⁻¹) • a`
  (`smul_eq_stabQuotHom`). The inverse appears because the `G`-action on `F.obj A` commutes
  with the `Aut F`-action, so `σ ↦ g` with `σ • a = g • a` is an anti-homomorphism.

The proof uses that `G` acts freely on the fibre of the connected object `A`
(`evaluation_aut_injective_of_isConnected`) and that `Aut F` acts transitively on it.

We then specialise to `C = FiniteEtale U` for a connected scheme `U` with geometric point `η'`
(`AlgebraicGeometry.FiniteEtale`): for a connected finite étale cover `f : V ⟶ U`, a geometric
point `η` of `V` over `η'` and an injective `ρ : G →* Aut (coverObj f)`, the quotient
`W = (qObj ρ).left` is a connected finite étale `U`-scheme (`connectedSpace_qObj`),
`q : V ⟶ W` is finite étale, and in `π₁ᵉᵗ(η')`:
`coverSubgroup f ≤ coverSubgroup (W ⟶ U)` (`coverSubgroup_le_quot`), normal
(`normal_coverSubgroup_quot`), with quotient `≃* G` (`coverSubgroupQuotEquiv`).
-/

open CategoryTheory Limits PreGaloisCategory

universe u w

namespace CurvesJacobian.Cusp

section Abstract

variable {C : Type*} [Category C] {A : C} {G : Type*} [Group G] (ρ : G →* Aut A)

/-- The action diagram `SingleObj G ⥤ C` of `ρ : G →* Aut A`. -/
abbrev qDiag : SingleObj G ⥤ C := SingleObj.functor ((Aut.toEnd A).comp ρ)

section Fibre

variable (F : C ⥤ FintypeCat.{w})

variable {ρ} in
/-- `G` acts on the fibre `F.obj A` through `ρ` by `F.map (ρ g).hom`. -/
lemma map_mul_apply (g h : G) (x : F.obj A) :
    F.map (ρ (g * h)).hom x = F.map (ρ g).hom (F.map (ρ h).hom x) := by
  rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, F.map_comp, FintypeCat.comp_apply]

variable {ρ} in
lemma map_one_apply (x : F.obj A) : F.map (ρ 1).hom x = x := by
  rw [map_one]
  exact one_smul (Aut A) x

variable {ρ} in
/-- The `G`-action on `F.obj A` commutes with the `Aut F`-action. -/
lemma smul_map_apply (σ : Aut F) (g : G) (x : F.obj A) :
    σ • F.map (ρ g).hom x = F.map (ρ g).hom (σ • x) :=
  mulAction_naturality F σ (ρ g).hom x

/-- The `G`-action on `F.obj A` induced by the action diagram is `g • x = F.map (ρ g).hom x`. -/
lemma qDiag_smul (g : G) (x : F.obj A) :
    g • (show (qDiag ρ ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star G) from x) =
      F.map (ρ g).hom x :=
  rfl

end Fibre

variable [GaloisCategory C] [Finite G]

/-- The quotient `A / G` of `A` by `ρ : G →* Aut A`, the colimit of the action diagram. -/
noncomputable abbrev qObj : C := colimit (qDiag ρ)

/-- The quotient map `A ⟶ A / G`. -/
noncomputable abbrev qMap : A ⟶ qObj ρ := colimit.ι (qDiag ρ) (SingleObj.star G)

/-- The quotient map is `G`-invariant. -/
lemma hom_comp_qMap (g : G) : (ρ g).hom ≫ qMap ρ = qMap ρ :=
  colimit.w (qDiag ρ) (show SingleObj.star G ⟶ SingleObj.star G from g)

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- **The fibre of the quotient is the orbit set**: `F.obj (A / G) ≃ (F.obj A) / G`. -/
noncomputable def fiberQuotEquiv :
    F.obj (qObj ρ) ≃
      MulAction.orbitRel.Quotient G ((qDiag ρ ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star G)) :=
  (preservesColimitIso (F ⋙ FintypeCat.incl) (qDiag ρ)).toEquiv.trans
    (SingleObj.Types.colimitEquivQuotient (qDiag ρ ⋙ F ⋙ FintypeCat.incl))

lemma fiberQuotEquiv_map (x : F.obj A) :
    fiberQuotEquiv ρ F (F.map (qMap ρ) x) =
      Quotient.mk (MulAction.orbitRel G
        ((qDiag ρ ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star G))) x := by
  have h1 : (preservesColimitIso (F ⋙ FintypeCat.incl) (qDiag ρ)).hom
      (F.map (qMap ρ) x) = colimit.ι (qDiag ρ ⋙ F ⋙ FintypeCat.incl) (SingleObj.star G) x :=
    by
      have h1 := ConcreteCategory.congr_hom
        (ι_preservesColimitIso_hom (F ⋙ FintypeCat.incl) (qDiag ρ) (SingleObj.star G)) x
      exact h1
  change SingleObj.colimitTypeRelEquivOrbitRelQuotient _
    (Types.colimitEquivColimitType _ ((preservesColimitIso (F ⋙ FintypeCat.incl) (qDiag ρ)).hom
      (F.map (qMap ρ) x))) = _
  rw [h1, Types.colimitEquivColimitType_apply]
  rfl

/-- Two points of `F.obj A` have the same image in `F.obj (A / G)` iff they lie in one
`G`-orbit. -/
theorem map_qMap_eq_iff (x y : F.obj A) :
    F.map (qMap ρ) x = F.map (qMap ρ) y ↔ ∃ g : G, F.map (ρ g).hom x = y := by
  rw [← (fiberQuotEquiv ρ F).injective.eq_iff, fiberQuotEquiv_map, fiberQuotEquiv_map, eq_comm,
    Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  rfl

/-- `F.map (qMap ρ)` is surjective. -/
theorem surjective_map_qMap : Function.Surjective (F.map (qMap ρ)) := by
  intro y
  obtain ⟨x, hx⟩ := Quotient.exists_rep (fiberQuotEquiv ρ F y)
  refine ⟨x, (fiberQuotEquiv ρ F).injective ?_⟩
  rw [fiberQuotEquiv_map, ← hx]

omit [FiberFunctor F] in
/-- The quotient map commutes with the action of `Aut F`. -/
lemma qMap_smul (σ : Aut F) (x : F.obj A) :
    σ • F.map (qMap ρ) x = F.map (qMap ρ) (σ • x) :=
  mulAction_naturality F σ (qMap ρ) x

/-- `fiberQuotEquiv` intertwines the `Aut F`-actions. -/
lemma fiberQuotEquiv_smul (σ : Aut F) (x : F.obj A) :
    fiberQuotEquiv ρ F (σ • F.map (qMap ρ) x) =
      Quotient.mk (MulAction.orbitRel G
        ((qDiag ρ ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star G))) (σ • x) := by
  rw [qMap_smul, fiberQuotEquiv_map]

/-- An object with nonempty fibre on which `Aut F` acts transitively is connected. -/
theorem isConnected_of_isPretransitive (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] : IsConnected X where
  notInitial := not_initial_of_inhabited F (Classical.arbitrary _)
  noTrivialComponent Y i _ hni := by
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty F Y).mp hni
    have : IsIso (F.map i) := by
      refine (ConcreteCategory.isIso_iff_bijective (F.map i)).mpr ⟨?_, fun x' ↦ ?_⟩
      · exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
      · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) (F.map i y) x'
        exact ⟨σ • y, (mulAction_naturality F σ i y).symm.trans hσ⟩
    exact isIso_of_reflects_iso i F

variable [IsConnected A]

include F in
/-- **The quotient of a connected object is connected.** -/
theorem isConnected_qObj : IsConnected (qObj ρ) := by
  haveI : Nonempty (F.obj (qObj ρ)) :=
    ⟨F.map (qMap ρ) (Classical.arbitrary (F.obj A))⟩
  haveI : MulAction.IsPretransitive (Aut F) (F.obj (qObj ρ)) := ⟨fun y y' ↦ by
    obtain ⟨x, rfl⟩ := surjective_map_qMap ρ F y
    obtain ⟨x', rfl⟩ := surjective_map_qMap ρ F y'
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) x x'
    exact ⟨σ, by rw [qMap_smul, hσ]⟩⟩
  exact isConnected_of_isPretransitive F _

variable {ρ}

omit [Finite G] in
/-- `G` acts freely on the fibre of the connected object `A` if `ρ` is injective. -/
lemma eq_of_map_apply_eq (hρ : Function.Injective ρ) {g g' : G} {x : F.obj A}
    (h : F.map (ρ g).hom x = F.map (ρ g').hom x) : g = g' :=
  hρ (evaluation_aut_injective_of_isConnected F A x h)

variable (a : F.obj A) {b : F.obj (qObj ρ)} (hb : F.map (qMap ρ) a = b)
include hb

omit [FiberFunctor F] [IsConnected A] in
/-- **`stabilizer a ≤ stabilizer (q a)`.** -/
theorem stabilizer_le_stabilizer_quot :
    MulAction.stabilizer (Aut F) a ≤ MulAction.stabilizer (Aut F) b := by
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [← hb, qMap_smul, hσ]

omit [IsConnected A] in
lemma exists_map_smul_eq (σ : MulAction.stabilizer (Aut F) b) :
    ∃ g : G, F.map (ρ g).hom ((σ : Aut F) • a) = a := by
  have hσ : (σ : Aut F) • b = b := σ.2
  rw [← map_qMap_eq_iff, ← qMap_smul, hb, hσ]

variable (hρ : Function.Injective ρ)

/-- **The homomorphism `stabilizer (q a) →* G`**: `σ ↦ g` with `ρ g • σ • a = a`. -/
noncomputable def stabQuotHom : MulAction.stabilizer (Aut F) b →* G where
  toFun σ := (exists_map_smul_eq F a hb σ).choose
  map_one' := by
    refine eq_of_map_apply_eq F hρ (x := a) ?_
    have h := (exists_map_smul_eq F a hb 1).choose_spec
    rw [map_one_apply]
    exact h
  map_mul' σ τ := by
    have hσ := (exists_map_smul_eq F a hb σ).choose_spec
    have hτ := (exists_map_smul_eq F a hb τ).choose_spec
    have hστ := (exists_map_smul_eq F a hb (σ * τ)).choose_spec
    refine eq_of_map_apply_eq F hρ (x := ((σ * τ : MulAction.stabilizer (Aut F) b) : Aut F) • a) ?_
    rw [hστ, map_mul_apply, Subgroup.coe_mul, mul_smul, ← smul_map_apply, hτ, hσ]

lemma stabQuotHom_spec' (σ : MulAction.stabilizer (Aut F) b) :
    F.map (ρ (stabQuotHom F a hb hρ σ)).hom ((σ : Aut F) • a) = a :=
  (exists_map_smul_eq F a hb σ).choose_spec

/-- The defining formula of `stabQuotHom`: `σ • a = ρ (stabQuotHom σ)⁻¹ • a`. -/
theorem smul_eq_stabQuotHom (σ : MulAction.stabilizer (Aut F) b) :
    (σ : Aut F) • a = F.map (ρ (stabQuotHom F a hb hρ σ)⁻¹).hom a := by
  have hs := stabQuotHom_spec' F a hb hρ σ
  obtain ⟨g, hg⟩ : ∃ g, stabQuotHom F a hb hρ σ = g := ⟨_, rfl⟩
  rw [hg] at hs ⊢
  conv_rhs => rw [← hs, ← map_mul_apply, inv_mul_cancel, map_one_apply]

/-- `stabQuotHom` is uniquely determined: `stabQuotHom σ = g` iff `ρ g • σ • a = a`. -/
theorem stabQuotHom_eq_iff (σ : MulAction.stabilizer (Aut F) b) (g : G) :
    stabQuotHom F a hb hρ σ = g ↔ F.map (ρ g).hom ((σ : Aut F) • a) = a := by
  refine ⟨fun h ↦ h ▸ stabQuotHom_spec' F a hb hρ σ, fun h ↦ ?_⟩
  exact eq_of_map_apply_eq F hρ ((stabQuotHom_spec' F a hb hρ σ).trans h.symm)

theorem ker_stabQuotHom :
    (stabQuotHom F a hb hρ).ker =
      (MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
    stabQuotHom_eq_iff, map_one_apply]

theorem surjective_stabQuotHom : Function.Surjective (stabQuotHom F a hb hρ) := by
  intro g
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) a (F.map (ρ g⁻¹).hom a)
  have hmem : σ ∈ MulAction.stabilizer (Aut F) b := by
    rw [MulAction.mem_stabilizer_iff, ← hb, qMap_smul, hσ, ← F.map_comp_apply,
      hom_comp_qMap]
  refine ⟨⟨σ, hmem⟩, (stabQuotHom_eq_iff F a hb hρ _ g).mpr ?_⟩
  change F.map (ρ g).hom (σ • a) = a
  rw [hσ, ← map_mul_apply, mul_inv_cancel, map_one_apply]

include hρ in
/-- **`stabilizer a` is normal in `stabilizer (q a)`.** -/
theorem normal_subgroupOf_stabilizer_quot :
    ((MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b)).Normal := by
  rw [← ker_stabQuotHom F a hb hρ]
  infer_instance

include hρ in
/-- Conjugation by an element of `stabilizer (q a)` preserves `stabilizer a`. -/
theorem conj_mem_stabilizer {σ τ : Aut F} (hσ : σ ∈ MulAction.stabilizer (Aut F) b)
    (hτ : τ ∈ MulAction.stabilizer (Aut F) a) : σ * τ * σ⁻¹ ∈ MulAction.stabilizer (Aut F) a := by
  have hn := normal_subgroupOf_stabilizer_quot F a hb hρ
  have h := hn.conj_mem ⟨τ, stabilizer_le_stabilizer_quot F a hb hτ⟩
    (Subgroup.mem_subgroupOf.mpr hτ) ⟨σ, hσ⟩
  exact Subgroup.mem_subgroupOf.mp h

/-- **`stabilizer (q a) ⧸ stabilizer a ≃* G`.** -/
noncomputable def stabQuotEquiv
    [hN : ((MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b)).Normal] :
    MulAction.stabilizer (Aut F) b ⧸
        (MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (ker_stabQuotHom F a hb hρ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_stabQuotHom F a hb hρ))

theorem stabQuotEquiv_mk
    [hN : ((MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b)).Normal]
    (σ : MulAction.stabilizer (Aut F) b) :
    stabQuotEquiv F a hb hρ (σ : MulAction.stabilizer (Aut F) b ⧸
        (MulAction.stabilizer (Aut F) a).subgroupOf (MulAction.stabilizer (Aut F) b)) =
      stabQuotHom F a hb hρ σ :=
  rfl

end Abstract

section Schemes

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

variable {U V : Scheme.{u}} [ConnectedSpace U] {f : V ⟶ U} [IsFiniteEtale f] [ConnectedSpace V]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ V) {η' : Spec (.of Ω) ⟶ U}
  (h : η ≫ f = η') {G : Type*} [Group G] [Finite G] (ρ : G →* Aut (coverObj f))

instance isConnected_coverObj : IsConnected (coverObj f) :=
  (FiniteEtale.isConnected_iff_connectedSpace (coverObj f)).mpr ‹ConnectedSpace V›

/-- **The quotient `W = V / G` is connected.** -/
instance connectedSpace_qObj : ConnectedSpace (qObj ρ).left :=
  (FiniteEtale.isConnected_iff_connectedSpace (qObj ρ)).mp
    (isConnected_qObj ρ (GaloisCategory.getFiberFunctor (FiniteEtale U)))

omit [ConnectedSpace V] in
/-- The quotient map `q : V ⟶ W` is finite étale. -/
theorem isFiniteEtale_qMap : IsFiniteEtale (qMap ρ).hom.left := inferInstance

omit [ConnectedSpace V] in
/-- The quotient map lies over `U`. -/
lemma qMap_comp_hom : (qMap ρ).hom.left ≫ (qObj ρ).hom = f :=
  Over.w (qMap ρ).hom

omit [ConnectedSpace V] [IsSepClosed Ω] in
include h in
lemma quotPt_spec : (η ≫ (qMap ρ).hom.left) ≫ (qObj ρ).hom = η' :=
  (Category.assoc _ _ _).trans ((congrArg (η ≫ ·) (qMap_comp_hom ρ)).trans h)

omit [ConnectedSpace V] in
/-- The point `η ≫ q` of the fibre of `W` over `η'` is the image of `η`. -/
lemma map_qMap_coverPt :
    (fiber η').map (qMap ρ) (coverPt f η h) =
      coverPt (qObj ρ).hom (η ≫ (qMap ρ).hom.left) (quotPt_spec η h ρ) := by
  rw [coverPt, fiberObjEquivHom_symm_naturality]
  rfl

/-- The open subgroup `π₁ᵉᵗ(W) ⊆ π₁ᵉᵗ(U)` of the quotient `W = V / G`: `coverSubgroup` of
`W ⟶ U` at the point `η ≫ q` over `η'`. -/
noncomputable abbrev quotCoverSubgroup : Subgroup π₁ᵉᵗ(η') :=
  (coverSubgroup (qObj ρ).hom (η ≫ (qMap ρ).hom.left) (quotPt_spec η h ρ)).toSubgroup

variable {η ρ}

omit [ConnectedSpace V] in
/-- **`π₁ᵉᵗ(V) ≤ π₁ᵉᵗ(W)` inside `π₁ᵉᵗ(U)`.** -/
theorem coverSubgroup_le_quot :
    (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) ≤ quotCoverSubgroup η h ρ :=
  stabilizer_le_stabilizer_quot (fiber η') (coverPt f η h) (map_qMap_coverPt η h ρ)

variable (hρ : Function.Injective ρ)
include hρ

/-- **`π₁ᵉᵗ(V)` is normal in `π₁ᵉᵗ(W)`.** -/
theorem normal_coverSubgroup_quot :
    ((coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')).subgroupOf
      (quotCoverSubgroup η h ρ)).Normal :=
  normal_subgroupOf_stabilizer_quot (fiber η') (coverPt f η h) (map_qMap_coverPt η h ρ) hρ

/-- **`π₁ᵉᵗ(W) ⧸ π₁ᵉᵗ(V) ≃* G`** for the quotient `W = V / G` by a finite group `G` of
automorphisms of the connected finite étale cover `V ⟶ U` (the normality instance is
`normal_coverSubgroup_quot`). -/
noncomputable def coverSubgroupQuotEquiv
    [hN : ((coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')).subgroupOf
      (quotCoverSubgroup η h ρ)).Normal] :
    quotCoverSubgroup η h ρ ⧸
      (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')).subgroupOf
        (quotCoverSubgroup η h ρ) ≃* G :=
  stabQuotEquiv (fiber η') (coverPt f η h) (map_qMap_coverPt η h ρ) hρ (hN := hN)

end Schemes

end CurvesJacobian.Cusp
