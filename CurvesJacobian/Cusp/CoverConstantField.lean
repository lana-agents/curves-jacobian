/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCurve
import CurvesJacobian.Scheme.GeomIntegralConstantField
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Unramified.Field

/-!
# The normalisation of a curve in a finite étale cover is a curve over its constant field

Let `k` be a field of characteristic zero, `N` an integral scheme over `Spec k` whose rings of
sections over affine opens are integrally closed. Let `k' = constField k N` be the algebraic
closure of `k` in the function field `K(N)` (the *constant field*). We prove:

* `CurvesJacobian.Cusp.exists_germToFunctionField_top`: a rational function regular on every
  nonempty affine open is a global section (gluing, using irreducibility);
* every element of `k'` is a global section, which gives a ring map `k' → Γ(N, ⊤)`
  (`CurvesJacobian.Cusp.constFieldToΓ`) and a morphism
  `CurvesJacobian.Cusp.toSpecConstField : N ⟶ Spec k'` lifting the structure morphism
  (`CurvesJacobian.Cusp.toSpecConstField_comp`);
* `CurvesJacobian.Cusp.finiteDimensional_constField`: if `N` is locally of finite type over
  `k`, then `k'/k` is finite;
* `CurvesJacobian.Cusp.isCurveOver_constField`: if moreover `N` is proper and smooth of
  relative dimension `1` over `k` with stalks of dimension `≤ 1`, then `N` is a curve over `k'`;
* `CurvesJacobian.Cusp.isCurveOver_normalization_constField`: in the setting of
  `CurvesJacobian.Cusp.CoverCurve` (normalisation `N` of a curve `X̄` over `k` in a finite étale
  cover `Y ⟶ U ⊆ X̄`, `Y` integral), `N` is a curve over its constant field, compatibly with
  `q ≫ (X̄ ↘ Spec k)`.

## Proof

* An element `α ∈ k'` is integral over `k`, hence over `Γ(N, V)` for every nonempty affine `V`;
  as `Γ(N, V)` is integrally closed with fraction field `K(N)`, `α` is regular on `V`. Any two
  nonempty opens of the irreducible `N` meet, so these local sections are compatible and glue.
* Finiteness: `k'` embeds into `Γ(N, V) ⧸ 𝔪` for a maximal ideal `𝔪`, a field of finite type
  over `k`, hence finite over `k` (Zariski's lemma).
* Proper: `IsProper.of_comp`. Smooth: oka's criterion (normal, stalks of dimension `≤ 1`,
  characteristic zero). Relative dimension: on a standard smooth chart the rank of `Ω` equals
  the rank of `Ω[K(N)⁄k']`, and `Ω[K(N)⁄k] ≅ Ω[K(N)⁄k']` because `Ω[k'⁄k] = 0` (separable).
* Geometric integrality: `k'` is algebraically closed in `K(N)` (transitivity of
  integrality), so `CurvesJacobian.geometricallyIntegral_of_isAlgClosedIn` applies.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped Belyi

universe u

namespace CurvesJacobian.Cusp

lemma nonempty_top_opens {X : Scheme.{u}} [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.arbitrary X, trivial⟩⟩

attribute [local instance] nonempty_top_opens

/-! ### Gluing rational functions -/

section Glue

variable {N : Scheme.{u}} [IsIntegral N]

/-- **A rational function regular on all nonempty affine opens is a global section.** -/
theorem exists_germToFunctionField_top {α : N.functionField}
    (h : ∀ (V : N.Opens), IsAffineOpen V → ∀ [Nonempty V],
      ∃ g : Γ(N, V), N.germToFunctionField V g = α) :
    ∃ g : Γ(N, ⊤), N.germToFunctionField ⊤ g = α := by
  classical
  let ι := {V : N.Opens // IsAffineOpen V ∧ (V : Set N).Nonempty}
  let U : ι → N.Opens := fun i ↦ i.1
  have hne : ∀ i : ι, Nonempty (U i) := fun i ↦ ⟨⟨_, i.2.2.some_mem⟩⟩
  choose sf hsf using fun i : ι ↦ @h (U i) i.2.1 (hne i)
  have hcov : (⊤ : N.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, x, hxV⟩, hxV⟩
  have hcomp : TopCat.Presheaf.IsCompatible N.presheaf U sf := by
    intro i j
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen i.2.2 j.2.2
    haveI : Nonempty (U i ⊓ U j : N.Opens) := ⟨⟨x, hx⟩⟩
    haveI := hne i
    haveI := hne j
    apply N.germToFunctionField_injective (U i ⊓ U j)
    change N.presheaf.germ _ _ _ (N.presheaf.map _ (sf i)) =
      N.presheaf.germ _ _ _ (N.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨g, hg, -⟩ :=
    N.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcov sf hcomp
  obtain ⟨x⟩ := (inferInstance : Nonempty N)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let i : ι := ⟨V, hV, x, hxV⟩
  haveI := hne i
  refine ⟨g, ?_⟩
  rw [← hsf i, ← hg i]
  change _ = N.presheaf.germ _ _ _ (N.presheaf.map _ g)
  rw [TopCat.Presheaf.germ_res_apply]

/-- Global sections of an integral scheme are the rational functions in the image of the germ
map. -/
noncomputable def germTopEquiv (N : Scheme.{u}) [IsIntegral N] :
    Γ(N, ⊤) ≃+* (N.germToFunctionField ⊤).hom.range :=
  RingEquiv.ofBijective (N.germToFunctionField ⊤).hom.rangeRestrict
    ⟨fun _ _ hxy ↦ N.germToFunctionField_injective ⊤ (congrArg Subtype.val hxy),
      (N.germToFunctionField ⊤).hom.rangeRestrict_surjective⟩

end Glue

/-! ### Kähler differentials along an unramified base extension -/

/-- If `Ω[A⁄R] = 0`, then `Ω[K⁄R]` and `Ω[K⁄A]` have the same rank over `K`. -/
theorem rank_kaehler_eq_of_subsingleton (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [Subsingleton Ω[A⁄R]] :
    Module.rank K Ω[K⁄R] = Module.rank K Ω[K⁄A] := by
  have hinj : Function.Injective (KaehlerDifferential.map R A K K) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R A K x).1 hx
    have hy : y = 0 := by
      clear hx
      induction y using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [hy, map_zero]
  exact (LinearEquiv.ofBijective _ ⟨hinj, KaehlerDifferential.map_surjective R A K⟩).rank_eq

section Charts

variable {N : Scheme.{u}} [IsIntegral N]

/-- On a standard smooth chart `Γ(Spec K, ⊤) ⟶ Γ(N, V)` of an integral scheme over a field `K`,
the relative dimension is the rank of `Ω[K(N)⁄K]`. -/
theorem isStandardSmoothOfRelativeDimension_appLE_iff {K : Type u} [Field K]
    [Algebra K N.functionField] (f : N ⟶ Spec (.of K))
    (hf : ∀ c : K, algebraMap K N.functionField c =
      N.germToFunctionField ⊤ (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c)))
    (n : ℕ) {V : N.Opens} (hV : IsAffineOpen V) [Nonempty V] (e : V ≤ f ⁻¹ᵁ ⊤)
    (h : (f.appLE ⊤ V e).hom.IsStandardSmooth) :
    (f.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension n ↔
      Module.rank N.functionField Ω[N.functionField⁄K] = n := by
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(N, V) := (f.appLE ⊤ V e).hom.toAlgebra
  letI : Algebra Γ(Spec (.of K), ⊤) N.functionField :=
    ((f.appLE ⊤ V e) ≫ N.germToFunctionField V).hom.toAlgebra
  letI : Algebra K Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  haveI : IsScalarTower Γ(Spec (.of K), ⊤) Γ(N, V) N.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K Γ(Spec (.of K), ⊤) N.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      rw [hf c]
      change _ = N.presheaf.germ _ _ _ (N.presheaf.map _ (f.app ⊤ _))
      rw [TopCat.Presheaf.germ_res_apply]
      rfl
  haveI : Subsingleton Ω[Γ(Spec (.of K), ⊤)⁄K] :=
    KaehlerDifferential.subsingleton_of_surjective _ _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2
  haveI : Algebra.IsStandardSmooth Γ(Spec (.of K), ⊤) Γ(N, V) := h
  haveI := functionField_isFractionRing_of_isAffineOpen N V hV
  rw [rank_kaehler_eq_of_subsingleton K Γ(Spec (.of K), ⊤) N.functionField,
    rank_kaehlerDifferential_fractionRing (B := Γ(N, V))]
  exact Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n

end Charts

/-! ### The constant field -/

section ConstField

variable (k : Type u) [Field k] (N : Scheme.{u}) [IsIntegral N] [N.Over (Spec (.of k))]

/-- The **constant field** of an integral `k`-scheme: the algebraic closure of `k` in `K(N)`. -/
noncomputable abbrev constField : IntermediateField k N.functionField :=
  algebraicClosure k N.functionField

/-- An element of `K(N)` integral over `k` is regular on every nonempty affine open on which the
sections form an integrally closed ring. -/
lemma exists_germ_of_isIntegral {α : N.functionField} (hα : IsIntegral k α) {V : N.Opens}
    (hV : IsAffineOpen V) [Nonempty V] [IsIntegrallyClosed Γ(N, V)] :
    ∃ g : Γ(N, V), N.germToFunctionField V g = α := by
  letI := sectionsAlgebra k N V
  haveI := functionField_isFractionRing_of_isAffineOpen N V hV
  haveI : IsScalarTower k Γ(N, V) N.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ algebraMap_functionField_eq_germ k N V c
  exact IsIntegrallyClosed.isIntegral_iff.1 (hα.tower_top (A := Γ(N, V)))

variable (hN : ∀ (V : N.Opens), IsAffineOpen V → ∀ [Nonempty V], IsIntegrallyClosed Γ(N, V))

include hN in
lemma exists_germ_top_of_mem_constField (a : constField k N) :
    ∃ g : Γ(N, ⊤), N.germToFunctionField ⊤ g = a :=
  exists_germToFunctionField_top fun V hV _ ↦
    haveI := hN V hV
    exists_germ_of_isIntegral k N a.2 hV

include hN in
lemma mem_range_germ_top (a : constField k N) :
    (constField k N).val.toRingHom a ∈ (N.germToFunctionField ⊤).hom.range :=
  exists_germ_top_of_mem_constField k N hN a

/-- The constant field consists of global sections: the ring map `k' → Γ(N, ⊤)`. -/
noncomputable def constFieldToΓ : constField k N →+* Γ(N, ⊤) :=
  (germTopEquiv N).symm.toRingHom.comp
    ((constField k N).val.toRingHom.codRestrict _ (mem_range_germ_top k N hN))

lemma germ_constFieldToΓ (a : constField k N) :
    N.germToFunctionField ⊤ (constFieldToΓ k N hN a) = a :=
  congrArg Subtype.val ((germTopEquiv N).apply_symm_apply
    ((constField k N).val.toRingHom.codRestrict _ (mem_range_germ_top k N hN) a))

/-- The structure morphism of `N` over its constant field. -/
noncomputable def toSpecConstField : N ⟶ Spec (.of (constField k N)) :=
  N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constFieldToΓ k N hN))

lemma ΓSpecIso_inv_appTop_toSpecConstField :
    (Scheme.ΓSpecIso (.of (constField k N))).inv ≫ (toSpecConstField k N hN).appTop =
      CommRingCat.ofHom (constFieldToΓ k N hN) := by
  simp [toSpecConstField, Scheme.toSpecΓ_appTop]

lemma germ_appTop_toSpecConstField (a : constField k N) :
    N.germToFunctionField ⊤
      ((toSpecConstField k N hN).appTop ((Scheme.ΓSpecIso (.of (constField k N))).inv a)) =
      a := by
  have h2 : (toSpecConstField k N hN).appTop ((Scheme.ΓSpecIso (.of (constField k N))).inv a) =
      constFieldToΓ k N hN a :=
    congrArg (fun φ ↦ φ.hom a) (ΓSpecIso_inv_appTop_toSpecConstField k N hN)
  rw [h2]
  exact germ_constFieldToΓ k N hN a

/-- **Compatibility**: `N ⟶ Spec k' ⟶ Spec k` is the structure morphism of `N`. -/
theorem toSpecConstField_comp :
    toSpecConstField k N hN ≫ Spec.map (CommRingCat.ofHom (algebraMap k (constField k N))) =
      N ↘ Spec (.of k) := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (toSpecConstField k N hN ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (constField k N)))).appTop =
      CommRingCat.ofHom (algebraMap k (constField k N)) ≫
        (Scheme.ΓSpecIso (.of (constField k N))).inv ≫ (toSpecConstField k N hN).appTop := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  rw [key]
  ext c
  apply N.germToFunctionField_injective ⊤
  refine (germ_appTop_toSpecConstField k N hN _).trans ?_
  rfl

/-- `k'` is algebraically closed in `K(N)`, for any `k'`-algebra structure on `K(N)` given by
the inclusion. -/
lemma constField_isAlgClosedIn (inst : Algebra (constField k N) N.functionField)
    (h : ∀ a : constField k N, @algebraMap _ _ _ _ inst a = a) (x : N.functionField)
    (hx : @IsAlgebraic (constField k N) _ _ _ inst x) :
    x ∈ (@algebraMap _ _ _ _ inst).range := by
  obtain rfl : inst = IntermediateField.toAlgebra (constField k N) :=
    Algebra.algebra_ext _ _ fun a ↦ (h a).trans rfl
  have hk : IsIntegral k x := isIntegral_trans (A := constField k N) x hx.isIntegral
  exact ⟨⟨x, hk⟩, rfl⟩

include hN in
/-- **The constant field is finite over `k`.** -/
theorem finiteDimensional_constField [LocallyOfFiniteType (N ↘ Spec (.of k))] :
    FiniteDimensional k (constField k N) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty N)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI := sectionsAlgebra k N V
  haveI : Algebra.FiniteType k Γ(N, V) := by
    have h1 := (N ↘ Spec (.of k)).finiteType_appLE (isAffineOpen_top _) hV (by simp)
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
    exact h1.comp h2
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(N, V)
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (Γ(N, V) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      Ideal.Quotient.mk_surjective
  haveI := finite_of_finite_type_of_isJacobsonRing k (Γ(N, V) ⧸ m)
  let r : Γ(N, ⊤) →+* Γ(N, V) := (N.presheaf.map (homOfLE le_top).op).hom
  have hr : ∀ c : k, r (constFieldToΓ k N hN (algebraMap k (constField k N) c)) =
      algebraMap k Γ(N, V) c := fun c ↦ by
    apply N.germToFunctionField_injective V
    rw [← algebraMap_functionField_eq_germ k N V c]
    change N.presheaf.germ _ _ _ (N.presheaf.map _ _) = _
    rw [TopCat.Presheaf.germ_res_apply]
    exact germ_constFieldToΓ k N hN _
  let ψ : constField k N →ₐ[k] Γ(N, V) ⧸ m :=
    { (Ideal.Quotient.mk m).comp (r.comp (constFieldToΓ k N hN)) with
      commutes' := fun c ↦ by
        change Ideal.Quotient.mk m (r _) = _
        rw [hr c]
        rfl }
  exact FiniteDimensional.of_injective ψ.toLinearMap ψ.toRingHom.injective

/-- `Ω[K(N)⁄k']` has rank `1` if `N` is smooth of relative dimension `1` over `k`. -/
theorem rank_kaehler_constField [CharZero k] [SmoothOfRelativeDimension 1 (N ↘ Spec (.of k))] :
    Module.rank N.functionField Ω[N.functionField⁄constField k N] = 1 := by
  haveI : Algebra.FormallyUnramified k (constField k N) :=
    Algebra.FormallyUnramified.of_isSeparable k (constField k N)
  rw [← rank_kaehler_eq_of_subsingleton k (constField k N) N.functionField]
  obtain ⟨x⟩ := (inferInstance : Nonempty N)
  obtain ⟨U₀, -, V₀, hV₀, hx, e₀, h₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1)
      (f := N ↘ Spec (.of k)) x
  obtain rfl : U₀ = ⊤ := opens_eq_top_of_mem (e₀ hx)
  haveI : Nonempty V₀ := ⟨⟨x, hx⟩⟩
  have := (isStandardSmoothOfRelativeDimension_appLE_iff (N ↘ Spec (.of k)) (fun _ ↦ rfl) 1
    hV₀ e₀ (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 _ h₀)).1 h₀
  exact_mod_cast this

include hN in
/-- `N` is locally of finite type over `k'`. -/
lemma locallyOfFiniteType_toSpecConstField [LocallyOfFiniteType (N ↘ Spec (.of k))] :
    LocallyOfFiniteType (toSpecConstField k N hN) := by
  haveI : LocallyOfFiniteType (toSpecConstField k N hN ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (constField k N)))) := by
    rw [toSpecConstField_comp]
    infer_instance
  exact locallyOfFiniteType_of_comp _
    (Spec.map (CommRingCat.ofHom (algebraMap k (constField k N))))

include hN in
/-- `N` is smooth over `k'`. -/
theorem smooth_toSpecConstField [CharZero k] [LocallyOfFiniteType (N ↘ Spec (.of k))]
    (hdim : ∀ x : N, ringKrullDim (N.presheaf.stalk x) ≤ 1) :
    Smooth (toSpecConstField k N hN) := by
  haveI : CharZero (constField k N) :=
    charZero_of_injective_algebraMap (algebraMap k (constField k N)).injective
  haveI := locallyOfFiniteType_toSpecConstField k N hN
  haveI : LocallyOfFinitePresentation (toSpecConstField k N hN) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI := hN V hV
  exact Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one _ hV hxV (hdim x)

include hN in
/-- `N` is smooth of relative dimension `1` over `k'`. -/
theorem smoothOfRelativeDimension_toSpecConstField [CharZero k]
    [LocallyOfFiniteType (N ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (N ↘ Spec (.of k))]
    (hdim : ∀ x : N, ringKrullDim (N.presheaf.stalk x) ≤ 1) :
    SmoothOfRelativeDimension 1 (toSpecConstField k N hN) := by
  haveI := smooth_toSpecConstField k N hN hdim
  have hrank := rank_kaehler_constField k N
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U₁, hU₁, V, hV, hx, e, hss⟩ := Smooth.exists_isStandardSmooth (toSpecConstField k N hN) x
  obtain rfl : U₁ = ⊤ := opens_eq_top_of_mem (e hx)
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  exact ⟨⊤, hU₁, V, hV, hx, e, (isStandardSmoothOfRelativeDimension_appLE_iff
    (toSpecConstField k N hN) (fun c ↦ (germ_appTop_toSpecConstField k N hN c).symm) 1 hV e
    hss).2 (by exact_mod_cast hrank)⟩

include hN in
/-- **An integral normal proper smooth `k`-scheme of relative dimension one with stalks of
dimension `≤ 1` is a curve over its constant field.** -/
theorem isCurveOver_constField [CharZero k] [IsProper (N ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (N ↘ Spec (.of k))]
    (hdim : ∀ x : N, ringKrullDim (N.presheaf.stalk x) ≤ 1) :
    @Belyi.IsCurveOver (constField k N) _ N ⟨toSpecConstField k N hN⟩ := by
  letI : N.Over (Spec (.of (constField k N))) := ⟨toSpecConstField k N hN⟩
  have h₁ := smoothOfRelativeDimension_toSpecConstField k N hN hdim
  have h₂ : IsProper (toSpecConstField k N hN) := by
    haveI : IsProper (toSpecConstField k N hN ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (constField k N)))) := by
      rw [toSpecConstField_comp]
      infer_instance
    exact IsProper.of_comp (f := toSpecConstField k N hN)
      (g := Spec.map (CommRingCat.ofHom (algebraMap k (constField k N))))
  haveI : CharZero (constField k N) :=
    charZero_of_injective_algebraMap (algebraMap k (constField k N)).injective
  have h₃ := geometricallyIntegral_of_isAlgClosedIn (K := constField k N) (X := N)
    (constField_isAlgClosedIn k N _ fun a ↦ germ_appTop_toSpecConstField k N hN a)
  exact { toSmoothOfRelativeDimension := h₁, toIsProper := h₂, toGeometricallyIntegral := h₃ }

end ConstField

/-! ### The normalisation of a curve in a finite étale cover -/

section Curve

variable {k : Type u} [Field k] [CharZero k] {Xb : Scheme.{u}} [Xb.Over (Spec (.of k))]
  [Belyi.IsCurveOver k Xb] {U : Xb.Opens} (hU : (U : Set Xb).Nonempty) {Y : Scheme.{u}}
  (p : Y ⟶ U) [IsFinite p] [Etale p]

include hU in
/-- **The constant field of the normalisation is finite over `k`.** -/
theorem finiteDimensional_constField_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    letI := normalizationOver k p
    FiniteDimensional k (constField k (p ≫ U.ι).normalization) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  letI := normalizationOver k p
  haveI := Belyi.IsCurveOver.isIntegral k Xb
  haveI : IsProper ((p ≫ U.ι).normalization ↘ Spec (.of k)) := isProper_normalization (k := k) hU p
  exact finiteDimensional_constField k _ fun V hV _ ↦
    isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := k)) hU p hV

include hU in
/-- **The normalisation of a curve in a finite étale cover is a curve over its constant field**
`k' = constField k N`, via a structure morphism `N ⟶ Spec k'` lifting `q ≫ (X̄ ↘ Spec k)`. -/
theorem isCurveOver_normalization_constField [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    letI := normalizationOver k p
    ∃ s' : (p ≫ U.ι).normalization ⟶ Spec (.of (constField k (p ≫ U.ι).normalization)),
      s' ≫ Spec.map (CommRingCat.ofHom
          (algebraMap k (constField k (p ≫ U.ι).normalization))) =
        (p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k)) ∧
      @Belyi.IsCurveOver (constField k (p ≫ U.ι).normalization) _ (p ≫ U.ι).normalization
        ⟨s'⟩ := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  letI := normalizationOver k p
  haveI := Belyi.IsCurveOver.isIntegral k Xb
  have hN : ∀ (V : (p ≫ U.ι).normalization.Opens), IsAffineOpen V → ∀ [Nonempty V],
      IsIntegrallyClosed Γ((p ≫ U.ι).normalization, V) := fun V hV _ ↦
    isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := k)) hU p hV
  haveI : IsProper ((p ≫ U.ι).normalization ↘ Spec (.of k)) := isProper_normalization (k := k) hU p
  haveI : SmoothOfRelativeDimension 1 ((p ≫ U.ι).normalization ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_normalization (k := k) hU p
  exact ⟨toSpecConstField k _ hN, toSpecConstField_comp k _ hN,
    isCurveOver_constField k _ hN (ringKrullDim_stalk_normalization_le (k := k) hU p)⟩

end Curve

end CurvesJacobian.Cusp
