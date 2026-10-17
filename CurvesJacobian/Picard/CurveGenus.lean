/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurveCover
import CurvesJacobian.Picard.CechBaseChange
import CurvesJacobian.FunctionField.CechGenus
import CurvesJacobian.Scheme.CurvePic
import CurvesJacobian.Scheme.CurveFunctionField

/-!
# `h¹(X, 𝒪_X) = g` for a curve

Let `X` be a curve over a perfect field `k` (`Belyi.IsCurveOver`) and let `U`, `V` be affine opens
covering `X`. The two-set Čech `H¹` of `𝒪_X` for `(U, V)` (`CurvesJacobian.Cech.cechH1`, the
cokernel of `Γ(U) × Γ(V) → Γ(U ∩ V)`) has dimension `curveGenus k X` over `Γ(Spec k) = k`
(`CurvesJacobian.finrank_cechH1_eq_curveGenus`); in particular it does not depend on the cover.
This closes the comparison "genus = h¹(𝒪)" of CJ4b (with `H¹` computed by any two-affine
cover, which exists by `IsCurveOver.exists_two_affine_cover`).

Ingredients:
* on an integral scheme, a rational function lies in `Γ(W, 𝒪)` iff it lies in every stalk
  `𝒪_{X,x}`, `x ∈ W` (gluing; `CurvesJacobian.exists_section_of_forall_mem_stalk`);
* on a curve, the complement of a nonempty open is a finite set of closed points
  (belyi's `finite_of_isClosed_of_genericPoint_notMem`), which correspond to places
  (`curvePlaceEquiv`), so `Γ(W, 𝒪) ≅ regularOutside s_W` (`CurvesJacobian.sectionsEquiv`);
* a curve is not affine, so `s_U`, `s_V` are nonempty (and disjoint as `U ∪ V = X`);
* the function-field computation `CurvesJacobian.finrank_cechH1FF` (Riemann–Roch), with
  `ℓ(0) = 1` since `k` is algebraically closed in `K(X)`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi Opposite
open WeilCurves.FunctionField WeilCurves.FunctionField.Divisor Module

universe u

noncomputable section

namespace CurvesJacobian

section Integral

variable {X : Scheme.{u}} [IsIntegral X]

lemma genericPoint_mem_of_nonempty (W : X.Opens) [h : Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.2).mpr ⟨h.some.1, trivial, h.some.2⟩

lemma germToFunctionField_res {W W' : X.Opens} [Nonempty W] [Nonempty W'] (i : W' ⟶ W)
    (a : Γ(X, W)) :
    X.germToFunctionField W' (X.presheaf.map i.op a) = X.germToFunctionField W a := by
  simp only [Scheme.germToFunctionField]
  exact X.presheaf.germ_res_apply i _ _ a

/-- On an integral scheme, a rational function which lies in every stalk `𝒪_{X,x}`, `x ∈ W`,
is a section over `W`. -/
lemma exists_section_of_forall_mem_stalk (W : X.Opens) [Nonempty W] (f : X.functionField)
    (hf : ∀ x ∈ W, f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    ∃ a : Γ(X, W), X.germToFunctionField W a = f := by
  choose s hs using fun x : W ↦ hf x.1 x.2
  choose U hxU b hb using fun x : W ↦ X.presheaf.exists_germ_eq (s x)
  let V : W → X.Opens := fun x ↦ U x ⊓ W
  have hxV : ∀ x : W, x.1 ∈ V x := fun x ↦ ⟨hxU x, x.2⟩
  haveI hne : ∀ x : W, Nonempty (V x) := fun x ↦ ⟨⟨x.1, hxV x⟩⟩
  haveI hneU : ∀ x : W, Nonempty (U x) := fun x ↦ ⟨⟨x.1, hxU x⟩⟩
  let sf : ∀ x : W, Γ(X, V x) := fun x ↦ X.presheaf.map (homOfLE inf_le_left).op (b x)
  have hsf : ∀ x : W, X.germToFunctionField (V x) (sf x) = f := by
    intro x
    rw [germToFunctionField_res, ← X.algebraMap_germ_eq_germToFunctionField (hxU x), hb,
      hs]
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V W (fun x ↦ homOfLE inf_le_right)
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩) sf (by
      intro x y
      haveI : Nonempty (V x ⊓ V y : X.Opens) :=
        ⟨⟨genericPoint X, genericPoint_mem_of_nonempty _, genericPoint_mem_of_nonempty _⟩⟩
      apply X.germToFunctionField_injective (V x ⊓ V y)
      change X.germToFunctionField _ (X.presheaf.map _ (sf x)) =
        X.germToFunctionField _ (X.presheaf.map _ (sf y))
      rw [germToFunctionField_res (W := V x), germToFunctionField_res (W := V y), hsf, hsf])
  refine ⟨a, ?_⟩
  obtain ⟨x⟩ := ‹Nonempty W›
  have hax : X.presheaf.map (homOfLE inf_le_right : V x ⟶ W).op a = sf x := ha x
  rw [← germToFunctionField_res (homOfLE inf_le_right : V x ⟶ W), hax, hsf]

/-- Every rational function lies in the stalk at the generic point. -/
lemma mem_range_algebraMap_of_eq_genericPoint {x : X} (hx : x = genericPoint X)
    (f : X.functionField) :
    f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  subst hx
  obtain ⟨U, hU, b, hb⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) f
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  exact ⟨X.presheaf.germ U _ hU b, by
    rw [X.algebraMap_germ_eq_germToFunctionField hU]
    exact hb⟩

end Integral

section Curve

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]

/-- The point of a curve corresponding to a place. -/
abbrev pointOfPlace [IsIntegral X] (P : Place k X.functionField) : X :=
  ((curvePlaceEquiv k X).symm P).1

lemma pointOfPlace_injective [IsIntegral X] : Function.Injective (pointOfPlace k X) :=
  fun _ _ h ↦ (curvePlaceEquiv k X).symm.injective (Subtype.ext h)

lemma place_val_eq [IsIntegral X] (P : Place k X.functionField) :
    P.1 = stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) (pointOfPlace k X P) := by
  rw [← curvePlaceEquiv_apply k X]
  simp

include k in
/-- The complement of a nonempty open of a curve is finite. -/
lemma finite_compl_of_nonempty [IsIntegral X] (W : X.Opens) [Nonempty W] :
    ((W : Set X)ᶜ).Finite := by
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  exact finite_of_isClosed_of_genericPoint_notMem (krullDimLE_one_stalk_of_isCurveOver k X)
    W.isOpen.isClosed_compl (fun h ↦ h (genericPoint_mem_of_nonempty W))

/-- The places "at infinity" of a nonempty open `W`: those whose point is not in `W`. -/
def placesOutside [IsIntegral X] (W : X.Opens) [Nonempty W] : Finset (Place k X.functionField) :=
  ((finite_compl_of_nonempty k X W).preimage
    (pointOfPlace_injective k X).injOn).toFinset

lemma mem_placesOutside [IsIntegral X] (W : X.Opens) [Nonempty W] (P : Place k X.functionField) :
    P ∈ placesOutside k X W ↔ pointOfPlace k X P ∉ W := by
  simp [placesOutside]

/-- Sections over a nonempty open `W` are the functions regular at all places of `W`. -/
lemma mem_regularOutside_iff [IsIntegral X] (W : X.Opens) [Nonempty W]
    {s : Finset (Place k X.functionField)} (hs : ∀ P, P ∈ s ↔ pointOfPlace k X P ∉ W)
    (f : X.functionField) :
    f ∈ regularOutside k s ↔ ∃ a : Γ(X, W), X.germToFunctionField W a = f := by
  constructor
  · intro hf
    apply exists_section_of_forall_mem_stalk W f
    intro x hx
    by_cases hη : x = genericPoint X
    · exact mem_range_algebraMap_of_eq_genericPoint hη f
    · let P := curvePlaceEquiv k X ⟨x, hη⟩
      have hPx : pointOfPlace k X P = x := by
        change ((curvePlaceEquiv k X).symm (curvePlaceEquiv k X ⟨x, hη⟩)).1 = x
        rw [Equiv.symm_apply_apply]
      have := hf P (by rw [hs, hPx]; exact not_not.mpr hx)
      rw [place_val_eq, hPx] at this
      exact this
  · rintro ⟨a, rfl⟩ P hP
    rw [hs, not_not] at hP
    rw [place_val_eq]
    exact ⟨X.presheaf.germ W _ hP a, X.algebraMap_germ_eq_germToFunctionField hP a⟩

/-- `Γ(W, 𝒪_X) ≅ regularOutside s_W`, as additive groups (via `Γ(W) ↪ K(X)`). -/
def sectionsEquiv [IsIntegral X] (W : X.Opens) [Nonempty W]
    {s : Finset (Place k X.functionField)} (hs : ∀ P, P ∈ s ↔ pointOfPlace k X P ∉ W) :
    Γ(X, W) ≃+ regularOutside k s :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun a ↦ (⟨X.germToFunctionField W a,
        (mem_regularOutside_iff k X W hs _).mpr ⟨a, rfl⟩⟩ : regularOutside k s))
      (fun a b ↦ Subtype.ext (map_add _ a b)) : Γ(X, W) →+ regularOutside k s)
    ⟨fun a b h ↦ X.germToFunctionField_injective W (congrArg Subtype.val h), fun f ↦ by
      obtain ⟨a, ha⟩ := (mem_regularOutside_iff k X W hs f).mp f.2
      exact ⟨a, Subtype.ext ha⟩⟩

lemma sectionsEquiv_apply [IsIntegral X] (W : X.Opens) [Nonempty W]
    {s : Finset (Place k X.functionField)} (hs : ∀ P, P ∈ s ↔ pointOfPlace k X P ∉ W)
    (a : Γ(X, W)) : (sectionsEquiv k X W hs a : X.functionField) = X.germToFunctionField W a :=
  rfl

include k in
/-- A curve is not affine. -/
lemma not_isAffine [IsIntegral X] : ¬ IsAffine X := by
  intro hX
  have hfield : IsField Γ(X, ⊤) := isField_of_universallyClosed k (X ↘ Spec (CommRingCat.of k))
  have hbot : ∀ p : Ideal Γ(X, ⊤), p.IsPrime → p = ⊥ := by
    intro p hp
    rw [eq_bot_iff]
    intro a ha
    by_contra ha0
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel (show a ≠ 0 from fun h ↦ ha0 (h ▸ Submodule.zero_mem _))
    exact hp.ne_top (p.eq_top_of_isUnit_mem ha (IsUnit.of_mul_eq_one b hb))
  obtain ⟨x⟩ := nonempty_closedPoint k X
  apply x.2
  apply X.isoSpec.hom.isOpenEmbedding.injective
  apply PrimeSpectrum.ext
  rw [hbot _ (X.isoSpec.hom x).isPrime, hbot _ (X.isoSpec.hom (genericPoint X)).isPrime]

include k in
lemma ne_top_of_isAffineOpen [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) : U ≠ ⊤ := by
  rintro rfl
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact not_isAffine k X (IsAffine.of_isIso X.topIso.inv)

include k in
lemma nonempty_of_sup_eq_top [IsIntegral X] {U V : X.Opens} (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) : Nonempty U := by
  by_contra hU
  rw [not_nonempty_iff] at hU
  apply ne_top_of_isAffineOpen k X hV
  rw [← h]
  have : U = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false, SetLike.mem_coe]
    exact fun hx ↦ hU.false ⟨x, hx⟩
  rw [this, bot_sup_eq]

lemma placesOutside_nonempty [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) :
    (placesOutside k X U).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply ne_top_of_isAffineOpen k X hU
  ext x
  simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
  by_cases hη : x = genericPoint X
  · exact hη ▸ genericPoint_mem_of_nonempty U
  · let P := curvePlaceEquiv k X ⟨x, hη⟩
    have hPx : pointOfPlace k X P = x := by
      change ((curvePlaceEquiv k X).symm (curvePlaceEquiv k X ⟨x, hη⟩)).1 = x
      rw [Equiv.symm_apply_apply]
    have : P ∉ placesOutside k X U := by simp [h]
    rw [mem_placesOutside, hPx, not_not] at this
    exact this

lemma disjoint_placesOutside [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : U ⊔ V = ⊤) : Disjoint (placesOutside k X U) (placesOutside k X V) := by
  rw [Finset.disjoint_left]
  intro P hU hV
  rw [mem_placesOutside] at hU hV
  have : pointOfPlace k X P ∈ U ⊔ V := h ▸ trivial
  rcases this with h' | h'
  · exact hU h'
  · exact hV h'

omit [PerfectField k] [IsCurveOver k X] in
open Cech in
/-- The scalar action of `Γ(Spec k, ⊤)` on sections, transported to `K(X)`. -/
lemma germToFunctionField_smul [IsIntegral X] (W : X.Opens) [Nonempty W]
    (c : Γ(Spec (CommRingCat.of k), ⊤)) (a : Γ(X, W)) :
    X.germToFunctionField W (c • a) =
      algebraMap k X.functionField ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c) *
        X.germToFunctionField W a := by
  rw [Algebra.smul_def, map_mul, algebraMap_functionField_eq_germ k X W]
  congr 2
  change ((X ↘ Spec (CommRingCat.of k)).appLE ⊤ W _) c =
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appLE ⊤ W _)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c)
  rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom,
    Iso.hom_inv_id, CommRingCat.id_apply]

/-- `ℓ(0) = 1` for the function field of a curve: `k` is algebraically closed in `K(X)`. -/
lemma ell_zero_eq_one [IsIntegral X] : ell (0 : Divisor k X.functionField) = 1 := by
  rw [ell_zero]
  have : integralClosure k X.functionField = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Algebra.mem_bot]
    obtain ⟨c, hc⟩ := curve_mem_range_algebraMap_of_isAlgebraic k X (IsIntegral.isAlgebraic hx)
    exact ⟨c, hc⟩
  rw [this, Subalgebra.finrank_bot]

lemma mem_placesOutside_inf [IsIntegral X] (U V : X.Opens) [Nonempty U] [Nonempty V]
    (P : Place k X.functionField) :
    P ∈ placesOutside k X U ∪ placesOutside k X V ↔ pointOfPlace k X P ∉ U ⊓ V := by
  rw [Finset.mem_union, mem_placesOutside, mem_placesOutside]
  change _ ↔ ¬ (_ ∈ U ∧ _ ∈ V)
  tauto

open Cech

/-- The scheme-theoretic Čech `H¹` of `𝒪_X` for `(U, V)` is the function-field one. -/
def cechH1Equiv [IsIntegral X] (U V : X.Opens) [Nonempty U] [Nonempty V]
    [Nonempty (U ⊓ V : X.Opens)] :
    cechH1 (Spec (CommRingCat.of k)) X U V ≃+
      cechH1FF k (placesOutside k X U) (placesOutside k X V) :=
  (((TwoCech.H1RestrictScalarsEquiv _ _).symm.trans
    (TwoCech.equivH1 (sectionsEquiv k X U (mem_placesOutside k X U)).toIntLinearEquiv
      (sectionsEquiv k X V (mem_placesOutside k X V)).toIntLinearEquiv
      (sectionsEquiv k X (U ⊓ V) (mem_placesOutside_inf k X U V)).toIntLinearEquiv
      (by
        ext a
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
          Submodule.coe_inclusion, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
          sectionsEquiv_apply, resLin_apply]
        rw [germToFunctionField_res])
      (by
        ext a
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
          Submodule.coe_inclusion, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
          sectionsEquiv_apply, resLin_apply]
        rw [germToFunctionField_res]))).trans
    (TwoCech.H1RestrictScalarsEquiv _ _)).toAddEquiv

lemma cechH1Equiv_mk [IsIntegral X] (U V : X.Opens) [Nonempty U] [Nonempty V]
    [Nonempty (U ⊓ V : X.Opens)] (r : Γ(X, U ⊓ V)) :
    cechH1Equiv k X U V (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (sectionsEquiv k X (U ⊓ V) (mem_placesOutside_inf k X U V) r) :=
  rfl

/-- **`h¹(X, 𝒪_X) = g`**: for a curve `X` over a perfect field `k` and any two affine opens
`U`, `V` covering `X`, the Čech `H¹` of `𝒪_X` for `(U, V)` has dimension `curveGenus k X` over
`Γ(Spec k, ⊤) = k`. -/
theorem finrank_cechH1_eq_curveGenus [IsIntegral X] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ⊔ V = ⊤) :
    (finrank Γ(Spec (CommRingCat.of k), ⊤) (cechH1 (Spec (CommRingCat.of k)) X U V) : ℤ) =
      curveGenus k X := by
  haveI : Nonempty U := nonempty_of_sup_eq_top k X hV h
  haveI : Nonempty V := nonempty_of_sup_eq_top k X hU (by rw [sup_comm]; exact h)
  haveI : Nonempty (U ⊓ V : X.Opens) :=
    ⟨⟨genericPoint X, genericPoint_mem_of_nonempty U, genericPoint_mem_of_nonempty V⟩⟩
  have hrank := rank_eq_of_equiv_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (cechH1Equiv k X U V)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom) (by
      intro c y
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, cechH1Equiv_mk, cechH1Equiv_mk,
        ← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_smul, sectionsEquiv_apply, sectionsEquiv_apply,
        germToFunctionField_smul, Algebra.smul_def])
  have hfin : finrank Γ(Spec (CommRingCat.of k), ⊤) (cechH1 (Spec (CommRingCat.of k)) X U V) =
      finrank k (cechH1FF k (placesOutside k X U) (placesOutside k X V)) :=
    congrArg Cardinal.toNat hrank
  rw [hfin, finrank_cechH1FF (disjoint_placesOutside k X h) (placesOutside_nonempty k X hU)
    (placesOutside_nonempty k X hV), ell_zero_eq_one]
  change _ = genus k X.functionField
  push_cast
  ring

end Curve

end CurvesJacobian

end
