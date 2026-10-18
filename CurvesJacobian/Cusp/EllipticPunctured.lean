/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticCurveScheme
import CurvesJacobian.Cusp.CoverGaloisData

/-!
# `Γ(E ∖ {O}) = K[E]`

The ring of functions of IUT's once-punctured elliptic curve `X = E ∖ {O} = q⁻¹ 𝔸¹ ⊆ Ē`
(`CurvesJacobian.Cusp.hypCurveX`) is the affine coordinate ring `K[E]` of the Weierstrass model
(`CurvesJacobian.Cusp.sectionsXEEquiv`), compatibly with `Γ(E ∖ E[2]) = K[E][1/ψ]`.

Inside `K(E)`, both are the integral closure of `K[x]`: a function on `q⁻¹ 𝔸¹` is integral over
`Γ(𝔸¹) = K[x]` (`q` is finite), and `K[E]` is integrally closed (`elliptic-curves`); conversely
`x = q^* T` is regular on `q⁻¹ 𝔸¹` and `y` is integral over `K[x]`, while `Γ(q⁻¹ 𝔸¹)` is integrally
closed.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian
open WeierstrassCurve.Affine.CoordinateRing

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-- For an open immersion `j : Spec R ⟶ X` onto an affine open `V`, the restriction
`Γ(X, V) ⟶ Γ(Spec R, ⊤)` is an isomorphism. -/
lemma isIso_appLE_of_isOpenImmersion {X : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ X)
    [IsOpenImmersion j] {V : X.Opens} (hV : IsAffineOpen V) (hr : Set.range j = (V : Set X))
    (hle : (⊤ : (Spec R).Opens) ≤ j ⁻¹ᵁ V) : IsIso (j.appLE V ⊤ hle) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec j hV (isAffineOpen_top _) hle
  rw [IsAffineOpen.fromSpec_top] at h
  have hr' : Set.range ((Spec R).isoSpec.inv ≫ j) = Set.range hV.fromSpec := by
    rw [IsAffineOpen.range_fromSpec, ← hr]
    ext y
    refine ⟨fun ⟨z, hz⟩ ↦ ⟨_, hz⟩, fun ⟨z, hz⟩ ↦ ⟨(Spec R).isoSpec.hom z, ?_⟩⟩
    rw [← hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  have h' : Spec.map (j.appLE V ⊤ hle) = (IsOpenImmersion.isoOfRangeEq _ _ hr').hom := by
    rw [← cancel_mono hV.fromSpec, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact h
  haveI : IsIso (Spec.map (j.appLE V ⊤ hle)) := by rw [h']; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).2 (isIso_SpecMap_iff.1 inferInstance)

lemma appLE_comp_appLE_of_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ h ⁻¹ᵁ U) : g.appLE U V e₁ ≫ f.appLE V W e₂ = h.appLE U W e := by
  subst hfg
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The affine line `𝔸¹ = D₊(X₁) ⊆ ℙ¹_k`. -/
abbrev A1 : (P1 k).Opens := (lineChart k).opensRange

lemma lineChart_le : (⊤ : (Spec (.of k[X])).Opens) ≤ lineChart k ⁻¹ᵁ A1 k := fun y _ ↦ ⟨y, rfl⟩

instance : IsIso ((lineChart k).appLE (A1 k) ⊤ (lineChart_le k)) :=
  isIso_appLE_of_isOpenImmersion _ (isAffineOpen_opensRange _) rfl _

/-- `Γ(𝔸¹) ≅ k[T]`. -/
def sectionsA1Iso : Γ(P1 k, A1 k) ≅ .of k[X] :=
  asIso ((lineChart k).appLE (A1 k) ⊤ (lineChart_le k)) ≪≫ Scheme.ΓSpecIso _

end Chart

section Punctured

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField

/-- `q^* : Γ(𝔸¹) → Γ(E ∖ {O})`. -/
abbrev qXE : Γ(P1 K, A1 K) ⟶ Γ(curveE E, XE E) := (qE E).app (A1 K)

/-- The restriction `Γ(E ∖ {O}) → Γ(E ∖ E[2])`. -/
abbrev resVX : Γ(curveE E, XE E) ⟶ Γ(curveE E, VE E) :=
  (curveE E).presheaf.map (homOfLE (VE_le_XE E)).op

omit [CharZero K] [E.IsElliptic] in
lemma qXE_resVX_restrVE : qXE E ≫ resVX E ≫ restrVE E = (sectionsA1Iso K).hom ≫
    CommRingCat.ofHom (algebraMap K[X] (coverRingE E)) ≫ (Scheme.ΓSpecIso _).inv := by
  have h1 : qXE E ≫ resVX E = (qE E).appLE (A1 K) (VE E) (VE_le_XE E) := by
    rw [qXE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have hcomp : toCurveE E ≫ qE E =
      Spec.map (CommRingCat.ofHom (algebraMap K[X] (coverRingE E))) ≫ lineChart K := by
    rw [Scheme.Hom.toNormalization_fromNormalization, pE_ι]
  rw [← Category.assoc, h1, restrVE, appLE_comp_appLE_of_eq _ _ _ hcomp _ _ _ _ _
    (by intro y _; change _ ∈ Set.range (lineChart K); exact ⟨_, rfl⟩),
    ← appLE_comp_appLE_of_eq _ _ _ rfl (A1 K) ⊤ ⊤ (lineChart_le K)
    le_rfl, sectionsA1Iso, Iso.trans_hom, asIso_hom, Category.assoc]
  congr 1
  rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rfl

/-- `Γ(E ∖ {O}) → K(E)`, through `Γ(E ∖ E[2]) = K[E][1/ψ] ⊆ K(E)`. -/
def thetaX : Γ(curveE E, XE E) →+* FF :=
  (algebraMap (coverRingE E) FF).comp ((sectionsVEEquiv E).toRingHom.comp (resVX E).hom)

lemma thetaX_qXE (p : K[X]) :
    thetaX E (qXE E ((sectionsA1Iso K).inv p)) = algebraMap K[X] FF p := by
  have h := congrArg (fun f ↦ f ((sectionsA1Iso K).inv p)) (qXE_resVX_restrVE E)
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h
  change algebraMap (coverRingE E) FF ((Scheme.ΓSpecIso _).hom (restrVE E (resVX E
    (qXE E ((sectionsA1Iso K).inv p))))) = _
  rw [h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change algebraMap (coverRingE E) FF (algebraMap K[X] (coverRingE E) p) = _
  rw [IsScalarTower.algebraMap_apply K[X] A (coverRingE E), ι_algebraMap_coordinateRing,
    ← IsScalarTower.algebraMap_apply]

instance : Nonempty (XE E) := by
  obtain ⟨⟨c, hc⟩⟩ : Nonempty (VE E) := inferInstance
  exact ⟨⟨c, VE_le_XE E hc⟩⟩

lemma resVX_injective : Function.Injective (resVX E) := by
  intro a b h
  apply (curveE E).germToFunctionField_injective (XE E)
  rw [← germToFunctionField_res (homOfLE (VE_le_XE E)) a,
    ← germToFunctionField_res (homOfLE (VE_le_XE E)) b]
  exact congrArg _ h

lemma thetaX_injective : Function.Injective (thetaX E) :=
  (algebraMap_coverRingE_injective E).comp ((sectionsVEEquiv E).injective.comp
    (resVX_injective E))

lemma isAffineOpen_XE : IsAffineOpen (XE E) := (isAffineOpen_opensRange (lineChart K)).preimage _

instance : IsIntegrallyClosed Γ(curveE E, XE E) :=
  isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := K)) (U0E_nonempty E)
    (pE E) (isAffineOpen_XE E)

instance : IsFractionRing Γ(curveE E, XE E) (curveE E).functionField :=
  functionField_isFractionRing_of_isAffineOpen (curveE E) (XE E) (isAffineOpen_XE E)

/-- `x = q^* T ∈ Γ(E ∖ {O})`. -/
abbrev xX : Γ(curveE E, XE E) := qXE E ((sectionsA1Iso K).inv X)

lemma resVX_xX : resVX E (xX E) = (sectionsVEEquiv E).symm (xB E) := by
  apply (sectionsVEEquiv E).injective
  apply algebraMap_coverRingE_injective E
  rw [RingEquiv.apply_symm_apply]
  refine (thetaX_qXE E X).trans ?_
  rw [ι_xB]
  rfl

lemma germ_xX : algebraMap Γ(curveE E, XE E) (curveE E).functionField (xX E) = xN E := by
  change (curveE E).germToFunctionField (XE E) (xX E) = _
  rw [← germToFunctionField_res (homOfLE (VE_le_XE E)) (xX E)]
  change (curveE E).germToFunctionField (VE E) (resVX E (xX E)) = _
  rw [resVX_xX]
  rfl

lemma germ_algebraMap_XE (c : K) :
    algebraMap Γ(curveE E, XE E) (curveE E).functionField (algebraMap K _ c) =
      algebraMap K (curveE E).functionField c :=
  (algebraMap_functionField_eq_germ K (curveE E) (XE E) c).symm

/-- `y ∈ Γ(E ∖ {O})`: it is integral over `K[x]` and `Γ(E ∖ {O})` is integrally closed. -/
lemma exists_yX : ∃ s : Γ(curveE E, XE E),
    algebraMap Γ(curveE E, XE E) (curveE E).functionField s = yN E := by
  refine IsIntegrallyClosed.isIntegral_iff.1 ⟨X ^ 2 + C (algebraMap K _ E.a₁ * xX E +
    algebraMap K _ E.a₃) * X - C (xX E ^ 3 + algebraMap K _ E.a₂ * xX E ^ 2 +
      algebraMap K _ E.a₄ * xX E + algebraMap K _ E.a₆), ?_, ?_⟩
  · refine Monic.sub_of_left (Monic.add_of_left (monic_X_pow 2) ?_) ?_
    · exact (degree_C_mul_X_le _).trans_lt (by rw [degree_X_pow]; norm_num)
    · refine (degree_C_le).trans_lt ?_
      rw [degree_add_eq_left_of_degree_lt ((degree_C_mul_X_le _).trans_lt (by
        rw [degree_X_pow]; norm_num)), degree_X_pow]
      norm_num
  · have h := wEq_curveE E
    rw [WEq] at h
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, map_add,
      map_mul, map_pow, germ_xX, germ_algebraMap_XE]
    linear_combination h

/-- A chosen `y ∈ Γ(E ∖ {O})`. -/
def yX : Γ(curveE E, XE E) := (exists_yX E).choose

lemma germ_yX : algebraMap Γ(curveE E, XE E) (curveE E).functionField (yX E) = yN E :=
  (exists_yX E).choose_spec

lemma thetaX_yX : thetaX E (yX E) = genY E.toAffine := by
  have h : resVX E (yX E) = (sectionsVEEquiv E).symm (yB E) := by
    apply (curveE E).germToFunctionField_injective (VE E)
    change (curveE E).germToFunctionField (VE E) ((curveE E).presheaf.map
      (homOfLE (VE_le_XE E)).op (yX E)) = _
    rw [germToFunctionField_res]
    exact germ_yX E
  change algebraMap (coverRingE E) FF (sectionsVEEquiv E (resVX E (yX E))) = _
  rw [h, RingEquiv.apply_symm_apply, ι_yB]

/-- `K[x] → Γ(E ∖ {O})`, `x ↦ q^* T`. -/
def polyToXE : K[X] →+* Γ(curveE E, XE E) := (qXE E).hom.comp (sectionsA1Iso K).inv.hom

lemma thetaX_comp_polyToXE : (thetaX E).comp (polyToXE E) = algebraMap K[X] FF :=
  RingHom.ext fun p ↦ thetaX_qXE E p

omit [CharZero K] [E.IsElliptic] in
lemma algebraMap_coordinateRing_mk (p : K[X][X]) :
    algebraMap A FF (AdjoinRoot.mk _ p) = p.eval₂ (algebraMap K[X] FF) (genY E.toAffine) := by
  rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq]
  rfl

/-- **`K[E] → Γ(E ∖ {O})`**, `x ↦ q^* T`, `y ↦ y`. -/
def coordToXE : A →+* Γ(curveE E, XE E) :=
  AdjoinRoot.lift (polyToXE E) (yX E) (by
    apply thetaX_injective E
    rw [map_zero, hom_eval₂, thetaX_comp_polyToXE, thetaX_yX, ← algebraMap_coordinateRing_mk,
      AdjoinRoot.mk_self, map_zero])

lemma thetaX_comp_coordToXE : (thetaX E).comp (coordToXE E) = algebraMap A FF := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, coordToXE, AdjoinRoot.lift_comp_of, thetaX_comp_polyToXE,
      IsScalarTower.algebraMap_eq K[X] A FF]
    rfl
  · rw [RingHom.comp_apply, coordToXE, AdjoinRoot.lift_root, thetaX_yX]
    rfl

omit [CharZero K] [E.IsElliptic] in
/-- `Γ(E ∖ {O})` is integral over `Γ(𝔸¹)` (`q` is finite). -/
lemma isIntegral_qXE (b : Γ(curveE E, XE E)) :
    letI := (qXE E).hom.toAlgebra
    IsIntegral Γ(P1 K, A1 K) b := by
  letI := (qXE E).hom.toAlgebra
  letI := ((pE E ≫ (U0E E).ι).app (A1 K)).hom.toAlgebra
  let e := (pE E ≫ (U0E E).ι).normalizationObjIso (isAffineOpen_opensRange (lineChart K))
  have hb : e.inv (e.hom b) = b := Iso.hom_inv_id_apply e b
  rw [← hb]
  refine IsIntegral.map_of_comp_eq (RingHom.id Γ(P1 K, A1 K)) e.inv.hom ?_
    (integralClosure.isIntegral (e.hom b))
  rw [RingHom.comp_id]
  exact congrArg CommRingCat.Hom.hom
    ((pE E ≫ (U0E E).ι).fromNormalization_app (isAffineOpen_opensRange (lineChart K)))

lemma coordToXE_bijective : Function.Bijective (coordToXE E) := by
  refine ⟨fun a b h ↦ IsFractionRing.injective A FF ?_, fun s ↦ ?_⟩
  · rw [← thetaX_comp_coordToXE, RingHom.comp_apply, RingHom.comp_apply, h]
  letI := (qXE E).hom.toAlgebra
  have h1 : IsIntegral K[X] (thetaX E s) := by
    refine IsIntegral.map_of_comp_eq (sectionsA1Iso K).hom.hom (thetaX E) ?_ (isIntegral_qXE E s)
    refine RingHom.ext fun t ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← thetaX_qXE E]
    erw [Iso.hom_inv_id_apply]
    rfl
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral E.toAffine.CoordinateRing (thetaX E s) from h1.tower_top)
  refine ⟨a, thetaX_injective E ?_⟩
  rw [← ha, ← thetaX_comp_coordToXE, RingHom.comp_apply]

lemma coordToXE_algebraMap (c : K) :
    coordToXE E (algebraMap K A c) = algebraMap K Γ(curveE E, XE E) c := by
  apply thetaX_injective E
  rw [← RingHom.comp_apply, thetaX_comp_coordToXE, ← IsScalarTower.algebraMap_apply]
  change _ = algebraMap (coverRingE E) FF (sectionsVEEquiv E (resVX E _))
  have : resVX E (algebraMap K Γ(curveE E, XE E) c) = algebraMap K Γ(curveE E, VE E) c := by
    change ((curveE E ↘ Spec (.of K)).appLE ⊤ (XE E) _ ≫ resVX E) _ = _
    rw [Scheme.Hom.appLE_map]
    rfl
  rw [this, sectionsVEEquiv_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **`Γ(E ∖ {O}) = K[E]`**: the ring of functions of IUT's once-punctured elliptic curve is the
affine coordinate ring of the Weierstrass model. -/
def sectionsXEAlgEquiv : Γ(curveE E, XE E) ≃ₐ[K] A :=
  (AlgEquiv.ofBijective { coordToXE E with commutes' := coordToXE_algebraMap E }
    (coordToXE_bijective E)).symm

lemma sectionsXEAlgEquiv_symm_apply (a : A) :
    (sectionsXEAlgEquiv E).symm a = coordToXE E a := rfl

/-- The restriction `Γ(E ∖ {O}) → Γ(E ∖ E[2])` is `K[E] → K[E][1/ψ]`. -/
lemma sectionsVEEquiv_resVX (s : Γ(curveE E, XE E)) :
    sectionsVEEquiv E (resVX E s) =
      algebraMap A (coverRingE E) (sectionsXEAlgEquiv E s) := by
  apply algebraMap_coverRingE_injective E
  rw [ι_algebraMap_coordinateRing, ← thetaX_comp_coordToXE, RingHom.comp_apply,
    ← sectionsXEAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]
  rfl

end Punctured

end CurvesJacobian.Cusp
