/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiPi1
import CurvesJacobian.Cusp.ArithmeticExt

/-!
# `Π_X ↪ Π_C` for `X = E ∖ {O}` in the normalisation of `arithmeticExt` (MR8, [AbsTopII] Cor. 3.3)

Let `K` be a number field, `E` an elliptic curve over `K`, `X = E ∖ {O}` (`hypCurveX E`),
`Ω' ⊇ K` an algebraic closure and `Π_X ↠ G_K` the arithmetic fundamental group of `X` used by
`CurvesJacobian.Cusp.arithmeticExt Ω' (hypCurveX E) _`. Let `Ω = K(Ē)^alg`, `k̄ ⊆ Ω` the algebraic
closure of `K` in `Ω` and `D = hemiData E` the Galois data of the hemi-elliptic orbicurve
`C = [X / ±1]` (`CurvesJacobian.Cusp.HemiPi1`), with `Π_C = etalePi1 D.R D.A Ω`.

* Generic part (any `K` of characteristic `0`, `Ω` algebraically closed):
  `CurvesJacobian.Cusp.constFiberIso₂`: the fibre functors of `Spec K` at `Spec k̄` and at
  `Spec Ω` are isomorphic (a `k̄`-point gives an `Ω`-point by composition with `Spec Ω ⟶ Spec k̄`);
  hence `CurvesJacobian.Cusp.constGalEquiv₂ : Gal(k̄ / K) ≃ₜ* π₁ᵉᵗ(Spec K, Spec Ω)`, under which
  the Galois action of `Gal(Ω / F)` through a point `Spec F ⟶ Spec K` is the restriction to `k̄`
  (`galoisAction_eq_constGalEquiv₂`). For Galois data `D : GaloisData K t`, the map
  `π₁ᵉᵗ(Spec R) → π₁ᵉᵗ(Spec K)` is `piConstX D` (`fundamentalGroupMap_equivPi1Spec_symm₂`).
* `CurvesJacobian.Cusp.hemiSpecIso : Spec R ≅ Spec Γ(E ∖ {O})` (from `sectionsXEHemiAlgEquiv`),
  and the change of base point `hemiPiXEquiv : Π_X ≃ₜ* π₁ᵉᵗ(Spec R, Spec Ω)` given by an
  isomorphism of fibre functors (`hemiFiberIso`; canonical up to inner automorphisms);
  `hemiPiXGal : Π_X ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩`.
* `CurvesJacobian.Cusp.hemiGkEquiv : G_K ≃ₜ* Gal(k̄ / K)`, the change of base point induced by
  the same isomorphism of fibre functors, followed by `constGalEquiv₂⁻¹`. **Compatibility**
  (`hemiGkEquiv_pr`): `hemiGkEquiv ∘ pr = piConstX D ∘ hemiPiXGal` (exactly, no conjugation).
* **`Π_X ↪ Π_C`** (`hemi_arith_orbiEmb`): `hemiPiXEmb : Π_X →ₜ* Π_C` is an open embedding with
  normal image of index `2`, and `hemiPrC : Π_C →ₜ* G_K` (`= hemiGkEquiv⁻¹ ∘ piConstC D`,
  `hemiGkEquiv_hemiPrC`) extends `pr`, with `ker hemiPrC ∩ Π_X = Δ_X`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Orbifold AffOrbicurve
open PreGaloisCategory Topology Belyi

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section ConstantsPi1

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CharZero K]

instance isAlgClosed_constField₂ : IsAlgClosed (ConstField₂ K Ω) := IsAlgClosure.isAlgClosed K

/-- The geometric point `Spec k̄ ⟶ Spec K`. -/
abbrev constPoint₂ : Spec (.of (ConstField₂ K Ω)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ConstField₂ K Ω)))

/-- `Spec Ω ⟶ Spec k̄`. -/
abbrev constIncl₂ : Spec (.of Ω) ⟶ Spec (.of (ConstField₂ K Ω)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ConstField₂ K Ω) Ω))

omit [IsAlgClosed Ω] [CharZero K] in
lemma constIncl₂_comp :
    constIncl₂ K Ω ≫ constPoint₂ K Ω = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

omit [IsAlgClosed Ω] [CharZero K] in
lemma epi_constIncl₂ : Epi (constIncl₂ K Ω) := by
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ConstField₂ K Ω) Ω))).2 (by
      rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
      change Module.FaithfullyFlat (ConstField₂ K Ω) Ω
      haveI : Module.Free (ConstField₂ K Ω) Ω := Module.Free.of_divisionRing _ _
      exact Module.FaithfullyFlat.of_linearEquiv _ _
        (Module.Free.chooseBasis (ConstField₂ K Ω) Ω).repr)
  haveI := h.1
  haveI := h.2
  exact Flat.epi_of_flat_of_surjective _

variable {K Ω}

/-- A `k̄`-point of a finite étale `K`-scheme gives an `Ω`-point. -/
def constFiberMap₂ (A : FiniteEtale (Spec (.of K))) :
    (fiber (constPoint₂ K Ω)).obj A →
      (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj A := fun q =>
  (fiberObjEquivHom _ A).symm (Over.homMk (constIncl₂ K Ω ≫ (fiberObjEquivHom _ A q).left)
    ((Category.assoc _ _ _).trans ((congrArg (constIncl₂ K Ω ≫ ·)
      (Over.w (fiberObjEquivHom _ A q))).trans (constIncl₂_comp K Ω))))

omit [CharZero K] in
lemma constFiberMap₂_left (A : FiniteEtale (Spec (.of K)))
    (q : (fiber (constPoint₂ K Ω)).obj A) :
    (fiberObjEquivHom _ A (constFiberMap₂ A q)).left =
      constIncl₂ K Ω ≫ (fiberObjEquivHom _ A q).left := by
  rw [constFiberMap₂, Equiv.apply_symm_apply]
  rfl

omit [CharZero K] in
lemma constFiberMap₂_naturality {A B : FiniteEtale (Spec (.of K))} (g : A ⟶ B)
    (q : (fiber (constPoint₂ K Ω)).obj A) :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).map g (constFiberMap₂ A q) =
      constFiberMap₂ B ((fiber (constPoint₂ K Ω)).map g q) := by
  apply (fiberObjEquivHom _ B).injective
  apply Over.OverMorphism.ext
  rw [← fiberObjEquivHom_naturality, constFiberMap₂_left, ← fiberObjEquivHom_naturality]
  change (fiberObjEquivHom _ A (constFiberMap₂ A q)).left ≫ g.hom.left = _
  rw [constFiberMap₂_left]
  exact Category.assoc _ _ _

omit [CharZero K] in
lemma constFiberMap₂_injective (A : FiniteEtale (Spec (.of K))) :
    Function.Injective (constFiberMap₂ (Ω := Ω) A) := by
  intro q₁ q₂ h
  have h1 := congrArg (fun q => (fiberObjEquivHom _ A q).left) h
  simp only [constFiberMap₂_left] at h1
  haveI := epi_constIncl₂ K Ω
  exact (fiberObjEquivHom _ A).injective
    (Over.OverMorphism.ext ((cancel_epi (constIncl₂ K Ω)).1 h1))

omit [CharZero K] in
lemma constFiberMap₂_bijective (A : FiniteEtale (Spec (.of K))) :
    Function.Bijective (constFiberMap₂ (Ω := Ω) A) := by
  obtain ⟨γ⟩ := nonempty_iso_of_fiberFunctor (fiber (constPoint₂ K Ω))
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
  exact (constFiberMap₂_injective A).bijective_of_nat_card_le
    (Nat.card_congr (FintypeCat.equivEquivIso.symm (γ.app A))).symm.le

variable (K Ω)

/-- **The fibre functors of `Spec K` at `Spec k̄` and at `Spec Ω` are isomorphic.** -/
def constFiberIso₂ :
    fiber (constPoint₂ K Ω) ≅ fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (Equiv.ofBijective _ (constFiberMap₂_bijective A)))
    fun {A B} g => by
      ext q
      exact (constFiberMap₂_naturality g q).symm

/-- **`Gal(k̄ / K) ≃ₜ* π₁ᵉᵗ(Spec K, Spec Ω)`**, `k̄` the algebraic closure of `K` in `Ω`. -/
def constGalEquiv₂ : (ConstField₂ K Ω ≃ₐ[K] ConstField₂ K Ω) ≃ₜ*
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  ContinuousMulEquiv.trans
    { mulEquivAutFiber K (ConstField₂ K Ω) with
      continuous_toFun := (isHomeomorph_mulEquivAutFiber K (ConstField₂ K Ω)).continuous
      continuous_invFun :=
        (isHomeomorph_mulEquivAutFiber K (ConstField₂ K Ω)).homeomorph.symm.continuous }
    (autContinuousMulEquivOfIso (constFiberIso₂ K Ω))

lemma constGalEquiv₂_hom_app (g' : ConstField₂ K Ω ≃ₐ[K] ConstField₂ K Ω)
    (A : FiniteEtale (Spec (.of K))) (q : (fiber (constPoint₂ K Ω)).obj A) :
    (constGalEquiv₂ K Ω g').hom.app A (constFiberMap₂ A q) =
      constFiberMap₂ A ((mulEquivAutFiber K (ConstField₂ K Ω) g').hom.app A q) := by
  have h : (constFiberIso₂ K Ω).inv.app A ((constFiberIso₂ K Ω).hom.app A q) = q :=
    FintypeCat.hom_inv_id_apply ((constFiberIso₂ K Ω).app A) q
  change (constFiberIso₂ K Ω).hom.app A ((mulEquivAutFiber K (ConstField₂ K Ω) g').hom.app A
    ((constFiberIso₂ K Ω).inv.app A ((constFiberIso₂ K Ω).hom.app A q))) = _
  rw [h]
  rfl

/-- `Gal(k̄ / K)` acts on `k̄`-points by precomposition. -/
lemma mulEquivAutFiber_const_left (g' : ConstField₂ K Ω ≃ₐ[K] ConstField₂ K Ω)
    (A : FiniteEtale (Spec (.of K))) (q : (fiber (constPoint₂ K Ω)).obj A) :
    (fiberObjEquivHom _ A ((mulEquivAutFiber K (ConstField₂ K Ω) g').hom.app A q)).left =
      Spec.map (CommRingCat.ofHom (g' : ConstField₂ K Ω →+* ConstField₂ K Ω)) ≫
        (fiberObjEquivHom _ A q).left := by
  have hz : Spec.map (CommRingCat.ofHom (algebraMap K (ConstField₂ K Ω))) ≫ 𝟙 _ =
      constPoint₂ K Ω := Category.comp_id _
  have he : galoisAction K (𝟙 _) hz g' = mulEquivAutFiber K (ConstField₂ K Ω) g' := by
    change fundamentalGroupMap (𝟙 _) hz _ = _
    rw [fundamentalGroupMap_id]
    rfl
  rw [← he]
  exact galoisAction_hom_app_left K (𝟙 _) hz g' A q

/-- **The Galois action through a field-valued point of `Spec K` is the restriction to the
constants**: for `j : Spec F ⟶ Spec K` and `g ∈ Gal(Ω / F)` restricting to `g' ∈ Gal(k̄ / K)`,
`galoisAction F j g = constGalEquiv₂ g'`. -/
theorem galoisAction_eq_constGalEquiv₂ (F : Type u) [Field F] [Algebra F Ω] [IsGalois F Ω]
    (j : Spec (.of F) ⟶ Spec (.of K))
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (g : Ω ≃ₐ[F] Ω) (g' : ConstField₂ K Ω ≃ₐ[K] ConstField₂ K Ω)
    (hg : ∀ c : ConstField₂ K Ω, ((g' c : ConstField₂ K Ω) : Ω) = g c) :
    galoisAction F j h g = constGalEquiv₂ K Ω g' := by
  refine ext_of_hom_app_left fun A p => ?_
  obtain ⟨q, rfl⟩ := (constFiberMap₂_bijective A).2 p
  rw [galoisAction_hom_app_left, constGalEquiv₂_hom_app, constFiberMap₂_left,
    constFiberMap₂_left, mulEquivAutFiber_const_left]
  have hring : CommRingCat.ofHom (algebraMap (ConstField₂ K Ω) Ω) ≫
      CommRingCat.ofHom (g : Ω →+* Ω) =
      CommRingCat.ofHom (g' : ConstField₂ K Ω →+* ConstField₂ K Ω) ≫
        CommRingCat.ofHom (algebraMap (ConstField₂ K Ω) Ω) := by
    ext c
    exact (hg c).symm
  have hs : Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ constIncl₂ K Ω =
      constIncl₂ K Ω ≫ Spec.map (CommRingCat.ofHom (g' : ConstField₂ K Ω →+* ConstField₂ K Ω)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  rw [← Category.assoc, hs, Category.assoc]

end ConstantsPi1

section GaloisDataConst

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CharZero K] {t : Ω}
  (D : GaloisData K t)

omit [IsAlgClosed Ω] [CharZero K] in
lemma specPoint_comp_structure₂ :
    specPoint D.R Ω ≫ Spec.map (CommRingCat.ofHom (algebraMap K D.R)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable [IsGalois (K₀ K t) Ω]

/-- **`π₁ᵉᵗ(Spec R) → π₁ᵉᵗ(Spec K)` is the restriction to the constants**: under
`π₁ᵉᵗ(Spec R) ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩` and `constGalEquiv₂ : Gal(k̄ / K) ≃ₜ* π₁ᵉᵗ(Spec K)`, the map
induced by `Spec R ⟶ Spec K` is `piConstX D`. -/
theorem fundamentalGroupMap_equivPi1Spec_symm₂ (x : GaloisPi1.pi1 D.HL D.S D.isClosed_HL) :
    fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K D.R)))
        (specPoint_comp_structure₂ D)
        (((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm x) =
      constGalEquiv₂ K Ω (piConstX D x) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm
      (QuotientGroup.mk (s := GaloisPi1.kernel (galoisDataHL D).H (galoisDataHL D).S) σ) =
      (galoisDataHL D).galoisHom (galoisDataHL_H_le D) σ :=
    (galoisDataHL D).equivPi1Spec_symm_mk (galoisDataHL_H_le D) σ
  have h₁ := (galoisDataHL D).genericPoint_comp
  have h : Spec.map (CommRingCat.ofHom (algebraMap (galoisDataHL D).L Ω)) ≫
      (galoisDataHL D).genericPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap K D.R)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Category.assoc, h₁]
    exact specPoint_comp_structure₂ D
  have key := fundamentalGroupMap_galoisAction (galoisDataHL D).L (galoisDataHL D).genericPoint
    (Spec.map (CommRingCat.ofHom (algebraMap K D.R))) h₁ (specPoint_comp_structure₂ D) h
    ((galoisDataHL D).toGalL (Subgroup.inclusion (galoisDataHL_H_le D) σ))
  have key2 := galoisAction_eq_constGalEquiv₂ K Ω (galoisDataHL D).L
    ((galoisDataHL D).genericPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap K D.R))) h
    ((galoisDataHL D).toGalL (Subgroup.inclusion (galoisDataHL_H_le D) σ))
    (galResConst t (σ : Ω ≃ₐ[K₀ K t] Ω)) fun _ => rfl
  exact (congrArg (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K D.R)))
    (specPoint_comp_structure₂ D)) h1).trans (key.trans key2)

end GaloisDataConst

section Hemi

/-- The range of `f ∘ e` for an isomorphism `e` is the range of `f`. -/
lemma range_comp_continuousMulEquiv₂ {G H M : Type*} [Group G] [Group H] [Group M]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace M] (f : H →ₜ* M) (e : G ≃ₜ* H) :
    (f.comp (ContinuousMonoidHom.toContinuousMonoidHom e)).toMonoidHom.range =
      f.toMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨e γ, rfl⟩
  · rintro ⟨τ, rfl⟩
    refine ⟨e.symm τ, ?_⟩
    change f (e (e.symm τ)) = f τ
    rw [ContinuousMulEquiv.apply_symm_apply]

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (Ω' : Type u) [Field Ω'] [Algebra K Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω']
  [CharZero Ω']

/-- **`Spec R ≅ Spec Γ(E ∖ {O})`**, from `sectionsXEHemiAlgEquiv : Γ(E ∖ {O}) ≃ₐ[K] R`. -/
def hemiSpecIso :
    Spec (.of (hemiData E).R) ≅ Spec (.of Γ((hypCurveX E).Xbar, (hypCurveX E).U)) :=
  Scheme.Spec.mapIso (sectionsXEHemiAlgEquiv E).toRingEquiv.toCommRingCatIso.op

lemma hemiSpecIso_hom : (hemiSpecIso E).hom =
    Spec.map (CommRingCat.ofHom (sectionsXEHemiAlgEquiv E).toRingEquiv.toRingHom) := rfl

lemma hemiSpecIso_hom_comp : (hemiSpecIso E).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (hemiData E).R)) := by
  have h : CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U)) ≫
      CommRingCat.ofHom (sectionsXEHemiAlgEquiv E).toRingEquiv.toRingHom =
      CommRingCat.ofHom (algebraMap K (hemiData E).R) := by
    ext c
    exact (sectionsXEHemiAlgEquiv E).commutes c
  exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map h)

lemma hemi_structure_comp :
    (specPoint (hemiData E).R (FFClosure (curveE E)) ≫ (hemiSpecIso E).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (FFClosure (curveE E)))) := by
  rw [Category.assoc, hemiSpecIso_hom_comp]
  exact specPoint_comp_structure₂ (hemiData E)

/-- The change of base point on `Spec Γ(E ∖ {O})`: an isomorphism between the fibre functor at
the base point of `arithmeticExt` and the one at `Spec Ω ⟶ Spec R ≅ Spec Γ(E ∖ {O})` (any two
fibre functors are isomorphic; the choice only matters up to inner automorphisms). -/
def hemiFiberIso :
    fiber (basePoint Ω' (hypCurveX E) (compl_XE_nonempty E) ≫
      baseChangeSpec K Ω' Γ((hypCurveX E).Xbar, (hypCurveX E).U)) ≅
    fiber (specPoint (hemiData E).R (FFClosure (curveE E)) ≫ (hemiSpecIso E).hom) :=
  haveI := isIntegral_specSections (hypCurveX E) (compl_XE_nonempty E)
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`Π_X ≃ₜ* π₁ᵉᵗ(Spec R, Spec Ω)`** for `X = E ∖ {O}`, `R ≅ Γ(X)` the ring of the Galois data
`hemiData E`: change of base point (`hemiFiberIso`), then `Spec R ≅ Spec Γ(X)`. -/
def hemiPiXEquiv : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
    π₁ᵉᵗ(specPoint (hemiData E).R (FFClosure (curveE E))) :=
  (autContinuousMulEquivOfIso (hemiFiberIso E Ω')).trans
    (fundamentalGroupEquivOfIso (hemiSpecIso E) _).symm

/-- `Π_X ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩` (`H_L = Gal(Ω / K(Ē))`). -/
def hemiPiXGal : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
    GaloisPi1.pi1 (hemiData E).HL (hemiData E).S (hemiData E).isClosed_HL :=
  (hemiPiXEquiv E Ω').trans
    ((galoisDataHL (hemiData E)).equivPi1Spec (galoisDataHL_H_le (hemiData E)))

/-- The change of base point on `Spec K` induced by `hemiFiberIso`. -/
def hemiGkFiberIso :
    fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω'))) ≅
      fiber (Spec.map (CommRingCat.ofHom (algebraMap K (FFClosure (curveE E))))) :=
  fiberIsoMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))))
    (basePoint_spec₂ Ω' (hypCurveX E) (compl_XE_nonempty E)) (hemi_structure_comp E)
    (hemiFiberIso E Ω')

/-- **`G_K ≃ₜ* Gal(k̄ / K)`**, `k̄` the algebraic closure of `K` in `Ω = K(Ē)^alg`: the change of
base point induced by `hemiFiberIso`, then `constGalEquiv₂⁻¹`. -/
def hemiGkEquiv : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).G ≃ₜ*
    (ConstField₂ K (FFClosure (curveE E)) ≃ₐ[K] ConstField₂ K (FFClosure (curveE E))) :=
  (autContinuousMulEquivOfIso (hemiGkFiberIso E Ω')).trans
    (constGalEquiv₂ K (FFClosure (curveE E))).symm

lemma fundamentalGroupMap_hemiPiXEquiv
    (γ : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) :
    fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K (hemiData E).R)))
        (specPoint_comp_structure₂ (hemiData E)) (hemiPiXEquiv E Ω' γ) =
      fundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))))
        (hemi_structure_comp E) (autContinuousMulEquivOfIso (hemiFiberIso E Ω') γ) := by
  have hc : specPoint (hemiData E).R (FFClosure (curveE E)) ≫ (hemiSpecIso E).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (FFClosure (curveE E)))) := by
    rw [← Category.assoc]
    exact hemi_structure_comp E
  have e1 := fundamentalGroupMap_congr (hemiSpecIso_hom_comp E).symm
    (specPoint_comp_structure₂ (hemiData E)) hc
  have e2 := fundamentalGroupMap_comp (hemiSpecIso E).hom
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))))
    rfl (hemi_structure_comp E) hc
  have e3 : fundamentalGroupMap (hemiSpecIso E).hom rfl (hemiPiXEquiv E Ω' γ) =
      autContinuousMulEquivOfIso (hemiFiberIso E Ω') γ :=
    (fundamentalGroupEquivOfIso (hemiSpecIso E) _).apply_symm_apply _
  rw [e1, e2, ContinuousMonoidHom.comp_toFun, e3]

/-- **`pr : Π_X → G_K` is the restriction to the constants**: under `hemiPiXGal` and
`hemiGkEquiv`, `pr` corresponds to `piConstX (hemiData E) : H_L ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / K)`. -/
theorem hemiGkEquiv_pr (γ : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) :
    hemiGkEquiv E Ω' ((arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr γ) =
      piConstX (hemiData E) (hemiPiXGal E Ω' γ) := by
  have h1 := fundamentalGroupMap_autContinuousMulEquivOfIso
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))))
    (basePoint_spec₂ Ω' (hypCurveX E) (compl_XE_nonempty E)) (hemi_structure_comp E)
    (hemiFiberIso E Ω') γ
  have h3 := fundamentalGroupMap_equivPi1Spec_symm₂ (hemiData E) (hemiPiXGal E Ω' γ)
  have h4 : ((galoisDataHL (hemiData E)).equivPi1Spec (galoisDataHL_H_le (hemiData E))).symm
      (hemiPiXGal E Ω' γ) = hemiPiXEquiv E Ω' γ :=
    ContinuousMulEquiv.symm_apply_apply _ _
  rw [h4, fundamentalGroupMap_hemiPiXEquiv, h1] at h3
  change (constGalEquiv₂ K (FFClosure (curveE E))).symm
    (autContinuousMulEquivOfIso (hemiGkFiberIso E Ω') (projGk Ω' (hypCurveX E)
      (compl_XE_nonempty E) γ)) = _
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact h3

/-- **`Π_X ↪ Π_C`**: `hemiPiXEquiv`, then `orbiEmb : π₁ᵉᵗ(Spec R) ↪ etalePi1 R A Ω`. -/
def hemiPiXEmb : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi →ₜ*
    etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E)) :=
  (orbiEmb (hemiData E)).comp (ContinuousMonoidHom.toContinuousMonoidHom (hemiPiXEquiv E Ω'))

/-- **`Π_C → G_K`**: `Π_C ≃ₜ* H ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / K) ≃ₜ* G_K`. -/
def hemiPrC : etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E)) →ₜ*
    (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).G where
  toMonoidHom := (hemiGkEquiv E Ω').symm.toMulEquiv.toMonoidHom.comp
    ((piConstC (hemiData E)).comp (hemiData E).equivPi1.toMulEquiv.toMonoidHom)
  continuous_toFun := (hemiGkEquiv E Ω').symm.continuous.comp
    ((continuous_piConst (hemiData E).H (hemiData E).S (hemiData E).isClosed_H
      fun _ hs => galResConst_S (hemiData E) hs).comp (hemiData E).equivPi1.continuous)

lemma hemiGkEquiv_hemiPrC (τ : etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E))) :
    hemiGkEquiv E Ω' (hemiPrC E Ω' τ) = piConstC (hemiData E) ((hemiData E).equivPi1 τ) :=
  (hemiGkEquiv E Ω').apply_symm_apply (piConstC (hemiData E) ((hemiData E).equivPi1 τ))

lemma hemiPrC_hemiPiXEmb (γ : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) :
    hemiPrC E Ω' (hemiPiXEmb E Ω' γ) =
      (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr γ := by
  have h1 : (hemiData E).equivPi1 (hemiPiXEmb E Ω' γ) =
      orbiIncl (hemiData E) (hemiPiXGal E Ω' γ) :=
    (hemiData E).equivPi1.apply_symm_apply (orbiIncl (hemiData E) (hemiPiXGal E Ω' γ))
  have h2 : piConstC (hemiData E) (orbiIncl (hemiData E) (hemiPiXGal E Ω' γ)) =
      piConstX (hemiData E) (hemiPiXGal E Ω' γ) :=
    DFunLike.congr_fun (piConst_comp_orbiIncl (hemiData E)) _
  apply (hemiGkEquiv E Ω').injective
  rw [hemiGkEquiv_hemiPrC, h1, h2, hemiGkEquiv_pr]

lemma range_hemiPiXEmb :
    (hemiPiXEmb E Ω').toMonoidHom.range = (orbiEmb (hemiData E)).toMonoidHom.range :=
  range_comp_continuousMulEquiv₂ (orbiEmb (hemiData E)) (hemiPiXEquiv E Ω')

/-- **`Π_X ⊆ Π_C`** for `X = E ∖ {O}` and the hemi-elliptic orbicurve `C = [X / ±1]`
([AbsTopII] Cor. 3.3 (i), IUT I §1), in the normalisation of `arithmeticExt`: `hemiPiXEmb` is an
open embedding with normal image of index `2`, `hemiPrC : Π_C → G_K` extends
`pr : Π_X ↠ G_K`, and `Δ_C ∩ Π_X = Δ_X`. -/
theorem hemi_arith_orbiEmb :
    IsOpenEmbedding (hemiPiXEmb E Ω') ∧ (hemiPiXEmb E Ω').toMonoidHom.range.Normal ∧
      (hemiPiXEmb E Ω').toMonoidHom.range.index = 2 ∧
      (hemiPrC E Ω').toMonoidHom.comp (hemiPiXEmb E Ω').toMonoidHom =
        (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr.toMonoidHom ∧
      (hemiPrC E Ω').toMonoidHom.ker ⊓ (hemiPiXEmb E Ω').toMonoidHom.range =
        (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr.toMonoidHom.ker.map
          (hemiPiXEmb E Ω').toMonoidHom := by
  have hcomp : (hemiPrC E Ω').toMonoidHom.comp (hemiPiXEmb E Ω').toMonoidHom =
      (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr.toMonoidHom :=
    MonoidHom.ext (hemiPrC_hemiPiXEmb E Ω')
  refine ⟨(isOpenEmbedding_orbiEmb (hemiData E)).comp
      (hemiPiXEquiv E Ω').toHomeomorph.isOpenEmbedding, ?_, ?_, hcomp, ?_⟩
  · rw [range_hemiPiXEmb]
    exact range_orbiEmb_normal₂ _
  · rw [range_hemiPiXEmb]
    exact (hemi_orbiEmb E).2.2
  · exact (ker_inf_range_eq_map₂ (hemiPrC E Ω').toMonoidHom (hemiPiXEmb E Ω').toMonoidHom).trans
      (congrArg (fun φ => φ.ker.map (hemiPiXEmb E Ω').toMonoidHom) hcomp)

end Hemi

end CurvesJacobian.Cusp
