/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianPoints

/-!
# Base change of `Pic⁰_{C/k,σ}` and the Jacobian of `C_Ω`

* `AlgebraicGeometry.RelEffCartier.comapOfIso`: transport of a relative effective Cartier
  divisor along an isomorphism `X' ≅ X` over `S` (ideal, class and degree).

Let `C` be a curve over a field `k` with a rational point `σ` and `Ω ⊇ k` a field. For a scheme
`T` over `Ω` write `C_Ω ×_Ω T ≅ C ×_k T` (`bcHom`).

* `CurvesJacobian.picSigmaBC`: `Pic_{C/k,σ}(T) ≃ Pic_{C_Ω/Ω,σ_Ω}(T)`, natural in `T`
  (`picSigmaBC_map`).
* `CurvesJacobian.degPic_map_bcHom`, `CurvesJacobian.picDeg_picSigmaBC_iff`: the degree (for any
  choice of finite morphisms to `ℙ¹`) is compatible with base change (for `k`, `Ω` perfect): over a
  field every class is `[D] − [E]`, and `D`, `E` are transported along `bcHom` keeping degrees.
* `CurvesJacobian.picZeroBC`: `Pic⁰_{C/k,σ}(T) ≃ Pic⁰_{C_Ω/Ω,σ_Ω}(T)`, natural in `T`.
* **`CurvesJacobian.jacobianBCRepresentableBy`**: for `Ω` separably closed and perfect, the
  Jacobian `J_Ω` of `C_Ω` represents the restriction of `Pic⁰_{C/k,σ}` to `(Sch/Ω)`:
  `Hom_Ω(T, J_Ω) ≃ Pic⁰_{C/k,σ}(T)`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.RelEffCartier

variable {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} (D : RelEffCartier f)
  (φ : X' ⟶ X) [IsIso φ]

lemma comapOfIso_locally_principal (x : X') :
    ∃ (U : X'.affineOpens) (a : Γ(X', U.1)), x ∈ U.1 ∧
      (D.ideal.comap φ).ideal U = Ideal.span {a} ∧ IsSMulRegular Γ(X', U.1) a := by
  obtain ⟨U, g, hxU, hU, hreg⟩ := D.locally_principal (φ x)
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩
  refine ⟨U', φ.appLE U.1 U'.1 le_rfl g, hxU, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_le D.ideal φ U U' le_rfl, hU, Ideal.map_span,
      Set.image_singleton]
  · have : IsIso (φ.appLE U.1 U'.1 le_rfl) := by
      rw [← Scheme.Hom.app_eq_appLE]
      infer_instance
    let e := (asIso (φ.appLE U.1 U'.1 le_rfl)).commRingCatIsoToRingEquiv
    intro a b hab
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    have h : e (g * a) = e (g * b) := by
      rw [map_mul, map_mul]
      exact hab
    exact congrArg e (hreg (e.injective h))

variable (hφ : φ ≫ f = f')

include hφ in
lemma flat_comapOfIso : Flat ((D.ideal.comap φ).subschemeι ≫ f') := by
  have : Flat (D.ideal.subschemeι ≫ f) := D.flat
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, ← hφ, Category.assoc, pullback.condition_assoc]
  infer_instance

/-- **Transport of a relative effective Cartier divisor along an isomorphism** `φ : X' ≅ X` over
`S`: the divisor with ideal `φ^{-1} I_D`. -/
def comapOfIso : RelEffCartier f' where
  ideal := D.ideal.comap φ
  locally_principal := D.comapOfIso_locally_principal φ
  flat := D.flat_comapOfIso φ hφ

lemma comapOfIso_ideal : (D.comapOfIso φ hφ).ideal = D.ideal.comap φ := rfl

lemma map_picClass_comapOfIso :
    Scheme.Pic.map φ D.picClass = (D.comapOfIso φ hφ).picClass :=
  map_picClass_of_ideal_eq D (D.comapOfIso φ hφ) φ rfl

lemma degree_comapOfIso [IsFinite (D.ideal.subschemeι ≫ f)] (s : S) :
    (D.comapOfIso φ hφ).degree s = D.degree s := by
  have : Flat (D.ideal.subschemeι ≫ f) := D.flat
  simp only [degree, comapOfIso_ideal]
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, ← hφ, Category.assoc, pullback.condition_assoc,
    Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_comp_left_of_isIso]

end AlgebraicGeometry.RelEffCartier

namespace CurvesJacobian

open Cech Belyi

section BaseChange

variable {k : Type u} [Field k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "CΩ" => pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) Ω)
local notation "sA" => specAlgebraMap (k₀ := k) Ω

/-- The isomorphism `C_Ω ×_Ω T ≅ C ×_k T` for `t : T ⟶ Spec Ω` (and `g = t ≫ (Spec Ω ⟶ Spec k)`). -/
def bcHom {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    pullback (CΩ ↘ SΩ) t ⟶ pullback (C ↘ Sk) g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [← hg, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]
    congr 1
    exact pullback.condition)

omit [IsCurveOver k C] in
variable {C Ω} in
@[reassoc (attr := simp)]
lemma bcHom_fst {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    bcHom C Ω t g hg ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [IsCurveOver k C] in
variable {C Ω} in
@[reassoc (attr := simp)]
lemma bcHom_snd {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    bcHom C Ω t g hg ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

instance {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    IsIso (bcHom C Ω t g hg) := by
  subst hg
  have e : bcHom C Ω t _ rfl = (pullbackLeftPullbackSndIso (C ↘ Sk) sA t).hom := by
    apply pullback.hom_ext
    · rw [bcHom_fst]
      exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm
    · rw [bcHom_snd]
      exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  rw [e]
  infer_instance

omit [IsCurveOver k C] in
@[reassoc]
lemma bcMap_bcHom {T T' : Scheme.{u}} (a : T' ⟶ T) (t : T ⟶ SΩ) (t' : T' ⟶ SΩ)
    (w : a ≫ t = t') (g : T ⟶ Sk) (g' : T' ⟶ Sk) (hg : t ≫ sA = g) (hg' : t' ≫ sA = g')
    (w' : a ≫ g = g') :
    bcMap (CΩ ↘ SΩ) a t t' w ≫ bcHom C Ω t g hg =
      bcHom C Ω t' g' hg' ≫ bcMap (C ↘ Sk) a g g' w' := by
  apply pullback.hom_ext <;> simp

omit [IsCurveOver k C] in
@[reassoc]
lemma secT_bcHom {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    secT (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) t ≫ bcHom C Ω t g hg =
      secT (C ↘ Sk) σ hσ g := by
  subst hg
  apply pullback.hom_ext <;> simp [sigmaExt]

/-- **Base change of the rigidified Picard group**: `Pic_{C/k,σ}(T) ≃ Pic_{C_Ω/Ω,σ_Ω}(T)` for a
scheme `T` over `Ω`. -/
def picSigmaBC {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    picSigmaGrp (C ↘ Sk) σ hσ g ≃+
      picSigmaGrp (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) t where
  toFun x := ⟨Scheme.Pic.map (bcHom C Ω t g hg) x.1, by
    rw [mem_picSigmaGrp, ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, secT_bcHom]
    exact x.2⟩
  invFun y := ⟨Scheme.Pic.map (inv (bcHom C Ω t g hg)) y.1, by
    rw [mem_picSigmaGrp, ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp]
    have e : secT (C ↘ Sk) σ hσ g ≫ inv (bcHom C Ω t g hg) =
        secT (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) t := by
      rw [IsIso.comp_inv_eq, secT_bcHom]
    rw [e]
    exact y.2⟩
  left_inv x := Subtype.ext (by
    change Scheme.Pic.map (inv (bcHom C Ω t g hg)) (Scheme.Pic.map (bcHom C Ω t g hg) x.1) = x.1
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, IsIso.inv_hom_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply])
  right_inv y := Subtype.ext (by
    change Scheme.Pic.map (bcHom C Ω t g hg) (Scheme.Pic.map (inv (bcHom C Ω t g hg)) y.1) = y.1
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, IsIso.hom_inv_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply])
  map_add' x y := Subtype.ext (map_add (Scheme.Pic.map (bcHom C Ω t g hg)) x.1 y.1)

omit [IsCurveOver k C] in
@[simp]
lemma coe_picSigmaBC {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g)
    (x : picSigmaGrp (C ↘ Sk) σ hσ g) :
    (picSigmaBC C σ hσ Ω t g hg x : (pullback (CΩ ↘ SΩ) t).Pic) =
      Scheme.Pic.map (bcHom C Ω t g hg) x.1 := rfl

omit [IsCurveOver k C] in
/-- `picSigmaBC` is natural in `T`. -/
lemma picSigmaBC_map {T T' : Scheme.{u}} (a : T' ⟶ T) (t : T ⟶ SΩ) (g : T ⟶ Sk)
    (hg : t ≫ sA = g) (x : picSigmaGrp (C ↘ Sk) σ hσ g) :
    picSigmaMap (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) a t (a ≫ t) rfl
        (picSigmaBC C σ hσ Ω t g hg x) =
      picSigmaBC C σ hσ Ω (a ≫ t) (a ≫ g) (by rw [Category.assoc, hg])
        (picSigmaMap (C ↘ Sk) σ hσ a g (a ≫ g) rfl x) := by
  apply Subtype.ext
  simp only [coe_picSigmaMap, coe_picSigmaBC]
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← AddMonoidHom.comp_apply,
    ← Scheme.Pic.map_comp, bcMap_bcHom]

variable [PerfectField k] [PerfectField Ω]

/-- **The degree is compatible with base change**: for `T` a field over `Ω`, the degree of a class
on `C ×_k T` is the degree of its transport to `C_Ω ×_Ω T` (for any finite morphisms to `ℙ¹`). -/
lemma degPic_map_bcHom (πk : C ⟶ ProjectiveLine.scheme k) [IsFinite πk]
    (πΩ : CΩ ⟶ ProjectiveLine.scheme Ω) [IsFinite πΩ] {T : Scheme.{u}} [IsAffine T]
    (hF : IsField Γ(T, ⊤)) (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g)
    (z : (pullback (C ↘ Sk) g).Pic) :
    letI : T.Over SΩ := ⟨t⟩
    letI : T.Over Sk := ⟨g⟩
    degPic πΩ (T := T) (Scheme.Pic.map (bcHom C Ω t g hg) z) = degPic πk (T := T) z := by
  letI : T.Over SΩ := ⟨t⟩
  letI : T.Over Sk := ⟨g⟩
  have hI1 : IsIso (bcHom C Ω t g hg) := inferInstance
  obtain ⟨s⟩ := nonempty_of_isField hF
  obtain ⟨D, E, rfl⟩ : ∃ D E : RelEffCartier (pullback.snd (C ↘ Sk) g),
      z = D.picClass - E.picClass := exists_eq_picClass_sub πk hF z
  haveI := D.isFinite C g
  haveI := E.isFinite C g
  have hφ : bcHom C Ω t g hg ≫ pullback.snd (C ↘ Sk) g = pullback.snd (CΩ ↘ SΩ) t :=
    bcHom_snd t g hg
  rw [map_sub, @RelEffCartier.map_picClass_comapOfIso _ _ _ _ _ D (bcHom C Ω t g hg) hI1 hφ,
    @RelEffCartier.map_picClass_comapOfIso _ _ _ _ _ E (bcHom C Ω t g hg) hI1 hφ]
  have h1 := degPic_sub_picClass πΩ hF
    (@RelEffCartier.comapOfIso _ _ _ _ _ D (bcHom C Ω t g hg) hI1 hφ)
    (@RelEffCartier.comapOfIso _ _ _ _ _ E (bcHom C Ω t g hg) hI1 hφ) s
  have h2 := degPic_sub_picClass πk hF D E s
  erw [@RelEffCartier.degree_comapOfIso _ _ _ _ _ D (bcHom C Ω t g hg) hI1 hφ _ s,
    @RelEffCartier.degree_comapOfIso _ _ _ _ _ E (bcHom C Ω t g hg) hI1 hφ _ s] at h1
  exact h1.trans h2.symm

/-- The degree condition is compatible with base change. -/
lemma picDeg_picSigmaBC_iff (πk : C ⟶ ProjectiveLine.scheme k) [IsFinite πk]
    (πΩ : CΩ ⟶ ProjectiveLine.scheme Ω) [IsFinite πΩ] (d : ℤ) {T : Scheme.{u}}
    (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) (x : picSigmaGrp (C ↘ Sk) σ hσ g) :
    picDeg (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) πΩ d T
        ⟨t, picSigmaBC C σ hσ Ω t g hg x⟩ ↔
      picDeg σ hσ πk d T ⟨g, x⟩ := by
  have key : ∀ (T' : Scheme.{u}) [IsAffine T'], IsField Γ(T', ⊤) → ∀ h : T' ⟶ T,
      chiPoint (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) πΩ
          ((sigmaG (picSigma (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω))).map h.op
            ⟨t, picSigmaBC C σ hσ Ω t g hg x⟩) - 1 + genusNat Ω CΩ =
        chiPoint σ hσ πk ((sigmaG (picSigma (C ↘ Sk) σ hσ)).map h.op ⟨g, x⟩) - 1 +
          genusNat k C := by
    intro T' _ hF h
    letI : T'.Over SΩ := ⟨h ≫ t⟩
    letI : T'.Over Sk := ⟨h ≫ g⟩
    have e := degPic_map_bcHom C Ω πk πΩ hF (h ≫ t) (h ≫ g) (by rw [Category.assoc, hg])
      (Scheme.Pic.map (bcMap (C ↘ Sk) h g (h ≫ g) rfl) x.1)
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp,
      ← bcMap_bcHom C Ω h t (h ≫ t) rfl g (h ≫ g) hg (by rw [Category.assoc, hg]) rfl,
      Scheme.Pic.map_comp, AddMonoidHom.comp_apply] at e
    exact e
  constructor
  · intro H T' _ hF h
    have := key T' hF h
    have := H T' hF h
    omega
  · intro H T' _ hF h
    have := key T' hF h
    have := H T' hF h
    omega

variable (πk : C ⟶ ProjectiveLine.scheme k) [IsFinite πk]
  (πΩ : pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) Ω) ⟶
    ProjectiveLine.scheme Ω) [IsFinite πΩ]

/-- **Base change of `Pic⁰`**: `Pic⁰_{C/k,σ}(T) ≃ Pic⁰_{C_Ω/Ω,σ_Ω}(T)` for `T` over `Ω`. -/
def picZeroBC {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g) :
    picZeroGrp πk σ hσ g ≃+ picZeroGrp πΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) t where
  toFun x := ⟨picSigmaBC C σ hσ Ω t g hg x.1,
    (picDeg_picSigmaBC_iff C σ hσ Ω πk πΩ 0 t g hg x.1).mpr x.2⟩
  invFun y := ⟨(picSigmaBC C σ hσ Ω t g hg).symm y.1,
    (picDeg_picSigmaBC_iff C σ hσ Ω πk πΩ 0 t g hg _).mp (by
      rw [AddEquiv.apply_symm_apply]
      exact y.2)⟩
  left_inv x := Subtype.ext ((picSigmaBC C σ hσ Ω t g hg).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((picSigmaBC C σ hσ Ω t g hg).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (picSigmaBC C σ hσ Ω t g hg) x.1 y.1)

lemma coe_coe_picZeroBC {T : Scheme.{u}} (t : T ⟶ SΩ) (g : T ⟶ Sk) (hg : t ≫ sA = g)
    (x : picZeroGrp πk σ hσ g) :
    ((picZeroBC C σ hσ Ω πk πΩ t g hg x : picSigmaGrp (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω)
      (sigmaExt_comp C σ hσ Ω) t) : (pullback (CΩ ↘ SΩ) t).Pic) =
        Scheme.Pic.map (bcHom C Ω t g hg) (x : picSigmaGrp (C ↘ Sk) σ hσ g).1 := rfl

/-- `picZeroBC` is natural in `T`. -/
lemma picZeroBC_symm_map {T T' : Over SΩ} (a : T' ⟶ T)
    (y : picZeroGrp πΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) T.hom) :
    (picZeroBC C σ hσ Ω πk πΩ T'.hom (T'.hom ≫ sA) rfl).symm
        (picZeroMap CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) πΩ a y) =
      picZeroMap C σ hσ πk ((Over.map sA).map a)
        ((picZeroBC C σ hσ Ω πk πΩ T.hom (T.hom ≫ sA) rfl).symm y) := by
  apply (picZeroBC C σ hσ Ω πk πΩ T'.hom (T'.hom ≫ sA) rfl).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_coe_picZeroBC]
  change Scheme.Pic.map (bcMap (CΩ ↘ SΩ) a.left T.hom T'.hom (Over.w a)) y.1.1 =
    Scheme.Pic.map (bcHom C Ω T'.hom (T'.hom ≫ sA) rfl)
      (Scheme.Pic.map (bcMap (C ↘ Sk) a.left (T.hom ≫ sA) (T'.hom ≫ sA)
        (by rw [← Category.assoc, Over.w a]))
        (Scheme.Pic.map (inv (bcHom C Ω T.hom (T.hom ≫ sA) rfl)) y.1.1))
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← AddMonoidHom.comp_apply,
    ← Scheme.Pic.map_comp, ← bcMap_bcHom C Ω a.left T.hom T'.hom (Over.w a)
      (T.hom ≫ sA) (T'.hom ≫ sA) rfl rfl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable [IsSepClosed Ω]

/-- **The Jacobian of `C_Ω` represents `Pic⁰_{C/k,σ}` restricted to `(Sch/Ω)`**: for `T` over
`Ω`, `Hom_Ω(T, J_Ω) ≃ Pic⁰_{C/k,σ}(T)`. -/
def jacobianBCRepresentableBy :
    ((Over.map sA).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat).RepresentableBy
      (Jacobian CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)) where
  homEquiv {T} :=
    (jacobianRepresentableBy CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)).homEquiv.trans
      (picZeroBC C σ hσ Ω (curveToP1 k C) (curveToP1 Ω CΩ) T.hom (T.hom ≫ sA) rfl).symm.toEquiv
  homEquiv_comp {T T'} f b := by
    change (picZeroBC C σ hσ Ω (curveToP1 k C) (curveToP1 Ω CΩ) T.hom (T.hom ≫ sA) rfl).symm
        ((jacobianRepresentableBy CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)).homEquiv
          (f ≫ b)) = _
    rw [(jacobianRepresentableBy CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)).homEquiv_comp]
    exact picZeroBC_symm_map C σ hσ Ω (curveToP1 k C) (curveToP1 Ω CΩ) f _

end BaseChange

end CurvesJacobian
