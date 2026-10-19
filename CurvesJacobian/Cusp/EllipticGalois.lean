/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticBelyi
import CurvesJacobian.Cusp.Cor37bBelyi
import EllipticCurves.FunctionField.TranslationAction
import EllipticCurves.FunctionField.MulByTwoDegree

/-!
# `[2] : E ∖ E[2] → E ∖ {O}` is a Galois cover; [AbsTopII] Cor 3.7 (b) for `E ∖ {O}`

Let `E` be an elliptic curve over a number field `K` whose `2`-torsion is `K`-rational, i.e.
`g = 4x³ + b₂x² + 2b₄x + b₆ = 4 (x - e₁)(x - e₂)(x - e₃)` over `K` (`he`; IUT I, Def 3.1 (b),
`Inter-universal Teichmuller Theory I.txt` l.3978–3979: "the 2 · 3-torsion points of `E_F` are
rational over `F`"). We show that `[2] : V = E ∖ E[2] → X = E ∖ {O}`
(`Spec` of `[2]^* : K[E] → K[E][1/ψ]`, `coverXMorK`) is a Galois object of the Galois category
`FiniteEtale (Spec Γ(X))` (`isGalois_coverXMorK`), and hence obtain the input
`galoisBelyiInputE : GaloisBelyiInput (hypCurveX E) K` of [AbsTopII] Cor 3.7 (b)
(`Cusp/Cor37bBelyi`) over `M = K`, and its consequences `cor37b_oncePunctured`,
`cor37b_oncePunctured_equiv`.

Proof of `isGalois_coverXMorK` (`AlgebraicGeometry.FiniteEtale.isGalois_coverObj_of_card`):
* `V` is integral, so `coverObj` is connected and `Aut → fibre` is injective;
* translations `τ_T` (`translateAut` of `elliptic-curves`) by the four `K`-rational points
  `T ∈ E[2]` (`twoTorsionPt`) are distinct automorphisms of `K(E)` fixing `[2]^* K(E)`
  (`translateAut_mulByTwoEndo`); they restrict to `B = K[E][1/ψ]` because `B` is integrally closed
  and integral over `[2]^* K[E]` (`restrictRingEquiv`), giving four automorphisms of `V` over `X`;
* the fibre over the geometric point `K[E] →[2]^* K(E) ⊆ \overline{K(E)}` has at most
  `[K(E) : [2]^* K(E)] = 4` points (`finite_card_fibre_le`, `finrank_mulByTwoFieldRange`);
* hence `Aut` acts simply transitively on the fibre (`isGalois_iff_pretransitive`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.FiniteEtale

variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsFiniteEtale (Spec.map f)]

/-- `Spec` of a ring automorphism of `S`. -/
def specIsoOfIso (σ : S ≅ S) : Spec S ≅ Spec S where
  hom := Spec.map σ.hom
  inv := Spec.map σ.inv
  hom_inv_id := by rw [← Spec.map_comp, σ.inv_hom_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, σ.hom_inv_id, Spec.map_id]

/-- A ring automorphism of `S` over `R`, as an automorphism of `Spec S` in
`FiniteEtale (Spec R)`. -/
def autOfRingIso (σ : S ≅ S) (hσ : f ≫ σ.hom = f) : Aut (coverObj (Spec.map f)) :=
  MorphismProperty.Over.isoMk (specIsoOfIso σ) (by
    change Spec.map σ.hom ≫ Spec.map f = Spec.map f
    rw [← Spec.map_comp, hσ])

lemma autOfRingIso_hom_left (σ : S ≅ S) (hσ : f ≫ σ.hom = f) :
    (autOfRingIso f σ hσ).hom.left = Spec.map σ.hom := rfl

/-- **A connected finite étale cover with enough automorphisms is Galois.** Let `R → S` be finite
étale with `R`, `S` domains, let `σ : ι → Aut_R(S)` be injective, and suppose that for some
separably closed field `Ω` and some `ζ : R → Ω` there are at most `|ι|` homomorphisms `S → Ω`
over `ζ`. Then `Spec S → Spec R` is a Galois object of `FiniteEtale (Spec R)`: the evaluation
`Aut → fibre` is injective (connectedness) between sets with `|fibre| ≤ |ι|`, hence bijective,
so `Aut` acts transitively on the fibre (`isGalois_iff_pretransitive`). -/
theorem isGalois_coverObj_of_card [IsDomain R] [IsDomain S] {ι : Type*} [Finite ι]
    (σ : ι → (S ≅ S)) (hσ : ∀ i, f ≫ (σ i).hom = f) (hinj : Function.Injective σ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : R ⟶ CommRingCat.of Ω)
    [Finite {g : S ⟶ CommRingCat.of Ω // f ≫ g = ζ}]
    (hcard : Nat.card {g : S ⟶ CommRingCat.of Ω // f ≫ g = ζ} ≤ Nat.card ι) :
    IsGalois (coverObj (Spec.map f)) := by
  haveI : IsConnected (coverObj (Spec.map f)) :=
    (isConnected_iff_connectedSpace (coverObj (Spec.map f))).2
      (inferInstanceAs (ConnectedSpace (Spec S)))
  set η : Spec (.of Ω) ⟶ Spec R := Spec.map ζ
  rw [isGalois_iff_pretransitive (fiber η)]
  have hw : ∀ x : (fiber η).obj (coverObj (Spec.map f)),
      f ≫ Spec.preimage (fiberObjEquivHom η _ x).left = ζ := fun x ↦ by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact w_left (fiberObjEquivHom η _ x)
  have hfib : Nat.card ((fiber η).obj (coverObj (Spec.map f))) ≤ Nat.card ι := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x ↦ ⟨Spec.preimage (fiberObjEquivHom η _ x).left, hw x⟩) fun x y hxy ↦ ?_) hcard
    have h : (fiberObjEquivHom η _ x).left = (fiberObjEquivHom η _ y).left := by
      rw [← Spec.map_preimage (fiberObjEquivHom η _ x).left,
        ← Spec.map_preimage (fiberObjEquivHom η _ y).left]
      exact congrArg (fun g ↦ Spec.map g.1) hxy
    exact (fiberObjEquivHom η _).injective (Over.OverMorphism.ext h)
  let a : ι → Aut (coverObj (Spec.map f)) := fun i ↦ autOfRingIso f (σ i) (hσ i)
  have ha : Function.Injective a := by
    intro i j hij
    have h : Spec.map (σ i).hom = Spec.map (σ j).hom := by
      rw [← autOfRingIso_hom_left f (σ i) (hσ i), ← autOfRingIso_hom_left f (σ j) (hσ j)]
      exact congrArg (fun e : Aut (coverObj (Spec.map f)) ↦ e.hom.left) hij
    exact hinj (Iso.ext (Spec.map_injective h))
  refine ⟨fun x y ↦ ?_⟩
  have hev : Function.Injective (fun i ↦ (fiber η).map (a i).hom x) :=
    (evaluation_aut_injective_of_isConnected (fiber η) _ x).comp ha
  obtain ⟨i, hi⟩ := (hev.bijective_of_nat_card_le hfib).2 y
  exact ⟨a i, hi⟩

end AlgebraicGeometry.FiniteEtale

/-! ### Restricting automorphisms of the fraction field to an integrally closed subring -/

namespace CurvesJacobian.Cusp

section Restrict

variable {A B L : Type*} [CommRing A] [CommRing B] [IsIntegrallyClosed B] [Field L]
  [Algebra B L] [IsFractionRing B L] (φ : A →+* B) (hφ : φ.IsIntegral)

include hφ in
lemma exists_restrict_of_isIntegral (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) (b : B) :
    ∃ c : B, algebraMap B L c = τ (algebraMap B L b) := by
  letI := φ.toAlgebra
  letI : Algebra A L := ((algebraMap B L).comp φ).toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let τA : L →ₐ[A] L := { τ.toRingHom with commutes' := hτ }
  have h1 : IsIntegral A (algebraMap B L b) :=
    (show IsIntegral A b from hφ b).map (IsScalarTower.toAlgHom A B L)
  exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map τA).tower_top

/-- The restriction of `τ` to `B`. -/
def restrictFun (τ : L ≃+* L) (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a))
    (b : B) : B :=
  (exists_restrict_of_isIntegral φ hφ τ hτ b).choose

lemma algebraMap_restrictFun (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) (b : B) :
    algebraMap B L (restrictFun φ hφ τ hτ b) = τ (algebraMap B L b) :=
  (exists_restrict_of_isIntegral φ hφ τ hτ b).choose_spec

omit [IsIntegrallyClosed B] [IsFractionRing B L] in
lemma symm_apply_of_forall {τ : L ≃+* L}
    (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) (a : A) :
    τ.symm (algebraMap B L (φ a)) = algebraMap B L (φ a) :=
  τ.symm_apply_eq.2 (hτ a).symm

/-- **An automorphism of `L = Frac B` fixing the image of `A` restricts to `B`** when `B` is
integrally closed and integral over `A`. -/
def restrictRingEquiv (τ : L ≃+* L) (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) :
    B ≃+* B where
  toFun := restrictFun φ hφ τ hτ
  invFun := restrictFun φ hφ τ.symm (symm_apply_of_forall φ hτ)
  left_inv b := IsFractionRing.injective B L (by
    rw [algebraMap_restrictFun, algebraMap_restrictFun, RingEquiv.symm_apply_apply])
  right_inv b := IsFractionRing.injective B L (by
    rw [algebraMap_restrictFun, algebraMap_restrictFun, RingEquiv.apply_symm_apply])
  map_mul' x y := IsFractionRing.injective B L (by
    simp only [map_mul, algebraMap_restrictFun])
  map_add' x y := IsFractionRing.injective B L (by
    simp only [map_add, algebraMap_restrictFun])

lemma algebraMap_restrictRingEquiv (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) (b : B) :
    algebraMap B L (restrictRingEquiv φ hφ τ hτ b) = τ (algebraMap B L b) :=
  algebraMap_restrictFun φ hφ τ hτ b

lemma restrictRingEquiv_apply_self (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap B L (φ a)) = algebraMap B L (φ a)) (a : A) :
    restrictRingEquiv φ hφ τ hτ (φ a) = φ a :=
  IsFractionRing.injective B L (by rw [algebraMap_restrictRingEquiv, hτ])

lemma eq_of_restrictRingEquiv_eq {τ₁ τ₂ : L ≃+* L}
    (h₁ : ∀ a, τ₁ (algebraMap B L (φ a)) = algebraMap B L (φ a))
    (h₂ : ∀ a, τ₂ (algebraMap B L (φ a)) = algebraMap B L (φ a))
    (h : restrictRingEquiv φ hφ τ₁ h₁ = restrictRingEquiv φ hφ τ₂ h₂) : τ₁ = τ₂ := by
  have : τ₁.toRingHom = τ₂.toRingHom := IsLocalization.ringHom_ext (nonZeroDivisors B)
    (RingHom.ext fun b ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← algebraMap_restrictRingEquiv φ hφ τ₁ h₁, ← algebraMap_restrictRingEquiv φ hφ τ₂ h₂, h])
  exact RingEquiv.ext fun x ↦ RingHom.congr_fun this x

end Restrict

/-- A ring map out of a ring integral over `A` is injective if it is injective on `A`. -/
lemma injective_of_isIntegral {A B C : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing C]
    (φ : A →+* B) (hφ : φ.IsIntegral) (g : B →+* C) (hg : Function.Injective (g.comp φ)) :
    Function.Injective g := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : Nontrivial A := φ.domain_nontrivial
  have hker : (RingHom.ker g).comap (algebraMap A B) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hg
  exact (RingHom.injective_iff_ker_eq_bot g).2 (Ideal.eq_bot_of_comap_eq_bot hker)

/-! ### The four translations by `E[2]` act on `B = K[E][1/ψ]` over `[2]^*` -/

section Translations

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField

instance : IsIntegrallyClosed (coverRingE E) :=
  isIntegrallyClosed_of_isLocalization (R := A) _ (Submonoid.powers (psiE E))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (psiE_ne_zero E))

/-- `B` is integral over `K[E]` via `[2]^*`. -/
lemma dupHom_isIntegral : (dupHom E).IsIntegral := fun b ↦
  Algebra.IsIntegral.isIntegral (R := E.toAffine.CoordinateRing) (show DupB E from b)

omit [E.IsElliptic] in
lemma algebraMap_dupHom (a : A) : algebraMap (coverRingE E) FF (dupHom E a) =
    mulByTwoEndo (W := E.toAffine) two_ne_zero (algebraMap A FF a) := by
  rw [mulByTwoEndo_algebraMap, ← coe_dupHom]
  rfl

variable {E}

/-- The points `(e, -(a₁ e + a₃)/2)`, `g(e) = 0`, are nonsingular. -/
lemma nonsingular_twoTorsion {e : K} (h0 : E.Ψ₂Sq.eval e = 0) :
    E.toAffine.Nonsingular e (-(E.a₁ * e + E.a₃) / 2) := by
  set y := -(E.a₁ * e + E.a₃) / 2
  have hy : 2 * y + E.a₁ * e + E.a₃ = 0 := by simp only [y]; ring
  rw [WeierstrassCurve.Ψ₂Sq] at h0
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h0
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.1
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₆, WeierstrassCurve.b₄] at h0
  linear_combination (1 / 4 : K) * (2 * y + E.a₁ * e + E.a₃ + 0) * hy - (1 / 4 : K) * h0

variable {e₁ e₂ e₃ : K} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

omit [CharZero K] [E.IsElliptic] in
include he in
lemma eval_Ψ₂Sq_e₁ : E.Ψ₂Sq.eval e₁ = 0 := by rw [he]; simp

omit [CharZero K] [E.IsElliptic] in
include he in
lemma eval_Ψ₂Sq_e₂ : E.Ψ₂Sq.eval e₂ = 0 := by rw [he]; simp

omit [CharZero K] [E.IsElliptic] in
include he in
lemma eval_Ψ₂Sq_e₃ : E.Ψ₂Sq.eval e₃ = 0 := by rw [he]; simp

/-- **The four points of `E[2]`** (all `K`-rational by `he`): `O` and `(eᵢ, -(a₁ eᵢ + a₃)/2)`. -/
def twoTorsionPt : Fin 4 → E.toAffine.Point :=
  ![0, .some _ _ (nonsingular_twoTorsion (eval_Ψ₂Sq_e₁ he)),
    .some _ _ (nonsingular_twoTorsion (eval_Ψ₂Sq_e₂ he)),
    .some _ _ (nonsingular_twoTorsion (eval_Ψ₂Sq_e₃ he))]

lemma twoTorsionPt_injective : Function.Injective (twoTorsionPt he) := by
  have h12 := roots_ne₁₂ he
  have h13 := roots_ne₁₃ he
  have h23 := roots_ne₂₃ he
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [twoTorsionPt]

open Classical in
lemma twoTorsionPt_mem (i : Fin 4) : twoTorsionPt he i ∈ E.toAffine.torsion 2 := by
  fin_cases i
  · exact zero_mem _
  all_goals exact (mem_torsion_two_some_iff _).2 (by ring)

/-- Translation by the `i`-th point of `E[2]`, an automorphism of `K(E)`. -/
def tau2 (i : Fin 4) : FF ≃ₐ[K] FF := translateAut (twoTorsionPt he i)

lemma tau2_injective : Function.Injective (tau2 he) :=
  translateAut_injective.comp (twoTorsionPt_injective he)

open Classical in
lemma tau2_dupHom (i : Fin 4) (a : A) :
    (tau2 he i).toRingEquiv (algebraMap (coverRingE E) FF (dupHom E a)) =
      algebraMap (coverRingE E) FF (dupHom E a) := by
  rw [algebraMap_dupHom]
  exact translateAut_mulByTwoEndo two_ne_zero (twoTorsionPt_mem he i) _

/-- Translation by the `i`-th point of `E[2]` restricted to `B = K[E][1/ψ]`. -/
def sigma2 (i : Fin 4) : coverRingE E ≃+* coverRingE E :=
  restrictRingEquiv (dupHom E) (dupHom_isIntegral E) (tau2 he i).toRingEquiv (tau2_dupHom he i)

lemma sigma2_dupHom (i : Fin 4) (a : A) : sigma2 he i (dupHom E a) = dupHom E a :=
  restrictRingEquiv_apply_self _ _ _ _ a

lemma sigma2_injective : Function.Injective (sigma2 he) := fun _ _ h ↦
  tau2_injective he (AlgEquiv.ext fun x ↦ RingEquiv.congr_fun
    (eq_of_restrictRingEquiv_eq _ _ _ _ h) x)

end Translations

/-! ### `[2] : E ∖ E[2] → E ∖ {O}` over `K` and its geometric generic fibre -/

section Cover

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField

/-- `[2]^* : Γ(E ∖ {O}) = K[E] → K[E][1/ψ] = Γ(E ∖ E[2])`. -/
def coverXHom : Γ(curveE E, XE E) →+* Γ(curveE E, VE E) :=
  (sectionsVEEquiv E).symm.toRingHom.comp
    ((dupHom E).comp (sectionsXEAlgEquiv E).toRingEquiv.toRingHom)

/-- `V → X`: `[2] : E ∖ E[2] → E ∖ {O}` over `K`. -/
abbrev coverXMorK : Spec Γ(curveE E, VE E) ⟶ Spec Γ(curveE E, XE E) :=
  Spec.map (CommRingCat.ofHom (coverXHom E))

lemma coverXMorK_eq : coverXMorK E =
    Spec.map (CommRingCat.ofHom (sectionsVEEquiv E).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dupHom E)) ≫
        Spec.map (CommRingCat.ofHom (sectionsXEAlgEquiv E).toRingEquiv.toRingHom) := by
  simp only [coverXMorK, coverXHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

instance isFiniteEtale_coverXMorK : IsFiniteEtale (coverXMorK E) := by
  rw [coverXMorK_eq]
  have h1 := isFiniteEtale_specMap_of_ringEquiv (sectionsVEEquiv E).symm
  have h3 := isFiniteEtale_specMap_of_ringEquiv (sectionsXEAlgEquiv E).toRingEquiv
  have h2 := isFiniteEtale_spec_dupHom E
  exact MorphismProperty.comp_mem @IsFiniteEtale _ _ h1 (MorphismProperty.comp_mem _ _ _ h2 h3)

lemma coverXHom_algebraMap (c : K) :
    coverXHom E (algebraMap K _ c) = algebraMap K Γ(curveE E, VE E) (algebraMap K K c) := by
  change (sectionsVEEquiv E).symm (dupHom E (sectionsXEAlgEquiv E (algebraMap K _ c))) = _
  rw [AlgEquiv.commutes, RingEquiv.symm_apply_eq, sectionsVEEquiv_algebraMap, ← dupHom_algebraMap,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The algebraically closed field `Ω = \overline{K(E)}` of the generic geometric point. -/
abbrev OmegaE : Type u := AlgebraicClosure FF

/-- The geometric generic point of `X` *through* `[2]`: `K[E] →[2]^* K(E) ⊆ Ω`. -/
def zetaE : Γ(curveE E, XE E) ⟶ CommRingCat.of (OmegaE E) :=
  CommRingCat.ofHom ((algebraMap FF (OmegaE E)).comp
    ((mulByTwoCoordHom (W := E.toAffine) two_ne_zero).comp
      (sectionsXEAlgEquiv E).toRingEquiv.toRingHom))

/-- A point of the fibre, as a map `B → Ω`. -/
def fibreHom (g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)) : coverRingE E →+* OmegaE E :=
  g.hom.comp (sectionsVEEquiv E).symm.toRingHom

variable {E}

lemma fibreHom_dupHom {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)}
    (hg : CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E) (a : A) :
    fibreHom E g (dupHom E a) =
      algebraMap FF (OmegaE E) (mulByTwoCoordHom (W := E.toAffine) two_ne_zero a) := by
  have h := congrArg (fun φ ↦ φ.hom ((sectionsXEAlgEquiv E).symm a)) hg
  simpa [coverXHom, zetaE, fibreHom] using h

lemma fibreHom_injective {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)}
    (hg : CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E) : Function.Injective (fibreHom E g) := by
  refine injective_of_isIntegral (dupHom E) (dupHom_isIntegral E) _ ?_
  have : (fibreHom E g).comp (dupHom E) = (algebraMap FF (OmegaE E)).comp
      (mulByTwoCoordHom (W := E.toAffine) two_ne_zero) := RingHom.ext (fibreHom_dupHom hg)
  rw [this]
  exact (algebraMap FF (OmegaE E)).injective.comp (mulByTwoCoordHom_injective two_ne_zero)

/-- The extension of a fibre point to `K(E) → Ω`. -/
def fibreLift {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)}
    (hg : CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E) : FF →+* OmegaE E :=
  IsFractionRing.lift (fibreHom_injective hg)

lemma fibreLift_algebraMap {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)}
    (hg : CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E) (b : coverRingE E) :
    fibreLift hg (algebraMap (coverRingE E) FF b) = fibreHom E g b :=
  IsFractionRing.lift_algebraMap _ _

omit [E.IsElliptic] in
lemma mulByTwoCoordHom_eq (a : A) : mulByTwoCoordHom (W := E.toAffine) two_ne_zero a =
    algebraMap (coverRingE E) FF (dupHom E a) := by
  rw [← coe_dupHom]
  rfl

/-- A fibre point is the identity on `[2]^* K(E)`. -/
lemma fibreLift_mulByTwoEndo {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E)}
    (hg : CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E) (u : FF) :
    fibreLift hg (mulByTwoEndo two_ne_zero u) =
      algebraMap FF (OmegaE E) (mulByTwoEndo two_ne_zero u) := by
  have : (fibreLift hg).comp (mulByTwoEndo two_ne_zero) =
      (algebraMap FF (OmegaE E)).comp (mulByTwoEndo two_ne_zero) :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, mulByTwoEndo_algebraMap]
      rw [← fibreHom_dupHom hg, ← fibreLift_algebraMap hg, mulByTwoCoordHom_eq])
  exact RingHom.congr_fun this u

variable (E)

/-- **The geometric generic fibre of `[2] : E ∖ E[2] → E ∖ {O}` has at most four points**: a
point is a map `B → Ω` over `K[E]`; it is injective (`B` is integral over `[2]^* K[E]`), extends
to `K(E) → Ω`, and is then a `[2]^* K(E)`-algebra map; there are at most
`[K(E) : [2]^* K(E)] = 4` of those (`finrank_mulByTwoFieldRange`). -/
theorem finite_card_fibre_le :
    Finite {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E) //
      CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E} ∧
    Nat.card {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E) //
      CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E} ≤ 4 := by
  set L' := (mulByTwoEndoAlgHom (W := E.toAffine) two_ne_zero).fieldRange
  letI : Algebra L' (OmegaE E) := ((algebraMap FF (OmegaE E)).comp (algebraMap L' FF)).toAlgebra
  have hdeg : Module.finrank L' FF = 4 := finrank_mulByTwoFieldRange two_ne_zero
  haveI : Module.Free L' FF := Module.Free.of_divisionRing L' FF
  haveI : Module.Finite L' FF := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  let Φ : {g : Γ(curveE E, VE E) ⟶ CommRingCat.of (OmegaE E) //
      CommRingCat.ofHom (coverXHom E) ≫ g = zetaE E} → (FF →ₐ[L'] OmegaE E) := fun g ↦
    { fibreLift g.2 with
      commutes' := fun l ↦ by
        obtain ⟨u, hu⟩ := AlgHom.mem_fieldRange.1 l.2
        change fibreLift g.2 (l : FF) = algebraMap FF (OmegaE E) (l : FF)
        rw [← hu]
        exact fibreLift_mulByTwoEndo g.2 u }
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    refine Subtype.ext (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    have h' := DFunLike.congr_fun h (algebraMap (coverRingE E) FF (sectionsVEEquiv E x))
    change fibreLift g₁.2 _ = fibreLift g₂.2 _ at h'
    simpa [fibreLift_algebraMap, fibreHom] using h'
  exact ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans
    ((card_algHom_le_finrank L' FF (OmegaE E)).trans hdeg.le)⟩

end Cover

/-! ### `[2]` is Galois, and the Galois Belyi input for `E ∖ {O}` -/

section Galois

open Polynomial

variable {K : Type u} [Field K] [CharZero K] {E : WeierstrassCurve K} [E.IsElliptic]
  {e₁ e₂ e₃ : K} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

/-- Translation by the `i`-th point of `E[2]` on `Γ(E ∖ E[2])`. -/
def rhoV (i : Fin 4) : Γ(curveE E, VE E) ≅ Γ(curveE E, VE E) :=
  RingEquiv.toCommRingCatIso
    ((sectionsVEEquiv E).trans ((sigma2 he i).trans (sectionsVEEquiv E).symm))

lemma rhoV_comm (i : Fin 4) :
    CommRingCat.ofHom (coverXHom E) ≫ (rhoV he i).hom = CommRingCat.ofHom (coverXHom E) := by
  ext x
  simp [rhoV, coverXHom, sigma2_dupHom]

lemma rhoV_injective : Function.Injective (rhoV he) := by
  intro i j h
  apply sigma2_injective he
  ext b
  have := congrArg (fun e : Γ(curveE E, VE E) ≅ Γ(curveE E, VE E) ↦
    e.hom ((sectionsVEEquiv E).symm b)) h
  simpa [rhoV] using this

include he in
/-- **`[2] : E ∖ E[2] → E ∖ {O}` is a Galois cover** (group `E[2]`) when the `2`-torsion of `E`
is `K`-rational (`he`): the four translations by `E[2]` are automorphisms over `X`, and the
geometric generic fibre has at most four points (`finite_card_fibre_le`). -/
theorem isGalois_coverXMorK : IsGalois (coverObj (coverXMorK E)) := by
  obtain ⟨hfin, hcard⟩ := finite_card_fibre_le E
  refine isGalois_coverObj_of_card (CommRingCat.ofHom (coverXHom E)) (rhoV he) (rhoV_comm he)
    (rhoV_injective he) (zetaE E) ?_
  exact hcard.trans (by simp)

variable (E) in
omit [E.IsElliptic] in
/-- If `E[2]` is `K`-rational (`g = 4x³ + b₂x² + 2b₄x + b₆` splits over `K`), then
`g = 4 (x - e₁)(x - e₂)(x - e₃)` over `K`. -/
lemma exists_roots_of_splits (h : E.Ψ₂Sq.Splits) : ∃ e₁ e₂ e₃ : K,
    E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have hcard : E.Ψ₂Sq.roots.card = 3 := by
    rw [← WeierstrassCurve.natDegree_Ψ₂Sq E h4]
    exact splits_iff_card_roots.1 h
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.1 hcard
  refine ⟨a, b, c, ?_⟩
  conv_lhs => rw [h.eq_prod_roots, WeierstrassCurve.leadingCoeff_Ψ₂Sq E h4, habc]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
    Multiset.prod_singleton]
  ring

variable [NumberField K]

/-- **[AbsTopII] Example 3.6 (ii) over `K` for IUT's `X = E ∖ {O}`** with `K`-rational `E[2]`
(`he`; IUT I Def 3.1 (b) assumes the `2·3`-torsion of `E_F` rational over `F`): `V = E ∖ E[2]`,
`[2] : V → X` and `V → Q = ℙ¹ ∖ {0, 1, λ, ∞}`, `t = (x - e₁)/(e₂ - e₁)`. -/
def strictlyBelyiInputEK : StrictlyBelyiInput (hypCurveX E) K where
  CV := hypCurveV E
  hcV := (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 (VE_le_XE E))
  FV := coverXMorK E
  finFV := isFiniteEtale_coverXMorK E
  hFV := by
    change coverXMorK E ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) = _
    simp only [coverXMorK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverXHom_algebraMap E c
  Q := QE e₁ e₂ e₃
  hQ := QE_le_puncturedLine
  hQne := QE_nonempty
  FQ := Spec.map (CommRingCat.ofHom (coverQHom he))
  finFQ := isFiniteEtale_coverQ he
  hFQ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverQHom_algebraMap he c

/-- **The Galois Belyi input for IUT's once-punctured elliptic curve** (lead decision for
[AbsTopII] Cor 3.7 (b)): over `M = K`, with `K`-rational `E[2]`, `[2] : E ∖ E[2] → E ∖ {O}` is a
Galois object of `FiniteEtale (Spec Γ(E ∖ {O}))` (`isGalois_coverXMorK`). -/
def galoisBelyiInputE : GaloisBelyiInput (hypCurveX E) K where
  toStrictlyBelyiInput := strictlyBelyiInputEK he
  isGalois := isGalois_coverXMorK he

variable (E) in
/-- **`X = E ∖ {O}` has a Galois Belyi input over `K`** when `E[2]` is `K`-rational. -/
theorem nonempty_galoisBelyiInput (h : E.Ψ₂Sq.Splits) :
    Nonempty (GaloisBelyiInput (hypCurveX E) K) := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_of_splits E h
  exact ⟨galoisBelyiInputE he⟩

end Galois

/-! ### [AbsTopII] Corollary 3.7 (b) for `X = E ∖ {O}` -/

section Cor37b

open Polynomial

variable {K : Type u} [Field K] [NumberField K] {E : WeierstrassCurve K} [E.IsElliptic]
  {e₁ e₂ e₃ : K} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (UX : (hypCurveX E).Xbar.Opens) (hUX : UX ≤ (hypCurveX E).U)
  (hne : (UX : Set (hypCurveX E).Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω (hypCurveX E) (compl_XE_nonempty E)) ≅
    fiber (fillPoint Ω (subCurve (hypCurveX E) UX hUX hne)
      (compl_nonempty_of_le hUX (compl_XE_nonempty E)) hUX))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Corollary 3.7 (b) for IUT's `X = E ∖ {O}`** (`E[2]` rational over `K`): for a
nonempty open `U_X ⊆ X` and `U = V ×_X U_X`, `V = E ∖ E[2] →[2] X`, the subgroup
`Π_U = im(Π_U → Π_{U_X})` is the preimage of `Π_V = im(Π_V → Π_X)` under `Π_{U_X} ↠ Π_X`. -/
theorem cor37b_oncePunctured :
    cor37bPiU Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne
        ((galoisBelyiInputE he).belyiCU (compl_XE_nonempty E) UX hUX hne)
        ((galoisBelyiInputE he).belyi_hcU (compl_XE_nonempty E) UX hUX hne)
        ((galoisBelyiInputE he).belyiFU (compl_XE_nonempty E) UX hUX hne) =
      (cor37bPiV Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (galoisBelyiInputE he).hcV
        (coverXMorK E)).comap (cor38Fill Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne α₀) :=
  cor37b_belyi Ω (compl_XE_nonempty E) UX hUX hne α₀ (galoisBelyiInputE he)

/-- **[AbsTopII] Corollary 3.7 (b) for IUT's `X = E ∖ {O}`**: `Π_{U_X} ≃* Π_U ⋊^out (Π_{U_X}/Π_U)`
and `Π_{U_X}/Π_U ≃* Π_X/Π_V` for `U = V ×_X U_X`, `V = E ∖ E[2] →[2] X` (Galois, group `E[2]`). -/
theorem cor37b_oncePunctured_equiv :
    haveI := cor37b_normalU Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne α₀ (hypCurveV E)
      (galoisBelyiInputE he).hcV (coverXMorK E)
      ((galoisBelyiInputE he).belyiCU (compl_XE_nonempty E) UX hUX hne)
      ((galoisBelyiInputE he).belyi_hcU (compl_XE_nonempty E) UX hUX hne)
      ((galoisBelyiInputE he).belyiFU (compl_XE_nonempty E) UX hUX hne)
      ((galoisBelyiInputE he).belyiJ (compl_XE_nonempty E) UX) (galoisBelyiInputE he).isGalois
      ((galoisBelyiInputE he).isPullback_belyiFU (compl_XE_nonempty E) UX hUX hne)
    haveI := cor37b_normal Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E)
      (galoisBelyiInputE he).hcV (coverXMorK E) (galoisBelyiInputE he).isGalois
    Nonempty ((arithmeticExt Ω (subCurve (hypCurveX E) UX hUX hne)
        (compl_nonempty_of_le hUX (compl_XE_nonempty E))).Pi ≃*
        outSemidirect (outerAction (cor37bPiU Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne
          ((galoisBelyiInputE he).belyiCU (compl_XE_nonempty E) UX hUX hne)
          ((galoisBelyiInputE he).belyi_hcU (compl_XE_nonempty E) UX hUX hne)
          ((galoisBelyiInputE he).belyiFU (compl_XE_nonempty E) UX hUX hne)))) ∧
      Nonempty ((arithmeticExt Ω (subCurve (hypCurveX E) UX hUX hne)
          (compl_nonempty_of_le hUX (compl_XE_nonempty E))).Pi ⧸
          cor37bPiU Ω (hypCurveX E) (compl_XE_nonempty E) UX hUX hne
            ((galoisBelyiInputE he).belyiCU (compl_XE_nonempty E) UX hUX hne)
            ((galoisBelyiInputE he).belyi_hcU (compl_XE_nonempty E) UX hUX hne)
            ((galoisBelyiInputE he).belyiFU (compl_XE_nonempty E) UX hUX hne) ≃*
        (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi ⧸
          cor37bPiV Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (galoisBelyiInputE he).hcV
            (coverXMorK E)) :=
  cor37b_belyi_equiv Ω (compl_XE_nonempty E) UX hUX hne α₀ (galoisBelyiInputE he)

end Cor37b

end CurvesJacobian.Cusp
