/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicTangentTwist

/-!
# `ker(Pic C_{k[ε]} → Pic C) ≅ Ȟ¹(U, V; 𝒪_C)`

For a scheme `C` over a field `k` covered by two affine opens `U`, `V` with affine
intersection, the twists `c₁ a = [𝒪(1 + a ε)]` (`CurvesJacobian.PicTangent.c₁`) satisfy

* `PicTangent.c₁_eq_c₁_iff`: `c₁ a = c₁ a'` iff `a - a'` is a Čech coboundary;
* `PicTangent.exists_c₁_eq`: every class of `Pic(C_{k[ε]})` which is trivial on `C` is some
  `c₁ a`.

This is the computation of the tangent space of the Picard functor at the origin as
`H¹(C, 𝒪_C)` (cf. Stacks, Lemma 44.6.7 (Tag 0BA0), where the tangent space is used to see that
`Pic` is smooth of dimension `g`), carried out with explicit two-chart cocycles: units of
`Γ(U ×_k k[ε])` are `u₀ + u₁ ε` with `u₀` a unit (`EpsDecomp`), and invertible sheaves trivial
modulo `ε` are trivial on the affine charts (`BasisLift`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TrivSqZeroExt

universe u

noncomputable section

namespace CurvesJacobian.PicTangent

open Scheme ModulesGlue MatSheaf Cech

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "R₀" => Γ(Sk, ⊤)

/-! ### Sections over the dual numbers -/

section Decomp

local notation "Tε" => Spec (CommRingCat.of (B₁ k))

/-- The generator `ε` of `Γ(Spec k[ε])`. -/
abbrev epsT : Γ(Tε, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (B₁ k))).inv (inr 1)

lemma decomp_hB (b : Γ(Tε, ⊤)) : ∃ a₀ a₁ : R₀,
    b = (gB (S := Sk) (B₁ k)).appTop a₀ + (gB (S := Sk) (B₁ k)).appTop a₁ * epsT (k := k) := by
  set β := (Scheme.ΓSpecIso (CommRingCat.of (B₁ k))).hom b with hβ
  refine ⟨β.fst, β.snd, ?_⟩
  rw [gB_appTop, gB_appTop, epsT, ← map_mul, ← map_add]
  have : algebraMap R₀ (B₁ k) β.fst + algebraMap R₀ (B₁ k) β.snd * inr 1 = β := by
    rw [algebraMap_eq_inl, inl_mul_inr, smul_eq_mul, mul_one, inl_fst_add_inr_snd_eq]
  rw [this, hβ]
  exact (Iso.hom_inv_id_apply _ b).symm

lemma decomp_hB' (a₀ a₁ : R₀)
    (h : (gB (S := Sk) (B₁ k)).appTop a₀ + (gB (S := Sk) (B₁ k)).appTop a₁ * epsT (k := k) = 0) :
    a₀ = 0 ∧ a₁ = 0 := by
  rw [gB_appTop, gB_appTop, epsT, ← map_mul, ← map_add] at h
  have h' : algebraMap R₀ (B₁ k) a₀ + algebraMap R₀ (B₁ k) a₁ * inr 1 = 0 :=
    (Scheme.ΓSpecIso (CommRingCat.of (B₁ k))).commRingCatIsoToRingEquiv.symm.injective
      (h.trans (map_zero _).symm)
  rw [algebraMap_eq_inl, inl_mul_inr, smul_eq_mul, mul_one] at h'
  have h0 := congrArg TrivSqZeroExt.fst h'
  have h1 := congrArg TrivSqZeroExt.snd h'
  simp only [fst_add, fst_inl, fst_inr, add_zero, fst_zero, snd_add, snd_inl, snd_inr, zero_add,
    snd_zero] at h0 h1
  exact ⟨h0, h1⟩

variable {C}

/-- **Sections of `𝒪` over the dual numbers**: `z = a + b ε`. -/
lemma decomp {O : C.Opens} (hO : IsAffineOpen O) {O' : (CT k C (B₁ k)).Opens}
    (hO' : O' = pB k C (B₁ k) ⁻¹ᵁ O) (z : Γ(CT k C (B₁ k), O')) :
    ∃ a b : Γ(C, O), z =
      fA k C (B₁ k) hO'.le a + fA k C (B₁ k) hO'.le b * fE k C (B₁ k) O' (inr 1) := by
  letI : (Spec (CommRingCat.of (B₁ k))).Over Sk := ⟨gB (S := Sk) (B₁ k)⟩
  exact EpsDecomp.exists_eq (S := Sk) (X := C) (T := Tε) (epsT (k := k)) decomp_hB decomp_hB'
    hO hO' z

lemma decomp_unique {O : C.Opens} (hO : IsAffineOpen O) {O' : (CT k C (B₁ k)).Opens}
    (hO' : O' = pB k C (B₁ k) ⁻¹ᵁ O) (a b : Γ(C, O))
    (h : fA k C (B₁ k) hO'.le a + fA k C (B₁ k) hO'.le b * fE k C (B₁ k) O' (inr 1) = 0) :
    a = 0 ∧ b = 0 := by
  letI : (Spec (CommRingCat.of (B₁ k))).Over Sk := ⟨gB (S := Sk) (B₁ k)⟩
  exact EpsDecomp.eq_zero_of_eq_zero (S := Sk) (X := C) (T := Tε) (epsT (k := k)) decomp_hB
    decomp_hB' hO hO' a b h

lemma epsE_sq (O' : (CT k C (B₁ k)).Opens) :
    fE k C (B₁ k) O' (inr 1) * fE k C (B₁ k) O' (inr 1) = 0 := by
  rw [← map_mul, inr_mul_inr, map_zero]

end Decomp

/-! ### Algebra of first-order perturbations

Generic ring computations: `R` contains `A` via `f`, `e² = 0` and `f a + f b e = 0 ⇒ a = b = 0`.
Keeping these computations away from the rings of sections keeps elaboration cheap. -/

namespace EpsAlg

variable {A R : Type*} [CommRing A] [CommRing R] (f : A →+* R) (e : R)

lemma unit_fst (he : e * e = 0) (huniq : ∀ a b : A, f a + f b * e = 0 → a = 0 ∧ b = 0)
    {u₀ u₁ w₀ w₁ : A} (h : (f u₀ + f u₁ * e) * (f w₀ + f w₁ * e) = 1) : u₀ * w₀ = 1 := by
  have key : f (u₀ * w₀ - 1) + f (u₀ * w₁ + u₁ * w₀) * e = 0 := by
    rw [map_sub, map_one, map_mul, map_add, map_mul, map_mul]
    linear_combination h - f u₁ * f w₁ * he
  exact sub_eq_zero.mp (huniq _ _ key).1

lemma exists_unit (he : e * e = 0) (hex : ∀ z : R, ∃ a b : A, z = f a + f b * e)
    (huniq : ∀ a b : A, f a + f b * e = 0 → a = 0 ∧ b = 0) (u : Rˣ) :
    ∃ u₀ u₁ w₀ : A, (u : R) = f u₀ + f u₁ * e ∧ u₀ * w₀ = 1 := by
  obtain ⟨u₀, u₁, hu⟩ := hex u
  obtain ⟨w₀, w₁, hw⟩ := hex ↑u⁻¹
  refine ⟨u₀, u₁, w₀, hu, unit_fst f e he huniq (u₁ := u₁) (w₁ := w₁) ?_⟩
  rw [← hu, ← hw, Units.mul_inv]

lemma sub_eq (he : e * e = 0) (huniq : ∀ a b : A, f a + f b * e = 0 → a = 0 ∧ b = 0)
    {a a' x₀ x₁ y₀ y₁ x₀' y₀' : A} (hx : x₀ * x₀' = 1) (hy : y₀ * y₀' = 1)
    (h : (f y₀ + f y₁ * e) * (1 + f a' * e) = (1 + f a * e) * (f x₀ + f x₁ * e)) :
    a - a' = y₀' * y₁ - x₀' * x₁ := by
  have key : f (y₀ - x₀) + f (y₁ + y₀ * a' - x₁ - a * x₀) * e = 0 := by
    simp only [map_sub, map_add, map_mul]
    linear_combination h - (f y₁ * f a' - f a * f x₁) * he
  obtain ⟨h1, h2⟩ := huniq _ _ key
  linear_combination (a * y₀' + x₁ * x₀' * y₀') * h1 - y₀' * h2 + (a' - a - x₁ * x₀') * hy +
    x₁ * y₀' * hx

lemma conv (he : e * e = 0) {a a' X Y : A} (h : X - Y = a - a') :
    (1 + f (-Y) * e) * (1 + f a' * e) = (1 + f a * e) * (1 + f (-X) * e) := by
  have h' := congrArg f h
  rw [map_sub, map_sub] at h'
  rw [map_neg, map_neg]
  linear_combination e * h' + (-(f Y) * f a' + f a * f X) * he

lemma eq_one_of {AW RW R' : Type*} [CommRing AW] [CommRing RW] [CommRing R'] (fW : AW →+* RW)
    (eW : RW) (g : RW →+* R') (f' : AW →+* R') (hg : ∀ c, g (fW c) = f' c) (he : g eW = 0)
    (hinj : Function.Injective f') {t : RW} {t₀ t₁ : AW} (ht : t = fW t₀ + fW t₁ * eW)
    (h1 : g t = 1) : t₀ = 1 := by
  apply hinj
  rw [map_one, ← h1, ht, map_add, map_mul, hg, hg, he, mul_zero, add_zero]

lemma eq_one_add {t : R} {t₀ t₁ : A} (ht : t = f t₀ + f t₁ * e) (h0 : t₀ = 1) :
    t = 1 + f t₁ * e := by
  rw [ht, h0, map_one]

variable {AU AV AW RU RV RW : Type*} [CommRing AU] [CommRing AV] [CommRing AW] [CommRing RU]
  [CommRing RV] [CommRing RW]

/-- Two-chart cocycles: an isomorphism of the twists by `1 + a ε` and `1 + a' ε` gives a
coboundary. -/
lemma cob (fU : AU →+* RU) (fV : AV →+* RV) (fW : AW →+* RW) (rU : AU →+* AW) (rV : AV →+* AW)
    (sU : RU →+* RW) (sV : RV →+* RW) (eU : RU) (eV : RV) (eW : RW) (heW : eW * eW = 0)
    (hUf : ∀ c, sU (fU c) = fW (rU c)) (hVf : ∀ c, sV (fV c) = fW (rV c)) (hUe : sU eU = eW)
    (hVe : sV eV = eW) (huniq : ∀ a b : AW, fW a + fW b * eW = 0 → a = 0 ∧ b = 0)
    {a a' : AW} {u₀ u₁ w₀ : AU} {v₀ v₁ z₀ : AV} {u : RU} {v : RV}
    (hu : u = fU u₀ + fU u₁ * eU) (hv : v = fV v₀ + fV v₁ * eV) (hw : u₀ * w₀ = 1)
    (hz : v₀ * z₀ = 1) (h : sV v * (1 + fW a' * eW) = (1 + fW a * eW) * sU u) :
    rU (-(w₀ * u₁)) - rV (-(z₀ * v₁)) = a - a' := by
  subst hu hv
  simp only [map_add, map_mul, hUf, hVf, hUe, hVe] at h
  have hc := sub_eq fW eW heW huniq (x₀ := rU u₀) (x₁ := rU u₁) (y₀ := rV v₀) (y₁ := rV v₁)
    (x₀' := rU w₀) (y₀' := rV z₀) (by rw [← map_mul, hw, map_one])
    (by rw [← map_mul, hz, map_one]) h
  rw [map_neg, map_neg, map_mul, map_mul]
  linear_combination -hc

/-- Two-chart cocycles: a coboundary gives an isomorphism of the twists. -/
lemma cob_conv (fU : AU →+* RU) (fV : AV →+* RV) (fW : AW →+* RW) (rU : AU →+* AW)
    (rV : AV →+* AW) (sU : RU →+* RW) (sV : RV →+* RW) (eU : RU) (eV : RV) (eW : RW)
    (heU : eU * eU = 0) (heV : eV * eV = 0) (heW : eW * eW = 0)
    (hUf : ∀ c, sU (fU c) = fW (rU c)) (hVf : ∀ c, sV (fV c) = fW (rV c)) (hUe : sU eU = eW)
    (hVe : sV eV = eW) {a a' : AW} {x : AU} {y : AV} (h : rU x - rV y = a - a') :
    ∃ (u : RUˣ) (v : RVˣ), sV v * (1 + fW a' * eW) = (1 + fW a * eW) * sU u := by
  refine ⟨sqUnit (fU (-x) * eU) (by rw [mul_mul_mul_comm, heU, mul_zero]),
    sqUnit (fV (-y) * eV) (by rw [mul_mul_mul_comm, heV, mul_zero]), ?_⟩
  rw [sqUnit_val, sqUnit_val]
  simp only [map_add, map_one, map_mul, hUf, hVf, hUe, hVe]
  rw [map_neg rV, map_neg rU]
  exact conv fW eW heW h

end EpsAlg

variable {C} {U V : C.Opens}

/-- A unit of `Γ(O ×_k k[ε])` reduces to a unit of `Γ(O)`. -/
lemma exists_unit_decomp {O : C.Opens} (hO : IsAffineOpen O)
    (u : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ O)ˣ) : ∃ u₀ u₁ w₀ : Γ(C, O),
      (u : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ O)) =
        fA k C (B₁ k) le_rfl u₀ + fA k C (B₁ k) le_rfl u₁ *
          fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ O) (inr 1) ∧
          u₀ * w₀ = 1 :=
  EpsAlg.exists_unit (fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ O) le_rfl)
    (fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ O) (inr 1)) (epsE_sq _) (fun z ↦ decomp hO rfl z)
    (fun a b h ↦ decomp_unique hO rfl a b h) u

lemma resU_fA (c : Γ(C, U)) :
    ρ (inf_le_left : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ U)
      (fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ U) le_rfl c) =
    fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl
      (ρ (inf_le_left : U ⊓ V ≤ U) c) :=
  (fA_res (k := k) (C := C) (B := B₁ k) (O := U) (O' := pB k C (B₁ k) ⁻¹ᵁ U) le_rfl
    inf_le_left c).trans
    (fA_map (k := k) (C := C) (B := B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      le_rfl (inf_le_left : U ⊓ V ≤ U) c).symm

lemma resV_fA (c : Γ(C, V)) :
    ρ (inf_le_right : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ V)
      (fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ V) le_rfl c) =
    fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl
      (ρ (inf_le_right : U ⊓ V ≤ V) c) :=
  (fA_res (k := k) (C := C) (B := B₁ k) (O := V) (O' := pB k C (B₁ k) ⁻¹ᵁ V) le_rfl
    inf_le_right c).trans
    (fA_map (k := k) (C := C) (B := B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      le_rfl (inf_le_right : U ⊓ V ≤ V) c).symm

lemma resU_fE :
    ρ (inf_le_left : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ U)
      (fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U) (inr 1)) =
    fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1) :=
  fE_res (k := k) (C := C) (B := B₁ k) inf_le_left (inr 1)

lemma resV_fE :
    ρ (inf_le_right : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ V)
      (fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ V) (inr 1)) =
    fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1) :=
  fE_res (k := k) (C := C) (B := B₁ k) inf_le_right (inr 1)

lemma uniqW (hW : IsAffineOpen (U ⊓ V)) (a b : Γ(C, U ⊓ V))
    (h : fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl a +
      fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl b *
        fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1) = 0) :
    a = 0 ∧ b = 0 :=
  decomp_unique hW (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) rfl a b h

/-! ### Injectivity -/

/-- **`c₁ a = c₁ a'` iff `a - a'` is a Čech coboundary.** -/
theorem c₁_eq_c₁_iff (hUV : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (U ⊓ V)) (a a' : Γ(C, U ⊓ V)) :
    c₁ (k := k) C U V hUV a = c₁ (k := k) C U V hUV a' ↔ a - a' ∈ LinearMap.range
      (TwoCech.d (resLin Sk C (inf_le_left : U ⊓ V ≤ U))
        (resLin Sk C (inf_le_right : U ⊓ V ≤ V))) := by
  unfold c₁ twK
  rw [TwoChart.twPic_eq_twPic_iff]
  constructor
  · rintro ⟨u, v, huv⟩
    obtain ⟨u₀, u₁, w₀, hu, hw⟩ := exists_unit_decomp hU u
    obtain ⟨v₀, v₁, z₀, hv, hz⟩ := exists_unit_decomp hV v
    refine ⟨(-(w₀ * u₁), -(z₀ * v₁)), ?_⟩
    rw [TwoCech.d_apply]
    exact EpsAlg.cob (fU := fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ U) le_rfl)
      (fV := fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ V) le_rfl)
      (fW := fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
        le_rfl)
      (rU := ρ (inf_le_left : U ⊓ V ≤ U)) (rV := ρ (inf_le_right : U ⊓ V ≤ V))
      (sU := ρ (inf_le_left : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ U))
      (sV := ρ (inf_le_right : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ V))
      (eU := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U) (inr 1))
      (eV := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
      (eW := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
      (heW := epsE_sq _) (hUf := resU_fA) (hVf := resV_fA) (hUe := resU_fE) (hVe := resV_fE)
      (huniq := uniqW hW) (a := a) (a' := a') hu hv hw hz huv
  · rintro ⟨⟨x, y⟩, hxy⟩
    rw [TwoCech.d_apply] at hxy
    exact EpsAlg.cob_conv (fU := fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ U) le_rfl)
      (fV := fA k C (B₁ k) (O' := pB k C (B₁ k) ⁻¹ᵁ V) le_rfl)
      (fW := fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
        le_rfl)
      (rU := ρ (inf_le_left : U ⊓ V ≤ U)) (rV := ρ (inf_le_right : U ⊓ V ≤ V))
      (sU := ρ (inf_le_left : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ U))
      (sV := ρ (inf_le_right : pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V ≤ pB k C (B₁ k) ⁻¹ᵁ V))
      (eU := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U) (inr 1))
      (eV := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
      (eW := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
      (heU := epsE_sq _) (heV := epsE_sq _) (heW := epsE_sq _)
      (hUf := resU_fA) (hVf := resV_fA) (hUe := resU_fE) (hVe := resV_fE) (a := a) (a' := a')
      hxy

/-! ### Surjectivity -/

lemma map_rs {Y : Scheme.{u}} (N : Y.Modules) {O W W' : Y.Opens} (h : W ≤ O) (h' : W' ≤ W)
    (m : Γ(N, O)) : N.presheaf.map (homOfLE h').op (rs N h m) = rs N (h'.trans h) m :=
  rs_rs N h h' m

lemma isIso_gB_self : IsIso (gB (S := Sk) R₀) := by
  have : CommRingCat.ofHom (algebraMap R₀ R₀) = 𝟙 _ := rfl
  rw [gB, this, Spec.map_id, Category.id_comp]
  infer_instance

lemma injective_appLE_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {O : Y.Opens}
    {O' : X.Opens} (h : O' ≤ f ⁻¹ᵁ O) (hO' : O' = f ⁻¹ᵁ O) :
    Function.Injective (f.appLE O O' h) := by
  subst hO'
  rw [Scheme.Hom.appLE_eq_app]
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.injective

lemma sqZero_fst : MatLift.SqZero (CommRingCat.ofHom (augM k R₀).toRingHom).hom := by
  intro a b ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [ha]
  · simp [ha, hb]

/-- A transition function between lifts of one basis restricts to `1`. -/
lemma appLE_eq_one_of_lift {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (L : Y.Modules)
    {g : Γ((Scheme.Modules.pullback i).obj L, ⊤)}
    (hg : ((Scheme.Modules.pullback i).obj L).IsBasisOn ⊤ g) {O₁ O₂ : Y.Opens}
    {ε : Γ(L, O₁)} {δ : Γ(L, O₂)}
    (hεg : Scheme.Modules.pullbackSection i ε = rs ((Scheme.Modules.pullback i).obj L) le_top g)
    (hδg : Scheme.Modules.pullbackSection i δ = rs ((Scheme.Modules.pullback i).obj L) le_top g)
    (t : Γ(Y, O₁ ⊓ O₂)) (ht : rs L inf_le_right δ = t • rs L inf_le_left ε) :
    (i.appLE (O₁ ⊓ O₂) (i ⁻¹ᵁ (O₁ ⊓ O₂)) le_rfl).hom t = 1 := by
  have eδ : Scheme.Modules.pullbackRes i L (U := O₁ ⊓ O₂) (U' := i ⁻¹ᵁ (O₁ ⊓ O₂)) le_rfl
      (rs L inf_le_right δ) = rs ((Scheme.Modules.pullback i).obj L) le_top g := by
    rw [Scheme.Modules.pullbackRes_res i L (le_rfl : i ⁻¹ᵁ O₂ ≤ _) inf_le_right
      (i.preimage_mono inf_le_right) le_rfl δ, Scheme.Modules.pullbackRes_apply, hδg, map_rs,
      rs_rs]
  have eε : Scheme.Modules.pullbackRes i L (U := O₁ ⊓ O₂) (U' := i ⁻¹ᵁ (O₁ ⊓ O₂)) le_rfl
      (rs L inf_le_left ε) = rs ((Scheme.Modules.pullback i).obj L) le_top g := by
    rw [Scheme.Modules.pullbackRes_res i L (le_rfl : i ⁻¹ᵁ O₁ ≤ _) inf_le_left
      (i.preimage_mono inf_le_left) le_rfl ε, Scheme.Modules.pullbackRes_apply, hεg, map_rs,
      rs_rs]
  have e := congrArg (Scheme.Modules.pullbackRes i L (U := O₁ ⊓ O₂)
    (U' := i ⁻¹ᵁ (O₁ ⊓ O₂)) le_rfl) ht
  rw [Scheme.Modules.pullbackRes_smul, eδ, eε] at e
  refine (smul_left_injective_of_isBasisOn (isBasisOn_rs hg le_top) ?_).symm
  rw [one_smul]
  exact e

lemma augM_inr : (augM k R₀) (inr 1 : B₁ k) = 0 := rfl

lemma bc_aug_fE :
    ((bc (augM k R₀)).appLE (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      ((bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) le_rfl).hom
      (fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1)) = 0 :=
  (bc_fE (augM k R₀) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
    (O'' := (bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) le_rfl (inr 1)).trans
    ((congrArg (fE k C R₀ _) (augM_inr (k := k))).trans (map_zero _))

lemma bc_aug_le :
    (bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) ≤ pB k C R₀ ⁻¹ᵁ (U ⊓ V) :=
  (bc_preimage (augM k R₀) (U ⊓ V)).le

lemma injective_fA_R₀ :
    Function.Injective (fA k C R₀ (bc_aug_le (k := k) (C := C) (U := U) (V := V))) := by
  haveI := isIso_gB_self (k := k)
  exact injective_appLE_of_isIso (pB k C R₀) _ (bc_preimage (augM k R₀) (U ⊓ V))

lemma t₀_eq_one (t : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V))
    (t₀ t₁ : Γ(C, U ⊓ V))
    (ht01 : t = fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl
        t₀ +
      fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl t₁ *
        fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
    (hit : ((bc (augM k R₀)).appLE (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      ((bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) le_rfl).hom t = 1) :
    t₀ = 1 :=
  EpsAlg.eq_one_of
    (fW := fA k C (B₁ k) (O := U ⊓ V) (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) le_rfl)
    (eW := fE k C (B₁ k) (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) (inr 1))
    (g := ((bc (augM k R₀)).appLE (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      ((bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) le_rfl).hom)
    (f' := fA k C R₀ bc_aug_le)
    (hg := fun c ↦ bc_fA (augM k R₀) (O := U ⊓ V)
      (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      (O'' := (bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V))
      le_rfl le_rfl bc_aug_le c)
    (he := bc_aug_fE) (hinj := injective_fA_R₀) ht01 hit

/-- A transition function of `C_{k[ε]}` which is `1` on `C` is `1 + a ε`. -/
lemma exists_c₁_eq_twPic (hUV : U ⊔ V = ⊤) (hW : IsAffineOpen (U ⊓ V))
    (t : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)ˣ)
    (hit : ((bc (augM k R₀)).appLE (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)
      ((bc (augM k R₀)) ⁻¹ᵁ (pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) le_rfl).hom
      (t : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V)) = 1) :
    ∃ a, c₁ (k := k) C U V hUV a = TwoChart.twPic (chart_sup U V hUV) t := by
  obtain ⟨t₀, t₁, ht01⟩ := decomp hW (O' := pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V) rfl
    (t : Γ(CT k C (B₁ k), pB k C (B₁ k) ⁻¹ᵁ U ⊓ pB k C (B₁ k) ⁻¹ᵁ V))
  have ht₀ := t₀_eq_one _ t₀ t₁ ht01 hit
  have htu : sqUnit (nE k U V t₁ (inr 1 : B₁ k)) (sq_one C t₁) = t :=
    Units.ext (EpsAlg.eq_one_add _ _ ht01 ht₀).symm
  exact ⟨t₁, congrArg (TwoChart.twPic (chart_sup U V hUV)) htu⟩

lemma isClosedImmersion_bc_aug :
    IsClosedImmersion (bc (C := C) (augM k R₀)) := by
  have hsurj : Function.Surjective (augM k R₀) := fun r ↦ ⟨inl r, rfl⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (augM k R₀).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_bcMap _ _ _ _ _).flip inferInstance

lemma surjective_bc_aug : Function.Surjective (bc (C := C) (augM k R₀)).base := by
  have hsurj : Function.Surjective (augM k R₀) := fun r ↦ ⟨inl r, rfl⟩
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom (augM k R₀).toRingHom)) :=
    (surjective_iff _).mpr
      (SmoothLift.surjective_of_thickening _ (SmoothLift.surjective_appTop_spec_map _ hsurj)
        (SmoothLift.sqZero_appTop_spec_map _ sqZero_fst))
  haveI : AlgebraicGeometry.Surjective (bc (C := C) (augM k R₀)) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective)
      (isPullback_bcMap _ _ _ _ _).flip inferInstance
  exact (surjective_iff _).mp inferInstance

/-- **Every class trivial on `C` is a twist `c₁ a`.** -/
theorem exists_c₁_eq (hUV : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (U ⊓ V))
    (κ : (CT k C (B₁ k)).Pic) (hκ : Scheme.Pic.map (bc (augM k R₀)) κ = 0) :
    ∃ a, c₁ (k := k) C U V hUV a = κ := by
  haveI := isClosedImmersion_bc_aug (k := k) (C := C)
  haveI : IsAffineHom (gB (S := Sk) (B₁ k)) := isAffineHom_of_isAffine _
  haveI : IsAffineHom (pB k C (B₁ k)) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  obtain ⟨L, hL, rfl⟩ := Scheme.Pic.mk_surjective κ
  have h0 : Scheme.Pic.mk ((Scheme.Modules.pullback (bc (C := C) (augM k R₀))).obj L) = 0 := by
    rw [← Scheme.Pic.map_mk]
    exact hκ
  obtain ⟨g, hg⟩ := BasisLift.exists_isBasisOn_top h0
  obtain ⟨ε, hε, hεg⟩ := BasisLift.exists_isBasisOn_lift _ surjective_bc_aug hg
    (hU.preimage (pB k C (B₁ k)))
  obtain ⟨δ, hδ, hδg⟩ := BasisLift.exists_isBasisOn_lift _ surjective_bc_aug hg
    (hV.preimage (pB k C (B₁ k)))
  obtain ⟨t, ht, htL⟩ := TwoChart.exists_twPic_eq (chart_sup U V hUV) hε hδ
  obtain ⟨a, ha⟩ := exists_c₁_eq_twPic hUV hW t
    (appLE_eq_one_of_lift _ L hg hεg hδg _ ht)
  exact ⟨a, ha.trans htL⟩

end CurvesJacobian.PicTangent
