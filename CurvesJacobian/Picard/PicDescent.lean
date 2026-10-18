/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.GaloisPoints
import CurvesJacobian.Picard.SectionDrop
import CurvesJacobian.Picard.AbelInj

/-!
# Galois descent for the rigidified Picard group of a curve

Let `C` be a curve over a perfect field `k` with a rational point `σ`, and `Ω / K` a Galois
extension of fields containing `k`.

## Over a field

For `T` affine over `k` with `Γ(T)` a field, write `s = [𝒪(σ_T)] ∈ Pic(C_T)` for the class of
the divisor of the base change of `σ` (`sigmaDiv`) and `deg z = χ(z) − (1 − g)` (`degPic`).

* `CurvesJacobian.eq_of_picClass_eq_of_not_isEff`: if `z` is not effective, then there is at most
  one effective divisor in the class `z + s`: `Γ(z) = 0` forces `h⁰(z + s) ≤ 1`
  (`Cech.exists_eq_smul_of_subsingleton`), and divisors in a class with cyclic `H⁰` coincide
  (`RelEffCartier.eq_of_picClass_eq`).
* **`CurvesJacobian.exists_unique_effective`**: for every class `c` there is `n ∈ ℤ` such that
  `c + n · s` contains exactly one effective divisor (take `n` minimal with `c + n · s`
  effective; it exists since effective classes have degree `≥ 0` and classes of degree `≥ g`
  are effective).

## Galois descent

* **`CurvesJacobian.exists_picRes_eq`**: for a Galois extension `Ω / K` (possibly infinite) of
  fields containing `k`, every `Gal(Ω/K)`-invariant element `c` of `Pic_{C/k,σ}(Ω)` comes from
  `Pic_{C/k,σ}(K)`: the unique effective divisor `D` in `c + n·[σ_Ω]` is a `Gal(Ω/K)`-invariant
  `Ω`-point of the `k`-scheme `Hilb^e_{C/k}`, hence a `K`-point (`exists_specMapAlg_comp_eq`),
  and `c` is the image of `[D_K] − n·[σ_K]`.
* **`CurvesJacobian.exists_jacPoints_picRes_eq`**: the same for the points of the Jacobian,
  `J(K) = Pic⁰_{C/k,σ}(K) ⟶ J(Ω)^{Gal(Ω/K)}` is surjective.

Injectivity of `J(K) ⟶ J(Ω)` (flat base change of `H⁰`) is not proved here.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules MonoidalCategory

universe u

noncomputable section

namespace CurvesJacobian

/-- The canonical section of `𝒪(D)` is nonzero. -/
lemma canonicalSection_ne_zero {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [Belyi.IsCurveOver k C] {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k))] [IsAffine T] (hF : IsField Γ(T, ⊤))
    (D : RelEffCartier (pullback.snd (C ↘ Spec (CommRingCat.of k))
      (T ↘ Spec (CommRingCat.of k)))) : D.canonicalSection ≠ 0 := by
  set Y := pullback (C ↘ Spec (CommRingCat.of k)) (T ↘ Spec (CommRingCat.of k))
  haveI := surjective_pullback_snd (C := C) (T ↘ Spec (CommRingCat.of k))
  obtain ⟨t⟩ := nonempty_of_isField hF
  obtain ⟨y, -⟩ := (pullback.snd (C ↘ Spec (CommRingCat.of k))
    (T ↘ Spec (CommRingCat.of k))).surjective t
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
  intro h
  have hinj := (D.injective_smul_canonicalSection ⊤).ne (one_ne_zero (α := Γ(Y, ⊤)))
  apply hinj
  simp [h]

open Cech Belyi

section SigmaDiv

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)

/-- The divisor of the base change `σ_T : T ⟶ C ×_k T` of the rational point `σ`. -/
def sigmaDiv {T : Scheme.{u}} (g : T ⟶ Sk) : RelEffCartier (pullback.snd (C ↘ Sk) g) :=
  RelEffCartier.ofSection C g (secT (C ↘ Sk) σ hσ g) (secT_snd _ _ _ _)

/-- The divisors `σ_T` are compatible with base change. -/
lemma map_picClass_sigmaDiv {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ Sk) (g' : T' ⟶ Sk)
    (w : a ≫ g = g') :
    Scheme.Pic.map (bcMap (C ↘ Sk) a g g' w) (sigmaDiv σ hσ g).picClass =
      (sigmaDiv σ hσ g').picClass := by
  rw [sigmaDiv, sigmaDiv, ← map_picClass_ofSection C σ hσ g, ← map_picClass_ofSection C σ hσ g',
    ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp,
    ← bcMap_comp _ _ _ _ _ _ _ _ (by rw [w, Category.comp_id])]
  congr 2
  exact bcMap_congr _ (by rw [w]) _ _ _ _

end SigmaDiv

section Field

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T ↘ Sk)

/-- The degree `χ(z) − (1 − g)` of a class `z ∈ Pic(C ×_k T)`. -/
def degPic (z : (pullback (C ↘ Sk) (T ↘ Sk)).Pic) : ℤ :=
  chiCurve π (T ↘ Sk) (Scheme.Pic.rep z) - 1 + genusNat k C

lemma degPic_add (hF : IsField Γ(T, ⊤)) (z z' : (XT).Pic) :
    degPic π (z + z') = degPic π z + degPic π z' := by
  unfold degPic
  rw [chiCurve_add_of_isField π hF]
  ring

lemma degPic_zero (hF : IsField Γ(T, ⊤)) : degPic π (0 : (XT).Pic) = 0 := by
  unfold degPic
  rw [chiCurve_rep_zero π hF]
  ring

/-- The degree as a homomorphism `Pic(C ×_k T) → ℤ`. -/
def degPicHom (hF : IsField Γ(T, ⊤)) : (XT).Pic →+ ℤ where
  toFun := degPic π
  map_zero' := degPic_zero π hF
  map_add' := degPic_add π hF

lemma degPic_picClass (hF : IsField Γ(T, ⊤)) (D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)))
    (t : T) : degPic π D.picClass = D.degree t := by
  unfold degPic
  rw [chiCurve_ofDivisor π hF D t]
  ring

lemma degPic_sigmaDiv (hF : IsField Γ(T, ⊤)) :
    degPic π (sigmaDiv σ hσ (T ↘ Sk)).picClass = 1 := by
  obtain ⟨t⟩ := nonempty_of_isField hF
  rw [degPic_picClass π hF _ t, sigmaDiv, RelEffCartier.degree_ofSection]
  rfl

/-- A class is effective if it is the class of a relative effective Cartier divisor. -/
def IsEff (z : (XT).Pic) : Prop :=
  ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)), D.picClass = z

include π in
lemma degPic_nonneg_of_isEff (hF : IsField Γ(T, ⊤)) {z : (XT).Pic} (hz : IsEff z) :
    0 ≤ degPic π z := by
  obtain ⟨D, rfl⟩ := hz
  obtain ⟨t⟩ := nonempty_of_isField hF
  rw [degPic_picClass π hF D t]
  positivity

lemma isEff_of_le_degPic (hF : IsField Γ(T, ⊤)) {z : (XT).Pic}
    (hz : (genusNat k C : ℤ) ≤ degPic π z) : IsEff z := by
  obtain ⟨D, hD⟩ := exists_relEffCartier_of_chiCurve_pos π (T ↘ Sk) hF (Scheme.Pic.rep z)
    (by unfold degPic at hz; omega)
  exact ⟨D, hD.trans (Scheme.Pic.mk_rep z)⟩

include π in
lemma subsingleton_of_not_isEff (hF : IsField Γ(T, ⊤)) {z : (XT).Pic} (hz : ¬ IsEff z) :
    Subsingleton Γ(Scheme.Pic.rep z, ⊤) := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(Scheme.Pic.rep z, ⊤))
  obtain ⟨D, hD⟩ := exists_relEffCartier_of_ne_zero π hF (Scheme.Pic.rep z) s hs
  exact hz ⟨D, hD.trans (Scheme.Pic.mk_rep z)⟩

include π in
/-- **At most one effective divisor in `z + [𝒪(σ_T)]` if `z` is not effective.** -/
theorem eq_of_picClass_eq_of_not_isEff (hF : IsField Γ(T, ⊤)) {z : (XT).Pic} (hz : ¬ IsEff z)
    (D₁ D₂ : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)))
    (h₁ : D₁.picClass = z + (sigmaDiv σ hσ (T ↘ Sk)).picClass)
    (h₂ : D₂.picClass = z + (sigmaDiv σ hσ (T ↘ Sk)).picClass) : D₁ = D₂ := by
  haveI hM := subsingleton_of_not_isEff π hF hz
  set Dσ := sigmaDiv σ hσ (T ↘ Sk)
  set σT := secT (C ↘ Sk) σ hσ (T ↘ Sk)
  haveI := isClosedImmersion_of_section C (T ↘ Sk) σT (secT_snd _ _ _ _)
  have hD : Dσ.ideal = σT.ker := RelEffCartier.ofSection_ideal C _ _ _
  have hσT : σT ≫ pullback.snd (C ↘ Sk) (T ↘ Sk) = 𝟙 T := secT_snd _ _ _ _
  -- `Γ(z + s)` is at most one-dimensional
  have hcyc : ∀ {t₁ : Γ(Scheme.Pic.rep z ⊗ Dσ.lineBundle, ⊤)}, t₁ ≠ 0 →
      ∀ t₂, ∃ μ : Γ(T, ⊤), t₂ = μ • t₁ := by
    intro t₁ ht₁ t₂
    have hU := isAffineOpen_chart (T₀ := T) π 0
    have hV := isAffineOpen_chart (T₀ := T) π 1
    have hUV := isAffineOpen_chart_inf (T₀ := T) π
    have hcov := chartOf_sup π (T ↘ Sk)
    rcases opens_eq_bot_or_top hF (σT ⁻¹ᵁ chartOf π (T ↘ Sk) 0) with h0 | h0
    · have h1 : ⊤ ≤ σT ⁻¹ᵁ chartOf π (T ↘ Sk) 1 := by
        have h := congrArg (σT ⁻¹ᵁ ·) hcov
        simp only [Scheme.Hom.preimage_sup, h0, bot_sup_eq, Scheme.Hom.preimage_top] at h
        rw [h]
      exact exists_eq_smul_of_subsingleton σT hσT Dσ hD _ hF hV hU
        (by rw [inf_comm]; exact hUV) (by rw [sup_comm]; exact hcov) h1 hM ht₁ t₂
    · exact exists_eq_smul_of_subsingleton σT hσT Dσ hD _ hF hU hV hUV hcov h0 hM ht₁ t₂
  -- transport to `𝒪(D₂)`
  have he : Scheme.Pic.mk D₂.lineBundle = Scheme.Pic.mk (Scheme.Pic.rep z ⊗ Dσ.lineBundle) := by
    rw [Scheme.Pic.mk_tensor, Scheme.Pic.mk_rep]
    exact h₂
  obtain ⟨e⟩ := Scheme.Pic.mk_eq_mk_iff.mp he
  let E := sectionsIso (S := T) e ⊤
  let H := globalSectionsEquivH0 T D₂.lineBundle (chartOf_sup π (T ↘ Sk))
  have hne : E D₂.canonicalSection ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]
    exact canonicalSection_ne_zero hF D₂
  refine RelEffCartier.eq_of_picClass_eq π (T ↘ Sk) D₁ D₂ (h₁.trans h₂.symm)
    (H D₂.canonicalSection) ?_
  rw [eq_top_iff]
  intro x _
  obtain ⟨μ, hμ⟩ := hcyc hne (E (H.symm x))
  rw [Submodule.mem_span_singleton]
  refine ⟨μ, ?_⟩
  rw [← LinearEquiv.map_smul] at hμ
  have h3 : H.symm x = μ • D₂.canonicalSection := E.injective hμ
  exact ((H.map_smul μ _).symm.trans (congrArg H h3.symm)).trans (H.apply_symm_apply x)

/-- Degrees of multiples of `s`. -/
lemma degPic_add_zsmul (hF : IsField Γ(T, ⊤)) (c : (XT).Pic) (n : ℤ) :
    degPic π (c + n • (sigmaDiv σ hσ (T ↘ Sk)).picClass) = degPic π c + n := by
  have h := map_zsmul (degPicHom π hF) n (sigmaDiv σ hσ (T ↘ Sk)).picClass
  change degPic π (n • _) = n • degPic π _ at h
  rw [degPic_add π hF, h, degPic_sigmaDiv π σ hσ hF, smul_eq_mul, mul_one]

include π in
/-- **Every class has a translate by a multiple of `[𝒪(σ_T)]` containing exactly one effective
divisor.** -/
theorem exists_unique_effective (hF : IsField Γ(T, ⊤)) (c : (XT).Pic) :
    ∃ n : ℤ, ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)),
      D.picClass = c + n • (sigmaDiv σ hσ (T ↘ Sk)).picClass ∧
      ∀ D' : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)), D'.picClass = D.picClass → D' = D := by
  set s := (sigmaDiv σ hσ (T ↘ Sk)).picClass
  set N : ℤ := degPic π c + 1
  have hex : ∃ e : ℕ, IsEff (c + ((e : ℤ) - N) • s) := by
    refine ⟨(genusNat k C + N - degPic π c).toNat, isEff_of_le_degPic π hF ?_⟩
    rw [degPic_add_zsmul π σ hσ hF]
    omega
  classical
  set e₀ := Nat.find hex
  have he₀ : IsEff (c + ((e₀ : ℤ) - N) • s) := Nat.find_spec hex
  have hpos : e₀ ≠ 0 := by
    intro h0
    have h := degPic_nonneg_of_isEff π hF he₀
    rw [degPic_add_zsmul π σ hσ hF, h0] at h
    omega
  obtain ⟨e₁, he₁⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin : ¬ IsEff (c + ((e₁ : ℤ) - N) • s) :=
    Nat.find_min hex (show e₁ < e₀ by omega)
  obtain ⟨D, hD⟩ := he₀
  have hz : c + ((e₀ : ℤ) - N) • s = (c + ((e₁ : ℤ) - N) • s) + s := by
    rw [he₁, add_assoc, ← add_one_zsmul]
    congr 2
    push_cast
    ring
  refine ⟨(e₀ : ℤ) - N, D, hD, fun D' hD' ↦ ?_⟩
  exact eq_of_picClass_eq_of_not_isEff π σ hσ hF hmin D' D (hD'.trans (hD.trans hz))
    (hD.trans hz)

end Field

section Galois

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)

omit [PerfectField k] [IsCurveOver k C] in
/-- Over a field, the Abel class of `D` is the class of `𝒪(D)`. -/
lemma coe_abelClass_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤))
    (g : T ⟶ Sk) (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) :
    (abelClass (C ↘ Sk) σ hσ D : (pullback (C ↘ Sk) g).Pic) = D.picClass := by
  haveI := subsingleton_pic_of_isField hF
  rw [coe_abelClass, Subsingleton.elim (Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) D.picClass) 0,
    map_zero, sub_zero]

/-- The ideal of `σ_{T'}` is the pullback of the ideal of `σ_T`. -/
lemma sigmaDiv_ideal_comap {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ Sk) (g' : T' ⟶ Sk)
    (w : a ≫ g = g') :
    (sigmaDiv σ hσ g').ideal = (sigmaDiv σ hσ g).ideal.comap (bcMap (C ↘ Sk) a g g' w) := by
  haveI := isClosedImmersion_of_section C g (secT (C ↘ Sk) σ hσ g) (secT_snd _ _ _ _)
  rw [sigmaDiv, sigmaDiv, RelEffCartier.ofSection_ideal, RelEffCartier.ofSection_ideal]
  exact (ker_comap_bcMap (C ↘ Sk) a g g' w _ (secT_snd _ _ _ _) _ (secT_snd _ _ _ _)
    (secT_bcMap _ _ _ _ _ _ _)).symm

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

lemma isField_ΓSpec' (F : Type u) [Field F] : IsField Γ(Spec (CommRingCat.of F), ⊤) :=
  MulEquiv.isField (Field.toIsField F)
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv

variable [IsGalois K Ω]

/-- **Galois descent for the rigidified Picard group of a curve**: for a Galois extension
`Ω / K` of fields containing `k`, every `Gal(Ω/K)`-invariant element of `Pic_{C/k,σ}(Ω)` comes
from `Pic_{C/k,σ}(K)`.

Proof: some translate `c + n·[σ]` of the invariant class `c` contains exactly one effective
divisor `D` (`exists_unique_effective`); `D` is a `Gal(Ω/K)`-invariant `Ω`-point of the
`k`-scheme `Hilb^e_{C/k}`, hence comes from a `K`-point (`exists_specMapAlg_comp_eq`), i.e. from
a divisor `D_K` on `C_K`, and `c` is the image of `[D_K] − n·[σ_K]`. -/
theorem exists_picRes_eq (c : picPt C σ hσ Ω) (hc : c ∈ picInv C σ hσ K Ω) :
    ∃ x : picPt C σ hσ K, picRes C σ hσ K Ω x = c := by
  letI : (Spec (CommRingCat.of Ω)).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
  set gΩ := specAlgebraMap (k₀ := k) Ω
  set gK := specAlgebraMap (k₀ := k) K
  have hF := isField_ΓSpec' Ω
  obtain ⟨n, D, hD, huniq⟩ : ∃ n : ℤ, ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) gΩ),
      D.picClass = (c : (pullback (C ↘ Sk) gΩ).Pic) + n • (sigmaDiv σ hσ gΩ).picClass ∧
      ∀ D' : RelEffCartier (pullback.snd (C ↘ Sk) gΩ), D'.picClass = D.picClass → D' = D :=
    exists_unique_effective (curveToP1 k C) σ hσ hF (c : (pullback (C ↘ Sk) gΩ).Pic)
  obtain ⟨t₀⟩ := nonempty_of_isField hF
  haveI := subsingleton_of_isField hF
  have hdeg : ∀ t, D.degree t = D.degree t₀ := fun t ↦ by rw [Subsingleton.elim t t₀]
  set e := D.degree t₀
  let a : Spec (CommRingCat.of Ω) ⟶ hilbCurve k C e :=
    (hilbCurveEquiv k C e _).symm ⟨gΩ, D, hdeg⟩
  have ha : hilbCurveEquiv k C e _ a = ⟨gΩ, D, hdeg⟩ := Equiv.apply_symm_apply _ _
  -- the invariant class `c + n·[σ]`
  have hinv : ∀ τ : Ω ≃ₐ[K] Ω, Scheme.Pic.map (bcMap (C ↘ Sk) (specAut τ) gΩ gΩ
      (specAut_comp_specAlgebraMap τ)) D.picClass = D.picClass := by
    intro τ
    rw [hD, map_add, map_zsmul, map_picClass_sigmaDiv]
    congr 1
    exact congrArg Subtype.val (hc τ)
  -- `D` is `Gal(Ω/K)`-invariant as a point of `Hilb^e`
  have hainv : ∀ τ : Ω ≃ₐ[K] Ω, specAut τ ≫ a = a := by
    intro τ
    apply (hilbCurveEquiv k C e _).injective
    rw [ha]
    obtain ⟨y, hy⟩ : ∃ y, hilbCurveEquiv k C e _ (specAut τ ≫ a) = y := ⟨_, rfl⟩
    rw [hy]
    obtain ⟨g', D', hD'⟩ := y
    have w : specAut τ ≫ gΩ = g' := by
      have h1 := hilbCurveEquiv_comp_fst k C (specAut τ) a
      rw [hy, ha] at h1
      exact h1.symm
    have hideal := hilbCurveEquiv_comp_ideal' k C (specAut τ) a _ ha _ hy w
    have hg' : g' = gΩ := w.symm.trans (specAut_comp_specAlgebraMap τ)
    subst hg'
    have hpic : D'.picClass = D.picClass := by
      rw [← RelEffCartier.map_picClass_of_ideal_eq D D' _ hideal]
      exact hinv τ
    obtain rfl := huniq D' hpic
    rfl
  -- descent of the point
  obtain ⟨b, hb⟩ := exists_specMapAlg_comp_eq a hainv
  obtain ⟨y, hy⟩ : ∃ y, hilbCurveEquiv k C e _ b = y := ⟨_, rfl⟩
  obtain ⟨g₁, DK, hDK⟩ := y
  have hab : hilbCurveEquiv k C e _ (specMapAlg K Ω ≫ b) = ⟨gΩ, D, hdeg⟩ := by rw [hb, ha]
  have wK : specMapAlg K Ω ≫ g₁ = gΩ := by
    have h1 := hilbCurveEquiv_comp_fst k C (specMapAlg K Ω) b
    rw [hy, hab] at h1
    exact h1.symm
  have hidealK := hilbCurveEquiv_comp_ideal' k C (specMapAlg K Ω) b _ hy _ hab wK
  have hg₁ : g₁ = gK := eq_of_specMapAlg_comp_eq (Ω := Ω)
    (wK.trans (specMapAlg_comp_specAlgebraMap K Ω).symm)
  subst hg₁
  -- the class over `K`
  refine ⟨abelClass (C ↘ Sk) σ hσ DK - n • abelClass (C ↘ Sk) σ hσ (sigmaDiv σ hσ gK), ?_⟩
  rw [map_sub, map_zsmul]
  have h1 : picRes C σ hσ K Ω (abelClass (C ↘ Sk) σ hσ DK) = abelClass (C ↘ Sk) σ hσ D :=
    picSigmaMap_abelClass _ σ hσ _ _ _ _ DK D hidealK
  have h2 : picRes C σ hσ K Ω (abelClass (C ↘ Sk) σ hσ (sigmaDiv σ hσ gK)) =
      abelClass (C ↘ Sk) σ hσ (sigmaDiv σ hσ gΩ) :=
    picSigmaMap_abelClass _ σ hσ _ _ _ _ _ _ (sigmaDiv_ideal_comap C σ hσ _ _ _ _)
  rw [h1, h2]
  apply Subtype.ext
  rw [AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, coe_abelClass_of_isField C σ hσ hF,
    coe_abelClass_of_isField C σ hσ hF, hD]
  abel

/-- **Galois descent for the points of the Jacobian**: for a Galois extension `Ω / K` of fields
containing `k`, every `Gal(Ω/K)`-invariant point of `J(Ω) = Pic⁰_{C/k,σ}(Ω)` comes from
`J(K) = Pic⁰_{C/k,σ}(K)`. -/
theorem exists_jacPoints_picRes_eq (c : picPt C σ hσ Ω) (hc₀ : c ∈ jacPoints C σ hσ Ω)
    (hc : c ∈ picInv C σ hσ K Ω) :
    ∃ x ∈ jacPoints C σ hσ K, picRes C σ hσ K Ω x = c := by
  obtain ⟨x, hx⟩ := exists_picRes_eq C σ hσ K Ω c hc
  refine ⟨x, ?_, hx⟩
  set π := curveToP1 k C
  have hd := picDeg_of_isField σ hσ π (isField_ΓSpec' K)
    (⟨specAlgebraMap (k₀ := k) K, x⟩ :
      (sigmaG (picSigma (C ↘ Sk) σ hσ)).obj (op (Spec (CommRingCat.of K))))
  set d := chiPoint σ hσ π (⟨specAlgebraMap (k₀ := k) K, x⟩ :
      (sigmaG (picSigma (C ↘ Sk) σ hσ)).obj (op (Spec (CommRingCat.of K)))) - 1 + genusNat k C
  have hdΩ := picDeg_map_over C σ hσ π d
    (Over.homMk (specMapAlg K Ω) (specMapAlg_comp_specAlgebraMap K Ω) :
      Over.mk (specAlgebraMap (k₀ := k) Ω) ⟶ Over.mk (specAlgebraMap (k₀ := k) K)) x hd
  have h1 := hdΩ _ (isField_ΓSpec' Ω) (𝟙 _)
  have h2 := hc₀ _ (isField_ΓSpec' Ω) (𝟙 _)
  have hxc : ((picSigma (C ↘ Sk) σ hσ).map (Over.homMk (specMapAlg K Ω)
      (specMapAlg_comp_specAlgebraMap K Ω) : Over.mk (specAlgebraMap (k₀ := k) Ω) ⟶
        Over.mk (specAlgebraMap (k₀ := k) K)).op).hom x = c := hx
  rw [hxc] at h1
  have hd0 : d = 0 := by
    have := h1.symm.trans h2
    omega
  rw [hd0] at hd
  exact hd

end Galois

end CurvesJacobian
