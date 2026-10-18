/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierDegree
import CurvesJacobian.Picard.RelEffCartierSection
import CurvesJacobian.Picard.RelEffCartierFinite
import CurvesJacobian.Picard.FlatAlgebra

/-!
# Differences of relative effective Cartier divisors (Stacks, Tags 0B8V, 0B9F)

* `CurvesJacobian.map_colon_of_isLocalization`: colon ideals `(I : J)` with `J` finitely
  generated commute with localization.
* `CurvesJacobian.fg_ideal_of_locally_principal`: a locally principal ideal sheaf has finitely
  generated ideals on affine opens.
* `CurvesJacobian.Module.Flat.of_exact_ker`: in a short exact sequence `0 → M → N → P → 0` with
  `N`, `P` flat, `M` is flat; `CurvesJacobian.flat_quotient_of_mul`: if `g` is a nonzerodivisor
  and `R/g`, `R/gh` are `A`-flat, so is `R/h`.
* **`AlgebraicGeometry.RelEffCartier.sub`** (Stacks, Lemma 31.19.4, Tag 0B8V): if `D₁ ⊆ D₂` are
  relative effective Cartier divisors on `X/S` (i.e. `I_{D₂} ≤ I_{D₁}`), the ideal sheaf
  `(I_{D₂} : I_{D₁})` defines a relative effective Cartier divisor `D₂ − D₁` with
  `D₁ + (D₂ − D₁) = D₂` (`RelEffCartier.add_sub`).
* **`CurvesJacobian.exists_eq_ofSection_add`** (Stacks, Lemma 44.3.3, Tag 0B9F, for a section):
  for a curve `C` over a perfect field `k`, a relative effective Cartier divisor `D` on
  `C ×_k T / T` containing the image of a section `x` is `x + D'` with `deg D' = deg D − 1`;
  `D'` is unique (`RelEffCartier.add_left_cancel`, `existsUnique_ofSection_add`: the bijection
  behind Stacks, Lemma 44.3.4, Tag 0B9G, on `T`-points).
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

section Algebra

/-- **Colon ideals commute with localization** when the second ideal is finitely generated. -/
theorem map_colon_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I J : Ideal R) (hJ : J.FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon (J.map (algebraMap R S) : Set S) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s (hs : s ∈ Submodule.span S (algebraMap R S '' (J : Set R)))
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [smul_eq_mul, ← map_mul]
      exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp hr j hj)
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  · classical
    intro x hx
    obtain ⟨s, hs⟩ := hJ
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp only at hx ⊢
    have key : ∀ j ∈ s, ∃ c : M, (c : R) * (a * j) ∈ I := by
      intro j hj
      have hjJ : j ∈ J := hs ▸ Submodule.subset_span hj
      have h1 : IsLocalization.mk' S a m * algebraMap R S j ∈ I.map (algebraMap R S) :=
        (Submodule.mem_colon.mp hx) _ (Ideal.mem_map_of_mem _ hjJ)
      have h2 : algebraMap R S (a * j) ∈ I.map (algebraMap R S) := by
        have := Ideal.mul_mem_left _ (algebraMap R S m) h1
        rwa [← mul_assoc, IsLocalization.mk'_spec', ← map_mul] at this
      obtain ⟨⟨i, c⟩, hc⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp h2
      rw [← map_mul] at hc
      obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists M S).mp hc
      refine ⟨c' * c, ?_⟩
      rw [Submonoid.coe_mul, show (c' : R) * c * (a * j) = c' * ((a * j) * c) by ring, hc']
      exact Ideal.mul_mem_left _ _ i.2
    choose! c hc using key
    set p : R := ∏ j ∈ s, (c j : R)
    have hpM : p ∈ M := Submonoid.prod_mem _ fun j _ ↦ (c j).2
    have hp : p * a ∈ I.colon (J : Set R) := by
      rw [← hs, Submodule.mem_colon]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem j hj =>
        have hj' : (j : R) ∈ s := hj
        have hpj : p = (c j : R) * ∏ i ∈ s.erase j, (c i : R) :=
          (Finset.mul_prod_erase s (fun j ↦ (c j : R)) hj').symm
        rw [smul_eq_mul, hpj,
          show (c j : R) * (∏ i ∈ s.erase j, (c i : R)) * a * j =
            (∏ i ∈ s.erase j, (c i : R)) * ((c j : R) * (a * j)) by ring]
        exact Ideal.mul_mem_left _ _ (hc j hj')
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul b y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ b hy
    have hx_eq : IsLocalization.mk' S a m =
        algebraMap R S (p * a) * IsLocalization.mk' S (1 : R) (⟨p, hpM⟩ * m) := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, mul_comm p a, mul_comm (⟨p, hpM⟩ : M) m]
      exact (IsLocalization.mk'_cancel a m ⟨p, hpM⟩).symm
    rw [hx_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)

variable {A : Type u} [CommRing A] {M N P : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- In a short exact sequence `0 → M → N → P → 0` with `N` and `P` flat, `M` is flat. -/
theorem Module.Flat.of_exact_ker [Module.Flat A N] [Module.Flat A P] (f : M →ₗ[A] N)
    (g : N →ₗ[A] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro K K' _ _ _ _ φ hφ
  have h1 : Function.Injective (f.lTensor K) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg K
  have h2 : Function.Injective (φ.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap φ hφ
  have h3 : Function.Injective ((f.lTensor K').comp (φ.rTensor M)) := by
    rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
    exact h2.comp h1
  exact Function.Injective.of_comp h3

variable {R : Type u} [CommRing R] [Algebra A R]

/-- If `g` is a nonzerodivisor and `R/g`, `R/gh` are flat over `A`, so is `R/h` (the algebra of
Stacks, Lemma 31.19.4, Tag 0B8V). -/
theorem flat_quotient_of_mul {g : R} (hg : IsSMulRegular R g) (h : R)
    [Module.Flat A (R ⧸ Ideal.span {g})] [Module.Flat A (R ⧸ Ideal.span {g * h})] :
    Module.Flat A (R ⧸ Ideal.span {h}) :=
  Module.Flat.of_exact_ker ((mulQuot g h).restrictScalars A) ((quotFactor g h).restrictScalars A)
    (mulQuot_injective hg h) (quotFactor_surjective g h) (exact_mulQuot_quotFactor g h)

end Algebra

section FG

open Scheme

/-- A locally principal ideal sheaf has finitely generated ideals on affine opens. -/
lemma fg_ideal_of_locally_principal {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : ∀ x : X, ∃ (U : X.affineOpens) (g : Γ(X, U.1)), x ∈ U.1 ∧
      I.ideal U = Ideal.span {g} ∧ IsSMulRegular Γ(X, U.1) g)
    (U : X.affineOpens) : (I.ideal U).FG := by
  classical
  have hloc : ∀ x : U.1, ∃ a : Γ(X, U.1), x.1 ∈ X.basicOpen a ∧
      ∃ g, I.ideal (X.affineBasicOpen a) = Ideal.span {g} := by
    rintro ⟨x, hxU⟩
    obtain ⟨W, g, hxW, hIW, hg⟩ := hI x
    obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 W.2 x ⟨hxU, hxW⟩
    exact ⟨a, hxa, _, (IdealSheafData.principal_basicOpen hIW hg (X.affineBasicOpen a) b hab
      ((le_of_eq hab).trans (X.basicOpen_le b))).1⟩
  choose a ha g hg using hloc
  have ht : Ideal.span (Set.range a) = ⊤ := by
    rw [← U.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
    exact Opens.mem_iSup.mpr ⟨⟨a ⟨x, hx⟩, ⟨_, rfl⟩⟩, ha ⟨x, hx⟩⟩
  refine Ideal.fg_of_localizationSpan (Set.range a) ht fun ⟨_, ⟨y, rfl⟩⟩ ↦ ?_
  haveI := U.2.isLocalization_basicOpen (a y)
  let e := IsLocalization.algEquiv (Submonoid.powers (a y)) Γ(X, X.basicOpen (a y))
    (Localization.Away (a y))
  have h1 : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen (a y))) =
      Ideal.span {g y} :=
    (I.map_ideal_basicOpen U (a y)).trans (hg y)
  have h2 : (I.ideal U).map (algebraMap Γ(X, U.1) (Localization.Away (a y))) =
      ((I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen (a y)))).map
        (e : Γ(X, X.basicOpen (a y)) →+* Localization.Away (a y)) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact (e.commutes r).symm
  rw [h2, h1]
  exact Ideal.FG.map (Submodule.fg_span_singleton (g y)) _

end FG

end CurvesJacobian

namespace AlgebraicGeometry

open Scheme CurvesJacobian

namespace RelEffCartier

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The ideal sheaf `(I_{D₂} : I_{D₁})`. -/
def colonIdeal (D₁ D₂ : RelEffCartier f) : X.IdealSheafData where
  ideal U := (D₂.ideal.ideal U).colon (D₁.ideal.ideal U : Set Γ(X, U.1))
  map_ideal_basicOpen U a := by
    haveI := U.2.isLocalization_basicOpen a
    change ((D₂.ideal.ideal U).colon (D₁.ideal.ideal U : Set Γ(X, U.1))).map
      (algebraMap Γ(X, U.1) Γ(X, X.basicOpen a)) = _
    rw [map_colon_of_isLocalization (Submonoid.powers a) _ _
      (fg_ideal_of_locally_principal D₁.locally_principal U)]
    exact congrArg₂ (fun I J : Ideal Γ(X, X.basicOpen a) ↦ I.colon (J : Set _))
      (D₂.ideal.map_ideal_basicOpen U a) (D₁.ideal.map_ideal_basicOpen U a)

lemma colonIdeal_ideal (D₁ D₂ : RelEffCartier f) (U : X.affineOpens) :
    (colonIdeal D₁ D₂).ideal U =
      (D₂.ideal.ideal U).colon (D₁.ideal.ideal U : Set Γ(X, U.1)) := rfl

variable {D₁ D₂ : RelEffCartier f}

/-- On an affine open where `I_{D₁} = (g)` and `I_{D₂} = (g h)` with `g` a nonzerodivisor,
`(I_{D₂} : I_{D₁}) = (h)`. -/
lemma colonIdeal_eq_span {W : X.affineOpens} {g h : Γ(X, W.1)} (hg : IsSMulRegular Γ(X, W.1) g)
    (h₁ : D₁.ideal.ideal W = Ideal.span {g}) (h₂ : D₂.ideal.ideal W = Ideal.span {g * h}) :
    (colonIdeal D₁ D₂).ideal W = Ideal.span {h} := by
  rw [colonIdeal_ideal, h₁, h₂]
  ext r
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul, Ideal.mem_span_singleton',
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, hg ?_⟩
    simp only [smul_eq_mul]
    linear_combination hc
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

/-- Simultaneous principal generators: if `I_{D₂} ≤ I_{D₁}`, around every point there is an
affine open where `I_{D₁} = (g)` and `I_{D₂} = (g h)` with `g`, `g h` nonzerodivisors. -/
lemma exists_affine_principal_mul (hle : D₂.ideal ≤ D₁.ideal) (x : X) (O : X.Opens)
    (hxO : x ∈ O) :
    ∃ (W : X.affineOpens) (g h : Γ(X, W.1)), x ∈ W.1 ∧ W.1 ≤ O ∧
      D₁.ideal.ideal W = Ideal.span {g} ∧ IsSMulRegular Γ(X, W.1) g ∧
      D₂.ideal.ideal W = Ideal.span {g * h} ∧ IsSMulRegular Γ(X, W.1) (g * h) := by
  obtain ⟨W, g, g₂, hxW, hWO, h₁, hg, h₂, hg₂⟩ := exists_affine_principal_principal
    D₁.locally_principal D₂.locally_principal x O hxO
  have hmem : g₂ ∈ Ideal.span {g} := by
    rw [← h₁]
    exact hle W (h₂ ▸ Ideal.mem_span_singleton_self g₂)
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨W, g, h, hxW, hWO, h₁, hg, ?_, ?_⟩ <;> rw [mul_comm g h, hh]
  exacts [h₂, hg₂]

/-- **The difference `D₂ − D₁`** of relative effective Cartier divisors with `D₁ ⊆ D₂`
(Stacks, Lemma 31.19.4, Tag 0B8V). -/
def sub (D₂ D₁ : RelEffCartier f) (hle : D₂.ideal ≤ D₁.ideal) : RelEffCartier f where
  ideal := colonIdeal D₁ D₂
  locally_principal x := by
    obtain ⟨W, g, h, hxW, -, h₁, hg, h₂, hgh⟩ := exists_affine_principal_mul hle x ⊤ trivial
    refine ⟨W, h, hxW, colonIdeal_eq_span hg h₁ h₂, fun a b hab ↦ hgh ?_⟩
    simp only [smul_eq_mul] at hab ⊢
    rw [mul_assoc, mul_assoc, hab]
  flat := by
    apply IdealSheafData.flat_of_flat_quotient
    intro x _
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (Opens.mem_top (f.base x))
    obtain ⟨W, g, h, hxW, hWV, h₁, hg, h₂, -⟩ := exists_affine_principal_mul hle x (f ⁻¹ᵁ V) hxV
    refine ⟨⟨V, hV⟩, W, hxW, hWV, ?_⟩
    have hD₁ := D₁.ideal.flat_quotient_of_flat (hf := D₁.flat) f ⟨V, hV⟩ W hWV
    have hD₂ := D₂.ideal.flat_quotient_of_flat (hf := D₂.flat) f ⟨V, hV⟩ W hWV
    rw [h₁] at hD₁
    rw [h₂] at hD₂
    rw [colonIdeal_eq_span hg h₁ h₂]
    letI := (f.appLE V W.1 hWV).hom.toAlgebra
    have key : ∀ I : Ideal Γ(X, W.1), (Ideal.Quotient.mk I).comp (f.appLE V W.1 hWV).hom =
        algebraMap Γ(S, V) (Γ(X, W.1) ⧸ I) := fun _ ↦ rfl
    rw [key, RingHom.flat_algebraMap_iff] at hD₁ hD₂ ⊢
    exact flat_quotient_of_mul hg h

lemma sub_ideal (D₂ D₁ : RelEffCartier f) (hle : D₂.ideal ≤ D₁.ideal) :
    (D₂.sub D₁ hle).ideal = colonIdeal D₁ D₂ := rfl

/-- **`D₁ + (D₂ − D₁) = D₂`** (Stacks, Lemma 31.19.4, Tag 0B8V). -/
theorem add_sub (D₂ D₁ : RelEffCartier f) (hle : D₂.ideal ≤ D₁.ideal) :
    D₁.add (D₂.sub D₁ hle) = D₂ := by
  apply ext_ideal
  choose W g h hxW _ h₁ hg h₂ _ using fun x : X ↦ exists_affine_principal_mul hle x ⊤ trivial
  refine IdealSheafData.ext_of_iSup_eq_top W ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  · change (D₁.ideal * colonIdeal D₁ D₂).ideal (W x) = _
    rw [IdealSheafData.ideal_mul, Pi.mul_apply, colonIdeal_eq_span (hg x) (h₁ x) (h₂ x), h₁ x,
      h₂ x, Ideal.span_singleton_mul_span_singleton]

lemma add_ideal_le_left (D E : RelEffCartier f) : (D.add E).ideal ≤ D.ideal := fun U ↦ by
  change (D.ideal * E.ideal).ideal U ≤ _
  rw [IdealSheafData.ideal_mul, Pi.mul_apply]
  exact Ideal.mul_le_right

/-- **`(D + E) − D = E`.** -/
theorem add_sub_cancel_left (D E : RelEffCartier f) :
    (D.add E).sub D (add_ideal_le_left D E) = E := by
  apply ext_ideal
  choose W g h hxW _ h₁ hg h₂ _ using fun x : X ↦
    exists_affine_principal_principal D.locally_principal E.locally_principal x ⊤ trivial
  refine IdealSheafData.ext_of_iSup_eq_top W ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  · rw [sub_ideal]
    refine (colonIdeal_eq_span (hg x) (h₁ x) ?_).trans (h₂ x).symm
    change (D.ideal * E.ideal).ideal (W x) = _
    rw [IdealSheafData.ideal_mul, Pi.mul_apply, h₁ x, h₂ x,
      Ideal.span_singleton_mul_span_singleton]

/-- **Cancellation**: `D + E = D + E'` implies `E = E'`. -/
theorem add_left_cancel {D E E' : RelEffCartier f} (h : D.add E = D.add E') : E = E' := by
  have h1 := congrArg ideal (add_sub_cancel_left D E)
  have h2 := congrArg ideal (add_sub_cancel_left D E')
  rw [sub_ideal] at h1 h2
  apply ext_ideal
  rw [← h1, ← h2, h]

end RelEffCartier

end AlgebraicGeometry

namespace CurvesJacobian

open AlgebraicGeometry

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [Belyi.IsCurveOver k C] {T : Scheme.{u}}
  (gT : T ⟶ Spec (CommRingCat.of k))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) gT
local notation "fT" => pullback.snd (C ↘ Sk) gT

/-- **A divisor containing a section splits off the section** (Stacks, Lemma 44.3.3, Tag 0B9F,
for `D₁` the image of a section): if the relative effective Cartier divisor `D` on
`C ×_k T / T` contains the image of the section `x` (i.e. `I_D ≤ I_x`), then `D = x + D'` for a
relative effective Cartier divisor `D'` with `deg D' = deg D − 1`. -/
theorem exists_eq_ofSection_add (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) (D : RelEffCartier (fT))
    (hle : D.ideal ≤ s.ker) :
    ∃ D' : RelEffCartier (fT), (RelEffCartier.ofSection C gT s hs).add D' = D ∧
      ∀ t, D'.degree t + 1 = D.degree t := by
  refine ⟨D.sub (RelEffCartier.ofSection C gT s hs) hle,
    RelEffCartier.add_sub D (RelEffCartier.ofSection C gT s hs) hle, fun t ↦ ?_⟩
  haveI := (RelEffCartier.ofSection C gT s hs).isFinite C gT
  haveI := (D.sub (RelEffCartier.ofSection C gT s hs) hle).isFinite C gT
  haveI := D.isFinite C gT
  haveI := ((RelEffCartier.ofSection C gT s hs).add
    (D.sub (RelEffCartier.ofSection C gT s hs) hle)).isFinite C gT
  have h := RelEffCartier.degree_add (RelEffCartier.ofSection C gT s hs)
    (D.sub (RelEffCartier.ofSection C gT s hs) hle) t
  rw [RelEffCartier.add_sub, RelEffCartier.degree_ofSection] at h
  rw [h, Pi.one_apply, add_comm]

/-- **Stacks, Lemma 44.3.4 (Tag 0B9G), on points**: divisors `D` of degree `d + 1` on
`C ×_k T / T` containing the image of a section `x` correspond bijectively to divisors `D'` of
degree `d`, via `D = x + D'`. -/
theorem existsUnique_ofSection_add (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T)
    (D : RelEffCartier (fT)) (hle : D.ideal ≤ s.ker) :
    ∃! D' : RelEffCartier (fT), (RelEffCartier.ofSection C gT s hs).add D' = D := by
  obtain ⟨D', h, -⟩ := exists_eq_ofSection_add C gT s hs D hle
  exact ⟨D', h, fun E hE ↦ RelEffCartier.add_left_cancel (hE.trans h.symm)⟩

end CurvesJacobian
