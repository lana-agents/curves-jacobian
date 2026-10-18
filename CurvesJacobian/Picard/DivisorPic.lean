/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.CurveIdealDivisor
import CurvesJacobian.Picard.RelEffCartierPicAdd
import CurvesJacobian.Picard.ChartTwist
import CurvesJacobian.Picard.JacobianPoints
import CurvesJacobian.Picard.PicProper
import CurvesJacobian.Picard.RelEffCartierSection
import WeilCurves.Hurwitz.Belyi

/-!
# Divisor classes and the Picard group of a curve

Let `Y` be a curve over a perfect field `κ` (integral, with function field `K(Y)`) and
`D P` a relative effective Cartier divisor on `Y` (over some base) for every place `P`, whose
ideal sheaf has divisor `P` (`IdealSheafData.HasDiv`). We show that `P ↦ [𝒪(D P)]` induces an
injective homomorphism from the divisor class group of `K(Y)` to `Pic(Y)`, and specialise to
the base change `C_κ = C ×_k κ` of a curve `C/k` to an algebraically closed field `κ ⊇ k`, with
`D P = x_P` the divisor of the `κ`-rational point at `P` (JAC-1b (ii)–(iv)).

Generic part (any family `D`):
* `CurvesJacobian.divPicOf D : Div(K(Y)) →+ Pic(Y)`, `single P n ↦ n • [𝒪(D P)]`;
* `CurvesJacobian.effDivOf D E`: the divisor `∑ E(P) · D P` of an effective `E`, with
  `hasDiv_effDivOf` and `picClass_effDivOf : [𝒪(effDivOf D E)] = divPicOf D E`;
* `CurvesJacobian.exists_sections_zeroDivisor_polarDivisor`: for `g ≠ 0` the invertible sheaf
  glued from the opens where `g`, resp. `g⁻¹`, is regular (transition function `g`) has two
  sections whose zero schemes are the zeros and the poles of `g`;
* `CurvesJacobian.divPicOf_div`: principal divisors map to `0`;
* `CurvesJacobian.mem_principal_of_divPicOf_eq_zero`: conversely (two sections of
  `𝒪(D₁) ≅ 𝒪(D₂)` differ by a rational function, `exists_ord_eq_sub`);
* `CurvesJacobian.picDivPicOf`, `picDivPicOf_injective`: `Pic(K(Y)) ↪ Pic(Y)`.

Base change to `κ` algebraically closed:
* `CurvesJacobian.pointDiv C κ P`, `divPic C κ`, `effDiv C κ E`, `divPic_div`,
  `divPic_eq_zero_iff`, `picDivPic C κ`, **`picDivPic_injective`**;
* `CurvesJacobian.degPic_divPic`: `deg [𝒪(E)] = deg E`;
* `CurvesJacobian.picDivPt C κ σ hσ : Pic(K(C_κ)) →+ Pic_{C/k,σ}(κ)` (injective), and
  **`CurvesJacobian.jacBridge C κ σ hσ : Pic⁰(K(C_κ)) →+ J(κ)`**, `jacBridge_injective`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Opposite
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

open Scheme ModulesGlue

section Generic

variable {κ : Type u} [Field κ] [PerfectField κ] {Y : Scheme.{u}} [Y.Over (Spec (.of κ))]
  [IsCurveOver κ Y] [IsIntegral Y] {S : Scheme.{u}} {f : Y ⟶ S}

/-! ### Divisors of lists of places -/

/-- The divisor `P₁ + ⋯ + Pₙ` of a list of places. -/
def listDiv (l : List (Place κ Y.functionField)) : Divisor κ Y.functionField :=
  (l.map fun P ↦ Finsupp.single P (1 : ℤ)).sum

omit [PerfectField κ] [IsCurveOver κ Y] in
lemma listDiv_apply (l : List (Place κ Y.functionField)) (P : Place κ Y.functionField) :
    listDiv l P = l.count P := by
  induction l with
  | nil => simp [listDiv]
  | cons Q l ih =>
    rw [listDiv, List.map_cons, List.sum_cons, Finsupp.add_apply, ← listDiv, ih,
      List.count_cons, Finsupp.single_apply]
    by_cases h : Q = P
    · simp [h, add_comm]
    · simp [h]

/-- A list of places with sum the effective divisor `E` (each place repeated `E P` times). -/
def posList (E : Divisor κ Y.functionField) : List (Place κ Y.functionField) :=
  (Finsupp.toMultiset (Finsupp.mapRange Int.toNat (by simp) E)).toList

omit [PerfectField κ] [IsCurveOver κ Y] in
lemma listDiv_posList {E : Divisor κ Y.functionField} (hE : 0 ≤ E) : listDiv (posList E) = E := by
  ext P
  rw [listDiv_apply, posList, ← Multiset.coe_count, Multiset.coe_toList,
    Finsupp.count_toMultiset, Finsupp.mapRange_apply, Int.toNat_of_nonneg (hE P)]

variable (D : Place κ Y.functionField → RelEffCartier f)

/-- The relative effective Cartier divisor `D P₁ + ⋯ + D Pₙ` of a list of places. -/
def effDivList : List (Place κ Y.functionField) → RelEffCartier f
  | [] => RelEffCartier.zero f
  | P :: l => (D P).add (effDivList l)

lemma hasDiv_effDivList (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    (l : List (Place κ Y.functionField)) : (effDivList D l).ideal.HasDiv (listDiv l) := by
  induction l with
  | nil => exact IdealSheafData.hasDiv_top
  | cons P l ih =>
    rw [listDiv, List.map_cons, List.sum_cons, ← listDiv]
    exact (hD P).mul ih (D P).locally_principal (effDivList D l).locally_principal

omit [PerfectField κ] [IsCurveOver κ Y] in
lemma picClass_effDivList (l : List (Place κ Y.functionField)) :
    (effDivList D l).picClass = (l.map fun P ↦ (D P).picClass).sum := by
  induction l with
  | nil => exact RelEffCartier.picClass_zero f
  | cons P l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    exact RelEffCartier.picClass_add (D P) (effDivList D l)

/-- The map `Div(K(Y)) → Pic(Y)`, `P ↦ [𝒪(D P)]`. -/
def divPicOf : Divisor κ Y.functionField →+ Y.Pic :=
  Finsupp.liftAddHom fun P ↦ zmultiplesHom Y.Pic (D P).picClass

omit [PerfectField κ] [IsCurveOver κ Y] in
@[simp]
lemma divPicOf_single (P : Place κ Y.functionField) (n : ℤ) :
    divPicOf D (Finsupp.single P n) = n • (D P).picClass := by
  simp [divPicOf]

omit [PerfectField κ] [IsCurveOver κ Y] in
lemma divPicOf_listDiv (l : List (Place κ Y.functionField)) :
    divPicOf D (listDiv l) = (l.map fun P ↦ (D P).picClass).sum := by
  rw [listDiv, map_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun P _ ↦ by simp

/-- The relative effective Cartier divisor `∑ E(P) · D P` of an effective divisor `E`. -/
def effDivOf (E : Divisor κ Y.functionField) : RelEffCartier f :=
  effDivList D (posList E)

lemma hasDiv_effDivOf (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    {E : Divisor κ Y.functionField} (hE : 0 ≤ E) : (effDivOf D E).ideal.HasDiv E := by
  have h := hasDiv_effDivList D hD (posList E)
  rwa [listDiv_posList hE] at h

omit [PerfectField κ] [IsCurveOver κ Y] in
lemma picClass_effDivOf {E : Divisor κ Y.functionField} (hE : 0 ≤ E) :
    (effDivOf D E).picClass = divPicOf D E := by
  rw [effDivOf, picClass_effDivList, ← divPicOf_listDiv, listDiv_posList hE]

/-! ### Sections of invertible sheaves and their zero schemes -/

/-- A section of an invertible sheaf whose zero scheme has a divisor is a nonzerodivisor on every
open. -/
lemma injective_smul_of_hasDiv (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    {E : Divisor κ Y.functionField} (hs : (Modules.zeroIdeal L s).HasDiv E) (U : Y.Opens) :
    Function.Injective fun r : Γ(Y, U) ↦ r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
  intro r r' h
  apply TopCat.Presheaf.section_ext Y.sheaf U r r'
  intro x hx
  obtain ⟨W₀, e₀, hxW₀, he₀⟩ := exists_isBasisOn_affineOpens L x
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpens_mem_le (O := U ⊓ W₀.1) ⟨hx, hxW₀⟩
  have hWU : W.1 ≤ U := hWle.trans inf_le_left
  have he := isBasisOn_rs he₀ (hWle.trans inf_le_right)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_isBasisOn he (L.presheaf.map (homOfLE le_top).op s)
  haveI : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
  obtain ⟨P, hP⟩ := exists_pointOfPlace_mem κ W.1
  have ha0 : a ≠ 0 := (hs W a (Modules.zeroIdeal_ideal_of_isBasisOn L s he ha.symm) P hP).1
  have key : rr hWU r * a = rr hWU r' * a := by
    apply smul_left_injective_of_isBasisOn he
    rw [mul_smul, mul_smul, ha]
    have h' := congrArg (rs L hWU) h
    simp only [rs_smul, rs_rs] at h'
    exact h'
  have h2 := congrArg (Y.presheaf.germ W.1 x hxW) (mul_right_cancel₀ ha0 key)
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h2

/-- If `E`, `E'` are the divisors of the zero schemes of two sections of the same invertible
sheaf, then `E` and `E'` have the same image in `Pic(Y)`. -/
theorem divPicOf_sub_eq_zero (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    (L : Y.Modules) [L.IsInvertible] (s s' : Γ(L, ⊤)) {E E' : Divisor κ Y.functionField}
    (hE : 0 ≤ E) (hE' : 0 ≤ E') (hs : (Modules.zeroIdeal L s).HasDiv E)
    (hs' : (Modules.zeroIdeal L s').HasDiv E') : divPicOf D (E - E') = 0 := by
  have key : ∀ (t : Γ(L, ⊤)) {F : Divisor κ Y.functionField} (hF : 0 ≤ F),
      (Modules.zeroIdeal L t).HasDiv F → divPicOf D F = Pic.mk L := by
    intro t F hF ht
    rw [← picClass_effDivOf D hF]
    refine RelEffCartier.picClass_eq_of_ideal_eq_zeroIdeal _ L t
      (fun U ↦ injective_smul_of_hasDiv L t ht U.1) ?_
    exact IdealSheafData.HasDiv.eq (hasDiv_effDivOf D hD hF) ht
      (effDivOf D F).locally_principal (isLocPrincipal_zeroIdeal_of_hasDiv L t ht)
  rw [map_sub, key s hE hs, key s' hE' hs', sub_self]

/-- **Injectivity**: a divisor with trivial class is principal. -/
theorem mem_principal_of_divPicOf_eq_zero (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    {E : Divisor κ Y.functionField} (h : divPicOf D E = 0) : E ∈ principal κ Y.functionField := by
  set G₁ : Divisor κ Y.functionField := Finsupp.mapRange (fun n ↦ max n 0) (by simp) E
  set G₂ : Divisor κ Y.functionField := Finsupp.mapRange (fun n ↦ max (-n) 0) (by simp) E
  have hG₁ : 0 ≤ G₁ := fun P ↦ by simp [G₁]
  have hG₂ : 0 ≤ G₂ := fun P ↦ by simp [G₂]
  have hG : E = G₁ - G₂ := by
    ext P
    simp only [G₁, G₂, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    omega
  have h1 : (effDivOf D G₁).picClass = (effDivOf D G₂).picClass := by
    rw [picClass_effDivOf D hG₁, picClass_effDivOf D hG₂, ← sub_eq_zero, ← map_sub, ← hG, h]
  obtain ⟨e⟩ := Pic.mk_eq_mk_iff.mp h1
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_sub (effDivOf D G₂).lineBundle
    (e.hom.app ⊤ (effDivOf D G₁).canonicalSection) (effDivOf D G₂).canonicalSection
    (E := G₁) (E' := G₂)
    (by rw [Modules.zeroIdeal_iso, RelEffCartier.zeroIdeal_canonicalSection]
        exact hasDiv_effDivOf D hD hG₁)
    (by rw [RelEffCartier.zeroIdeal_canonicalSection]
        exact hasDiv_effDivOf D hD hG₂)
  refine mem_principal.mpr ⟨g, hg0, ?_⟩
  ext P
  rw [Divisor.div_apply, hg, hG]
  rfl

/-! ### Principal divisors -/

variable (κ) in
/-- The open complement of the points of a finite set `F` of places. -/
def regOpen (F : Finset (Place κ Y.functionField)) : Y.Opens :=
  ⟨(⋃ P ∈ (F : Set (Place κ Y.functionField)), {pointOfPlace κ Y P})ᶜ,
    (F.finite_toSet.isClosed_biUnion fun P _ ↦
      (isClosed_singleton_iff κ Y _).2 ((curvePlaceEquiv κ Y).symm P).2).isOpen_compl⟩

lemma mem_regOpen_iff (F : Finset (Place κ Y.functionField)) (P : Place κ Y.functionField) :
    pointOfPlace κ Y P ∈ regOpen κ F ↔ P ∉ F := by
  change pointOfPlace κ Y P ∈ (⋃ Q ∈ (F : Set (Place κ Y.functionField)),
    {pointOfPlace κ Y Q})ᶜ ↔ _
  simp [(pointOfPlace_injective κ Y).eq_iff]

lemma genericPoint_mem_regOpen (F : Finset (Place κ Y.functionField)) :
    genericPoint Y ∈ regOpen κ F := by
  change genericPoint Y ∈ (⋃ Q ∈ (F : Set (Place κ Y.functionField)),
    {pointOfPlace κ Y Q})ᶜ
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
  exact fun Q _ h ↦ ((curvePlaceEquiv κ Y).symm Q).2 h.symm

instance (F : Finset (Place κ Y.functionField)) : Nonempty (regOpen κ F) :=
  ⟨⟨_, genericPoint_mem_regOpen F⟩⟩

lemma exists_eq_pointOfPlace_of_notMem_regOpen {F : Finset (Place κ Y.functionField)} {y : Y}
    (hy : y ∉ regOpen κ F) : ∃ P ∈ F, pointOfPlace κ Y P = y := by
  change y ∉ (⋃ Q ∈ (F : Set (Place κ Y.functionField)), {pointOfPlace κ Y Q})ᶜ at hy
  simp only [Set.mem_compl_iff, not_not, Set.mem_iUnion, Set.mem_singleton_iff] at hy
  obtain ⟨P, hP, rfl⟩ := hy
  exact ⟨P, hP, rfl⟩

lemma exists_section_regOpen (F : Finset (Place κ Y.functionField)) (g : Y.functionField)
    (h : ∀ P ∉ F, 0 ≤ P.ord g) :
    ∃ τ : Γ(Y, regOpen κ F), Y.germToFunctionField _ τ = g :=
  (mem_regularOutside_iff κ Y (regOpen κ F) (s := F)
    (fun P ↦ by rw [mem_regOpen_iff, not_not]) g).1 fun P hP ↦ P.mem_of_ord_nonneg (h P hP)

/-- Restricting a coordinate `s|_O = c • e` to a small affine neighbourhood of a place. -/
lemma exists_chart_of_res (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤)) {O : Y.Opens}
    [Nonempty O] {e : Γ(L, O)} (he : L.IsBasisOn O e) {c : Γ(Y, O)}
    (hs : L.presheaf.map (homOfLE le_top).op s = c • e) (P : Place κ Y.functionField)
    (hP : pointOfPlace κ Y P ∈ O) (hc : Y.germToFunctionField O c ≠ 0) :
    ∃ (W : Y.affineOpens) (e' : Γ(L, W.1)) (a : Γ(Y, W.1)) (hP : pointOfPlace κ Y P ∈ W.1),
      L.IsBasisOn W.1 e' ∧ L.presheaf.map (homOfLE le_top).op s = a • e' ∧ a ≠ 0 ∧
        ordAt P hP a = P.ord (Y.germToFunctionField O c) := by
  obtain ⟨W, hPW, hWO⟩ := exists_affineOpens_mem_le hP
  haveI : Nonempty W.1 := ⟨⟨_, hPW⟩⟩
  have hres : Y.germToFunctionField W.1 (rr hWO c) = Y.germToFunctionField O c :=
    germToFunctionField_res (homOfLE hWO) c
  refine ⟨W, rs L hWO e, rr hWO c, hPW, isBasisOn_rs he hWO, ?_, ?_, ?_⟩
  · have h' := congrArg (rs L hWO) hs
    rw [rs_rs, rs_smul] at h'
    exact h'
  · intro h0
    apply hc
    rw [← hres, h0, map_zero]
  · rw [ordAt_eq_ord_germToFunctionField, hres]

/-- The divisor of the zero scheme of a section `(a, b)` of a twist `𝒪(t)` glued from two
charts: `div a` on `U` and `div b` on `V`. -/
theorem hasDiv_twistSection {U V : Y.Opens} [Nonempty U] [Nonempty V] (hUV : U ⊔ V = ⊤)
    {t : Γ(Y, U ⊓ V)} (ht : IsUnit t) {a : Γ(Y, U)} {b : Γ(Y, V)}
    (h : Y.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a =
      t * Y.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b)
    [(Modules.twoSetTwist (SheafOfModules.unit Y.ringCatSheaf) U V t).IsInvertible]
    {E : Divisor κ Y.functionField} (ha : Y.germToFunctionField U a ≠ 0)
    (hb : Y.germToFunctionField V b ≠ 0)
    (hU : ∀ P, pointOfPlace κ Y P ∈ U → P.ord (Y.germToFunctionField U a) = E P)
    (hV : ∀ P, pointOfPlace κ Y P ∈ V → pointOfPlace κ Y P ∉ U →
      P.ord (Y.germToFunctionField V b) = E P) :
    (Modules.zeroIdeal (Modules.twoSetTwist (SheafOfModules.unit Y.ringCatSheaf) U V t)
      (Modules.twistSection a b h)).HasDiv E := by
  refine hasDiv_zeroIdeal _ _ E fun P ↦ ?_
  by_cases hPU : pointOfPlace κ Y P ∈ U
  · obtain ⟨W, e, c, hP, he, hs, hc, hord⟩ := exists_chart_of_res _ _
      (Modules.isBasisOn_twistBasisLeft ht) (Modules.twistSection_res_left ht) P hPU ha
    exact ⟨W, e, c, hP, he, hs, hc, hord.trans (hU P hPU)⟩
  · have hPV : pointOfPlace κ Y P ∈ V := by
      have : pointOfPlace κ Y P ∈ U ⊔ V := hUV ▸ trivial
      exact this.resolve_left hPU
    obtain ⟨W, e, c, hP, he, hs, hc, hord⟩ := exists_chart_of_res
      (Modules.twoSetTwist (SheafOfModules.unit Y.ringCatSheaf) U V t) _
      Modules.isBasisOn_twistBasisRight Modules.twistSection_res_right P hPV hb
    exact ⟨W, e, c, hP, he, hs, hc, hord.trans (hV P hPV hPU)⟩

/-- **Zeros and poles as zero schemes**: for `g ≠ 0` there is an invertible sheaf (glued from
the opens where `g`, resp. `g⁻¹`, is regular, with transition function `g`) with two sections
whose zero schemes have divisors the zero divisor and the polar divisor of `g`. -/
theorem exists_sections_zeroDivisor_polarDivisor {g : Y.functionField} (hg : g ≠ 0) :
    ∃ (L : Y.Modules) (_ : L.IsInvertible) (s s' : Γ(L, ⊤)),
      (Modules.zeroIdeal L s).HasDiv (Divisor.zeroDivisor κ g) ∧
      (Modules.zeroIdeal L s').HasDiv (Divisor.polarDivisor κ g) := by
  classical
  set F₀ := (Divisor.polarDivisor κ g).support
  set F₁ := (Divisor.zeroDivisor κ g).support
  have hF₀ : ∀ P, P ∈ F₀ ↔ P.ord g < 0 := fun P ↦ by
    rw [Finsupp.mem_support_iff, Divisor.polarDivisor_apply]
    omega
  have hF₁ : ∀ P, P ∈ F₁ ↔ 0 < P.ord g := fun P ↦ by
    rw [Finsupp.mem_support_iff, Divisor.zeroDivisor_apply]
    omega
  obtain ⟨τ, hτ⟩ := exists_section_regOpen (κ := κ) F₀ g fun P hP ↦ by
    rw [hF₀] at hP
    omega
  obtain ⟨σ, hσ⟩ := exists_section_regOpen (κ := κ) F₁ g⁻¹ fun P hP ↦ by
    rw [hF₁] at hP
    rw [P.ord_inv]
    omega
  have hUV : regOpen κ F₀ ⊔ regOpen κ F₁ = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ regOpen κ F₀
    · exact Or.inl hy
    · obtain ⟨P, hP, rfl⟩ := exists_eq_pointOfPlace_of_notMem_regOpen hy
      refine Or.inr ((mem_regOpen_iff F₁ P).2 fun h ↦ ?_)
      rw [hF₀] at hP
      rw [hF₁] at h
      omega
  haveI : Nonempty (regOpen κ F₀ ⊓ regOpen κ F₁ : Y.Opens) :=
    ⟨⟨genericPoint Y, genericPoint_mem_regOpen F₀, genericPoint_mem_regOpen F₁⟩⟩
  set t : Γ(Y, regOpen κ F₀ ⊓ regOpen κ F₁) :=
    Y.presheaf.map (homOfLE inf_le_left : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op τ with ht_def
  have htt' : t * Y.presheaf.map (homOfLE inf_le_right : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op σ =
      1 := by
    apply Y.germToFunctionField_injective (regOpen κ F₀ ⊓ regOpen κ F₁)
    rw [ht_def, map_mul, map_one, germToFunctionField_res, germToFunctionField_res, hτ, hσ,
      mul_inv_cancel₀ hg]
  have ht : IsUnit t := IsUnit.of_mul_eq_one _ htt'
  haveI := Modules.isInvertible_twist hUV ht
  have h₀ : Y.presheaf.map (homOfLE inf_le_left : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op τ =
      t * Y.presheaf.map (homOfLE inf_le_right : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op 1 := by
    rw [map_one, mul_one]
  have h₁ : Y.presheaf.map (homOfLE inf_le_left : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op 1 =
      t * Y.presheaf.map (homOfLE inf_le_right : regOpen κ F₀ ⊓ regOpen κ F₁ ⟶ _).op σ := by
    rw [map_one]
    exact htt'.symm
  refine ⟨_, inferInstance, Modules.twistSection τ 1 h₀, Modules.twistSection 1 σ h₁, ?_, ?_⟩
  · refine hasDiv_twistSection hUV ht h₀ ?_ ?_ ?_ ?_
    · rw [hτ]
      exact hg
    · rw [map_one]
      exact one_ne_zero
    · intro P hP
      rw [mem_regOpen_iff, hF₀] at hP
      rw [hτ, Divisor.zeroDivisor_apply]
      omega
    · intro P _ hP
      rw [mem_regOpen_iff, not_not, hF₀] at hP
      rw [map_one, P.ord_one, Divisor.zeroDivisor_apply]
      omega
  · refine hasDiv_twistSection hUV ht h₁ ?_ ?_ ?_ ?_
    · rw [map_one]
      exact one_ne_zero
    · rw [hσ]
      exact inv_ne_zero hg
    · intro P hP
      rw [mem_regOpen_iff, hF₀] at hP
      rw [map_one, P.ord_one, Divisor.polarDivisor_apply]
      omega
    · intro P hP _
      rw [mem_regOpen_iff, hF₁] at hP
      rw [hσ, P.ord_inv, Divisor.polarDivisor_apply]
      omega

/-- **Principal divisors have trivial class.** -/
theorem divPicOf_div (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1)) (g : Y.functionField) :
    divPicOf D (Divisor.div κ g) = 0 := by
  by_cases hg : g = 0
  · rw [hg, Divisor.div_zero, map_zero]
  obtain ⟨L, _, s, s', hs, hs'⟩ := exists_sections_zeroDivisor_polarDivisor (κ := κ) hg
  rw [Divisor.div_eq_zeroDivisor_sub_polarDivisor]
  exact divPicOf_sub_eq_zero D hD L s s' (Divisor.zeroDivisor_nonneg g)
    (Divisor.polarDivisor_nonneg g) hs hs'

/-- The kernel of `Div(K(Y)) → Pic(Y)` is the group of principal divisors. -/
theorem divPicOf_eq_zero_iff (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    (E : Divisor κ Y.functionField) : divPicOf D E = 0 ↔ E ∈ principal κ Y.functionField := by
  refine ⟨mem_principal_of_divPicOf_eq_zero D hD, fun h ↦ ?_⟩
  obtain ⟨g, -, rfl⟩ := mem_principal.mp h
  exact divPicOf_div D hD g

/-- The induced map `Pic(K(Y)) = Div / Prin → Pic(Y)`. -/
def picDivPicOf (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1)) :
    Pic κ Y.functionField →+ Y.Pic :=
  QuotientAddGroup.lift _ (divPicOf D) fun E hE ↦
    AddMonoidHom.mem_ker.mpr ((divPicOf_eq_zero_iff D hD E).2 hE)

@[simp]
lemma picDivPicOf_mk (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1))
    (E : Divisor κ Y.functionField) :
    picDivPicOf D hD (QuotientAddGroup.mk E) = divPicOf D E :=
  rfl

/-- `Pic(K(Y)) → Pic(Y)` is injective. -/
theorem picDivPicOf_injective (hD : ∀ P, (D P).ideal.HasDiv (Finsupp.single P 1)) :
    Function.Injective (picDivPicOf D hD) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H E =>
    rw [QuotientAddGroup.eq_zero_iff]
    exact (divPicOf_eq_zero_iff D hD E).1 hx

end Generic

/-! ### Curves base changed to an algebraically closed field -/

section BaseChange

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
  [IsCurveOver k C] (κ : Type u) [Field κ] [IsAlgClosed κ] [Algebra k κ]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "Cκ" => pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) κ)

omit [PerfectField k] [IsAlgClosed κ] in
/-- The base change `C_κ` of a curve is integral. -/
instance isIntegral_baseChange : IsIntegral Cκ := IsCurveOver.isIntegral κ _

/-- The relative effective Cartier divisor `x_P ⊂ C_κ` of the `κ`-rational point at the place
`P` (the image of `placeSection κ C_κ P`). -/
def pointDiv (P : Place κ (Cκ).functionField) :
    RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) κ)) :=
  RelEffCartier.ofSection C (specAlgebraMap (k₀ := k) κ) (placeSection κ (Cκ) P)
    (placeSection_comp P)

lemma pointDiv_ideal (P : Place κ (Cκ).functionField) :
    (pointDiv C κ P).ideal = (placeSection κ (Cκ) P).ker :=
  rfl

lemma hasDiv_pointDiv (P : Place κ (Cκ).functionField) :
    (pointDiv C κ P).ideal.HasDiv (Finsupp.single P 1) :=
  hasDiv_ker_placeSection P

/-- **The map `Div(K(C_κ)) → Pic(C_κ)`**, `P ↦ [𝒪(x_P)]`. -/
def divPic : Divisor κ (Cκ).functionField →+ (Cκ).Pic :=
  divPicOf (pointDiv C κ)

@[simp]
lemma divPic_single (P : Place κ (Cκ).functionField) (n : ℤ) :
    divPic C κ (Finsupp.single P n) = n • (pointDiv C κ P).picClass :=
  divPicOf_single _ P n

/-- The relative effective Cartier divisor `∑ E(P) x_P` of an effective divisor `E`. -/
def effDiv (E : Divisor κ (Cκ).functionField) :
    RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) κ)) :=
  effDivOf (pointDiv C κ) E

lemma hasDiv_effDiv {E : Divisor κ (Cκ).functionField} (hE : 0 ≤ E) :
    (effDiv C κ E).ideal.HasDiv E :=
  hasDiv_effDivOf _ (hasDiv_pointDiv C κ) hE

lemma picClass_effDiv {E : Divisor κ (Cκ).functionField} (hE : 0 ≤ E) :
    (effDiv C κ E).picClass = divPic C κ E :=
  picClass_effDivOf _ hE

/-- **Principal divisors have trivial class**: `[𝒪(div g)] = 0`. -/
theorem divPic_div (g : (Cκ).functionField) : divPic C κ (Divisor.div κ g) = 0 :=
  divPicOf_div _ (hasDiv_pointDiv C κ) g

/-- The kernel of `Div(K(C_κ)) → Pic(C_κ)` is the group of principal divisors. -/
theorem divPic_eq_zero_iff (E : Divisor κ (Cκ).functionField) :
    divPic C κ E = 0 ↔ E ∈ principal κ (Cκ).functionField :=
  divPicOf_eq_zero_iff _ (hasDiv_pointDiv C κ) E

/-- **The map `Pic(K(C_κ)) → Pic(C_κ)`** on divisor classes. -/
def picDivPic : Pic κ (Cκ).functionField →+ (Cκ).Pic :=
  picDivPicOf (pointDiv C κ) (hasDiv_pointDiv C κ)

@[simp]
lemma picDivPic_mk (E : Divisor κ (Cκ).functionField) :
    picDivPic C κ (QuotientAddGroup.mk E) = divPic C κ E :=
  rfl

/-- **`Pic(K(C_κ)) → Pic(C_κ)` is injective.** -/
theorem picDivPic_injective : Function.Injective (picDivPic (k := k) C κ) :=
  picDivPicOf_injective (pointDiv C κ) (hasDiv_pointDiv C κ)

/-- The degree of `[𝒪(E)]` is `deg E`. -/
theorem degPic_divPic (E : Divisor κ (Cκ).functionField) :
    letI : (Spec (CommRingCat.of κ)).Over Sk := ⟨specAlgebraMap (k₀ := k) κ⟩
    degPic (curveToP1 k C) (T := Spec (CommRingCat.of κ)) (divPic C κ E) = E.deg := by
  letI : (Spec (CommRingCat.of κ)).Over Sk := ⟨specAlgebraMap (k₀ := k) κ⟩
  have hF := isField_ΓSpec' κ
  obtain ⟨t⟩ := nonempty_of_isField hF
  have key : ∀ P, degPic (curveToP1 k C) (T := Spec (CommRingCat.of κ))
      (pointDiv C κ P).picClass = 1 := fun P ↦
    (degPic_picClass (curveToP1 k C) hF (pointDiv C κ P) t).trans (by
      have hdeg := RelEffCartier.degree_ofSection C (specAlgebraMap (k₀ := k) κ)
        (placeSection κ (Cκ) P) (placeSection_comp P)
      exact congrArg (Nat.cast : ℕ → ℤ) (congrFun hdeg t))
  induction E using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, Divisor.deg_zero]
    exact degPic_zero (curveToP1 k C) hF
  | add a b ha hb =>
    rw [map_add, Divisor.deg_add, ← ha, ← hb]
    exact degPic_add (curveToP1 k C) hF _ _
  | single P n =>
    rw [divPic_single, Divisor.deg_single, Place.deg_eq_one]
    calc degPic (curveToP1 k C) (T := Spec (CommRingCat.of κ)) (n • (pointDiv C κ P).picClass)
        = n • degPicHom (curveToP1 k C) hF (pointDiv C κ P).picClass :=
          map_zsmul (degPicHom (curveToP1 k C) hF) n _
      _ = n * ((1 : ℕ) : ℤ) := by
          rw [smul_eq_mul, Nat.cast_one, mul_one]
          exact congrArg (n * ·) (key P) |>.trans (mul_one n)

variable (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed κ] in
/-- Over a field, every class lies in the rigidified Picard group `Pic_{C/k,σ}(κ)` (since
`Pic(Spec κ) = 0`). -/
lemma mem_picPt (x : (Cκ).Pic) : x ∈ picPt C σ hσ κ :=
  haveI := subsingleton_pic_of_isField (isField_ΓSpec' κ)
  (mem_picSigmaGrp _ σ hσ x).2 (Subsingleton.elim _ _)

/-- **The map `Pic(K(C_κ)) → Pic_{C/k,σ}(κ)`**. -/
def picDivPt : WeilCurves.FunctionField.Pic κ (Cκ).functionField →+ picPt C σ hσ κ :=
  AddMonoidHom.codRestrict (picDivPic C κ) (picPt C σ hσ κ) fun _ ↦ mem_picPt C κ σ hσ _


@[simp]
lemma coe_picDivPt (x : Pic κ (Cκ).functionField) :
    (picDivPt C κ σ hσ x : (Cκ).Pic) = picDivPic C κ x :=
  rfl

/-- `Pic(K(C_κ)) → Pic_{C/k,σ}(κ)` is injective. -/
theorem picDivPt_injective : Function.Injective (picDivPt C κ σ hσ) := fun _ _ h ↦
  picDivPic_injective C κ (congrArg Subtype.val h)

omit [IsAlgClosed κ] in
/-- A class lies in `J(κ)` iff its degree is `0`. -/
lemma mem_jacPoints_iff_degPic (x : picPt C σ hσ κ) :
    letI : (Spec (CommRingCat.of κ)).Over Sk := ⟨specAlgebraMap (k₀ := k) κ⟩
    x ∈ jacPoints C σ hσ κ ↔
      degPic (curveToP1 k C) (T := Spec (CommRingCat.of κ)) (x : (Cκ).Pic) = 0 := by
  letI : (Spec (CommRingCat.of κ)).Over Sk := ⟨specAlgebraMap (k₀ := k) κ⟩
  exact picDeg_zero_iff_degPic (curveToP1 k C) σ hσ (isField_ΓSpec' κ) x

/-- **Degree-zero divisor classes land in `J(κ)`.** -/
theorem picDivPt_mem_jacPoints {x : Pic κ (Cκ).functionField} (hx : Pic.deg κ _ x = 0) :
    picDivPt C κ σ hσ x ∈ jacPoints C σ hσ κ := by
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [mem_jacPoints_iff_degPic, coe_picDivPt, picDivPic_mk, degPic_divPic]
  exact hx

/-- **The bridge `Pic⁰(K(C_κ)) → J(κ)`** from degree-zero divisor classes of the function field
to the `κ`-points of the Jacobian, `[∑ nᵢ Pᵢ] ↦ ∑ nᵢ [𝒪(x_{Pᵢ})]`. -/
def jacBridge : (Pic.deg κ (Cκ).functionField).ker →+ jacPoints C σ hσ κ :=
  ((picDivPt C κ σ hσ).comp (Pic.deg κ (Cκ).functionField).ker.subtype).codRestrict _
    fun x ↦ picDivPt_mem_jacPoints C κ σ hσ x.2

@[simp]
lemma coe_jacBridge (x : (Pic.deg κ (Cκ).functionField).ker) :
    ((jacBridge C κ σ hσ x : picPt C σ hσ κ) : (Cκ).Pic) = picDivPic C κ x :=
  rfl

/-- **The bridge `Pic⁰(K(C_κ)) → J(κ)` is injective.** -/
theorem jacBridge_injective : Function.Injective (jacBridge C κ σ hσ) := fun _ _ h ↦
  Subtype.ext (picDivPic_injective C κ (congrArg (fun z ↦ (z.1 : (Cκ).Pic)) h))

end BaseChange

end CurvesJacobian
