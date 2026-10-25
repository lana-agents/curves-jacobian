/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Characters
import CurvesJacobian.Cusp.CompletionSubgroup
import Pi1.Surface.SchreierTransversal
import Pi1.Surface.Profinite

/-!
# The continuous `ℤ/m`-characters of open subgroups of `Π̂_{g,r}` (`r > 0`)

Let `D` be a topological group with `Φ : D ≃ₜ* Π̂_{g,r}`, where `r > 0` and `2 ≤ 2g + r`, and let
`H ⊆ D` be an open subgroup. Then `Π_{g,r}` is free of rank `2g + r - 1`
(`Pi1.SurfaceGroup.freeEquiv`), `H₀ = η⁻¹(Φ H) ⊆ Π_{g,r}` has index `[D : H]`, it is free of
rank `[D : H](2g + r - 2) + 1` (Reidemeister–Schreier with Schreier's index formula), and the
continuous characters `H → ℤ/m` are the characters of `H₀` (`Ĥ₀ ≃ₜ* Φ(H)`,
`CurvesJacobian.Cusp.completionComapEquiv`).

## Main results

* `CurvesJacobian.CuspChar.exists_mulEquiv_freeGroup_card`: **Schreier's index formula**, a
  subgroup of index `k` of a free group of rank `n` is free of rank `k (n - 1) + 1`;
* `CurvesJacobian.CuspChar.index_comap_of_denseRange`: `[G : ψ⁻¹(H)] = [D : H]` for an open
  subgroup `H` and a homomorphism `ψ : G → D` with dense range;
* `CurvesJacobian.CuspChar.restrictCharEquiv`: for `Φ : D ≃ₜ* Ĝ`, the continuous characters
  `H → ℤ/m` are the characters `H₀ → ℤ/m` of `H₀ = (Φ⁻¹ ∘ η)⁻¹(H)`, as a `ℤ/m`-linear
  isomorphism;
* `CurvesJacobian.CuspChar.free_charSpace`, `CurvesJacobian.CuspChar.finrank_charSpace`,
  `CurvesJacobian.CuspChar.natCard_charSpace`: `charSpace m H` is a free `ℤ/m`-module of rank
  `[D : H](2g + r - 2) + 1`, with `m ^ ([D : H](2g + r - 2) + 1)` elements;
* `CurvesJacobian.CuspChar.free_charSpace_top`, `CurvesJacobian.CuspChar.finrank_charSpace_top`,
  `CurvesJacobian.CuspChar.natCard_charSpace_top`: the case `H = D` (rank `2g + r - 1`).
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite Module

universe u v

namespace CurvesJacobian.CuspChar

/-! ### Schreier's index formula -/

section Schreier

open Pi1.ReidemeisterSchreier

/-- **Schreier's index formula**: a subgroup `K` of finite index of a free group `F(α)` is free on
a set `ι` with `|ι| + [F(α) : K] = [F(α) : K] · |α| + 1`. -/
theorem exists_mulEquiv_freeGroup_card {α : Type v} [Finite α] (K : Subgroup (FreeGroup α))
    [K.FiniteIndex] :
    ∃ (ι : Type v) (_ : Finite ι), Nonempty (K ≃* FreeGroup ι) ∧
      Nat.card ι + K.index = K.index * Nat.card α + 1 := by
  have htrans : ∀ ω : FreeGroup α ⧸ K,
      ∃ x : FreeGroup α, x • ((1 : FreeGroup α) : FreeGroup α ⧸ K) = ω := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x => exact ⟨x, by rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]⟩
  set T := (Parent.bfs htrans).toTransversal
  exact ⟨T.Gens, inferInstance,
    ⟨(MulEquiv.subgroupCongr (MulAction.stabilizer_quotient K)).symm.trans T.basis.repr⟩,
    (Parent.bfs htrans).card_gens⟩

/-- Schreier's index formula for a subgroup of a group `G ≃* F(α)`. -/
theorem exists_mulEquiv_freeGroup_card_of_mulEquiv {G : Type u} [Group G] {α : Type v}
    [Finite α] (e : G ≃* FreeGroup α) (K : Subgroup G) [K.FiniteIndex] :
    ∃ (ι : Type v) (_ : Finite ι), Nonempty (K ≃* FreeGroup ι) ∧
      Nat.card ι + K.index = K.index * Nat.card α + 1 := by
  set K' := K.map (e : G →* FreeGroup α)
  have hidx : K'.index = K.index := Subgroup.index_map_equiv K e
  haveI : K'.FiniteIndex := ⟨by rw [hidx]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  obtain ⟨ι, hι, ⟨f⟩, hc⟩ := exists_mulEquiv_freeGroup_card K'
  exact ⟨ι, hι, ⟨(K.equivMapOfInjective (e : G →* FreeGroup α) e.injective).trans f⟩,
    hidx ▸ hc⟩

end Schreier

/-! ### Characters of a free group -/

section Free

variable {K : Type*} [Group K] {ι : Type*} (m : ℕ)

/-- The characters `K → ℤ/m` of a group `K ≃* F(ι)` are the functions `ι → ℤ/m`. -/
def freeCharEquiv (e : K ≃* FreeGroup ι) :
    (Additive K →+ ZMod m) ≃ₗ[ZMod m] (ι → ZMod m) where
  toFun χ i := χ (Additive.ofMul (e.symm (FreeGroup.of i)))
  invFun f := AddMonoidHom.toMultiplicativeRight.symm
    ((FreeGroup.lift fun i ↦ Multiplicative.ofAdd (f i)).comp (e : K →* FreeGroup ι))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv χ := by
    apply AddMonoidHom.toMultiplicativeRight.injective
    rw [Equiv.apply_symm_apply]
    refine MonoidHom.ext fun k ↦ ?_
    obtain ⟨x, rfl⟩ := e.symm.surjective k
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.apply_symm_apply]
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => simp [AddMonoidHom.toMultiplicativeRight]
    | inv_of i h => simp only [map_inv, h]
    | mul x y hx hy => simp only [map_mul, hx, hy]
  right_inv f := by
    funext i
    simp [AddMonoidHom.toMultiplicativeRight]

end Free

/-! ### The index of the preimage of an open subgroup under a dense map -/

section Index

variable {G : Type*} [Group G] {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]

/-- **`[G : ψ⁻¹(H)] = [D : H]`** for an open subgroup `H ⊆ D` and `ψ : G →* D` with dense
range. -/
theorem index_comap_of_denseRange (ψ : G →* D) (hψ : DenseRange ψ) (H : OpenSubgroup D) :
    ((H : Subgroup D).comap ψ).index = (H : Subgroup D).index := by
  let f : G ⧸ (H : Subgroup D).comap ψ → D ⧸ (H : Subgroup D) :=
    Quotient.map' ψ fun a b hab ↦ by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [← map_inv, ← map_mul]
      exact hab
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      have h : (ψ a : D ⧸ (H : Subgroup D)) = ψ b := hxy
      rw [QuotientGroup.eq] at h ⊢
      rw [Subgroup.mem_comap, map_mul, map_inv]
      exact h
    · induction y using QuotientGroup.induction_on with | H d => ?_
      have hU : IsOpen ((fun y ↦ d⁻¹ * y) ⁻¹' (H : Set D)) :=
        H.isOpen.preimage (continuous_const.mul continuous_id)
      obtain ⟨x, hx⟩ := hψ.exists_mem_open hU ⟨d, by simp⟩
      refine ⟨(x : G ⧸ (H : Subgroup D).comap ψ), ?_⟩
      change (ψ x : D ⧸ (H : Subgroup D)) = d
      rw [QuotientGroup.eq]
      have := (H : Subgroup D).inv_mem (show d⁻¹ * ψ x ∈ (H : Subgroup D) from hx)
      simpa using this
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Index

/-! ### Continuous characters of an open subgroup of a profinite completion -/

section Restrict

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {G : Type} [Group G]
  (Φ : D ≃ₜ* completion (GrpCat.of G)) (H : OpenSubgroup D)

/-- `Φ(H) ⊆ Ĝ`, written as `(Φ⁻¹)⁻¹(H)`. -/
def imageSub : Subgroup (completion (GrpCat.of G)) :=
  (H : Subgroup D).comap Φ.symm.toMulEquiv.toMonoidHom

omit [IsTopologicalGroup D] in
lemma isOpen_imageSub : IsOpen (imageSub Φ H : Set (completion (GrpCat.of G))) :=
  H.isOpen.preimage Φ.symm.continuous

/-- The subgroup `H₀ = η⁻¹(Φ(H))` of finite index of `G`. -/
noncomputable abbrev denseSub : Subgroup G := (imageSub Φ H).comap (CurvesJacobian.Cusp.etaHom G)

instance finiteIndex_denseSub : (denseSub Φ H).FiniteIndex :=
  CurvesJacobian.Cusp.finiteIndex_comap_etaHom _ (isOpen_imageSub Φ H)

/-- **`[G : H₀] = [D : H]`.** -/
theorem index_denseSub : (denseSub Φ H).index = (H : Subgroup D).index :=
  index_comap_of_denseRange (Φ.symm.toMulEquiv.toMonoidHom.comp (CurvesJacobian.Cusp.etaHom G))
    (Φ.symm.surjective.denseRange.comp (denseRange _) Φ.symm.continuous) H

/-- The inclusion `H₀ → H`, `h ↦ Φ⁻¹(η h)`, additively. -/
noncomputable def denseIncl : Additive (denseSub Φ H) →+ Additive (H : Subgroup D) where
  toFun h := Additive.ofMul ⟨Φ.symm (CurvesJacobian.Cusp.etaHom G (Additive.toMul h).1),
    (Additive.toMul h).2⟩
  map_zero' := by
    apply Additive.toMul.injective
    ext
    change Φ.symm (CurvesJacobian.Cusp.etaHom G 1) = 1
    rw [map_one, map_one]
  map_add' h k := by
    apply Additive.toMul.injective
    ext
    change Φ.symm (CurvesJacobian.Cusp.etaHom G ((Additive.toMul h).1 * (Additive.toMul k).1)) =
      Φ.symm (CurvesJacobian.Cusp.etaHom G (Additive.toMul h).1) *
        Φ.symm (CurvesJacobian.Cusp.etaHom G (Additive.toMul k).1)
    rw [map_mul, map_mul]

variable (m : ℕ)

/-- Restriction of continuous characters of `H` to `H₀`. -/
noncomputable def restrictChar : charSpace m H →ₗ[ZMod m] (Additive (denseSub Φ H) →+ ZMod m) where
  toFun ξ := ξ.1.comp (denseIncl Φ H)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restrictChar_injective : Function.Injective (restrictChar Φ H m) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  have hcl : IsClosed (kerSub (H : Subgroup D) ξ.1 : Set D) := Subgroup.isClosed_of_isOpen _ ξ.2
  have hdense : DenseRange fun x : G ↦ Φ.symm (CurvesJacobian.Cusp.etaHom G x) :=
    Φ.symm.surjective.denseRange.comp (denseRange _) Φ.symm.continuous
  refine Subtype.ext (AddMonoidHom.ext fun a ↦ ?_)
  by_contra hne
  have hU : IsOpen ((H : Set D) ∩ (kerSub (H : Subgroup D) ξ.1 : Set D)ᶜ) :=
    H.isOpen.inter hcl.isOpen_compl
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU
    ⟨(Additive.toMul a).1, (Additive.toMul a).2, fun ⟨_, h0⟩ ↦ hne h0⟩
  have hxH : x ∈ denseSub Φ H := hx.1
  exact hx.2 ⟨hx.1, DFunLike.congr_fun hξ (Additive.ofMul ⟨x, hxH⟩)⟩

variable [NeZero m]

lemma restrictChar_surjective : Function.Surjective (restrictChar Φ H m) := by
  intro χ
  set O := imageSub Φ H
  set E := CurvesJacobian.Cusp.completionComapEquiv O (isOpen_imageSub Φ H)
  set χm := AddMonoidHom.toMultiplicativeRight χ
  set L := liftFinite χm
  have hmem : ∀ h : (H : Subgroup D), Φ h.1 ∈ O := fun h ↦ by
    change Φ.symm (Φ h.1) ∈ (H : Subgroup D)
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact h.2
  let j : (H : Subgroup D) →* O :=
    { toFun := fun h ↦ ⟨Φ h.1, hmem h⟩
      map_one' := Subtype.ext (map_one Φ)
      map_mul' := fun a b ↦ Subtype.ext (map_mul Φ a.1 b.1) }
  have hj : Continuous j := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  let ψ : (H : Subgroup D) →* Multiplicative (ZMod m) :=
    L.comp (E.symm.toMulEquiv.toMonoidHom.comp j)
  let ξ : Additive (H : Subgroup D) →+ ZMod m := AddMonoidHom.toMultiplicativeRight.symm ψ
  have hopen : IsOpen (kerSub (H : Subgroup D) ξ : Set D) := by
    have hV : IsOpen ((fun a : (H : Subgroup D) ↦ E.symm (j a)) ⁻¹'
        {x | L x = 1}) :=
      (isOpen_liftFinite_fiber χm (1 : Multiplicative (ZMod m))).preimage
        (E.symm.continuous.comp hj)
    convert H.isOpen.isOpenMap_subtype_val _ hV using 1
    ext x
    constructor
    · rintro ⟨hx, e⟩
      exact ⟨⟨x, hx⟩, (ofAdd_eq_one (A := ZMod m)).2 e, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, (toAdd_eq_zero (α := ZMod m)).2 ha⟩
  refine ⟨⟨ξ, hopen⟩, AddMonoidHom.ext fun h ↦ ?_⟩
  have hjE : j (Additive.toMul (denseIncl Φ H h)) = E (etaFn _ (Additive.toMul h)) := by
    apply Subtype.ext
    change Φ (Φ.symm _) = _
    rw [ContinuousMulEquiv.apply_symm_apply, CurvesJacobian.Cusp.completionComapEquiv_eta]
    rfl
  change Multiplicative.toAdd (L (E.symm (j _))) = χ h
  rw [hjE, ContinuousMulEquiv.symm_apply_apply, liftFinite_eta]
  rfl

/-- **Continuous characters of an open subgroup of `Ĝ` are characters of `H₀`**: for
`Φ : D ≃ₜ* Ĝ` and `H ⊆ D` open, restriction along `H₀ → H`, `h ↦ Φ⁻¹(η h)`, is a linear
isomorphism `charSpace m H ≃ Hom(H₀, ℤ/m)`. -/
noncomputable def restrictCharEquiv :
    charSpace m H ≃ₗ[ZMod m] (Additive (denseSub Φ H) →+ ZMod m) :=
  LinearEquiv.ofBijective (restrictChar Φ H m)
    ⟨restrictChar_injective Φ H m, restrictChar_surjective Φ H m⟩

end Restrict

/-! ### Open subgroups of `Π̂_{g,r}` -/

section Surface

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {g r : ℕ}

/-- `SurfaceGen g r ≃ (Fin g ⊕ Fin g) ⊕ Fin r`. -/
private def genEquiv (g r : ℕ) : Pi1.SurfaceGen g r ≃ (Fin g ⊕ Fin g) ⊕ Fin r where
  toFun
    | .a i => .inl (.inl i)
    | .b i => .inl (.inr i)
    | .c j => .inr j
  invFun
    | .inl (.inl i) => .a i
    | .inl (.inr i) => .b i
    | .inr j => .c j
  left_inv s := by cases s <;> rfl
  right_inv x := by rcases x with (i | i) | j <;> rfl

instance finite_surfaceGen : Finite (Pi1.SurfaceGen g r) := Finite.of_equiv _ (genEquiv g r).symm

lemma natCard_surfaceGen : Nat.card (Pi1.SurfaceGen g r) = 2 * g + r := by
  rw [Nat.card_congr (genEquiv g r)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  ring

/-- **`charSpace m H ≃ₗ (ι → ℤ/m)` with Schreier's count**: for `Φ : D ≃ₜ* Π̂_{g,r}` (`r > 0`)
and `H ⊆ D` open, `charSpace m H ≃ₗ[ℤ/m] (ι → ℤ/m)` for a finite `ι` with
`|ι| + [D : H] = [D : H] (2g + r - 1) + 1`. -/
theorem exists_charSpace_linearEquiv (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r) (hr : 0 < r)
    (m : ℕ) [NeZero m] (H : OpenSubgroup D) :
    ∃ (ι : Type) (_ : Finite ι), Nonempty (charSpace m H ≃ₗ[ZMod m] (ι → ZMod m)) ∧
      Nat.card ι + (H : Subgroup D).index = (H : Subgroup D).index * (2 * g + r - 1) + 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨ι, hι, ⟨e⟩, hc⟩ := exists_mulEquiv_freeGroup_card_of_mulEquiv
    (Pi1.SurfaceGroup.freeEquiv (g := g) (r := r')) (denseSub Φ H)
  refine ⟨ι, hι, ⟨(restrictCharEquiv Φ H m).trans (freeCharEquiv m e)⟩, ?_⟩
  rw [index_denseSub, natCard_surfaceGen] at hc
  rw [show 2 * g + (r' + 1) - 1 = 2 * g + r' by omega]
  exact hc

omit [IsTopologicalGroup D] in
lemma card_eq_of_add_eq (hgr : 2 ≤ 2 * g + r) {c i : ℕ} (h : c + i = i * (2 * g + r - 1) + 1) :
    c = i * (2 * g + r - 2) + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * g + r - 1 = k + 1 := ⟨2 * g + r - 2, by omega⟩
  have hk' : 2 * g + r - 2 = k := by omega
  rw [hk, Nat.mul_succ] at h
  rw [hk']
  omega

variable (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r) (hr : 0 < r) (hgr : 2 ≤ 2 * g + r)
  (m : ℕ) [NeZero m] (H : OpenSubgroup D)

include Φ hr in
/-- **`charSpace m H` is a free `ℤ/m`-module.** -/
theorem free_charSpace : Module.Free (ZMod m) (charSpace m H) := by
  obtain ⟨ι, hι, ⟨e⟩, -⟩ := exists_charSpace_linearEquiv Φ hr m H
  exact Module.Free.of_equiv e.symm

include Φ hr hgr in
/-- **Rank of the continuous `ℤ/m`-characters of an open subgroup of `Π̂_{g,r}`**:
`[D : H] (2g + r - 2) + 1`. -/
theorem finrank_charSpace [Fact (1 < m)] :
    Module.finrank (ZMod m) (charSpace m H) = (H : Subgroup D).index * (2 * g + r - 2) + 1 := by
  obtain ⟨ι, hι, ⟨e⟩, hc⟩ := exists_charSpace_linearEquiv Φ hr m H
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
  exact card_eq_of_add_eq hgr hc

include Φ hr hgr in
/-- **Number of continuous `ℤ/m`-characters of an open subgroup of `Π̂_{g,r}`**. -/
theorem natCard_charSpace :
    Nat.card (charSpace m H) = m ^ ((H : Subgroup D).index * (2 * g + r - 2) + 1) := by
  obtain ⟨ι, hι, ⟨e⟩, hc⟩ := exists_charSpace_linearEquiv Φ hr m H
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, card_eq_of_add_eq hgr hc]

include Φ hr in
/-- **`charSpace m D` is a free `ℤ/m`-module.** -/
theorem free_charSpace_top : Module.Free (ZMod m) (charSpace m (⊤ : OpenSubgroup D)) :=
  free_charSpace Φ hr m ⊤

include Φ hr hgr in
/-- **`D ≃ₜ* Π̂_{g,r}` has `ℤ/m`-character rank `2g + r - 1`.** -/
theorem finrank_charSpace_top [Fact (1 < m)] :
    Module.finrank (ZMod m) (charSpace m (⊤ : OpenSubgroup D)) = 2 * g + r - 1 := by
  rw [finrank_charSpace Φ hr hgr m ⊤, OpenSubgroup.toSubgroup_top, Subgroup.index_top]
  omega

include Φ hr hgr in
/-- **`D ≃ₜ* Π̂_{g,r}` has `m ^ (2g + r - 1)` continuous `ℤ/m`-characters.** -/
theorem natCard_charSpace_top :
    Nat.card (charSpace m (⊤ : OpenSubgroup D)) = m ^ (2 * g + r - 1) := by
  rw [natCard_charSpace Φ hr hgr m ⊤, OpenSubgroup.toSubgroup_top, Subgroup.index_top]
  congr 1
  omega

end Surface

end CurvesJacobian.CuspChar
