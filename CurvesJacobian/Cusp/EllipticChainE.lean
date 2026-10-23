/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticArithChain
import CurvesJacobian.Cusp.EllipticGalois
import CurvesJacobian.Cusp.ConjInducedCusps

/-!
# The elliptic chain of `E ∖ {O}` for `N = 2` (MR8)

[AbsTopII] Example 3.2 (i) (`Topics in Absolute Anabelian Geometry II.txt` l.4326–4400) and
Corollary 3.3 (iii)(a) (l.4481–4491) for IUT's once-punctured elliptic curve
`X = D = V = E ∖ {O}` (`hypCurveX E`) and `N = 2`, with `E[2]` `K`-rational (`E.Ψ₂Sq.Splits`):
`U = E ∖ E[2]` (`hypCurveV E`), `β = [2] : U → D` (`coverXMorK E`), and the run of fillings
`E ∖ E[2] = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_n = E ∖ {O}` of the nonzero points of order two.

## Main results

* `CurvesJacobian.Cusp.isIso_residueFieldMap_of_mem_XE_diff`: if `E[2]` is `K`-rational, every
  point of `(E ∖ {O}) ∖ (E ∖ E[2])` is `K`-rational. A point `c` of `E ∖ {O}` outside `E ∖ E[2]`
  corresponds to a prime of `K[E]` containing `ψ = 2y + a₁x + a₃`; it contains some `x - eᵢ`
  (`ψ² = g(x) = 4 ∏ (x - eᵢ)`) and is the kernel of the evaluation at `(eᵢ, -(a₁eᵢ + a₃)/2)`, so
  `c` is the image of a section `Spec K ⟶ Ē`.
* `CurvesJacobian.Cusp.finite_XE_diff_VE`, `CurvesJacobian.Cusp.isClosed_of_mem_XE_diff`, and the
  run `CurvesJacobian.Cusp.exists_runE` (via `exists_fillSeq`).
* `CurvesJacobian.Cusp.ellipticDataE`: the `EllipticData` of `E ∖ {O}` with `CQ = CV = X`,
  `CW = E ∖ E[2]`, `β = [2]`, `FV = FQ = 𝟙` and `FD : Spec Γ(X) = Spec Γ(U_n)`.
* `CurvesJacobian.Cusp.exists_ellipticCandidate_oncePunctured`: the resulting candidate in
  `ellipticCusp (Π_X)` is, up to continuous isomorphisms, `Π_{E ∖ E[2]} ↠ Π_{E ∖ {O}}`
  (`fillPiHom`), with `Π_V ↪ Π_{E ∖ {O}}` and `Π_V ↪ Π_X` isomorphisms.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Polynomial Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The evaluation of `K[E]` at a point of order two -/

section TwoTorsion

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K)

local notation "A" => E.toAffine.CoordinateRing

lemma eval₂_polynomial_twoTorsion {e : K} (h0 : E.Ψ₂Sq.eval e = 0) :
    E.toAffine.polynomial.eval₂ (evalRingHom e) (-(E.a₁ * e + E.a₃) / 2) = 0 := by
  rw [WeierstrassCurve.Ψ₂Sq] at h0
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h0
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₆, WeierstrassCurve.b₄] at h0
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination (-1 / 4 : K) * h0

/-- The evaluation `K[E] → K` at the point `(e, -(a₁ e + a₃)/2)` of order two (`g(e) = 0`). -/
def evalTwoTorsion {e : K} (h0 : E.Ψ₂Sq.eval e = 0) : A →+* K :=
  AdjoinRoot.lift (evalRingHom e) (-(E.a₁ * e + E.a₃) / 2) (eval₂_polynomial_twoTorsion E h0)

omit [CharZero K] in
lemma algebraMap_coordinateRing_eq_of (c : K) :
    algebraMap K A c = AdjoinRoot.of E.toAffine.polynomial (C c) := by
  rw [AdjoinRoot.algebraMap_eq']
  rfl

lemma evalTwoTorsion_algebraMap {e : K} (h0 : E.Ψ₂Sq.eval e = 0) (c : K) :
    evalTwoTorsion E h0 (algebraMap K A c) = c := by
  rw [algebraMap_coordinateRing_eq_of, evalTwoTorsion, AdjoinRoot.lift_of, coe_evalRingHom,
    eval_C]

/-- **A prime of `K[E]` containing `ψ` and `x - e` is the kernel of the evaluation at
`(e, -(a₁ e + a₃)/2)`.** -/
lemma ker_evalTwoTorsion {e : K} (h0 : E.Ψ₂Sq.eval e = 0) (Q : Ideal A) [hQ : Q.IsPrime]
    (hψ : psiE E ∈ Q) (hx : algebraMap K[X] A (X - C e) ∈ Q) :
    RingHom.ker (evalTwoTorsion E h0) = Q := by
  have hunit : ∀ c : K, c ≠ 0 → algebraMap K A c ∉ Q := fun c hc h ↦ hQ.ne_top
    ((Ideal.eq_top_iff_one Q).2 (by
      have := Q.mul_mem_right (algebraMap K A c⁻¹) h
      rwa [← map_mul, mul_inv_cancel₀ hc, map_one] at this))
  have hx' : xE E - algebraMap K A e ∈ Q := by
    have h := hx
    rwa [AdjoinRoot.algebraMap_eq, map_sub, ← algebraMap_coordinateRing_eq_of] at h
  have hy : yE E - algebraMap K A (-(E.a₁ * e + E.a₃) / 2) ∈ Q := by
    have h2 : (2 : A) * algebraMap K A (-(E.a₁ * e + E.a₃) / 2) =
        -(algebraMap K A E.a₁ * algebraMap K A e + algebraMap K A E.a₃) := by
      rw [← map_ofNat (algebraMap K A) 2, ← map_mul, ← map_mul, ← map_add, ← map_neg]
      congr 1
      ring
    have hid : (2 : A) * (yE E - algebraMap K A (-(E.a₁ * e + E.a₃) / 2)) =
        psiE E - algebraMap K A E.a₁ * (xE E - algebraMap K A e) := by
      rw [psiE_eq']
      linear_combination (-1 : A) * h2
    have hmem : (2 : A) * (yE E - algebraMap K A (-(E.a₁ * e + E.a₃) / 2)) ∈ Q := by
      rw [hid]
      exact Q.sub_mem hψ (Q.mul_mem_left _ hx')
    have h2Q : (2 : A) ∉ Q := by
      rw [← map_ofNat (algebraMap K A) 2]
      exact hunit 2 two_ne_zero
    exact (hQ.mem_or_mem hmem).resolve_left h2Q
  have key : Ideal.Quotient.mk Q =
      ((Ideal.Quotient.mk Q).comp (algebraMap K A)).comp (evalTwoTorsion E h0) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp only [RingHom.comp_apply]
        rw [evalTwoTorsion, AdjoinRoot.lift_of, coe_evalRingHom, eval_C,
          algebraMap_coordinateRing_eq_of]
      · simp only [RingHom.comp_apply]
        rw [evalTwoTorsion, AdjoinRoot.lift_of, coe_evalRingHom, eval_X]
        exact Ideal.Quotient.eq.2 hx'
    · simp only [RingHom.comp_apply]
      rw [evalTwoTorsion, AdjoinRoot.lift_root]
      exact Ideal.Quotient.eq.2 hy
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, key, RingHom.comp_apply,
    RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    rw [h, map_zero]
    exact Q.zero_mem
  · intro h
    by_contra hne
    exact hunit _ hne h

/-- **A prime of `K[E]` containing `ψ` is the kernel of the evaluation at a point of order two**
if `g = 4 (x - e₁)(x - e₂)(x - e₃)` splits over `K`. -/
lemma exists_ker_evalTwoTorsion {e₁ e₂ e₃ : K}
    (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃))) (Q : Ideal A) [hQ : Q.IsPrime]
    (hψ : psiE E ∈ Q) :
    ∃ (e : K) (h0 : E.Ψ₂Sq.eval e = 0), RingHom.ker (evalTwoTorsion E h0) = Q := by
  have hg : algebraMap K[X] A (gE E) ∈ Q := by
    rw [← psi_sq]
    exact Q.pow_mem_of_mem hψ 2 two_pos
  rw [gE, he, map_mul, map_mul, map_mul] at hg
  have h4 : algebraMap K[X] A (C 4) ∉ Q := fun h ↦ hQ.ne_top
    ((Ideal.eq_top_iff_one Q).2 (by
      have := Q.mul_mem_right (algebraMap K A 4⁻¹) h
      rwa [AdjoinRoot.algebraMap_eq, ← algebraMap_coordinateRing_eq_of, ← map_mul,
        mul_inv_cancel₀ (by norm_num : (4 : K) ≠ 0), map_one] at this))
  rcases hQ.mem_or_mem hg with h | h
  · exact absurd h h4
  rcases hQ.mem_or_mem h with h | h3
  · rcases hQ.mem_or_mem h with h1 | h2
    · exact ⟨e₁, by rw [he]; simp, ker_evalTwoTorsion E _ Q hψ h1⟩
    · exact ⟨e₂, by rw [he]; simp, ker_evalTwoTorsion E _ Q hψ h2⟩
  · exact ⟨e₃, by rw [he]; simp, ker_evalTwoTorsion E _ Q hψ h3⟩

end TwoTorsion

/-! ### The points of `(E ∖ {O}) ∖ (E ∖ E[2])` -/

section Points

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing

/-- **A point of `E ∖ {O}` outside `E ∖ E[2]` lies on `ψ = 0`.** -/
lemma psiE_mem_of_not_mem_VE {c : curveE E} (hc : c ∈ XE E) (hcV : c ∉ VE E) :
    psiE E ∈ ((isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩).asIdeal.comap (coordToXE E) := by
  by_contra hψ
  set P := (isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩ with hP
  have hd : Disjoint (Submonoid.powers (psiE E) : Set A) (P.asIdeal.comap (coordToXE E)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 hψ
  haveI hQ₂ : (Ideal.map (algebraMap A (coverRingE E)) (P.asIdeal.comap (coordToXE E))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (psiE E)) (coverRingE E) _
      inferInstance hd
  have hQ₂c : Ideal.comap (algebraMap A (coverRingE E))
      (Ideal.map (algebraMap A (coverRingE E)) (P.asIdeal.comap (coordToXE E))) =
        P.asIdeal.comap (coordToXE E) :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (psiE E)) (coverRingE E)
      inferInstance hd
  let Q' : PrimeSpectrum Γ(curveE E, VE E) :=
    ⟨(Ideal.map (algebraMap A (coverRingE E)) (P.asIdeal.comap (coordToXE E))).comap
      (sectionsVEEquiv E).toRingHom, Ideal.comap_isPrime _ _⟩
  have hQ' : PrimeSpectrum.comap (resVX E).hom Q' = P := by
    refine PrimeSpectrum.ext (Ideal.ext fun s ↦ ?_)
    change sectionsVEEquiv E (resVX E s) ∈ Ideal.map (algebraMap A (coverRingE E))
      (P.asIdeal.comap (coordToXE E)) ↔ s ∈ P.asIdeal
    rw [sectionsVEEquiv_resVX]
    refine (SetLike.ext_iff.1 hQ₂c _).trans ?_
    change coordToXE E (sectionsXEAlgEquiv E s) ∈ P.asIdeal ↔ _
    rw [← sectionsXEAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]
  have hc' : (isAffineOpen_VE E).fromSpec Q' = c := by
    rw [← IsAffineOpen.map_fromSpec (isAffineOpen_XE E) (isAffineOpen_VE E)
      (homOfLE (VE_le_XE E)).op, Scheme.Hom.comp_apply, Spec.map_apply]
    change (isAffineOpen_XE E).fromSpec (PrimeSpectrum.comap (resVX E).hom Q') = c
    rw [hQ', hP, IsAffineOpen.fromSpec_primeIdealOf]
  have hmem : (isAffineOpen_VE E).fromSpec Q' ∈ Set.range (isAffineOpen_VE E).fromSpec :=
    ⟨Q', rfl⟩
  rw [IsAffineOpen.range_fromSpec, hc'] at hmem
  exact hcV hmem

/-- **The points of `(E ∖ {O}) ∖ (E ∖ E[2])` are `K`-rational** if `E[2]` is `K`-rational. -/
theorem isIso_residueFieldMap_of_mem_XE_diff (hE : E.Ψ₂Sq.Splits) {c : curveE E}
    (hc : c ∈ XE E) (hcV : c ∉ VE E) :
    IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap c) := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_of_splits E hE
  have hψ := psiE_mem_of_not_mem_VE E hc hcV
  set P := (isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩ with hP
  obtain ⟨e, h0, hker⟩ := exists_ker_evalTwoTorsion E he _ hψ
  have hφK : ∀ a : K, (evalTwoTorsion E h0).comp (sectionsXEAlgEquiv E).toRingHom
      (algebraMap K Γ(curveE E, XE E) a) = a := fun a ↦ by
    rw [RingHom.comp_apply]
    change evalTwoTorsion E h0 (sectionsXEAlgEquiv E (algebraMap K _ a)) = a
    rw [AlgEquiv.commutes, evalTwoTorsion_algebraMap]
  have hσ : (Spec.map (CommRingCat.ofHom ((evalTwoTorsion E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) ≫ (isAffineOpen_XE E).fromSpec) ≫
        (curveE E ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, fromSpec_comp_structure K (curveE E) (isAffineOpen_XE E),
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h' : CommRingCat.ofHom (((evalTwoTorsion E h0).comp
        (sectionsXEAlgEquiv E).toRingHom).comp (algebraMap K Γ(curveE E, XE E))) =
          𝟙 (CommRingCat.of K) := by
      ext a
      exact hφK a
    exact (congrArg Spec.map h').trans (Spec.map_id _)
  let pt : Spec (.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h1 : Spec.map (CommRingCat.ofHom ((evalTwoTorsion E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) pt = P := by
    rw [Spec.map_apply]
    refine PrimeSpectrum.ext (Ideal.ext fun s ↦ ?_)
    change evalTwoTorsion E h0 (sectionsXEAlgEquiv E s) ∈ (⊥ : Ideal K) ↔ s ∈ P.asIdeal
    rw [Ideal.mem_bot, ← RingHom.mem_ker, hker]
    change coordToXE E (sectionsXEAlgEquiv E s) ∈ P.asIdeal ↔ _
    rw [← sectionsXEAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]
  have hpt : (Spec.map (CommRingCat.ofHom ((evalTwoTorsion E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) ≫ (isAffineOpen_XE E).fromSpec) pt = c := by
    rw [Scheme.Hom.comp_apply, h1, hP, IsAffineOpen.fromSpec_primeIdealOf]
  have key := isIso_residueFieldMap_of_comp_eq_id _ _ hσ pt
  rw [hpt] at key
  exact key

/-- `(E ∖ {O}) ∖ (E ∖ E[2])` is finite. -/
theorem finite_XE_diff_VE : ((XE E : Set (curveE E)) \ VE E).Finite :=
  (hypCurveV E).cusps_finite.subset fun _ hx ↦ hx.2

/-- The points of `(E ∖ {O}) ∖ (E ∖ E[2])` are closed. -/
theorem isClosed_of_mem_XE_diff {c : curveE E} (hc : c ∈ (XE E : Set (curveE E)) \ VE E) :
    IsClosed ({c} : Set (curveE E)) :=
  isClosed_singleton_of_not_mem (k := K) (curveE E) (VE E) (VE_nonempty E) hc.2

end Points

/-! ### The run of fillings `E ∖ E[2] = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_n = E ∖ {O}` -/

section Run

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `E ∖ E[2]` has a cusp. -/
lemma compl_VE_nonempty₂ : ((VE E : (curveE E).Opens) : Set (curveE E))ᶜ.Nonempty :=
  (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 (VE_le_XE E))

/-- **The run of fillings of the nonzero points of order two** `E ∖ E[2] = U₀ ⊆ ⋯ ⊆ U_n =
E ∖ {O}`, one `K`-rational point at a time (`E[2]` `K`-rational). -/
theorem exists_runE (hE : E.Ψ₂Sq.Splits) :
    ∃ (n : ℕ) (UW : Fin (n + 1) → (curveE E).Opens) (x : Fin n → curveE E),
      UW 0 = VE E ∧ UW (Fin.last n) = XE E ∧ (∀ i, VE E ≤ UW i) ∧ (∀ i, UW i ≤ XE E) ∧
      (∀ i : Fin n, UW i.castSucc ≤ UW i.succ) ∧ (∀ i, x i ∈ UW i.succ) ∧
      (∀ i, x i ∉ UW i.castSucc) ∧ (∀ i, (UW i.succ : Set (curveE E)) \ UW i.castSucc ⊆ {x i}) ∧
      ∀ i, IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap (x i)) := by
  obtain ⟨r, -, -, UW, x, h0, hlast, -, hle, hleU, hmono, hx1, hx2, hx3⟩ :=
    exists_fillSeq (VE E) (XE E) (XE E) (VE_le_XE E) le_rfl (finite_XE_diff_VE E)
      (fun _ hc ↦ isClosed_of_mem_XE_diff E hc)
  exact ⟨r, UW, x, h0, hlast, hle, hleU, hmono, hx1, hx2, hx3, fun i ↦
    isIso_residueFieldMap_of_mem_XE_diff E hE (hleU i.succ (hx1 i))
      (fun h ↦ hx2 i (hle i.castSucc h))⟩

/-- The number of fillings of the run `exists_runE`. -/
def runNE (hE : E.Ψ₂Sq.Splits) : ℕ := (exists_runE E hE).choose

/-- The opens of the run `exists_runE`. -/
def runUWE (hE : E.Ψ₂Sq.Splits) : Fin (runNE E hE + 1) → (curveE E).Opens :=
  (exists_runE E hE).choose_spec.choose

/-- The filled points of the run `exists_runE`. -/
def runXE (hE : E.Ψ₂Sq.Splits) : Fin (runNE E hE) → curveE E :=
  (exists_runE E hE).choose_spec.choose_spec.choose

lemma runSpecE (hE : E.Ψ₂Sq.Splits) :
    runUWE E hE 0 = VE E ∧ runUWE E hE (Fin.last _) = XE E ∧ (∀ i, VE E ≤ runUWE E hE i) ∧
      (∀ i, runUWE E hE i ≤ XE E) ∧
      (∀ i : Fin (runNE E hE), runUWE E hE i.castSucc ≤ runUWE E hE i.succ) ∧
      (∀ i, runXE E hE i ∈ runUWE E hE i.succ) ∧ (∀ i, runXE E hE i ∉ runUWE E hE i.castSucc) ∧
      (∀ i, (runUWE E hE i.succ : Set (curveE E)) \ runUWE E hE i.castSucc ⊆ {runXE E hE i}) ∧
      ∀ i, IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap (runXE E hE i)) :=
  (exists_runE E hE).choose_spec.choose_spec.choose_spec

end Run

/-! ### The elliptic data of `E ∖ {O}` -/

section Data

lemma eqToHom_specΓ_algebraMap {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    {U U' : X.Opens} (h : U = U') :
    eqToHom (congrArg (fun V : X.Opens ↦ Spec Γ(X, V)) h) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U'))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
  subst h
  rw [eqToHom_refl, Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id]

lemma isFiniteEtale_of_isIso₂ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsFiniteEtale f :=
  (isFiniteEtale_iff f).2 ⟨inferInstance, inferInstance⟩

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **The elliptic data of IUT's once-punctured elliptic curve `X = E ∖ {O}` for `N = 2`**
([AbsTopII] Example 3.2 (i)), `E[2]` `K`-rational: `D = V = X`, `U = E ∖ E[2]`, `β = [2]`,
the run of fillings `E ∖ E[2] ⊆ ⋯ ⊆ E ∖ {O}` of `exists_runE`, `FV = FQ = 𝟙` and `FD` the
identification `Spec Γ(E ∖ {O}) = Spec Γ(U_n)`. -/
def ellipticDataE (hE : E.Ψ₂Sq.Splits) : EllipticData (M := K) (hypCurveX E) where
  CQ := hypCurveX E
  hcQ := compl_XE_nonempty E
  CW := hypCurveV E
  hcW := compl_VE_nonempty₂ E
  n := runNE E hE
  UW := runUWE E hE
  hUW0 := (runSpecE E hE).1
  hleW := (runSpecE E hE).2.2.1
  hmonoW := (runSpecE E hE).2.2.2.2.1
  hcUW i := (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 ((runSpecE E hE).2.2.2.1 i))
  hypW i := hyperbolic_of_le E ((runSpecE E hE).2.2.1 i) ((runSpecE E hE).2.2.2.1 i)
  xW := runXE E hE
  hxUW := (runSpecE E hE).2.2.2.2.2.1
  hxUW' := (runSpecE E hE).2.2.2.2.2.2.1
  hxW := (runSpecE E hE).2.2.2.2.2.2.2.1
  ratW := (runSpecE E hE).2.2.2.2.2.2.2.2
  CV := hypCurveX E
  hcV := compl_XE_nonempty E
  FV := 𝟙 _
  finFV := isFiniteEtale_of_isIso₂ _
  hFV := by
    rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Category.comp_id]
  FQ := 𝟙 _
  finFQ := isFiniteEtale_of_isIso₂ _
  hFQ := by
    rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Category.comp_id]
  β := coverXMorK E
  finβ := isFiniteEtale_coverXMorK E
  hβ := by
    change coverXMorK E ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) = _
    simp only [coverXMorK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverXHom_algebraMap E c
  FD := eqToHom (congrArg (fun V : (curveE E).Opens ↦ Spec Γ(curveE E, V))
    (runSpecE E hE).2.1.symm)
  finFD := isFiniteEtale_of_isIso₂ _
  hFD := eqToHom_specΓ_algebraMap (runSpecE E hE).2.1.symm

lemma isIso_ellipticDataE_FV (hE : E.Ψ₂Sq.Splits) : IsIso (ellipticDataE E hE).FV := by
  dsimp only [ellipticDataE]
  infer_instance

lemma isIso_ellipticDataE_FD (hE : E.Ψ₂Sq.Splits) : IsIso (ellipticDataE E hE).FD := by
  dsimp only [ellipticDataE]
  infer_instance

end Data

/-! ### The candidate of the elliptic chain of `E ∖ {O}` -/

section Candidate

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `Π_{U'} → Π_U` is bijective for an isomorphism `U' ≅ U`. -/
lemma coverPiHom_bijective_of_isIso₂ (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (C' : HypCurve K)
    (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty) (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U))
    (hF : IsIso F) : Function.Bijective (coverPiHom Ω C hc C' hc' F) :=
  haveI := hF
  (EquivLike.bijective (autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F))).comp
    (fundamentalGroupMap_bijective_of_isIso F rfl)

/-- **A run `U = U₁ ⊆ U₂ = U'` of fillings is `fillPiHom`** up to continuous isomorphisms. -/
theorem exists_fillStepMap_eq_fillPiHom (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {U₁ U₂ U' : C.Xbar.Opens} (h₁ : C.U ≤ U₁) (h₂ : U₁ ≤ U₂) (e₁ : U₁ = C.U) (e₂ : U₂ = U')
    (h : C.U ≤ U') (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
      2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U') :
    ∃ (a : π₁ᵉᵗ(fillPoint Ω C hc h₁ ≫ baseChangeSpec K Ω Γ(C.Xbar, U₁)) ≃ₜ*
        π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
      (b : π₁ᵉᵗ(fillPoint Ω C hc (h₁.trans h₂) ≫ baseChangeSpec K Ω Γ(C.Xbar, U₂)) ≃ₜ*
        π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec K Ω Γ(C.Xbar, U'))),
      ∀ y, b (fillStepMap Ω C hc h₁ h₂ y) = fillPiHom Ω C hc h hc' hyp (a y) := by
  subst e₁ e₂
  have hb := fillMap_bijective_of_eq Ω C hc h₁ rfl
  refine ⟨(continuousMulEquivOfBijective (fillMap Ω C hc h₁) hb).symm,
    (fillTransport Ω C hc h hc' hyp).symm, fun y ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := hb.2 y
  have e1 : (continuousMulEquivOfBijective (fillMap Ω C hc h₁) hb).symm
      (fillMap Ω C hc h₁ γ) = γ :=
    (continuousMulEquivOfBijective (fillMap Ω C hc h₁) hb).symm_apply_apply γ
  rw [e1, fillStepMap_fillMap, ContinuousMulEquiv.symm_apply_eq, fillTransport_fillPiHom]

variable (E : WeierstrassCurve K) [E.IsElliptic]

/-- **[AbsTopII] Example 3.2 (i), Corollary 3.3 (iii)(a) for `X = E ∖ {O}` and `N = 2`**
(`E[2]` `K`-rational): the elliptic chain of `ellipticDataE` gives a candidate in
`ellipticCusp (Π_X)` which is, up to continuous isomorphisms, the filling
`Π_{E ∖ E[2]} ↠ Π_{E ∖ {O}}` (`fillPiHom` of `E ∖ E[2] ⊆ E ∖ {O}`) together with isomorphisms
`Π_V ≅ Π_{E ∖ {O}}` (`ψ`) and `Π_V ≅ Π_X` (`emb`). -/
theorem exists_ellipticCandidate_oncePunctured (hE : E.Ψ₂Sq.Splits) :
    ∃ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
      ∃ (eU : x.PiU ≃ₜ* π₁ᵉᵗ(basePoint Ω (hypCurveV E) (compl_VE_nonempty₂ E) ≫
          baseChangeSpec K Ω Γ(curveE E, VE E)))
        (eD : x.PiD ≃ₜ* π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveV E) (VE_le_XE E)
          (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
            baseChangeSpec K Ω Γ(curveE E, XE E)))
        (eV : x.PiV ≃ₜ* (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi)
        (ψ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveV E) (VE_le_XE E)
            (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
              baseChangeSpec K Ω Γ(curveE E, XE E))),
        (∀ u, eD (x.surj u) = fillPiHom Ω (hypCurveV E) (compl_VE_nonempty₂ E) (VE_le_XE E)
          (compl_XE_nonempty E) (hyperbolic_of_le E (VE_le_XE E) le_rfl) (eU u)) ∧
        (∀ v, eD (x.incl v) = ψ (eV v)) ∧ ∀ v, x.emb v = eV v := by
  obtain ⟨eU, eD, eV, h1, h2, h3⟩ :=
    (ellipticDataE E hE).ellipticCandidate_spec Ω (compl_XE_nonempty E)
  obtain ⟨a, b, hab⟩ := exists_fillStepMap_eq_fillPiHom Ω (hypCurveV E) (compl_VE_nonempty₂ E)
    ((ellipticDataE E hE).hleW ⟨0, Nat.succ_pos _⟩)
    ((ellipticDataE E hE).monoW (Fin.mk_le_mk.2 (Nat.zero_le _) :
      (⟨0, Nat.succ_pos _⟩ : Fin ((ellipticDataE E hE).n + 1)) ≤ Fin.last _))
    (ellipticDataE E hE).hUW0 (runSpecE E hE).2.1 (VE_le_XE E) (compl_XE_nonempty E)
    (hyperbolic_of_le E (VE_le_XE E) le_rfl)
  have hb1 : Function.Bijective ((ellipticDataE E hE).φ₁ Ω (compl_XE_nonempty E)) :=
    coverPiHom_bijective_of_isIso₂ Ω _ _ _ _ _ (isIso_ellipticDataE_FV E hE)
  have hb5 : Function.Bijective ((ellipticDataE E hE).φ₅ Ω) :=
    (EquivLike.bijective ((ellipticDataE E hE).TW Ω)).comp
      (coverPiHom_bijective_of_isIso₂ Ω _ _ _ _ _ (isIso_ellipticDataE_FD E hE))
  refine ⟨_, (ellipticDataE E hE).ellipticCandidate_mem Ω (compl_XE_nonempty E), eU.trans a,
    eD.trans b, eV.trans (continuousMulEquivOfBijective _ hb1),
    (continuousMulEquivOfBijective _ hb1).symm.trans
      ((continuousMulEquivOfBijective _ hb5).trans b), fun u ↦ ?_, fun v ↦ ?_, fun v ↦ ?_⟩
  · change b (eD _) = _
    rw [h1]
    exact hab _
  · change b (eD _) = b _
    rw [h2]
    congr 1
    change _ = (continuousMulEquivOfBijective _ hb5) ((continuousMulEquivOfBijective _ hb1).symm
      ((continuousMulEquivOfBijective _ hb1) (eV v)))
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  · exact h3 v

end Candidate

end CurvesJacobian.Cusp
