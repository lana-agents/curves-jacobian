/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticCuspSpec
import CurvesJacobian.Cusp.EllipticMulByN

/-!
# The elliptic chain of `E ∖ {O}` for every `N ≥ 1` (MR8)

[AbsTopII] Example 3.2 (i) (`Topics in Absolute Anabelian Geometry II.txt` l.4326–4400) and
Corollary 3.3 (iii)(a) (l.4481–4491) for IUT's once-punctured elliptic curve
`X = D = V = E ∖ {O}` (`hypCurveX E`) and general `N`, generalising `EllipticChainE.lean`
(`N = 2`): `U = E ∖ E[N]` (`hypCurveVN E N`, the open `VNE E N = {ψ_N ≠ 0}`),
`β = [N] : U → D` (`mulByNXMor E N`), and the run of fillings
`E ∖ E[N] = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_n = E ∖ {O}` of the nonzero `N`-torsion points.

`E[N]` is assumed `K`-rational in the coordinate form `CurvesJacobian.Cusp.TorsionRationalN`:
`ΨSq_N` (the polynomial in `x` with `ψ_N² = ΨSq_N(x)`) splits over `K` and over each of its roots
`e` there is a `K`-point `(e, y)` of `E` (for `N = 2` this is `E.Ψ₂Sq.Splits`,
`CurvesJacobian.Cusp.torsionRationalN_two`).

## Main results

* `CurvesJacobian.Cusp.isIso_residueFieldMap_of_mem_XE_diff_VNE`: every point of
  `(E ∖ {O}) ∖ (E ∖ E[N])` is `K`-rational. Such a point is a prime `Q` of `K[E]` containing `ψ_N`,
  hence `ΨSq_N(x)`; it contains `x - e` for a root `e`, then `(y - y₀)(y - y₁)` for the two
  `K`-points `(e, y₀)`, `(e, y₁)` over `e`, and is the kernel of the evaluation at one of them.
* `CurvesJacobian.Cusp.hypCurveVN`: `E ∖ E[N]` as a hyperbolic curve; `finite_XE_diff_VNE`,
  `isClosed_of_mem_XE_diff_VNE` and the run `CurvesJacobian.Cusp.exists_runEN`.
* `CurvesJacobian.Cusp.ellipticDataEN`: the `EllipticData` of `E ∖ {O}` with `CQ = CV = X`,
  `CW = E ∖ E[N]`, `β = [N]`, `FV = FQ = 𝟙`.
* `CurvesJacobian.Cusp.exists_ellipticCandidate_oncePuncturedN`: the resulting candidate in
  `ellipticCusp (Π_X)` is, up to continuous isomorphisms, `Π_{E ∖ E[N]} ↠ Π_{E ∖ {O}}`
  (`fillPiHom`), with `Π_V ≅ Π_{E ∖ {O}}` and `Π_V ≅ Π_X`;
  `CurvesJacobian.Cusp.ellipticCusp_spec_oncePuncturedN` packages soundness, existence and
  functoriality as in `EllipticCuspSpec.lean`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Polynomial Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### `K`-rationality of `E[N]` and the evaluation of `K[E]` at a `K`-point -/

section Torsion

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K)

local notation "A" => E.toAffine.CoordinateRing

/-- **`E[N]` is `K`-rational** (in coordinates): `ΨSq_N` splits over `K` (its roots are the
`x`-coordinates of the nonzero `N`-torsion points) and over each root `e` there is a `K`-point
`(e, y)` of `E`. -/
def TorsionRationalN (N : ℕ) : Prop :=
  (E.ΨSq N).Splits ∧ ∀ e : K, (E.ΨSq N).eval e = 0 → ∃ y : K, E.toAffine.Equation e y

/-- For `N = 2`, `K`-rationality of `E[2]` is the splitting of `Ψ₂Sq = 4x³ + b₂x² + 2b₄x + b₆`. -/
theorem torsionRationalN_two (hE : E.Ψ₂Sq.Splits) : TorsionRationalN E 2 := by
  have h2 : E.ΨSq ((2 : ℕ) : ℤ) = E.Ψ₂Sq := by
    rw [Nat.cast_ofNat, WeierstrassCurve.ΨSq_two]
  refine ⟨h2 ▸ hE, fun e he ↦ ⟨-(E.a₁ * e + E.a₃) / 2, ?_⟩⟩
  rw [h2, WeierstrassCurve.Ψ₂Sq] at he
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at he
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₆, WeierstrassCurve.b₄] at he
  rw [WeierstrassCurve.Affine.equation_iff']
  linear_combination (-1 / 4 : K) * he

omit [CharZero K] in
lemma eval₂_polynomial_of_equationN {e y : K} (h : E.toAffine.Equation e y) :
    E.toAffine.polynomial.eval₂ (evalRingHom e) y = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination h

omit [CharZero K] in
/-- The evaluation `K[E] → K` at a `K`-point `(e, y)`. -/
def evalPtN {e y : K} (h : E.toAffine.Equation e y) : A →+* K :=
  AdjoinRoot.lift (evalRingHom e) y (eval₂_polynomial_of_equationN E h)

omit [CharZero K] in
lemma evalPtN_algebraMap {e y : K} (h : E.toAffine.Equation e y) (c : K) :
    evalPtN E h (algebraMap K A c) = c := by
  rw [algebraMap_coordinateRing_eq_of, evalPtN, AdjoinRoot.lift_of, coe_evalRingHom, eval_C]

omit [CharZero K] in
lemma algebraMap_not_mem_of_isPrime (Q : Ideal A) [hQ : Q.IsPrime] {c : K} (hc : c ≠ 0) :
    algebraMap K A c ∉ Q := fun h ↦ hQ.ne_top
  ((Ideal.eq_top_iff_one Q).2 (by
    have := Q.mul_mem_right (algebraMap K A c⁻¹) h
    rwa [← map_mul, mul_inv_cancel₀ hc, map_one] at this))

omit [CharZero K] in
/-- **A prime of `K[E]` containing `x - e` and `y - y₀` is the kernel of the evaluation at
`(e, y₀)`.** -/
lemma ker_evalPtN {e y : K} (h : E.toAffine.Equation e y) (Q : Ideal A) [hQ : Q.IsPrime]
    (hx : xE E - algebraMap K A e ∈ Q) (hy : yE E - algebraMap K A y ∈ Q) :
    RingHom.ker (evalPtN E h) = Q := by
  have key : Ideal.Quotient.mk Q =
      ((Ideal.Quotient.mk Q).comp (algebraMap K A)).comp (evalPtN E h) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp only [RingHom.comp_apply]
        rw [evalPtN, AdjoinRoot.lift_of, coe_evalRingHom, eval_C,
          algebraMap_coordinateRing_eq_of]
      · simp only [RingHom.comp_apply]
        rw [evalPtN, AdjoinRoot.lift_of, coe_evalRingHom, eval_X]
        exact Ideal.Quotient.eq.2 hx
    · simp only [RingHom.comp_apply]
      rw [evalPtN, AdjoinRoot.lift_root]
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
    exact algebraMap_not_mem_of_isPrime E Q hne h

/-- **A prime of `K[E]` containing `ψ_N` is the kernel of the evaluation at a `K`-point**
(`E[N]` `K`-rational). -/
lemma exists_ker_evalPtN {N : ℕ} [NeZero N] (hEN : TorsionRationalN E N) (Q : Ideal A)
    [hQ : Q.IsPrime] (hψ : psiN E N ∈ Q) :
    ∃ (e y : K) (h : E.toAffine.Equation e y), RingHom.ker (evalPtN E h) = Q := by
  have h0 : E.ΨSq N ≠ 0 := E.ΨSq_ne_zero (by
    rw [Int.cast_natCast]
    exact Nat.cast_ne_zero.2 (NeZero.ne N))
  have hg : algebraMap K[X] A (E.ΨSq N) ∈ Q := by
    rw [← psiN_sq]
    exact Q.pow_mem_of_mem hψ 2 two_pos
  rw [hEN.1.eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map] at hg
  have hlc : algebraMap K[X] A (C (E.ΨSq N).leadingCoeff) ∉ Q := by
    rw [AdjoinRoot.algebraMap_eq, ← algebraMap_coordinateRing_eq_of]
    exact algebraMap_not_mem_of_isPrime E Q (leadingCoeff_ne_zero.2 h0)
  rcases hQ.mem_or_mem hg with h | h
  · exact absurd h hlc
  obtain ⟨a, ha, haQ⟩ := (hQ.multiset_prod_mem_iff_exists_mem _).1 h
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 ha
  have hroot : (E.ΨSq N).eval e = 0 := ((mem_roots h0).1 he)
  have hx : xE E - algebraMap K A e ∈ Q := by
    have h' := haQ
    simp only [Function.comp_apply] at h'
    rwa [AdjoinRoot.algebraMap_eq, map_sub, ← algebraMap_coordinateRing_eq_of] at h'
  obtain ⟨y₀, hy₀⟩ := hEN.2 e hroot
  have hy₁ : E.toAffine.Equation e (-y₀ - E.a₁ * e - E.a₃) := by
    rw [WeierstrassCurve.Affine.equation_iff] at hy₀ ⊢
    linear_combination hy₀
  have hy₀A : algebraMap K A y₀ ^ 2 + algebraMap K A E.a₁ * algebraMap K A e * algebraMap K A y₀ +
      algebraMap K A E.a₃ * algebraMap K A y₀ = algebraMap K A e ^ 3 +
        algebraMap K A E.a₂ * algebraMap K A e ^ 2 + algebraMap K A E.a₄ * algebraMap K A e +
          algebraMap K A E.a₆ := by
    rw [WeierstrassCurve.Affine.equation_iff] at hy₀
    have h' := congrArg (algebraMap K A) hy₀
    simpa only [map_add, map_mul, map_pow] using h'
  have hprod : (yE E - algebraMap K A y₀) * (yE E - algebraMap K A (-y₀ - E.a₁ * e - E.a₃)) =
      (xE E - algebraMap K A e) * (-(algebraMap K A E.a₁) * yE E + xE E ^ 2 +
        xE E * algebraMap K A e + algebraMap K A e ^ 2 +
          algebraMap K A E.a₂ * (xE E + algebraMap K A e) + algebraMap K A E.a₄) := by
    rw [map_sub, map_sub, map_neg, map_mul]
    linear_combination equation_E E - hy₀A
  have hmem : (yE E - algebraMap K A y₀) *
      (yE E - algebraMap K A (-y₀ - E.a₁ * e - E.a₃)) ∈ Q := by
    rw [hprod]
    exact Q.mul_mem_right _ hx
  rcases hQ.mem_or_mem hmem with h1 | h1
  · exact ⟨e, y₀, hy₀, ker_evalPtN E hy₀ Q hx h1⟩
  · exact ⟨e, _, hy₁, ker_evalPtN E hy₁ Q hx h1⟩

end Torsion

/-! ### The hyperbolic curve `E ∖ E[N]` -/

section HypCurve

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

/-- `E ∖ E[N]` is nonempty: `Γ(E ∖ E[N]) ≅ K[E][1/ψ_N]` is a domain. -/
lemma VNE_nonempty : ((VNE E N : (curveE E).Opens) : Set (curveE E)).Nonempty := by
  haveI : Nontrivial Γ(curveE E, VNE E N) := (sectionsVNEEquiv E N).toEquiv.nontrivial
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(curveE E, VNE E N)) := inferInstance
  refine ⟨(isAffineOpen_VNE E N).fromSpec p, ?_⟩
  rw [← IsAffineOpen.range_fromSpec (isAffineOpen_VNE E N)]
  exact ⟨p, rfl⟩

omit [NeZero N] in
/-- A nonempty open `U ⊆ E ∖ {O}` has a cusp of positive degree (the origin). -/
lemma one_le_cuspDegreeN {U : (curveE E).Opens} (hne : (U : Set (curveE E)).Nonempty)
    (hUX : U ≤ XE E) : 1 ≤ Anabelian.cuspDegree K (curveE E) U := by
  have hfin := finite_compl_of_isCurveOver (k := K) (curveE E) U hne
  obtain ⟨c, hc⟩ := (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 hUX)
  unfold Anabelian.cuspDegree
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    ((Set.Finite.mem_toFinset hfin).2 hc))
  letI := Anabelian.residueFieldAlgebra K (curveE E) c
  haveI := finite_residueField K (X := curveE E) (isClosed_singleton_of_not_mem (k := K) _ U hne hc)
  exact Module.finrank_pos

omit [NeZero N] in
/-- Every nonempty open `U ⊆ E ∖ {O}` is hyperbolic. -/
lemma hyperbolic_of_le_XEN {U : (curveE E).Opens} (hne : (U : Set (curveE E)).Nonempty)
    (hUX : U ≤ XE E) :
    haveI := IsCurveOver.isIntegral K (curveE E)
    2 < 2 * Anabelian.curveGenus K (curveE E) + Anabelian.cuspDegree K (curveE E) U := by
  have h1 := one_le_curveGenus_curveE E
  have h2 := one_le_cuspDegreeN E hne hUX
  omega

/-- **`E ∖ E[N]` as a hyperbolic curve over `K`** (compactification `Ē`, `U = {ψ_N ≠ 0}`). -/
def hypCurveVN : HypCurve K where
  Xbar := curveE E
  U := VNE E N
  nonempty := VNE_nonempty E N
  cusps_finite := finite_compl_of_isCurveOver (k := K) (curveE E) _ (VNE_nonempty E N)
  hyperbolic := hyperbolic_of_le_XEN E (VNE_nonempty E N) (VNE_le_XE E N)

omit [NeZero N] in
/-- `E ∖ E[N]` has a cusp. -/
lemma compl_VNE_nonempty : ((VNE E N : (curveE E).Opens) : Set (curveE E))ᶜ.Nonempty :=
  (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 (VNE_le_XE E N))

end HypCurve

/-! ### The points of `(E ∖ {O}) ∖ (E ∖ E[N])` -/

section Points

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

omit [NeZero N] in
/-- **A point of `E ∖ {O}` outside `E ∖ E[N]` lies on `ψ_N = 0`.** -/
lemma psiN_mem_of_not_mem_VNE {c : curveE E} (hc : c ∈ XE E) (hcV : c ∉ VNE E N) :
    psiN E N ∈ ((isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩).asIdeal.comap (coordToXE E) := by
  have h1 : (isAffineOpen_XE E).fromSpec ((isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩) ∉
      VNE E N := by
    rwa [IsAffineOpen.fromSpec_primeIdealOf]
  have h2 : (isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩ ∉
      PrimeSpectrum.basicOpen (psiNX E N) := by
    rw [← IsAffineOpen.fromSpec_preimage_basicOpen (isAffineOpen_XE E)]
    exact h1
  rw [PrimeSpectrum.mem_basicOpen, not_not] at h2
  change coordToXE E (psiN E N) ∈ ((isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩).asIdeal
  rw [← sectionsXEAlgEquiv_symm_apply]
  exact h2

/-- **The points of `(E ∖ {O}) ∖ (E ∖ E[N])` are `K`-rational** if `E[N]` is `K`-rational. -/
theorem isIso_residueFieldMap_of_mem_XE_diff_VNE (hEN : TorsionRationalN E N) {c : curveE E}
    (hc : c ∈ XE E) (hcV : c ∉ VNE E N) :
    IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap c) := by
  have hψ := psiN_mem_of_not_mem_VNE E N hc hcV
  set P := (isAffineOpen_XE E).primeIdealOf ⟨c, hc⟩ with hP
  obtain ⟨e, y, h0, hker⟩ := exists_ker_evalPtN E hEN _ hψ
  have hφK : ∀ a : K, (evalPtN E h0).comp (sectionsXEAlgEquiv E).toRingHom
      (algebraMap K Γ(curveE E, XE E) a) = a := fun a ↦ by
    rw [RingHom.comp_apply]
    change evalPtN E h0 (sectionsXEAlgEquiv E (algebraMap K _ a)) = a
    rw [AlgEquiv.commutes, evalPtN_algebraMap]
  have hσ : (Spec.map (CommRingCat.ofHom ((evalPtN E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) ≫ (isAffineOpen_XE E).fromSpec) ≫
        (curveE E ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, fromSpec_comp_structure K (curveE E) (isAffineOpen_XE E),
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h' : CommRingCat.ofHom (((evalPtN E h0).comp
        (sectionsXEAlgEquiv E).toRingHom).comp (algebraMap K Γ(curveE E, XE E))) =
          𝟙 (CommRingCat.of K) := by
      ext a
      exact hφK a
    exact (congrArg Spec.map h').trans (Spec.map_id _)
  let pt : Spec (.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h1 : Spec.map (CommRingCat.ofHom ((evalPtN E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) pt = P := by
    rw [Spec.map_apply]
    refine PrimeSpectrum.ext (Ideal.ext fun s ↦ ?_)
    change evalPtN E h0 (sectionsXEAlgEquiv E s) ∈ (⊥ : Ideal K) ↔ s ∈ P.asIdeal
    rw [Ideal.mem_bot, ← RingHom.mem_ker, hker]
    change coordToXE E (sectionsXEAlgEquiv E s) ∈ P.asIdeal ↔ _
    rw [← sectionsXEAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]
  have hpt : (Spec.map (CommRingCat.ofHom ((evalPtN E h0).comp
      (sectionsXEAlgEquiv E).toRingHom)) ≫ (isAffineOpen_XE E).fromSpec) pt = c := by
    rw [Scheme.Hom.comp_apply, h1, hP, IsAffineOpen.fromSpec_primeIdealOf]
  have key := isIso_residueFieldMap_of_comp_eq_id _ _ hσ pt
  rw [hpt] at key
  exact key

/-- `(E ∖ {O}) ∖ (E ∖ E[N])` is finite. -/
theorem finite_XE_diff_VNE : ((XE E : Set (curveE E)) \ VNE E N).Finite :=
  (hypCurveVN E N).cusps_finite.subset fun _ hx ↦ hx.2

/-- The points of `(E ∖ {O}) ∖ (E ∖ E[N])` are closed. -/
theorem isClosed_of_mem_XE_diff_VNE {c : curveE E}
    (hc : c ∈ (XE E : Set (curveE E)) \ VNE E N) : IsClosed ({c} : Set (curveE E)) :=
  isClosed_singleton_of_not_mem (k := K) (curveE E) (VNE E N) (VNE_nonempty E N) hc.2

end Points

/-! ### The run of fillings `E ∖ E[N] = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_n = E ∖ {O}` -/

section Run

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

/-- **The run of fillings of the nonzero `N`-torsion points** `E ∖ E[N] = U₀ ⊆ ⋯ ⊆ U_n =
E ∖ {O}`, one `K`-rational point at a time (`E[N]` `K`-rational). -/
theorem exists_runEN (hEN : TorsionRationalN E N) :
    ∃ (n : ℕ) (UW : Fin (n + 1) → (curveE E).Opens) (x : Fin n → curveE E),
      UW 0 = VNE E N ∧ UW (Fin.last n) = XE E ∧ (∀ i, VNE E N ≤ UW i) ∧ (∀ i, UW i ≤ XE E) ∧
      (∀ i : Fin n, UW i.castSucc ≤ UW i.succ) ∧ (∀ i, x i ∈ UW i.succ) ∧
      (∀ i, x i ∉ UW i.castSucc) ∧ (∀ i, (UW i.succ : Set (curveE E)) \ UW i.castSucc ⊆ {x i}) ∧
      ∀ i, IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap (x i)) := by
  obtain ⟨r, -, -, UW, x, h0, hlast, -, hle, hleU, hmono, hx1, hx2, hx3⟩ :=
    exists_fillSeq (VNE E N) (XE E) (XE E) (VNE_le_XE E N) le_rfl (finite_XE_diff_VNE E N)
      (fun _ hc ↦ isClosed_of_mem_XE_diff_VNE E N hc)
  exact ⟨r, UW, x, h0, hlast, hle, hleU, hmono, hx1, hx2, hx3, fun i ↦
    isIso_residueFieldMap_of_mem_XE_diff_VNE E N hEN (hleU i.succ (hx1 i))
      (fun h ↦ hx2 i (hle i.castSucc h))⟩

/-- The number of fillings of the run `exists_runEN`. -/
def runNEN (hEN : TorsionRationalN E N) : ℕ := (exists_runEN E N hEN).choose

/-- The opens of the run `exists_runEN`. -/
def runUWEN (hEN : TorsionRationalN E N) : Fin (runNEN E N hEN + 1) → (curveE E).Opens :=
  (exists_runEN E N hEN).choose_spec.choose

/-- The filled points of the run `exists_runEN`. -/
def runXEN (hEN : TorsionRationalN E N) : Fin (runNEN E N hEN) → curveE E :=
  (exists_runEN E N hEN).choose_spec.choose_spec.choose

lemma runSpecEN (hEN : TorsionRationalN E N) :
    runUWEN E N hEN 0 = VNE E N ∧ runUWEN E N hEN (Fin.last _) = XE E ∧
      (∀ i, VNE E N ≤ runUWEN E N hEN i) ∧ (∀ i, runUWEN E N hEN i ≤ XE E) ∧
      (∀ i : Fin (runNEN E N hEN), runUWEN E N hEN i.castSucc ≤ runUWEN E N hEN i.succ) ∧
      (∀ i, runXEN E N hEN i ∈ runUWEN E N hEN i.succ) ∧
      (∀ i, runXEN E N hEN i ∉ runUWEN E N hEN i.castSucc) ∧
      (∀ i, (runUWEN E N hEN i.succ : Set (curveE E)) \ runUWEN E N hEN i.castSucc ⊆
        {runXEN E N hEN i}) ∧
      ∀ i, IsIso ((curveE E ↘ Spec (.of K)).residueFieldMap (runXEN E N hEN i)) :=
  (exists_runEN E N hEN).choose_spec.choose_spec.choose_spec

end Run

/-! ### The elliptic data of `E ∖ {O}` for `[N]` -/

section Data

section Alg

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

omit [NeZero N] in
lemma algebraMap_XE_VNE (c : K) :
    algebraMap Γ(curveE E, XE E) Γ(curveE E, VNE E N) (algebraMap K _ c) =
      algebraMap K Γ(curveE E, VNE E N) c := by
  change ((curveE E ↘ Spec (.of K)).appLE ⊤ (XE E) _ ≫
    (curveE E).presheaf.map (homOfLE (VNE_le_XE E N)).op) _ = _
  rw [Scheme.Hom.appLE_map]
  rfl

omit [NeZero N] in
lemma sectionsVNEEquiv_algebraMapK (c : K) :
    sectionsVNEEquiv E N (algebraMap K Γ(curveE E, VNE E N) c) =
      algebraMap K (coverRingN E N) c := by
  rw [← algebraMap_XE_VNE, sectionsVNEEquiv_algebraMap, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

lemma mulByNXHom_algebraMap (c : K) :
    mulByNXHom E N (algebraMap K _ c) = algebraMap K Γ(curveE E, VNE E N) (algebraMap K K c) := by
  change (sectionsVNEEquiv E N).symm (mulByNHom E N (sectionsXEAlgEquiv E (algebraMap K _ c))) = _
  rw [AlgEquiv.commutes, RingEquiv.symm_apply_eq, sectionsVNEEquiv_algebraMapK,
    mulByNHom_algebraMap, Algebra.algebraMap_self, RingHom.id_apply]

end Alg

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

/-- **The elliptic data of IUT's once-punctured elliptic curve `X = E ∖ {O}` for `[N]`**
([AbsTopII] Example 3.2 (i)), `E[N]` `K`-rational: `D = V = X`, `U = E ∖ E[N]`, `β = [N]`,
the run of fillings `E ∖ E[N] ⊆ ⋯ ⊆ E ∖ {O}` of `exists_runEN`, `FV = FQ = 𝟙` and `FD` the
identification `Spec Γ(E ∖ {O}) = Spec Γ(U_n)`. -/
def ellipticDataEN (hEN : TorsionRationalN E N) : EllipticData (M := K) (hypCurveX E) where
  CQ := hypCurveX E
  hcQ := compl_XE_nonempty E
  CW := hypCurveVN E N
  hcW := compl_VNE_nonempty E N
  n := runNEN E N hEN
  UW := runUWEN E N hEN
  hUW0 := (runSpecEN E N hEN).1
  hleW := (runSpecEN E N hEN).2.2.1
  hmonoW := (runSpecEN E N hEN).2.2.2.2.1
  hcUW i := (compl_XE_nonempty E).mono
    (Set.compl_subset_compl.2 ((runSpecEN E N hEN).2.2.2.1 i))
  hypW i := hyperbolic_of_le_XEN E ((VNE_nonempty E N).mono ((runSpecEN E N hEN).2.2.1 i))
    ((runSpecEN E N hEN).2.2.2.1 i)
  xW := runXEN E N hEN
  hxUW := (runSpecEN E N hEN).2.2.2.2.2.1
  hxUW' := (runSpecEN E N hEN).2.2.2.2.2.2.1
  hxW := (runSpecEN E N hEN).2.2.2.2.2.2.2.1
  ratW := (runSpecEN E N hEN).2.2.2.2.2.2.2.2
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
  β := mulByNXMor E N
  finβ := isFiniteEtale_mulByNXMor E N
  hβ := by
    change mulByNXMor E N ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) = _
    simp only [mulByNXMor, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ mulByNXHom_algebraMap E N c
  FD := eqToHom (congrArg (fun V : (curveE E).Opens ↦ Spec Γ(curveE E, V))
    (runSpecEN E N hEN).2.1.symm)
  finFD := isFiniteEtale_of_isIso₂ _
  hFD := eqToHom_specΓ_algebraMap (runSpecEN E N hEN).2.1.symm

lemma isIso_ellipticDataEN_FV (hEN : TorsionRationalN E N) : IsIso (ellipticDataEN E N hEN).FV := by
  dsimp only [ellipticDataEN]
  infer_instance

lemma isIso_ellipticDataEN_FD (hEN : TorsionRationalN E N) : IsIso (ellipticDataEN E N hEN).FD := by
  dsimp only [ellipticDataEN]
  infer_instance

end Data

/-! ### The candidate of the elliptic chain of `E ∖ {O}` for `[N]` -/

section Candidate

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

variable (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ) [NeZero N]

/-- **[AbsTopII] Example 3.2 (i), Corollary 3.3 (iii)(a) for `X = E ∖ {O}` and `[N]`**
(`E[N]` `K`-rational): the elliptic chain of `ellipticDataEN` gives a candidate in
`ellipticCusp (Π_X)` which is, up to continuous isomorphisms, the filling
`Π_{E ∖ E[N]} ↠ Π_{E ∖ {O}}` (`fillPiHom` of `E ∖ E[N] ⊆ E ∖ {O}`) together with isomorphisms
`Π_V ≅ Π_{E ∖ {O}}` (`ψ`) and `Π_V ≅ Π_X` (`emb`). -/
theorem exists_ellipticCandidate_oncePuncturedN (hEN : TorsionRationalN E N) :
    ∃ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
      ∃ (eU : x.PiU ≃ₜ* π₁ᵉᵗ(basePoint Ω (hypCurveVN E N) (compl_VNE_nonempty E N) ≫
          baseChangeSpec K Ω Γ(curveE E, VNE E N)))
        (eD : x.PiD ≃ₜ* π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveVN E N) (VNE_le_XE E N)
          (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
            baseChangeSpec K Ω Γ(curveE E, XE E)))
        (eV : x.PiV ≃ₜ* (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi)
        (ψ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveVN E N) (VNE_le_XE E N)
            (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
              baseChangeSpec K Ω Γ(curveE E, XE E))),
        (∀ u, eD (x.surj u) = fillPiHom Ω (hypCurveVN E N) (compl_VNE_nonempty E N)
          (VNE_le_XE E N) (compl_XE_nonempty E) (hyperbolic_of_le E (VE_le_XE E) le_rfl)
            (eU u)) ∧
        (∀ v, eD (x.incl v) = ψ (eV v)) ∧ ∀ v, x.emb v = eV v := by
  obtain ⟨eU, eD, eV, h1, h2, h3⟩ :=
    (ellipticDataEN E N hEN).ellipticCandidate_spec Ω (compl_XE_nonempty E)
  obtain ⟨a, b, hab⟩ := exists_fillStepMap_eq_fillPiHom Ω (hypCurveVN E N)
    (compl_VNE_nonempty E N) ((ellipticDataEN E N hEN).hleW ⟨0, Nat.succ_pos _⟩)
    ((ellipticDataEN E N hEN).monoW (Fin.mk_le_mk.2 (Nat.zero_le _) :
      (⟨0, Nat.succ_pos _⟩ : Fin ((ellipticDataEN E N hEN).n + 1)) ≤ Fin.last _))
    (ellipticDataEN E N hEN).hUW0 (runSpecEN E N hEN).2.1 (VNE_le_XE E N) (compl_XE_nonempty E)
    (hyperbolic_of_le E (VE_le_XE E) le_rfl)
  have hb1 : Function.Bijective ((ellipticDataEN E N hEN).φ₁ Ω (compl_XE_nonempty E)) :=
    coverPiHom_bijective_of_isIso₂ Ω _ _ _ _ _ (isIso_ellipticDataEN_FV E N hEN)
  have hb5 : Function.Bijective ((ellipticDataEN E N hEN).φ₅ Ω) :=
    (EquivLike.bijective ((ellipticDataEN E N hEN).TW Ω)).comp
      (coverPiHom_bijective_of_isIso₂ Ω _ _ _ _ _ (isIso_ellipticDataEN_FD E N hEN))
  refine ⟨_, (ellipticDataEN E N hEN).ellipticCandidate_mem Ω (compl_XE_nonempty E), eU.trans a,
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

/-- **[AbsTopII] Cor 3.3 (iii)(a) for `X = E ∖ {O}` and `[N]`** (`E[N]` `K`-rational):
soundness of the elliptic candidates (torsion-free `Δ_U`), existence of the elliptic candidate
realising `Π_{E ∖ E[N]} ↠ Π_{E ∖ {O}}`, and functoriality of `ellipticCusp`. -/
theorem ellipticCusp_spec_oncePuncturedN
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hEN : TorsionRationalN E N) :
    (∀ (c : PiChain (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E))) (n : ℕ)
      (hc : c.IsEllipticType n) (t : c.TerminalIso (PiChain.trivial _))
      (_ : IsTorsionFreeSubgroup (c.objN 3 (by have := hc.len_eq; omega)).Delta),
      IsGeomCandidate₂ Ω (hypCurveX E) (compl_XE_nonempty E)
        (PiChain.ellipticCandidate hc t).toCuspCandidate) ∧
    (∃ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
      ∃ (eU : x.PiU ≃ₜ* π₁ᵉᵗ(basePoint Ω (hypCurveVN E N) (compl_VNE_nonempty E N) ≫
          baseChangeSpec K Ω Γ(curveE E, VNE E N)))
        (eD : x.PiD ≃ₜ* π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveVN E N) (VNE_le_XE E N)
          (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
            baseChangeSpec K Ω Γ(curveE E, XE E)))
        (eV : x.PiV ≃ₜ* (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi)
        (ψ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (fillCurve (hypCurveVN E N) (VNE_le_XE E N)
            (hyperbolic_of_le E (VE_le_XE E) le_rfl)) (compl_XE_nonempty E) ≫
              baseChangeSpec K Ω Γ(curveE E, XE E))),
        (∀ u, eD (x.surj u) = fillPiHom Ω (hypCurveVN E N) (compl_VNE_nonempty E N)
          (VNE_le_XE E N) (compl_XE_nonempty E) (hyperbolic_of_le E (VE_le_XE E) le_rfl)
            (eU u)) ∧
        (∀ v, eD (x.incl v) = ψ (eV v)) ∧ ∀ v, x.emb v = eV v) ∧
    (∀ {E' : CuspidalExt.{u + 1}}
      (Φ : (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Iso E'),
      ∀ x ∈ ellipticCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)),
        x.transport Φ ∈ ellipticCusp E') :=
  ⟨fun _ _ hc t htf ↦ hc.isGeomCandidate₂ t hDGC htf,
    exists_ellipticCandidate_oncePuncturedN Ω E N hEN, fun Φ _ hx ↦ ellipticCusp_transport Φ hx⟩

end Candidate

end CurvesJacobian.Cusp
