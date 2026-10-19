/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.WeilPairing

/-!
# Transport of the Weil pairing along semilinear isomorphisms

Let `φ : K ≃+* K'` be a ring isomorphism of function fields over `κ`, `κ'` which is semilinear
along `ψ : κ ≃+* κ'` (`φ (c • 1) = ψ c • 1`). Then `φ` transports places, orders, values,
divisors, divisor classes and the Weil pairing:

* `CurvesJacobian.placeTr φ ψ hφ`, `placeTrEquiv`, `ord_placeTr` (`ord_{φP}(φ x) = ord_P x`),
  `val_placeTr` (`(φ x)(φP) = ψ(x(P))`);
* `divTr`, `div_tr`, `evalDiv_tr`, `picTr` (on `Pic`), `picTr_mem_picTorsion`;
* **`CurvesJacobian.weilPairing_tr`**: `e_n(φ a, φ b) = ψ(e_n(a, b))`.

Special cases: Galois equivariance (`φ = τ ∈ constAut κ K`, `ψ = τ|_κ`) and invariance under
`κ`-isomorphisms of function fields (`ψ = id`).
-/

open WeilCurves.FunctionField
open scoped WithZero

namespace CurvesJacobian

variable {κ K κ' K' : Type*} [Field κ] [Field K] [Algebra κ K] [Field κ'] [Field K']
  [Algebra κ' K'] (φ : K ≃+* K') (ψ : κ ≃+* κ')
  (hφ : ∀ c : κ, φ (algebraMap κ K c) = algebraMap κ' K' (ψ c))

include hφ in
lemma symm_algebraMap_tr (c : κ') : φ.symm (algebraMap κ' K' c) = algebraMap κ K (ψ.symm c) := by
  apply φ.injective
  rw [RingEquiv.apply_symm_apply, hφ, RingEquiv.apply_symm_apply]

/-- The place `φ(P)` (valuation ring `φ(𝒪_P)`). -/
def placeTr (P : Place κ K) : Place κ' K' :=
  ⟨P.1.comap (φ.symm : K' →+* K), fun h ↦ P.ne_top (top_unique fun x _ ↦ by
      have : φ x ∈ P.1.comap (φ.symm : K' →+* K) := by rw [h]; trivial
      simpa using (ValuationSubring.mem_comap.mp this)),
    fun c ↦ ValuationSubring.mem_comap.mpr (by
      change φ.symm (algebraMap κ' K' c) ∈ P.1
      rw [symm_algebraMap_tr φ ψ hφ]
      exact P.algebraMap_mem _)⟩

lemma mem_placeTr {P : Place κ K} {x : K'} :
    x ∈ (placeTr φ ψ hφ P).1 ↔ φ.symm x ∈ P.1 :=
  ValuationSubring.mem_comap

lemma mem_placeTr_apply {P : Place κ K} {x : K} : φ x ∈ (placeTr φ ψ hφ P).1 ↔ x ∈ P.1 := by
  rw [mem_placeTr, RingEquiv.symm_apply_apply]

include hφ in
/-- The inverse transport hypothesis. -/
lemma symm_tr : ∀ c : κ', φ.symm (algebraMap κ' K' c) = algebraMap κ K (ψ.symm c) :=
  symm_algebraMap_tr φ ψ hφ

/-- Places correspond under `φ`. -/
def placeTrEquiv : Place κ K ≃ Place κ' K' where
  toFun := placeTr φ ψ hφ
  invFun := placeTr φ.symm ψ.symm (symm_tr φ ψ hφ)
  left_inv P := Place.ext (by ext x; simp [mem_placeTr])
  right_inv Q := Place.ext (by ext x; simp [mem_placeTr])

@[simp]
lemma placeTrEquiv_apply (P : Place κ K) : placeTrEquiv φ ψ hφ P = placeTr φ ψ hφ P := rfl

/-- Divisors correspond under `φ`. -/
noncomputable def divTr : Divisor κ K ≃+ Divisor κ' K' :=
  Finsupp.domCongr (placeTrEquiv φ ψ hφ)

lemma divTr_apply_placeTr (D : Divisor κ K) (P : Place κ K) :
    divTr φ ψ hφ D (placeTr φ ψ hφ P) = D P := by
  change D ((placeTrEquiv φ ψ hφ).symm (placeTrEquiv φ ψ hφ P)) = D P
  rw [Equiv.symm_apply_apply]

lemma divTr_apply (D : Divisor κ K) (Q : Place κ' K') :
    divTr φ ψ hφ D Q = D ((placeTrEquiv φ ψ hφ).symm Q) := rfl

section Ord

variable [PerfectField κ] [IsFunctionField κ K] [PerfectField κ'] [IsFunctionField κ' K']

/-- **`ord_{φP}(φ x) = ord_P x`**. -/
theorem ord_placeTr (P : Place κ K) (x : K) : (placeTr φ ψ hφ P).ord (φ x) = P.ord x := by
  set w : Valuation K' ℤᵐ⁰ := P.valuation.comap (φ.symm : K' →+* K)
  have hw : ∀ y, y ∈ (placeTr φ ψ hφ P).1 ↔ w y ≤ 1 := by
    intro y
    rw [mem_placeTr, P.mem_iff_valuation_le_one]
    rfl
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπw : w (φ π) = WithZero.exp (-1) := by
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
    simp only [w, Valuation.comap_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    rw [P.valuation_eq_exp hπ0, hπ]
  rw [(placeTr φ ψ hφ P).ord_eq_neg_log w hw ⟨_, hπw⟩ (φ x)]
  simp only [w, Valuation.comap_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply, Place.ord]

lemma div_tr (f : K) : Divisor.div κ' (φ f) = divTr φ ψ hφ (Divisor.div κ f) := by
  ext Q
  rw [divTr_apply, Divisor.div_apply, Divisor.div_apply]
  conv_lhs => rw [← (placeTrEquiv φ ψ hφ).apply_symm_apply Q]
  exact ord_placeTr φ ψ hφ _ f

lemma map_principal_tr :
    (principal κ K).map (divTr φ ψ hφ).toAddMonoidHom = principal κ' K' := by
  ext D'
  simp only [AddSubgroup.mem_map, mem_principal]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨φ f, by simpa using hf, div_tr φ ψ hφ f⟩
  · rintro ⟨f', hf', rfl⟩
    refine ⟨Divisor.div κ (φ.symm f'), ⟨_, by simpa using hf', rfl⟩, ?_⟩
    change divTr φ ψ hφ _ = _
    rw [← div_tr, RingEquiv.apply_symm_apply]

/-- Divisor class groups correspond under `φ`. -/
noncomputable def picTr : Pic κ K ≃+ Pic κ' K' :=
  QuotientAddGroup.congr _ _ (divTr φ ψ hφ) (map_principal_tr φ ψ hφ)

@[simp]
lemma picTr_mk (D : Divisor κ K) :
    picTr φ ψ hφ (QuotientAddGroup.mk D) = QuotientAddGroup.mk (divTr φ ψ hφ D) := rfl

lemma picTr_mem_picTorsion {n : ℕ} {x : Pic κ K} (hx : x ∈ picTorsion κ K n) :
    picTr φ ψ hφ x ∈ picTorsion κ' K' n := by
  change n • picTr φ ψ hφ x = 0
  rw [← map_nsmul, show n • x = 0 from hx, map_zero]

/-- `φ` on `n`-torsion. -/
noncomputable def picTorsionTr (n : ℕ) : picTorsion κ K n →+ picTorsion κ' K' n :=
  ((picTr φ ψ hφ).toAddMonoidHom.comp (picTorsion κ K n).subtype).codRestrict _
    fun x ↦ picTr_mem_picTorsion φ ψ hφ x.2

@[simp]
lemma coe_picTorsionTr (n : ℕ) (x : picTorsion κ K n) :
    (picTorsionTr φ ψ hφ n x : Pic κ' K') = picTr φ ψ hφ x := rfl

end Ord

section Val

variable [IsAlgClosed κ] [IsFunctionField κ K] [IsAlgClosed κ'] [IsFunctionField κ' K']

/-- **`(φ x)(φ P) = ψ(x(P))`**. -/
theorem val_placeTr (P : Place κ K) (x : K) :
    Place.val (placeTr φ ψ hφ P) (φ x) = ψ (Place.val P x) := by
  by_cases hx : x ∈ P.1
  · rw [Place.val_eq_iff _ ((mem_placeTr_apply φ ψ hφ).mpr hx), ← hφ, ← map_sub,
      map_eq_zero_iff φ φ.injective, ord_placeTr]
    exact (Place.val_eq_iff P hx _).mp rfl
  · rw [Place.val_of_notMem P hx, Place.val_of_notMem _ (by rwa [mem_placeTr_apply]), map_zero]

lemma avoids_tr {f : K} {D : Divisor κ K} (h : Avoids f D) : Avoids (φ f) (divTr φ ψ hφ D) := by
  refine ⟨by simpa using h.1, fun Q hQ ↦ ?_⟩
  obtain ⟨P, rfl⟩ := (placeTrEquiv φ ψ hφ).surjective Q
  rw [placeTrEquiv_apply, divTr_apply_placeTr] at hQ
  rw [placeTrEquiv_apply, ord_placeTr]
  exact h.2 P hQ

/-- **`(φ f)(φ D) = ψ(f(D))`**. -/
theorem evalDiv_tr (f : K) (D : Divisor κ K) :
    evalDiv (φ f) (divTr φ ψ hφ D) = ψ (evalDiv f D) := by
  classical
  rw [evalDiv, evalDiv, divTr, Finsupp.domCongr_apply, Finsupp.prod_equivMapDomain,
    Finsupp.prod, Finsupp.prod, map_prod]
  simp only [placeTrEquiv_apply, val_placeTr, map_zpow₀]

/-- Transport of a representative. -/
noncomputable def TorsRep.tr {n : ℕ} {a : Pic κ K} (r : TorsRep n a) :
    TorsRep n (picTr φ ψ hφ a) where
  D := divTr φ ψ hφ r.D
  f := φ r.f
  f_ne := by simpa using r.f_ne
  mk_eq := by rw [← picTr_mk, r.mk_eq]
  nsmul_eq := by rw [← map_nsmul, r.nsmul_eq, div_tr (κ := κ)]

omit [IsAlgClosed κ] [IsFunctionField κ K] [IsAlgClosed κ'] [IsFunctionField κ' K'] in
lemma DisjSupp.tr {D E : Divisor κ K} (h : DisjSupp D E) :
    DisjSupp (divTr φ ψ hφ D) (divTr φ ψ hφ E) := fun Q ↦ by
  rw [divTr_apply, divTr_apply]; exact h _

/-- **Transport of the Weil pairing**: `e_n(φ a, φ b) = ψ(e_n(a, b))`. -/
theorem weilPairing_tr {n : ℕ} [NeZero n] (a b : picTorsion κ K n) :
    weilPairing n (picTorsionTr φ ψ hφ n a) (picTorsionTr φ ψ hφ n b) =
      ψ (weilPairing n a b) := by
  obtain ⟨r, s, h⟩ := exists_disj_reps a.2 b.2
  rw [weilPairing_eq a b r s h,
    weilPairing_eq _ _ (r.tr φ ψ hφ) (s.tr φ ψ hφ) (h.tr φ ψ hφ), pairVal, pairVal, map_div₀]
  exact congrArg₂ (· / ·) (evalDiv_tr φ ψ hφ _ _) (evalDiv_tr φ ψ hφ _ _)

end Val

end CurvesJacobian
