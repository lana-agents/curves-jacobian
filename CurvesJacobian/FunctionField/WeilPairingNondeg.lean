/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.WeilPairingTransport

/-!
# Nondegeneracy of the Weil pairing via the generic point

Let `K/κ` be a function field over an algebraically closed field `κ`. Nondegeneracy of the
Weil pairing `e_n` on `Pic(K)[n]` is deduced from a *generic point datum*: an algebraically closed
field `K' ⊇ K` (embedding `j`) and the function field `L/K'` of the base change of the curve to
`K'` (`ι : K → L`), with

* the base change `P ↦ β P` of places, compatible with orders and values; all zeros and poles
  of functions from `K` lie at base-changed places;
* the **generic point**: a place `η` of `L` at which every `f ∈ K` takes the value `j f`;
* the semilinear action of `Aut(K'/K)` on `L` fixing `K`, the places `β P` and `η`;
* divisibility of `Pic⁰(L)`, `#Pic(K)[n] ≥ #Pic(L)[n]`, `Pic(L)[n]` finite, and
  `K'^{Aut(K'/K)} = K`.

**Key identity** (`GenericPointDatum.exists_kummer`): for `a ∈ Pic(K)[n]` with `n D = div f`
and `αⁿ = f` in `K'`, and every `δ ∈ Aut(K'/K)`,

  `δ(α) / α = e_n(β a, [δ Z − Z])`,  where `n Z ~ η − β P₀`.

Proof: `c = f(Z) / h(β D)` (`n Z = η − β P₀ + div h`) satisfies `cⁿ = f / f(P₀)` by Weil
reciprocity, so `c / α ∈ κ`, and `δ(c) / c = f(δZ − Z) / (δh/h)(βD)`.

Consequences: `β : Pic(K)[n] → Pic(L)[n]` is injective (if `β a = 0` then `α` is
`Aut(K'/K)`-invariant, so `f` is an `n`-th power), hence bijective by counting, and **`e_n` is
nondegenerate** (`GenericPointDatum.weilPairing_nondegenerate`): if `e_n(a, ·) = 1` then
`e_n(β a, ·) = 1` on `Pic(L)[n] = β(Pic(K)[n])`, so again `α` is invariant and `a = 0`.
This is the divisor-level form of the classical identification of the Kummer cover of the
`[n]`-division points of `[η − P₀]` (cf. Milne, *Abelian Varieties*, §13).
-/

open WeilCurves.FunctionField

namespace CurvesJacobian

variable (κ K K' L : Type*) [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K]
  [IsFunctionField κ K] [Field K'] [IsAlgClosed K'] [Field L] [Algebra K' L]
  [IsFunctionField K' L]

/-- A **generic point datum** for the function field `K/κ` (see the module docstring). -/
structure GenericPointDatum where
  /-- The embedding `K ⊆ K'`. -/
  j : K →+* K'
  /-- The function field map `K → L` (pull-back along `C_{K'} → C_κ`). -/
  ι : K →+* L
  ι_algebraMap : ∀ c : κ, ι (algebraMap κ K c) = algebraMap K' L (j (algebraMap κ K c))
  /-- Base change of places. -/
  β : Place κ K → Place K' L
  β_injective : Function.Injective β
  ord_β : ∀ P f, (β P).ord (ι f) = P.ord f
  ord_of_notMem : ∀ (Q : Place K' L) (f : K), f ≠ 0 → (∀ P, Q ≠ β P) → Q.ord (ι f) = 0
  val_β : ∀ P f, f ∈ P.1 → Place.val (β P) (ι f) = j (algebraMap κ K (Place.val P f))
  /-- The generic point. -/
  η : Place K' L
  η_ne : ∀ P, η ≠ β P
  val_η : ∀ f, Place.val η (ι f) = j f
  /-- The action of `Aut(K'/K)` on `L`. -/
  act : ∀ δ : K' ≃+* K', (∀ x, δ (j x) = j x) → L ≃+* L
  act_ι : ∀ δ hδ f, act δ hδ (ι f) = ι f
  act_algebraMap : ∀ δ hδ c, act δ hδ (algebraMap K' L c) = algebraMap K' L (δ c)
  act_β : ∀ δ hδ P, placeTr (act δ hδ) δ (act_algebraMap δ hδ) (β P) = β P
  act_η : ∀ δ hδ, placeTr (act δ hδ) δ (act_algebraMap δ hδ) η = η
  divisible : ∀ (n : ℕ), n ≠ 0 → ∀ x : Pic K' L, Pic.deg K' L x = 0 → ∃ y, n • y = x
  finite : ∀ n : ℕ, n ≠ 0 → Finite (picTorsion K' L n)
  card_le : ∀ n : ℕ, n ≠ 0 → Nat.card (picTorsion K' L n) ≤ Nat.card (picTorsion κ K n)
  fixed : ∀ c : K', (∀ δ : K' ≃+* K', (∀ x, δ (j x) = j x) → δ c = c) → c ∈ Set.range j

namespace GenericPointDatum

variable {κ K K' L} (B : GenericPointDatum κ K K' L)

/-- `κ → K'`. -/
abbrev jκ : κ →+* K' := B.j.comp (algebraMap κ K)

/-- Push-forward of divisors along `β`. -/
noncomputable def divMap : Divisor κ K →+ Divisor K' L := Finsupp.mapDomain.addMonoidHom B.β

lemma divMap_apply_β (D : Divisor κ K) (P : Place κ K) : B.divMap D (B.β P) = D P :=
  Finsupp.mapDomain_apply B.β_injective D P

lemma divMap_apply_of_notMem (D : Divisor κ K) {Q : Place K' L} (hQ : ∀ P, Q ≠ B.β P) :
    B.divMap D Q = 0 :=
  Finsupp.mapDomain_notin_range _ _ (by rintro ⟨P, rfl⟩; exact hQ P rfl)

lemma ι_ne_zero {f : K} (hf : f ≠ 0) : B.ι f ≠ 0 := (map_ne_zero B.ι).mpr hf

lemma div_ι (f : K) : Divisor.div K' (B.ι f) = B.divMap (Divisor.div κ f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  ext Q
  by_cases hQ : ∃ P, Q = B.β P
  · obtain ⟨P, rfl⟩ := hQ
    rw [Divisor.div_apply, divMap_apply_β, Divisor.div_apply, B.ord_β]
  · simp only [not_exists] at hQ
    rw [Divisor.div_apply, divMap_apply_of_notMem _ _ hQ, B.ord_of_notMem Q f hf hQ]

lemma divMap_mem_principal {D : Divisor κ K} (hD : D ∈ principal κ K) :
    B.divMap D ∈ principal K' L := by
  obtain ⟨f, hf, rfl⟩ := mem_principal.mp hD
  rw [← div_ι]
  exact div_mem_principal (B.ι_ne_zero hf)

/-- Base change on divisor classes. -/
noncomputable def picMap : Pic κ K →+ Pic K' L :=
  QuotientAddGroup.map _ _ B.divMap fun _ hD ↦ B.divMap_mem_principal hD

@[simp]
lemma picMap_mk (D : Divisor κ K) :
    B.picMap (QuotientAddGroup.mk D) = QuotientAddGroup.mk (B.divMap D) := rfl

/-- Base change on `n`-torsion. -/
noncomputable def picTorsionMap (n : ℕ) : picTorsion κ K n →+ picTorsion K' L n :=
  (B.picMap.comp (picTorsion κ K n).subtype).codRestrict _ fun x ↦ by
    change n • B.picMap x = 0
    rw [← map_nsmul, show n • (x : Pic κ K) = 0 from x.2, map_zero]

@[simp]
lemma coe_picTorsionMap (n : ℕ) (x : picTorsion κ K n) :
    (B.picTorsionMap n x : Pic K' L) = B.picMap x := rfl

/-- Values at base-changed divisors. -/
lemma evalDiv_ι {f : K} {E : Divisor κ K} (hf : Avoids f E) :
    evalDiv (B.ι f) (B.divMap E) = B.jκ (evalDiv f E) := by
  classical
  rw [evalDiv, divMap, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.prod_mapDomain_index_inj B.β_injective, evalDiv, Finsupp.prod, Finsupp.prod,
    map_prod]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  rw [B.val_β P f (Place.mem_of_ord_eq_zero P (hf.2 P (Finsupp.mem_support_iff.mp hP))),
    map_zpow₀]
  rfl

lemma DisjSupp.divMap {D E : Divisor κ K} (h : DisjSupp D E) :
    DisjSupp (B.divMap D) (B.divMap E) := fun Q ↦ by
  by_cases hQ : ∃ P, Q = B.β P
  · obtain ⟨P, rfl⟩ := hQ
    rw [divMap_apply_β, divMap_apply_β]; exact h P
  · simp only [not_exists] at hQ
    exact Or.inl (B.divMap_apply_of_notMem D hQ)

variable {n : ℕ}

/-- Base change of a representative. -/
noncomputable def repMap {a : Pic κ K} (r : TorsRep n a) : TorsRep n (B.picMap a) where
  D := B.divMap r.D
  f := B.ι r.f
  f_ne := B.ι_ne_zero r.f_ne
  mk_eq := by rw [← picMap_mk, r.mk_eq]
  nsmul_eq := by rw [← map_nsmul, r.nsmul_eq, div_ι]

/-- **Compatibility of the Weil pairing with base change.** -/
theorem weilPairing_map [NeZero n] (a b : picTorsion κ K n) :
    weilPairing n (B.picTorsionMap n a) (B.picTorsionMap n b) = B.jκ (weilPairing n a b) := by
  obtain ⟨r, s, h⟩ := exists_disj_reps a.2 b.2
  rw [weilPairing_eq a b r s h,
    weilPairing_eq _ _ (B.repMap r) (B.repMap s) (DisjSupp.divMap B h), pairVal, pairVal,
    map_div₀]
  exact congrArg₂ (· / ·) (B.evalDiv_ι (avoids_of_disjSupp r.f_ne r.nsmul_eq h))
    (B.evalDiv_ι (avoids_of_disjSupp s.f_ne s.nsmul_eq h.symm))

/-- An `n`-th root (in `K'`) of a constant is a constant. -/
lemma mem_range_of_pow_eq (hn : n ≠ 0) {y : K'} {u : κ} (hy : y ^ n = B.jκ u) :
    y ∈ B.jκ.range := by
  have hf0 : (Polynomial.X ^ n - Polynomial.C u : Polynomial κ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) u
  refine (IsAlgClosed.splits _).mem_range_of_isRoot hf0 ?_
  simp [Polynomial.IsRoot, hy]

/-- Zeros and poles of `ι f` lie at base-changed places. -/
lemma exists_eq_β_of_ord_ne_zero {f : K} (hf : f ≠ 0) {Q : Place K' L} (hQ : Q.ord (B.ι f) ≠ 0) :
    ∃ P, Q = B.β P ∧ P.ord f ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and] at h
  by_cases hQ' : ∃ P, Q = B.β P
  · obtain ⟨P, rfl⟩ := hQ'
    exact h P rfl (by rwa [B.ord_β] at hQ)
  · simp only [not_exists] at hQ'
    exact hQ (B.ord_of_notMem Q f hf hQ')

lemma ord_η (f : K) : B.η.ord (B.ι f) = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  by_contra h
  obtain ⟨P, hP, -⟩ := B.exists_eq_β_of_ord_ne_zero hf h
  exact B.η_ne P hP

/-- The place `φ(Q)` for the action of `δ`. -/
abbrev actPlace (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) : Place K' L ≃ Place K' L :=
  placeTrEquiv (B.act δ hδ) δ (B.act_algebraMap δ hδ)

lemma actPlace_symm_β (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) (P : Place κ K) :
    (B.actPlace δ hδ).symm (B.β P) = B.β P := by
  rw [Equiv.symm_apply_eq]; exact (B.act_β δ hδ P).symm

lemma actPlace_symm_η (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) :
    (B.actPlace δ hδ).symm B.η = B.η := by
  rw [Equiv.symm_apply_eq]; exact (B.act_η δ hδ).symm

lemma actPlace_symm_ne_β (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) {Q : Place K' L}
    (hQ : ∀ P, Q ≠ B.β P) (P : Place κ K) : (B.actPlace δ hδ).symm Q ≠ B.β P := by
  intro h
  rw [Equiv.symm_apply_eq] at h
  exact hQ P (h.trans (B.act_β δ hδ P))

/-- The action fixes base-changed divisors. -/
lemma divTr_divMap (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) (D : Divisor κ K) :
    divTr (B.act δ hδ) δ (B.act_algebraMap δ hδ) (B.divMap D) = B.divMap D := by
  ext Q
  rw [divTr_apply]
  by_cases hQ : ∃ P, Q = B.β P
  · obtain ⟨P, rfl⟩ := hQ
    rw [B.actPlace_symm_β δ hδ P]
  · simp only [not_exists] at hQ
    rw [B.divMap_apply_of_notMem D hQ, B.divMap_apply_of_notMem D (B.actPlace_symm_ne_β δ hδ hQ)]

lemma divTr_single (δ : K' ≃+* K') (hδ : ∀ x, δ (B.j x) = B.j x) (Q : Place K' L) (m : ℤ) :
    divTr (B.act δ hδ) δ (B.act_algebraMap δ hδ) (Finsupp.single Q m) =
      Finsupp.single (B.actPlace δ hδ Q) m :=
  Finsupp.equivMapDomain_single _ _ _

/-- **The key identity**: `δ(α)/α = e_n(β a, [δ Z − Z])` for `αⁿ = f`, `n D = div f`. -/
theorem exists_kummer [NeZero n] (a : picTorsion κ K n) (r : TorsRep n (a : Pic κ K))
    (P₀ : Place κ K) (hP₀ : r.D P₀ = 0) {α : K'} (hα : α ^ n = B.j r.f) (δ : K' ≃+* K')
    (hδ : ∀ x, δ (B.j x) = B.j x) :
    ∃ b : picTorsion K' L n, δ α / α = weilPairing n (B.picTorsionMap n a) b := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  set A := B.divMap r.D with hAdef
  set F := B.ι r.f with hFdef
  have hF0 : F ≠ 0 := B.ι_ne_zero r.f_ne
  have hA : n • A = Divisor.div K' F := by rw [← map_nsmul, r.nsmul_eq, div_ι]
  have hordD : ∀ P, P.ord r.f = n * r.D P := fun P ↦ by
    have h4 := congrArg (fun E : Divisor κ K ↦ E P) r.nsmul_eq
    simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
    exact h4.symm
  have hFsupp : ∀ Q : Place K' L, Q.ord F ≠ 0 → ∃ P, Q = B.β P ∧ r.D P ≠ 0 := by
    intro Q hQ
    obtain ⟨P, rfl, hP⟩ := B.exists_eq_β_of_ord_ne_zero r.f_ne hQ
    exact ⟨P, rfl, fun h0 ↦ hP (by rw [hordD, h0, mul_zero])⟩
  have hβne : ∀ P, r.D P ≠ 0 → B.β P₀ ≠ B.β P := fun P hP he ↦
    hP (by rw [← B.β_injective he]; exact hP₀)
  -- the divisor `η − β P₀`
  set E₀ : Divisor K' L := Finsupp.single B.η 1 - Finsupp.single (B.β P₀) 1 with hE₀def
  have hE₀ : Pic.deg K' L (QuotientAddGroup.mk E₀) = 0 := by
    rw [Pic.deg_mk, hE₀def, Divisor.deg_sub, Divisor.deg_single, Divisor.deg_single,
      Place.deg_eq_one, Place.deg_eq_one, sub_self]
  have hE₀β : ∀ P, r.D P ≠ 0 → E₀ (B.β P) = 0 := fun P hP ↦ by
    rw [hE₀def, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (B.η_ne P), if_neg (hβne P hP), sub_zero]
  obtain ⟨y, hy⟩ := B.divisible n hn _ hE₀
  obtain ⟨Z₀, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨h₁, h₁0, hZ⟩ := exists_add_div_avoid Z₀ (r.D.support.image B.β)
  set Z := Z₀ + Divisor.div K' h₁ with hZdef
  have hZβ : ∀ P, r.D P ≠ 0 → Z (B.β P) = 0 := fun P hP ↦
    hZ _ (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hP))
  have hmk : (QuotientAddGroup.mk (n • Z - E₀) : Pic K' L) = 0 := by
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, hZdef, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).mpr (div_mem_principal h₁0), add_zero, hy, sub_self]
  obtain ⟨h, h0, hh⟩ := mem_principal.mp ((QuotientAddGroup.eq_zero_iff _).mp hmk)
  have hnZ : n • Z = E₀ + Divisor.div K' h := by rw [hh]; abel
  -- zeros and poles of `F` avoid `Z`, `E₀`, `div h`
  have hkey : ∀ Q : Place K' L, Q.ord F ≠ 0 → Z Q = 0 ∧ E₀ Q = 0 ∧ Q.ord h = 0 := by
    intro Q hQ
    obtain ⟨P, rfl, hP⟩ := hFsupp Q hQ
    refine ⟨hZβ P hP, hE₀β P hP, ?_⟩
    have h5 := congrArg (fun E : Divisor K' L ↦ E (B.β P)) hnZ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, Divisor.div_apply, hZβ P hP,
      hE₀β P hP, smul_zero, zero_add] at h5
    exact h5.symm
  have hav : ∀ E : Divisor K' L, (∀ Q, Q.ord F ≠ 0 → E Q = 0) → Avoids F E :=
    fun E hE ↦ ⟨hF0, fun Q hQ ↦ by by_contra hc; exact hQ (hE Q hc)⟩
  have hFZ : Avoids F Z := hav Z fun Q hQ ↦ (hkey Q hQ).1
  have hFE₀ : Avoids F E₀ := hav E₀ fun Q hQ ↦ (hkey Q hQ).2.1
  have hFh : Avoids F (Divisor.div K' h) := hav _ fun Q hQ ↦ by
    rw [Divisor.div_apply]; exact (hkey Q hQ).2.2
  have hAF : ∀ Q, A Q ≠ 0 → Q.ord F ≠ 0 := fun Q hQ hc ↦ by
    have h5 := congrArg (fun E : Divisor K' L ↦ E Q) hA
    simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply, hc] at h5
    exact hQ ((mul_eq_zero.mp h5).resolve_left (by exact_mod_cast hn))
  have hhA : Avoids h A := ⟨h0, fun Q hQ ↦ (hkey Q (hAF Q hQ)).2.2⟩
  have hrec := weil_reciprocity (κ := K') hF0 h0 fun Q ↦ by
    by_cases hQ : Q.ord F = 0
    · exact Or.inl hQ
    · exact Or.inr (hkey Q hQ).2.2
  -- the constant `c`
  set c := evalDiv F Z / evalDiv h A with hcdef
  have hP₀f : r.f ∈ P₀.1 := Place.mem_of_ord_eq_zero P₀ (by rw [hordD, hP₀, mul_zero])
  have hv₀ : Place.val P₀ r.f ≠ 0 :=
    Place.val_ne_zero P₀ r.f_ne (by rw [hordD, hP₀, mul_zero])
  have hc : c ^ n = B.j r.f / B.jκ (Place.val P₀ r.f) := by
    have e1 : evalDiv F Z ^ n = evalDiv F E₀ * evalDiv F (Divisor.div K' h) := by
      rw [← evalDiv_nsmul hFZ, hnZ, evalDiv_add hFE₀ hFh]
    have e2 : evalDiv h A ^ n = evalDiv F (Divisor.div K' h) := by
      rw [← evalDiv_nsmul hhA, hA, ← hrec]
    have hs1 : Avoids F (Finsupp.single B.η 1) := hav _ fun Q hQ ↦ by
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hQ (B.ord_η r.f)
    have hs2 : Avoids F (Finsupp.single (B.β P₀) 1) := hav _ fun Q hQ ↦ by
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hQ (by rw [hFdef, B.ord_β, hordD, hP₀, mul_zero])
    have e3 : evalDiv F E₀ = B.j r.f / B.jκ (Place.val P₀ r.f) := by
      rw [hE₀def, evalDiv_sub hs1 hs2, evalDiv_single, evalDiv_single, zpow_one, zpow_one,
        hFdef, B.val_η, B.val_β P₀ r.f hP₀f]
      rfl
    have hne : evalDiv F (Divisor.div K' h) ≠ 0 := evalDiv_ne_zero hFh
    rw [hcdef, div_pow, e1, e2, e3, mul_div_assoc, div_self hne, mul_one]
  have hjf : B.j r.f ≠ 0 := (map_ne_zero B.j).mpr r.f_ne
  have hα0 : α ≠ 0 := fun h0' ↦ by rw [h0', zero_pow hn] at hα; exact hjf hα.symm
  have hcα : (c / α) ^ n = B.jκ (Place.val P₀ r.f)⁻¹ := by
    rw [div_pow, hc, hα, map_inv₀]
    field_simp
  obtain ⟨w, hw⟩ := B.mem_range_of_pow_eq hn hcα
  have hδw : δ (c / α) = c / α := by rw [← hw]; exact hδ _
  -- the action
  set φ := B.act δ hδ with hφdef
  have hφ := B.act_algebraMap δ hδ
  set Z' := divTr φ δ hφ Z with hZ'def
  have hE₀' : divTr φ δ hφ E₀ = E₀ := by
    rw [hE₀def, map_sub, B.divTr_single, B.divTr_single]
    simp only [placeTrEquiv_apply, B.act_η, B.act_β]
  have hnZ' : n • Z' = E₀ + Divisor.div K' (φ h) := by
    rw [hZ'def, ← map_nsmul, hnZ, map_add, hE₀', div_tr (κ := K')]
  have hδc : δ c = evalDiv F Z' / evalDiv (φ h) A := by
    rw [hcdef, map_div₀, ← evalDiv_tr φ δ hφ F Z, ← evalDiv_tr φ δ hφ h A, hFdef, B.act_ι,
      B.divTr_divMap]
  -- the class `b = [Z' − Z]`
  have hφh0 : φ h ≠ 0 := (map_ne_zero φ).mpr h0
  have hb : n • (Z' - Z) = Divisor.div K' (φ h / h) := by
    rw [smul_sub, hnZ', hnZ, Divisor.div_div hφh0 h0]; abel
  have hbmem : (QuotientAddGroup.mk (Z' - Z) : Pic K' L) ∈ picTorsion K' L n := by
    change n • (QuotientAddGroup.mk (Z' - Z) : Pic K' L) = 0
    rw [← QuotientAddGroup.mk_nsmul, hb, QuotientAddGroup.eq_zero_iff]
    exact div_mem_principal (div_ne_zero hφh0 h0)
  let s : TorsRep n (QuotientAddGroup.mk (Z' - Z) : Pic K' L) :=
    ⟨Z' - Z, φ h / h, div_ne_zero hφh0 h0, rfl, hb⟩
  have hZ'β : ∀ P, r.D P ≠ 0 → Z' (B.β P) = 0 := fun P hP ↦ by
    rw [hZ'def, divTr_apply]
    change Z ((B.actPlace δ hδ).symm (B.β P)) = 0
    rw [B.actPlace_symm_β δ hδ P]; exact hZβ P hP
  have hdisj : DisjSupp (B.repMap r).D s.D := fun Q ↦ by
    by_cases hQ : A Q = 0
    · exact Or.inl hQ
    · right
      obtain ⟨P, rfl, hP⟩ := hFsupp Q (hAF Q hQ)
      change Z' (B.β P) - Z (B.β P) = 0
      rw [hZ'β P hP, hZβ P hP, sub_zero]
  refine ⟨⟨_, hbmem⟩, ?_⟩
  rw [weilPairing_eq (B.picTorsionMap n a) ⟨_, hbmem⟩ (B.repMap r) s hdisj, pairVal]
  have hFZ' : Avoids F Z' := hav Z' fun Q hQ ↦ by
    obtain ⟨P, rfl, hP⟩ := hFsupp Q hQ
    exact hZ'β P hP
  have hφhA : Avoids (φ h) A := ⟨hφh0, fun Q hQ ↦ by
    obtain ⟨P, rfl, hP⟩ := hFsupp Q (hAF Q hQ)
    have h6 := ord_placeTr φ δ hφ (B.β P) h
    rw [B.act_β δ hδ P] at h6
    rw [h6]
    exact hhA.2 _ hQ⟩
  change δ α / α = evalDiv F (Z' - Z) / evalDiv (φ h / h) A
  rw [evalDiv_sub hFZ' hFZ, evalDiv_div hφhA hhA]
  have hcα0 : c / α ≠ 0 := by
    intro h0'
    rw [h0', zero_pow hn] at hcα
    exact (inv_ne_zero hv₀) ((map_eq_zero_iff _ B.jκ.injective).mp hcα.symm)
  have hhA0 : evalDiv h A ≠ 0 := evalDiv_ne_zero hhA
  have hφhA0 : evalDiv (φ h) A ≠ 0 := evalDiv_ne_zero hφhA
  have hFZ0 : evalDiv F Z ≠ 0 := evalDiv_ne_zero hFZ
  have e : evalDiv F Z' / evalDiv F Z / (evalDiv (φ h) A / evalDiv h A) = δ c / c := by
    rw [hδc, hcdef]; field_simp
  rw [e]
  have hc0 : c ≠ 0 := fun h0' ↦ hcα0 (by rw [h0', zero_div])
  conv_rhs => rw [show c = α * (c / α) by field_simp]
  rw [map_mul, hδw]
  field_simp

/-- If `e_n(β a, ·) = 1` on `Pic(L)[n]`, then `a = 0`. -/
theorem eq_zero_of_forall_weilPairing_map [NeZero n] (a : picTorsion κ K n)
    (h : ∀ b : picTorsion K' L n, weilPairing n (B.picTorsionMap n a) b = 1) : a = 0 := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Place κ K))
  obtain ⟨r, hr⟩ := TorsRep.exists_avoid a.2 {P₀}
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (B.j r.f) (Nat.pos_of_ne_zero hn)
  have hfix : ∀ δ : K' ≃+* K', (∀ x, δ (B.j x) = B.j x) → δ α = α := by
    intro δ hδ
    obtain ⟨b, hb⟩ := B.exists_kummer a r P₀ (hr P₀ (Finset.mem_singleton_self _)) hα δ hδ
    rw [h b] at hb
    have hα0 : α ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow hn] at hα
      exact (map_ne_zero B.j).mpr r.f_ne hα.symm
    exact (div_eq_one_iff_eq hα0).mp hb
  obtain ⟨u, hu⟩ := B.fixed α hfix
  have hfu : r.f = u ^ n := B.j.injective (by rw [map_pow, hu, hα])
  have hu0 : u ≠ 0 := fun h0 ↦ r.f_ne (by rw [hfu, h0, zero_pow hn])
  have hD : r.D = Divisor.div κ u := by
    apply nsmul_injective (Nat.pos_of_ne_zero hn)
    change n • r.D = n • Divisor.div κ u
    rw [r.nsmul_eq, hfu, Divisor.div_pow]
  apply Subtype.ext
  change (a : Pic κ K) = 0
  rw [← r.mk_eq, hD, QuotientAddGroup.eq_zero_iff]
  exact div_mem_principal hu0

/-- **Base change is injective on `n`-torsion.** -/
theorem picTorsionMap_injective [NeZero n] : Function.Injective (B.picTorsionMap n) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  exact B.eq_zero_of_forall_weilPairing_map a fun b ↦ by rw [ha, weilPairing_zero_left]

/-- **Base change is bijective on `n`-torsion** (counting). -/
theorem picTorsionMap_bijective [NeZero n] : Function.Bijective (B.picTorsionMap n) := by
  haveI := B.finite n (NeZero.ne n)
  exact B.picTorsionMap_injective.bijective_of_nat_card_le (B.card_le n (NeZero.ne n))

include B in
/-- **Nondegeneracy of the Weil pairing**: if `e_n(a, b) = 1` for all `b`, then `a = 0`. -/
theorem weilPairing_nondegenerate [NeZero n] (a : picTorsion κ K n)
    (h : ∀ b : picTorsion κ K n, weilPairing n a b = 1) : a = 0 := by
  refine B.eq_zero_of_forall_weilPairing_map a fun b' ↦ ?_
  obtain ⟨b, rfl⟩ := B.picTorsionMap_bijective.2 b'
  rw [B.weilPairing_map, h b, map_one]

end GenericPointDatum

end CurvesJacobian
