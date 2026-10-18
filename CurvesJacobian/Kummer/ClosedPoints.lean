/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.Values
import CurvesJacobian.Kummer.PointRestriction
import CurvesJacobian.Galois.FunctionFieldF
import CurvesJacobian.Cusp.DecompositionInertia
import ContinuousKummerTheory.Curve.ClosedPoint
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# [AbsTopIII] Prop. 1.8(i), "only if", at points over finite extensions `k_x`

[AbsTopIII] Prop. 1.8(i) (T3 l.2078–2087): if `η = κ_U(f)` for a nonconstant function `f`, there
are a positive multiple `η† = η^N` and points `x₁, x₂ ∈ U(k_x)`, `k_x / k` finite, with
`η†|x₁ = 0` and `η†|x₂ ≠ 0`. The proof (l.2099–2106) uses that a nonconstant function takes
(almost) every value at points of `U`. In `pi1`'s Galois model:

* `CurvesJacobian.Kummer.exists_place_isPrimitiveRoot`, `exists_place_residue_eq`: a function `f`
  transcendental over `k` has, for every `n ≥ 1`, a zero of `Φ_n(f)` (a place where `f(P)` is a
  primitive `n`-th root of unity) and, for every `c ∈ k`, a place with `f(P) = c`; these places
  are pairwise distinct, so infinitely many of them avoid the finitely many cusps (poles of `t`)
  (`exists_place_isPrimitiveRoot_notMem`, `exists_place_natCast_notMem`);
* `CurvesJacobian.Kummer.isAlgebraic_residue_of_trdeg_le_one`: the residue field of a proper
  valuation subring `W ⊇ k` of a field of transcendence degree `≤ 1` over `k` is algebraic over
  `k` (no algebraic closedness of `k` needed);
* `CurvesJacobian.Kummer.finiteDimensional_pointField`: for a place `W` of `Ω` above a place `P`
  of `F`, the residue field `k_x = κ(W ∩ F) ⊆ κ(W)` is finite over `k`;
* `CurvesJacobian.Kummer.exists_restrict_kummerMap_of_transcendental` (**Prop. 1.8(i), "only
  if"**): for `k` torally Kummer-faithful and `f ∈ Γ(U, 𝒪^×)` nonconstant there are `N ≥ 1` and
  two closed points `x₁, x₂` of `U` with finite residue fields such that the restrictions of
  `κ_U(f^N)` along `D_{x₁} → Π_U` vanish at every level, while some restriction along
  `D_{x₂} → Π_U` does not (`η|_x` vanishes iff its restriction along `D_x → Π_U` does, see
  `ContinuousKummerTheory/Curve/ClosedPoint.lean`).

The NF-conditions of Def. 1.7 are not imposed here.
-/

open WeilCurves.FunctionField Polynomial IsLocalRing KummerTheory Curve AffOrbicurve

namespace CurvesJacobian.Kummer

section Places

variable {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [PerfectField κ] [IsFunctionField κ K]

omit [PerfectField κ] [IsFunctionField κ K] in
/-- Values of polynomials: `(q(x))(P) = q(x(P))`. -/
lemma residue_aeval (P : Place κ K) {x : K} (hx : x ∈ P.1) (q : κ[X]) :
    ∃ h : aeval x q ∈ P.1, P.residue ⟨_, h⟩ = aeval (P.residue ⟨x, hx⟩) q := by
  have hcomp : (P.1.subtype : P.1 →+* K).comp P.baseHom = algebraMap κ K :=
    RingHom.ext fun c => P.coe_baseHom c
  have e : aeval x q = ((eval₂ P.baseHom ⟨x, hx⟩ q : P.1) : K) := by
    change _ = (P.1.subtype : P.1 →+* K) (eval₂ P.baseHom ⟨x, hx⟩ q)
    rw [hom_eval₂, hcomp, aeval_def]
    rfl
  refine ⟨e ▸ (eval₂ P.baseHom ⟨x, hx⟩ q).2, ?_⟩
  have e' : (⟨_, e ▸ (eval₂ P.baseHom ⟨x, hx⟩ q).2⟩ : P.1) = eval₂ P.baseHom ⟨x, hx⟩ q :=
    Subtype.ext e
  rw [e', hom_eval₂, aeval_def]
  rfl

omit [PerfectField κ] [IsFunctionField κ K] in
/-- If `q(x) ∈ O_P` for a monic `q ∈ κ[X]` of positive degree, then `x ∈ O_P` (`O_P` is
integrally closed). -/
lemma mem_of_aeval_mem (P : Place κ K) {x : K} {q : κ[X]} (hq : q.Monic) (hq0 : 0 < q.natDegree)
    (h : aeval x q ∈ P.1) : x ∈ P.1 := by
  have hint : IsIntegral P.1 x := by
    refine ⟨q.map P.baseHom - C ⟨_, h⟩, ?_, ?_⟩
    · refine (hq.map _).sub_of_left ?_
      rw [degree_map_eq_of_injective P.baseHom.injective]
      exact lt_of_le_of_lt degree_C_le (by exact_mod_cast natDegree_pos_iff_degree_pos.1 hq0)
    · have hcomp : (algebraMap P.1 K).comp P.baseHom = algebraMap κ K :=
        RingHom.ext fun c => P.coe_baseHom c
      rw [eval₂_sub, eval₂_map, hcomp, eval₂_C, ← aeval_def, sub_eq_zero]
      rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

/-- A nonconstant function `g` has a zero: `g ∈ O_P` with residue `0`. -/
lemma exists_place_residue_eq_zero {g : K} (hg : Transcendental κ g) :
    ∃ (P : Place κ K) (hgP : g ∈ P.1), P.residue ⟨g, hgP⟩ = 0 := by
  obtain ⟨P, hP⟩ := Place.exists_ord_pos hg
  have hgP : g ∈ P.1 := P.mem_of_ord_nonneg hP.le
  refine ⟨P, hgP, ?_⟩
  rw [Place.residue_eq_zero_iff]
  exact (P.ord_pos_iff_mem_maximalIdeal (a := ⟨g, hgP⟩) (ne_zero_of_transcendental hg)).1 hP

variable [CharZero κ]

omit [PerfectField κ] [IsFunctionField κ K] in
lemma charZero_residueField (P : Place κ K) : CharZero P.ResidueField :=
  charZero_of_injective_algebraMap (algebraMap κ P.ResidueField).injective

/-- **`f` takes a primitive `n`-th root of unity as a value**: for `f` transcendental and
`n ≥ 1`, some place `P` has `f ∈ O_P` and `f(P)` a primitive `n`-th root of unity (a zero of
`Φ_n(f)`). -/
lemma exists_place_isPrimitiveRoot {f : K} (hf : Transcendental κ f) {n : ℕ} (hn : 0 < n) :
    ∃ (P : Place κ K) (hfP : f ∈ P.1), IsPrimitiveRoot (P.residue ⟨f, hfP⟩) n := by
  have hdeg : (cyclotomic n κ).natDegree ≠ 0 := by
    rw [natDegree_cyclotomic]
    exact (Nat.totient_pos.2 hn).ne'
  have hg : Transcendental κ (aeval f (cyclotomic n κ)) :=
    hf.aeval _ hdeg (by rw [(cyclotomic.monic n κ).leadingCoeff]; exact one_mem _)
  obtain ⟨P, hgP, hres⟩ := exists_place_residue_eq_zero hg
  have hfP : f ∈ P.1 := mem_of_aeval_mem P (cyclotomic.monic n κ) (Nat.pos_of_ne_zero hdeg) hgP
  refine ⟨P, hfP, ?_⟩
  haveI := charZero_residueField P
  obtain ⟨h, hres'⟩ := residue_aeval P hfP (cyclotomic n κ)
  rw [hres] at hres'
  rw [← isRoot_cyclotomic_iff_charZero hn, IsRoot.def, ← map_cyclotomic n
    (algebraMap κ P.ResidueField), eval_map, ← aeval_def, ← hres']

omit [CharZero κ] in
/-- **`f` takes every constant value**: `f(P) = c` for some place `P`. -/
lemma exists_place_residue_eq {f : K} (hf : Transcendental κ f) (c : κ) :
    ∃ (P : Place κ K) (hfP : f ∈ P.1), P.residue ⟨f, hfP⟩ = algebraMap κ P.ResidueField c := by
  have hg : Transcendental κ (f - algebraMap κ K c) := transcendental_sub_algebraMap hf c
  obtain ⟨P, hgP, hres⟩ := exists_place_residue_eq_zero hg
  have hfP : f ∈ P.1 := by
    have := add_mem hgP (P.algebraMap_mem c)
    rwa [sub_add_cancel] at this
  refine ⟨P, hfP, ?_⟩
  rw [← sub_eq_zero, ← P.residue_mk_algebraMap, ← map_sub, ← hres]
  rfl

/-- Infinitely many of the places of `exists_place_isPrimitiveRoot` avoid a finite set. -/
lemma exists_place_isPrimitiveRoot_notMem {f : K} (hf : Transcendental κ f)
    {S : Set (Place κ K)} (hS : S.Finite) :
    ∃ (n : ℕ) (_ : 0 < n) (P : Place κ K) (_ : P ∉ S) (hfP : f ∈ P.1),
      IsPrimitiveRoot (P.residue ⟨f, hfP⟩) n := by
  choose Q hQ hprim using fun n : ℕ => exists_place_isPrimitiveRoot hf (Nat.succ_pos n)
  have key : ∀ {P P' : Place κ K} (_ : P = P') {a b : ℕ} (hfP : f ∈ P.1) (hfP' : f ∈ P'.1),
      IsPrimitiveRoot (P.residue ⟨f, hfP⟩) a → IsPrimitiveRoot (P'.residue ⟨f, hfP'⟩) b →
        a = b := by
    rintro P _ rfl a b hfP hfP' ha hb
    exact ha.unique hb
  have hinj : Function.Injective Q := fun m n hmn =>
    Nat.succ_injective (key hmn (hQ m) (hQ n) (hprim m) (hprim n))
  by_contra hcon
  push Not at hcon
  exact Set.infinite_range_of_injective hinj (hS.subset (Set.range_subset_iff.2 fun n => by
    by_contra hn
    exact hcon (n + 1) (Nat.succ_pos n) (Q n) hn (hQ n) (hprim n)))

/-- Infinitely many of the places of `exists_place_residue_eq` (values `2, 3, 4, …`) avoid a
finite set. -/
lemma exists_place_natCast_notMem {f : K} (hf : Transcendental κ f)
    {S : Set (Place κ K)} (hS : S.Finite) :
    ∃ (m : ℕ) (P : Place κ K) (_ : P ∉ S) (hfP : f ∈ P.1),
      P.residue ⟨f, hfP⟩ = algebraMap κ P.ResidueField ((m + 2 : ℕ) : κ) := by
  choose Q hQ hval using fun m : ℕ => exists_place_residue_eq hf ((m + 2 : ℕ) : κ)
  have key : ∀ {P P' : Place κ K} (_ : P = P') {a b : ℕ} (hfP : f ∈ P.1) (hfP' : f ∈ P'.1),
      P.residue ⟨f, hfP⟩ = algebraMap κ P.ResidueField (a : κ) →
      P'.residue ⟨f, hfP'⟩ = algebraMap κ P'.ResidueField (b : κ) → a = b := by
    rintro P _ rfl a b hfP hfP' ha hb
    rw [ha] at hb
    exact_mod_cast (algebraMap κ P.ResidueField).injective hb
  have hinj : Function.Injective Q := fun m n hmn => by
    have := key hmn (hQ m) (hQ n) (hval m) (hval n)
    omega
  by_contra hcon
  push Not at hcon
  exact Set.infinite_range_of_injective hinj (hS.subset (Set.range_subset_iff.2 fun m => by
    by_contra hm
    exact hcon m (Q m) hm (hQ m) (hval m)))

end Places

section Residue

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (W : ValuationSubring Ω)
  (hk : ∀ c : k, algebraMap k Ω c ∈ W) [Algebra k (ResidueField W)]
  (hkres : ∀ c : k, residue W ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField W) c)

include hkres in
/-- Values of polynomials at a place: `residue (q(a)) = q(ā)`. -/
lemma residue_eval₂_codRestrict (a : W) (q : k[X]) :
    residue W (eval₂ ((algebraMap k Ω).codRestrict W.toSubring hk) a q) =
      aeval (residue W a) q := by
  rw [hom_eval₂, aeval_def]
  congr 1
  exact RingHom.ext fun c => hkres c

include hkres in
/-- **The residue field of a place of a field of transcendence degree `≤ 1` is algebraic**: for
a proper valuation subring `W ⊇ k` of `Ω` with `trdeg_k Ω ≤ 1`, `κ(W)` is algebraic over `k`
(the argument of `CurvesJacobian.Cusp.exists_valuation_sub_lt_one`, without assuming `k`
algebraically closed). -/
theorem isAlgebraic_residue_of_trdeg_le_one (htr : Algebra.trdeg k Ω ≤ 1) (hW : W ≠ ⊤)
    (y : ResidueField W) : IsAlgebraic k y := by
  by_contra hy
  obtain ⟨a, rfl⟩ := residue_surjective y
  set ψk : k →+* W := (algebraMap k Ω).codRestrict W.toSubring hk
  have hcoe : ∀ q : k[X], ((eval₂ ψk a q : W) : Ω) = aeval (a : Ω) q := fun q => by
    change (W.toSubring.subtype : W →+* Ω) (eval₂ ψk a q) = _
    rw [hom_eval₂, aeval_def]
    rfl
  -- nonzero polynomials in `a` are units of `W`
  have h1 : ∀ q : k[X], q ≠ 0 → W.valuation (aeval (a : Ω) q) = 1 := by
    intro q hq
    rw [← hcoe, ← ValuationSubring.valuation_eq_one_iff]
    by_contra hu
    apply hy
    refine ⟨q, hq, ?_⟩
    rw [← residue_eval₂_codRestrict W hk hkres a q]
    exact (residue_eq_zero_iff _).2 hu
  have htra : Transcendental k (a : Ω) := by
    rintro ⟨p, hp, hpa⟩
    have := h1 p hp
    rw [hpa, map_zero] at this
    exact zero_ne_one this
  have hind : AlgebraicIndependent k (fun _ : PUnit.{u + 1} ↦ (a : Ω)) :=
    algebraicIndependent_unique_type_iff.2 htra
  have hbasis := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg := hbasis.isAlgebraic
  have hadj : ∀ z : Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ (a : Ω)),
      z ≠ 0 → W.valuation (z : Ω) = 1 := by
    rintro ⟨z, hz⟩ hz0
    rw [Set.range_const, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    refine h1 p ?_
    rintro rfl
    exact hz0 (Subtype.ext (by simp))
  have hadjW : ∀ z : Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ (a : Ω)),
      (z : Ω) ∈ W.valuation.integer := fun z ↦ by
    rw [Valuation.mem_integer_iff]
    by_cases hz0 : z = 0
    · rw [hz0, ZeroMemClass.coe_zero, map_zero]
      exact zero_le_one
    · exact (hadj z hz0).le
  apply hW
  rw [eq_top_iff]
  intro x _
  obtain ⟨z, hz0, hz⟩ := (halg.isAlgebraic x).exists_integral_multiple
  let φ := RingHom.codRestrict
    (algebraMap (Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ (a : Ω))) Ω)
    W.valuation.integer hadjW
  have hint : IsIntegral W.valuation.integer (RingHom.id Ω (z • x)) :=
    hz.map_of_comp_eq φ (RingHom.id Ω) (RingHom.ext fun _ ↦ rfl)
  have hmem := (Valuation.integer.integers W.valuation).mem_of_integral hint
  rw [Valuation.mem_integer_iff, RingHom.id_apply, Algebra.smul_def, map_mul] at hmem
  rw [← W.valuation_le_one_iff]
  have hz1 : W.valuation (algebraMap _ Ω z) = 1 := hadj z hz0
  rwa [hz1, one_mul] at hmem

end Residue

section GaloisModel

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k]

attribute [local instance] isFunctionField_F

/-- A unit `x` of a valuation subring: `x⁻¹ ∈ A`. -/
lemma inv_mem_of_isUnit {K : Type*} [Field K] {A : ValuationSubring K} {x : A} (hx : IsUnit x) :
    (x : K)⁻¹ ∈ A := by
  obtain ⟨v, rfl⟩ := hx
  have h : (((v⁻¹ : Aˣ) : A) : K) = ((v : A) : K)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val v.inv_mul)
  rw [← h]
  exact ((v⁻¹ : Aˣ) : A).2

lemma isUnit_of_inv_mem {K : Type*} [Field K] {A : ValuationSubring K} {x : A} (hx0 : (x : K) ≠ 0)
    (hx : (x : K)⁻¹ ∈ A) : IsUnit x :=
  ⟨⟨x, ⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

variable {D} (P : Place k (F D)) (W : ValuationSubring Ω)
  (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1)

/-- `O_P → κ(W)` for a place `W` of `Ω` above the place `P` of `F`. -/
noncomputable def placeToResidue : P.1 →+* ResidueField W :=
  (residue W).comp (((algebraMap (F D) Ω).comp P.1.subtype).codRestrict W.toSubring
    fun x => (hW x).2 x.2)

instance isLocalHom_placeToResidue : IsLocalHom (placeToResidue P W hW) := by
  refine ⟨fun x hx => ?_⟩
  have hx0 : placeToResidue P W hW x ≠ 0 := hx.ne_zero
  have hunit : IsUnit (⟨_, (hW x).2 x.2⟩ : W) := by
    by_contra hu
    exact hx0 ((residue_eq_zero_iff _).2 hu)
  have hxne : ((x : F D) : Ω) ≠ 0 := fun h0 => hx0 (by
    have e : placeToResidue P W hW x = residue W ⟨_, (hW x).2 x.2⟩ := rfl
    have : (⟨_, (hW x).2 x.2⟩ : W) = 0 := Subtype.ext h0
    rw [e, this, map_zero])
  have hinvW := inv_mem_of_isUnit hunit
  have hinvP : (x : F D)⁻¹ ∈ P.1 := by
    rw [← hW]
    change algebraMap (F D) Ω (x : F D)⁻¹ ∈ W
    rw [map_inv₀]
    exact hinvW
  exact isUnit_of_inv_mem (fun h => hxne (by rw [h]; rfl)) hinvP

/-- **The residue field `κ(P)` of the place `P` of `F` embeds into `κ(W)`.** -/
noncomputable def placeResidueMap : P.ResidueField →+* ResidueField W :=
  IsLocalRing.ResidueField.lift (placeToResidue P W hW)

omit [CharZero k] in
lemma placeResidueMap_residue (a : F D) (ha : a ∈ P.1) :
    placeResidueMap P W hW (P.residue ⟨a, ha⟩) = residue W ⟨algebraMap (F D) Ω a, (hW a).2 ha⟩ :=
  rfl

variable (hk : ∀ c : k, algebraMap k Ω c ∈ W) [Algebra k (ResidueField W)]
  (hkres : ∀ c : k, residue W ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField W) c)

omit [CharZero k] in
include hkres in
lemma placeResidueMap_algebraMap (c : k) :
    placeResidueMap P W hW (algebraMap k P.ResidueField c) = algebraMap k (ResidueField W) c := by
  rw [Place.algebraMap_residueField, ← hkres]
  rfl

include hW hkres in
/-- **`[k_x : k] < ∞`**: the residue field `k_x = κ(W ∩ F) ⊆ κ(W)` of a place `W` of `Ω` above a
place `P` of `F` is finite over `k` (it is the image of `κ(P)`). -/
theorem finiteDimensional_pointField [IsGalois (K₀ k t) Ω] :
    FiniteDimensional k (Decomposition.pointField (F D) W hk hkres) := by
  have hmem : ∀ z : P.ResidueField,
      placeResidueMap P W hW z ∈ Decomposition.pointField (F D) W hk hkres := by
    intro z
    obtain ⟨⟨a, ha⟩, rfl⟩ := P.residue_surjective z
    rw [placeResidueMap_residue P W hW a ha]
    exact Decomposition.residue_mem_pointField (F D) W hk hkres a _
  let L : P.ResidueField →ₗ[k] Decomposition.pointField (F D) W hk hkres :=
    { toFun := fun z => ⟨_, hmem z⟩
      map_add' := fun z z' => Subtype.ext (map_add _ z z')
      map_smul' := fun c z => Subtype.ext (by
        simp only [Algebra.smul_def, map_mul, placeResidueMap_algebraMap P W hW hk hkres,
          RingHom.id_apply]
        rfl) }
  refine Module.Finite.of_surjective L fun y => ?_
  obtain ⟨a, ha, hy⟩ := y.2
  refine ⟨P.residue ⟨a, (hW a).1 ha⟩, Subtype.ext ?_⟩
  change placeResidueMap P W hW _ = _
  rw [placeResidueMap_residue P W hW a]
  exact hy

end GaloisModel

section Main

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

omit [IsAlgClosed Ω] in
/-- The closed points of `U` with finite residue fields: a place `P` of `F` with `t ∈ O_P`
(not a cusp) lies below a place `W` of `Ω` with `k ⊆ W`, `t ∈ W`, `κ(W)` algebraic over `k` and
`[k_x : k] < ∞`. -/
theorem exists_point_of_place (P : Place k (F D)) (htP : tF D ∈ P.1) :
    ∃ (W : ValuationSubring Ω) (_ : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1)
      (hk : ∀ c : k, algebraMap k Ω c ∈ W), t ∈ W ∧
      letI := Decomposition.residueAlgebra W hk
      Algebra.IsIntegral k (ResidueField W) ∧
      FiniteDimensional k (Decomposition.pointField (F D) W hk
        (Decomposition.residue_algebraMap_residueAlgebra W hk)) := by
  obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
  have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c => (hW (algebraMap k (F D) c)).2
    (P.algebraMap_mem c)
  refine ⟨W, hW, hk, (hW (tF D)).2 htP, ?_⟩
  letI := Decomposition.residueAlgebra W hk
  have hkres := Decomposition.residue_algebraMap_residueAlgebra W hk
  have hWtop : W ≠ ⊤ := by
    rintro rfl
    obtain ⟨x, hx⟩ : ∃ x : F D, x ∉ P.1 := by
      by_contra h
      push Not at h
      exact P.ne_top (eq_top_iff.2 fun x _ => h x)
    exact hx ((hW x).1 trivial)
  have htr : Algebra.trdeg k Ω ≤ 1 := Cusp.trdeg_le_one_of_isAlgebraic (t := t)
  haveI : Algebra.IsAlgebraic k (ResidueField W) :=
    ⟨isAlgebraic_residue_of_trdeg_le_one W hk hkres htr hWtop⟩
  exact ⟨inferInstance, finiteDimensional_pointField P W hW hk hkres⟩

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero k] in
lemma residue_units_pow (W : ValuationSubring Ω) (f : units D) (N : ℕ)
    (hf : algebraMap (F D) Ω ((f : (F D)ˣ) : F D) ∈ W)
    (hfN : algebraMap (F D) Ω (((f ^ N : units D) : (F D)ˣ) : F D) ∈ W) :
    residue W ⟨_, hfN⟩ = residue W ⟨_, hf⟩ ^ N := by
  rw [← map_pow]
  congr 1

section Point

variable (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W)
  [Algebra k (ResidueField W)]
  (hkres : ∀ c : k, residue W ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField W) c)
  (ht : t ∈ W)

include ht in
/-- At a point where `f(x)` is an `N`-th root of unity, all restrictions of `κ_U(f^N)` along
`D_x → Π_U` vanish. -/
theorem restrict_eq_one_of_isPrimitiveRoot (f : units D) {N : ℕ}
    (hfW : algebraMap (F D) Ω ((f : (F D)ˣ) : F D) ∈ W)
    (hprim : IsPrimitiveRoot (residue W ⟨_, hfW⟩) N) (n : ℕ) [NeZero n] :
    letI := Decomposition.muAction (F D) W hk hkres n
    ContH1.map (decompToPi D W) (continuous_decompToPi D W)
      (Decomposition.reduceMu W n (NeZero.ne n)) continuous_of_discreteTopology
      (reduceMu_decompToPi_smul D W hk hkres n) (kummerMap D n (f ^ N)) = 1 := by
  obtain ⟨hu, hu'⟩ := units_val_mem D W hk (f ^ N) ht
  rw [decompToPi_kummerMap_eq_one_iff D W hk hkres n (f ^ N) hu hu']
  refine ⟨1, fun σ => map_one _, ?_⟩
  rw [one_pow, residue_units_pow D W f N hfW hu, hprim.pow_eq_one]

include ht in
/-- At a point with finite residue field where `f(x) = m + 2`, not all restrictions of
`κ_U(f^N)` (`N ≥ 1`) along `D_x → Π_U` vanish (`k` torally Kummer-faithful). -/
theorem not_restrict_eq_one_of_natCast [Algebra.IsIntegral k (ResidueField W)]
    [FiniteDimensional k (Decomposition.pointField (F D) W hk hkres)]
    (htf : IsTorallyKummerFaithful k) (f : units D) {N m : ℕ} (hN : 0 < N)
    (hfW : algebraMap (F D) Ω ((f : (F D)ˣ) : F D) ∈ W)
    (hval : residue W ⟨_, hfW⟩ = algebraMap k (ResidueField W) ((m + 2 : ℕ) : k)) :
    ¬ ∀ (n : ℕ) [NeZero n],
      letI := Decomposition.muAction (F D) W hk hkres n
      ContH1.map (decompToPi D W) (continuous_decompToPi D W)
        (Decomposition.reduceMu W n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D W hk hkres n) (kummerMap D n (f ^ N)) = 1 := by
  intro h
  haveI := isGalois_residueField W hk hkres
  obtain ⟨hu, hu'⟩ := units_val_mem D W hk (f ^ N) ht
  have h1 := (forall_decompToPi_kummerMap_eq_one_iff D W hk hkres htf (f ^ N) hu hu').1 h
  rw [residue_units_pow D W f N hfW hu, hval, ← map_pow, ← map_one (algebraMap k _),
    (algebraMap k (ResidueField W)).injective.eq_iff] at h1
  have h2 : ((m + 2) ^ N : ℕ) = 1 := by exact_mod_cast h1
  have h3 : 1 < (m + 2) ^ N := Nat.one_lt_pow hN.ne' (by omega)
  omega

end Point

omit [IsAlgClosed Ω] in
/-- A nonconstant `f` takes a primitive `N`-th root of unity (some `N ≥ 1`) as value at a closed
point of `U` with finite residue field. -/
theorem exists_point_isPrimitiveRoot (f : F D) (hf : Transcendental k f) :
    ∃ N : ℕ, 0 < N ∧ ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
      letI := Decomposition.residueAlgebra A hk
      Algebra.IsIntegral k (ResidueField A) ∧
      FiniteDimensional k (Decomposition.pointField (F D) A hk
        (Decomposition.residue_algebraMap_residueAlgebra A hk)) ∧
      ∃ hfA : algebraMap (F D) Ω f ∈ A, IsPrimitiveRoot (residue A ⟨_, hfA⟩) N := by
  have hS : {P : Place k (F D) | tF D ∉ P.1}.Finite := Place.finite_setOf_notMem (tF D)
  obtain ⟨N, hN, P, hP, hfP, hprim⟩ := exists_place_isPrimitiveRoot_notMem hf hS
  obtain ⟨W, hW, hk, ht, hint, hfin⟩ := exists_point_of_place D P (not_not.1 hP)
  exact ⟨N, hN, W, hk, ht, hint, hfin, (hW f).2 hfP,
    hprim.map_of_injective (placeResidueMap P W hW).injective⟩

omit [IsAlgClosed Ω] in
/-- A nonconstant `f` takes a value `m + 2 ∈ ℕ` at a closed point of `U` with finite residue
field. -/
theorem exists_point_natCast (f : F D) (hf : Transcendental k f) :
    ∃ m : ℕ, ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
      letI := Decomposition.residueAlgebra A hk
      Algebra.IsIntegral k (ResidueField A) ∧
      FiniteDimensional k (Decomposition.pointField (F D) A hk
        (Decomposition.residue_algebraMap_residueAlgebra A hk)) ∧
      ∃ hfA : algebraMap (F D) Ω f ∈ A,
        residue A ⟨_, hfA⟩ = algebraMap k (ResidueField A) ((m + 2 : ℕ) : k) := by
  have hS : {P : Place k (F D) | tF D ∉ P.1}.Finite := Place.finite_setOf_notMem (tF D)
  obtain ⟨m, P, hP, hfP, hval⟩ := exists_place_natCast_notMem hf hS
  obtain ⟨W, hW, hk, ht, hint, hfin⟩ := exists_point_of_place D P (not_not.1 hP)
  letI := Decomposition.residueAlgebra W hk
  refine ⟨m, W, hk, ht, hint, hfin, (hW f).2 hfP, ?_⟩
  rw [← placeResidueMap_residue P W hW _ hfP, hval,
    placeResidueMap_algebraMap P W hW hk (Decomposition.residue_algebraMap_residueAlgebra W hk)]

/-- **[AbsTopIII] Prop. 1.8(i), "only if", over finite extensions `k_x`** (T3 l.2078–2087,
proof l.2099–2106): let `k` be torally Kummer-faithful and `f ∈ Γ(U, 𝒪^×)` nonconstant. Then
there are `N ≥ 1` and two closed points `x₁, x₂` of `U` (places `A ⊇ k` of `Ω` with `t ∈ A`,
`κ(A)` algebraic over `k`, `[k_{x_i} : k] < ∞`) such that the restrictions of `κ_U(f^N)` along
`D_{x₁} → Π_U` vanish at every level (`η†|x₁ = 0`), while not all restrictions along
`D_{x₂} → Π_U` vanish (`η†|x₂ ≠ 0`). Here `f(x₁)` is a primitive `N`-th root of unity and
`f(x₂) ∈ {2, 3, …}`. -/
theorem exists_restrict_kummerMap_of_transcendental (htf : IsTorallyKummerFaithful k)
    (f : units D) (hf : Transcendental k ((f : (F D)ˣ) : F D)) :
    ∃ N : ℕ, 0 < N ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
        letI := Decomposition.residueAlgebra A hk
        Algebra.IsIntegral k (ResidueField A) ∧
        FiniteDimensional k (Decomposition.pointField (F D) A hk
          (Decomposition.residue_algebraMap_residueAlgebra A hk)) ∧
        ∀ (n : ℕ) [NeZero n],
          letI := Decomposition.muAction (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk) n
          ContH1.map (decompToPi D A) (continuous_decompToPi D A)
            (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
            (reduceMu_decompToPi_smul D A hk
              (Decomposition.residue_algebraMap_residueAlgebra A hk) n)
            (kummerMap D n (f ^ N)) = 1) ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
        letI := Decomposition.residueAlgebra A hk
        Algebra.IsIntegral k (ResidueField A) ∧
        FiniteDimensional k (Decomposition.pointField (F D) A hk
          (Decomposition.residue_algebraMap_residueAlgebra A hk)) ∧
        ¬ ∀ (n : ℕ) [NeZero n],
          letI := Decomposition.muAction (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk) n
          ContH1.map (decompToPi D A) (continuous_decompToPi D A)
            (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
            (reduceMu_decompToPi_smul D A hk
              (Decomposition.residue_algebraMap_residueAlgebra A hk) n)
            (kummerMap D n (f ^ N)) = 1) := by
  obtain ⟨N, hN, W, hk, ht, hint, hfin, hfW, hprim⟩ := exists_point_isPrimitiveRoot D _ hf
  obtain ⟨m, W₂, hk₂, ht₂, hint₂, hfin₂, hfW₂, hval⟩ := exists_point_natCast D _ hf
  refine ⟨N, hN, ⟨W, hk, ht, hint, hfin, fun n _ => ?_⟩, ⟨W₂, hk₂, ht₂, hint₂, hfin₂, ?_⟩⟩
  · letI := Decomposition.residueAlgebra W hk
    exact restrict_eq_one_of_isPrimitiveRoot D W hk
      (Decomposition.residue_algebraMap_residueAlgebra W hk) ht f hfW hprim n
  · letI := Decomposition.residueAlgebra W₂ hk₂
    haveI := hint₂
    haveI := hfin₂
    exact not_restrict_eq_one_of_natCast D W₂ hk₂
      (Decomposition.residue_algebraMap_residueAlgebra W₂ hk₂) ht₂ htf f hN hfW₂ hval

end Main

end CurvesJacobian.Kummer
