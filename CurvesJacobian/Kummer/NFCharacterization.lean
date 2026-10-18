/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ClosedCharacterization
import CurvesJacobian.Kummer.NF

/-!
# [AbsTopIII] Prop. 1.8 for NF-curves at NF-points over finite extensions `k_x`

[AbsTopIII] Prop. 1.8 (T3 l.2061–2106), with the NF-notions of Def. 1.7 (`Kummer/NF.lean`) and the
`Ẑ(1)`-level restriction `η|_x = s_x^*(η)` to closed points (`Kummer/ClosedRestriction.lean`):

* `NFModel.isAlgebraic_of_residue_eq`: the value of an NF-rational function at an NF-point is an
  algebraic number (NF-points are `k̄_NF`-points of `X_NF`);
* `NFModel.eq_toKummerCompletion_of_restrictClosed_eq` (**Prop. 1.8(ii), "if"**): if
  `κ_U(f)|_x = c|_{G_{k_x}}` for an NF-rational unit `f`, an NF-point `x` and `c ∈ (kˣ)^∧`, then `c`
  is the Kummer class of an NF-constant;
* `NFModel.exists_restrictClosed_eq_of_isNFConstant` (**Prop. 1.8(ii), "only if"**);
* `NFModel.exists_restrictClosed_of_isNF` (**Prop. 1.8(i), "only if"**, `Ẑ(1)`-level);
* `NFModel.exists_eq_kummerMapZHat_of_restrictClosed` (**Prop. 1.8(i), "if"**), under the
  hypothesis `NFModel.UnitsDescend`: units of `U` are NF-rational functions up to constants of
  `k̄`. This is the descent of principal divisors supported on NF-points from `X_{k̄}` to `X_NF`
  (implicit in the proof of [AbsTopIII] Prop. 1.8, T3 l.2099–2106); it is not yet formalised and
  enters as an explicit, named hypothesis (a debt recorded in continuous-kummer-theory's
  `Plans/MR5Plan.md`).
-/

open KummerTheory Curve AffOrbicurve IsLocalRing Polynomial

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]

namespace NFModel

variable (N : NFModel D)

/-- Values of polynomials with rational coefficients at elements of a subfield stay in it. -/
lemma eval₂_mem_of_mem (S : Subfield Ω) {y : Ω} (hy : y ∈ S) (p : ℚ[X]) :
    eval₂ (algebraMap ℚ Ω) y p ∈ S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact S.add_mem hp hq
  | monomial n c =>
    rw [eval₂_monomial, eq_ratCast (algebraMap ℚ Ω) c]
    exact S.mul_mem (SubfieldClass.ratCast_mem S c) (S.pow_mem hy n)

omit [CharZero k] in
/-- **The value of an NF-rational function at an NF-point is an algebraic number**
([AbsTopIII] Def. 1.7: NF-points are the `k̄_NF`-points of `X_NF`): if `g ∈ F_NF` has the same
residue at an NF-point `W` as an element `y` of `k̄`, then `y` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_residue_eq {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hkbar : ∀ z ∈ kbar k Ω, z ∈ W) (hW : N.IsNFPoint W) {g : Ω} (hg : g ∈ N.FNF) (hgW : g ∈ W)
    {y : Ω} (hy : y ∈ kbar k Ω) (h : residue W ⟨g, hgW⟩ = residue W ⟨y, hkbar y hy⟩) :
    IsAlgebraic ℚ y := by
  -- the place `V = W ∩ F_NF` of `F_NF`
  set V : ValuationSubring N.FNF := W.comap N.FNF.subtype
  have hVmem : ∀ x : N.FNF, x ∈ V ↔ (x : Ω) ∈ W := fun x => Iff.rfl
  have hV : V ≠ ⊤ := by
    obtain ⟨g₀, hg₀, hg₀W⟩ := hW
    intro hV
    exact hg₀W ((hVmem ⟨g₀, hg₀⟩).1 (hV ▸ ValuationSubring.mem_top _))
  have hQ : ∀ c : ℚ, algebraMap ℚ Ω c ∈ W := fun c => by
    rw [eq_ratCast (algebraMap ℚ Ω) c, ← map_ratCast (algebraMap k Ω) c]
    exact hk _
  have hkV : ∀ c : ℚ, algebraMap ℚ N.FNF c ∈ V := fun c => by
    rw [hVmem]
    have : ((algebraMap ℚ N.FNF c : N.FNF) : Ω) = algebraMap ℚ Ω c := by
      rw [eq_ratCast (algebraMap ℚ N.FNF) c, eq_ratCast (algebraMap ℚ Ω) c]
      push_cast
      rfl
    rw [this]
    exact hQ c
  letI := Decomposition.residueAlgebra V hkV
  have hkresV := Decomposition.residue_algebraMap_residueAlgebra V hkV
  obtain ⟨p, hp0, hp⟩ := isAlgebraic_residue_of_trdeg_le_one V hkV hkresV N.trdeg_le_one hV
    (residue V ⟨⟨g, hg⟩, hgW⟩)
  rw [← residue_eval₂_codRestrict V hkV hkresV ⟨⟨g, hg⟩, hgW⟩ p] at hp
  set ψV := (algebraMap ℚ N.FNF).codRestrict V.toSubring hkV
  set e : V := eval₂ ψV ⟨⟨g, hg⟩, hgW⟩ p
  have he : ((e : N.FNF) : Ω) = eval₂ (algebraMap ℚ Ω) g p := by
    have := Polynomial.hom_eval₂ p ψV (N.FNF.subtype.comp V.toSubring.subtype)
      ⟨⟨g, hg⟩, hgW⟩
    rw [show (N.FNF.subtype.comp V.toSubring.subtype).comp ψV = algebraMap ℚ Ω from
      RingHom.ext_rat _ _] at this
    exact this
  -- `p(g)` lies in the maximal ideal of `W`
  set ψW := (algebraMap ℚ Ω).codRestrict W.toSubring hQ
  have hcoeW : ∀ z : W, ((eval₂ ψW z p : W) : Ω) = eval₂ (algebraMap ℚ Ω) (z : Ω) p := by
    intro z
    have := Polynomial.hom_eval₂ p ψW W.toSubring.subtype z
    rw [show W.toSubring.subtype.comp ψW = algebraMap ℚ Ω from RingHom.ext_rat _ _] at this
    exact this
  have hresW : ∀ z : W, residue W (eval₂ ψW z p) = eval₂ ((residue W).comp ψW) (residue W z) p :=
    fun z => Polynomial.hom_eval₂ p ψW (residue W) z
  have hgmax : residue W (eval₂ ψW ⟨g, hgW⟩ p) = 0 := by
    rw [residue_eq_zero_iff]
    intro hunit
    have hmem : (e : N.FNF) ∈ V := e.2
    apply (residue_eq_zero_iff e).1 hp
    by_cases h0 : ((e : N.FNF) : Ω) = 0
    · exfalso
      apply hunit.ne_zero
      apply Subtype.ext
      rw [hcoeW]
      exact he ▸ h0
    · refine isUnit_of_inv_mem (A := V) (fun h' => h0 (by rw [h']; rfl)) ?_
      rw [hVmem]
      have hinv := inv_mem_of_isUnit hunit
      rw [hcoeW] at hinv
      rw [← he] at hinv
      exact hinv
  -- hence `p(y)` lies in it too, and `p(y) ∈ k̄`, so `p(y) = 0`
  have hymax : residue W (eval₂ ψW ⟨y, hkbar y hy⟩ p) = 0 := by
    rw [hresW, ← h, ← hresW]
    exact hgmax
  refine ⟨p, hp0, ?_⟩
  rw [aeval_def]
  by_contra h0
  have hmemk : eval₂ (algebraMap ℚ Ω) y p ∈ kbar k Ω :=
    eval₂_mem_of_mem (kbar k Ω).toSubfield hy p
  have hinv : (eval₂ (algebraMap ℚ Ω) y p)⁻¹ ∈ W :=
    hkbar _ ((kbar k Ω).inv_mem hmemk)
  rw [residue_eq_zero_iff] at hymax
  apply hymax
  refine isUnit_of_inv_mem (fun h' => h0 ?_) ?_
  · exact (hcoeW _).symm.trans h'
  · simpa only [hcoeW] using hinv

variable [IsAlgClosed Ω]

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(ii), "if", at NF-points over finite extensions `k_x`**: for `k`
torally Kummer-faithful, an NF-rational unit `f` of `U`, an NF-point `x` of `U` with
`[k_x : k] < ∞` and `c ∈ (kˣ)^∧ ≅ H¹(G_k, Ẑ(1))`: if `κ_U(f)|_x = c|_{G_{k_x}}`, then `c` is the
Kummer class of an NF-constant `b ∈ kˣ` (`b = f(x)`). -/
theorem eq_toKummerCompletion_of_restrictClosed_eq (htf : IsTorallyKummerFaithful k)
    (hHL : D.HL = D.H) (f : units D) (hNF : N.IsNFFunction ((f : (F D)ˣ) : F D))
    (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)]
    [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)] (ht : t ∈ A)
    (hA : N.IsNFPoint A) (c : KummerCompletion k)
    (h : restrictClosed D A hk hkres hHL ht (kummerMapZHat D f) =
      restrictClosed D A hk hkres hHL ht (constMapZHat D c)) :
    ∃ b : kˣ, c = toKummerCompletion k b ∧ IsNFConstant Ω (b : k) ∧
      constMapZHat D c = kummerMapZHat D (constUnit D b) := by
  obtain ⟨hf, hf'⟩ := units_mem (D := D) ⟨hk, ht⟩ f.2
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  have e1 := congrArg (kummerZHatEquiv _ (ResidueField A))
    (restrictClosed_kummerMapZHat D A hk hkres hHL ht f hf hf')
  rw [kummerZHatEquiv_kummerZHat] at e1
  have e2 := kummerZHatEquiv_restrictClosed_constMapZHat D A hk hkres hHL ht c
  have hc := e1.symm.trans ((congrArg (kummerZHatEquiv _ (ResidueField A)) h).trans e2)
  obtain ⟨b, hb, hba⟩ := exists_eq_toKummerCompletion_of_completionMap_eq htf c _ hc.symm
  refine ⟨b, hb, ?_, by rw [hb, constMapZHat_toKummerCompletion]⟩
  -- `f(x) = b`
  have hval : residue A ⟨_, hf⟩ = residue A ⟨algebraMap k Ω b, hk b⟩ := by
    rw [hkres]
    have := congrArg (fun z : (Decomposition.pointField (F D) A hk hkres)ˣ =>
      ((z : Decomposition.pointField (F D) A hk hkres) : ResidueField A)) hba
    exact this.symm
  have hkbar : ∀ z ∈ kbar k Ω, z ∈ A := fun z hz => kbar_mem A hk ⟨z, hz⟩
  exact N.isAlgebraic_of_residue_eq hk hkbar hA hNF hf
    (IntermediateField.algebraMap_mem _ _) hval

/-- **[AbsTopIII] Prop. 1.8(i), "only if", for NF-curves at the `Ẑ(1)`-level**: for `k` torally
Kummer-faithful and a nonconstant NF-rational unit `f`, there are `M ≥ 1` and NF-points
`x₁, x₂ ∈ U(k_x)` (`[k_{x_i} : k] < ∞`) with `κ_U(f^M)|x₁ = 0` and `κ_U(f^M)|x₂ ≠ 0`. -/
theorem exists_restrictClosed_of_isNF (htf : IsTorallyKummerFaithful k) (hHL : D.HL = D.H)
    (f : units D) (hf : Transcendental k ((f : (F D)ˣ) : F D))
    (hNF : N.IsNFFunction ((f : (F D)ˣ) : F D)) :
    ∃ M : ℕ, 0 < M ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
        N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (kummerMapZHat D (f ^ M)) = 1) ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
        N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (kummerMapZHat D (f ^ M)) ≠ 1) := by
  obtain ⟨M, hM, ⟨A, hk, ht, hA, hint, hfin, h1⟩, ⟨A₂, hk₂, ht₂, hA₂, hint₂, hfin₂, h2⟩⟩ :=
    N.exists_restrict_kummerMap_of_isNF htf f hf hNF
  refine ⟨M, hM, ⟨A, hk, ht, hA, hint, hfin, ?_⟩, ⟨A₂, hk₂, ht₂, hA₂, hint₂, hfin₂, ?_⟩⟩
  · letI := Decomposition.residueAlgebra A hk
    exact (restrictClosed_kummerMapZHat_eq_one_iff_forall D A hk _ hHL ht _).2 h1
  · letI := Decomposition.residueAlgebra A₂ hk₂
    exact fun h => h2 ((restrictClosed_kummerMapZHat_eq_one_iff_forall D A₂ hk₂ _ hHL ht₂ _).1 h)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω] [IsAlgClosed Ω] in
/-- The unit `f^M · b` (`f` a unit of `U`, `b ∈ kˣ`) as an element of `F`. -/
lemma coe_pow_mul_constUnit (f : units D) (M : ℕ) (b : kˣ) :
    (((f ^ M * constUnit D b : units D) : (F D)ˣ) : F D) =
      ((f : (F D)ˣ) : F D) ^ M * algebraMap k (F D) (b : k) := by
  rw [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(ii), "only if"**: if there is a nonconstant NF-rational unit `f₀` of
`U`, then for every NF-constant `b ∈ kˣ` there are a nonconstant NF-rational unit `f` and an
NF-point `x ∈ U(k_x)`, `[k_x : k] < ∞`, with `κ_U(f)|_x = κ(b)|_{G_{k_x}}`. -/
theorem exists_restrictClosed_eq_of_isNFConstant (htf : IsTorallyKummerFaithful k)
    (hHL : D.HL = D.H) (f₀ : units D) (hf₀ : Transcendental k ((f₀ : (F D)ˣ) : F D))
    (hNF₀ : N.IsNFFunction ((f₀ : (F D)ˣ) : F D)) (b : kˣ) (hb : IsNFConstant Ω (b : k)) :
    ∃ f : units D, Transcendental k ((f : (F D)ˣ) : F D) ∧
      N.IsNFFunction ((f : (F D)ˣ) : F D) ∧
      ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
        N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
              (kummerMapZHat D f) =
            restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
              (constMapZHat D (toKummerCompletion k b)) := by
  obtain ⟨M, hM, ⟨A, hk, ht, hA, hint, hfin, h1⟩, -⟩ :=
    N.exists_restrictClosed_of_isNF htf hHL f₀ hf₀ hNF₀
  refine ⟨f₀ ^ M * constUnit D b, ?_, ?_, A, hk, ht, hA, hint, hfin, ?_⟩
  · intro halg
    apply hf₀
    rw [coe_pow_mul_constUnit] at halg
    have h1 := halg.mul (isAlgebraic_algebraMap (R := k) (A := F D) ((b⁻¹ : kˣ) : k))
    rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] at h1
    exact h1.of_pow hM
  · simp only [IsNFFunction]
    have e : ((((f₀ ^ M * constUnit D b : units D) : (F D)ˣ) : F D) : Ω) =
        (((f₀ : (F D)ˣ) : F D) : Ω) ^ M * algebraMap k Ω (b : k) := by
      rw [coe_pow_mul_constUnit]
      rfl
    rw [e]
    exact N.FNF.mul_mem (N.FNF.pow_mem hNF₀ M) (N.algebraic_mem _ hb)
  · letI := Decomposition.residueAlgebra A hk
    rw [map_mul, map_mul, h1, one_mul, constMapZHat_toKummerCompletion]

/-- **Descent of units to `k̄_NF` up to constants** (the part of [AbsTopIII] Prop. 1.8, proof
T3 l.2099–2106, which says that a function on `X_{k̄}` whose divisor is supported on NF-points —
here: a unit of `U`, whose divisor is supported on the NF-cusps — is NF up to a constant). Not yet
formalised; used as an explicit hypothesis of `exists_eq_kummerMapZHat_of_restrictClosed`. -/
def UnitsDescend : Prop :=
  ∀ w : units D, ∃ l : Ω, l ≠ 0 ∧ l ∈ kbar k Ω ∧
    l * algebraMap (F D) Ω ((w : (F D)ˣ) : F D) ∈ N.FNF

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), "if", for NF-curves** (modulo the descent hypothesis
`UnitsDescend`): if `η ∈ P_U` restricts trivially to an NF-point `x₁` and nontrivially to a
closed point `x₂` (`[k_{x_i} : k] < ∞`), then `η` is the Kummer class of a nonconstant
NF-rational function. Applied to a positive multiple `η†` of a class this is (i). -/
theorem exists_eq_kummerMapZHat_of_restrictClosed (hdesc : N.UnitsDescend)
    (htf : IsTorallyKummerFaithful k) (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) (hHL : D.HL = D.H)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (hη : η ∈ PU D)
    (A₁ : ValuationSubring Ω) (hk₁ : ∀ c : k, algebraMap k Ω c ∈ A₁)
    [Algebra k (ResidueField A₁)]
    (hkres₁ : ∀ c : k, residue A₁ ⟨algebraMap k Ω c, hk₁ c⟩ = algebraMap k (ResidueField A₁) c)
    [Algebra.IsIntegral k (ResidueField A₁)]
    [FiniteDimensional k (Decomposition.pointField (F D) A₁ hk₁ hkres₁)] (ht₁ : t ∈ A₁)
    (hA₁ : N.IsNFPoint A₁)
    (A₂ : ValuationSubring Ω) (hk₂ : ∀ c : k, algebraMap k Ω c ∈ A₂)
    [Algebra k (ResidueField A₂)]
    (hkres₂ : ∀ c : k, residue A₂ ⟨algebraMap k Ω c, hk₂ c⟩ = algebraMap k (ResidueField A₂) c)
    [Algebra.IsIntegral k (ResidueField A₂)]
    [FiniteDimensional k (Decomposition.pointField (F D) A₂ hk₂ hkres₂)] (ht₂ : t ∈ A₂)
    (h₁ : restrictClosed D A₁ hk₁ hkres₁ hHL ht₁ η = 1)
    (h₂ : restrictClosed D A₂ hk₂ hkres₂ hHL ht₂ η ≠ 1) :
    ∃ w : units D, η = kummerMapZHat D w ∧ w ∉ Set.range (constUnit D) ∧
      N.IsNFFunction ((w : (F D)ˣ) : F D) := by
  obtain ⟨w, rfl, hw⟩ := CurvesJacobian.Kummer.exists_eq_kummerMapZHat_of_restrictClosed D htf hJ
    hkF hHL η hη A₁ hk₁ hkres₁ ht₁ A₂ hk₂ hkres₂ ht₂ h₁ h₂
  refine ⟨w, rfl, hw, ?_⟩
  obtain ⟨hwA, hwA'⟩ := units_mem (D := D) ⟨hk₁, ht₁⟩ w.2
  -- `w(x₁) = 1`
  have hw1 :=
    (restrictClosed_kummerMapZHat_eq_one_iff D A₁ hk₁ hkres₁ hHL ht₁ htf w hwA hwA').1 h₁
  obtain ⟨l, hl0, hlk, hlw⟩ := hdesc w
  have hkbar : ∀ z ∈ kbar k Ω, z ∈ A₁ := fun z hz => kbar_mem A₁ hk₁ ⟨z, hz⟩
  have hlwA : l * algebraMap (F D) Ω ((w : (F D)ˣ) : F D) ∈ A₁ :=
    A₁.mul_mem _ _ (hkbar l hlk) hwA
  -- `(l w)(x₁) = l̄`, so `l` is an algebraic number
  have hres : residue A₁ ⟨_, hlwA⟩ = residue A₁ ⟨l, hkbar l hlk⟩ := by
    have e : (⟨_, hlwA⟩ : A₁) = ⟨l, hkbar l hlk⟩ * ⟨_, hwA⟩ := rfl
    rw [e, map_mul, hw1, mul_one]
  have hlQ := N.isAlgebraic_of_residue_eq hk₁ hkbar hA₁ hlw hlwA hlk hres
  have hl : l ∈ N.FNF := N.algebraic_mem l hlQ
  simp only [IsNFFunction]
  have : (((w : (F D)ˣ) : F D) : Ω) =
      l⁻¹ * (l * algebraMap (F D) Ω ((w : (F D)ˣ) : F D)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rfl
  rw [this]
  exact N.FNF.mul_mem (N.FNF.inv_mem hl) hlw

end NFModel

end CurvesJacobian.Kummer
