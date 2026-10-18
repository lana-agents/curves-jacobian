/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ClosedPoints
import CurvesJacobian.Kummer.ConstantExtension
import Mathlib.FieldTheory.LinearDisjoint

/-!
# NF-curves, NF-points, NF-rational functions and NF-constants ([AbsTopIII] Def. 1.7)

[AbsTopIII] Def. 1.7 (T3 l.2040–2050): for `char k = 0`, `k̄_NF ⊆ k̄` is the algebraic closure of
`ℚ` in `k̄`; `X` is an NF-curve if `X_{k̄}` is defined over `k̄_NF`, and NF-points (resp.
NF-rational functions, NF-constants) are the points of `X(k̄)` (resp. rational functions on
`X_{k̄}`, constants) that descend to `k̄_NF`.

In `pi1`'s Galois model (`k̄ = kbar k Ω`, `F k̄ = F (baseChange D)` the function field of `X_{k̄}`,
`ConstantExtension.lean`), with `Ω` of characteristic `0`:

* `CurvesJacobian.Kummer.NFModel D`: a **descent of `X_{k̄}` to `k̄_NF`**, i.e. a subfield
  `F_NF ⊆ F k̄` (the function field `k̄_NF(X_NF)`) containing `k̄_NF`, with `F_NF ∩ k̄ = k̄_NF` and
  `F_NF · k̄ = F k̄`, `F_NF` and `k̄` linearly disjoint over `k̄_NF` (so `F_NF ⊗_{k̄_NF} k̄` embeds
  into `F k̄` with image generating it: `X_{k̄} ≅ X_NF ×_{k̄_NF} k̄` on function fields), such
  that the cusps of `U = Spec R` (the places `W ⊇ k` with `t ∉ W`) descend (`U` is an NF-curve).
  That `X_NF` is a curve over `k̄_NF` (`F_NF` has transcendence degree `≤ 1`) follows:
  `NFModel.trdeg_le_one` in `Kummer/NFDescent.lean`, where also the descent of units of `U`
  (`NFModel.unitsDescend`) is proved.
* `CurvesJacobian.Kummer.NFModel.IsNFPoint`: a place `W` of `Ω` (a point of `X(k̄)`) is an NF-point
  if its restriction to `F_NF` is nontrivial, i.e. `W ∩ F k̄` lies over a (`k̄_NF`-rational) point
  of `X_NF`;
* NF-rational functions are the elements of `F_NF`; NF-constants the `c ∈ k` algebraic over `ℚ`.

Main result: `CurvesJacobian.Kummer.NFModel.exists_restrict_kummerMap_of_isNF` — **[AbsTopIII]
Prop. 1.8(i), "only if", for NF-curves**: the points `x₁, x₂` of
`exists_restrict_kummerMap_of_transcendental` can be chosen to be NF-points when `f` is an
NF-rational function.
-/

open WeilCurves.FunctionField Polynomial IsLocalRing KummerTheory Curve AffOrbicurve

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]

omit [IsGalois (K₀ k t) Ω] in
/-- `k̄_NF ⊆ k̄`: an algebraic number of `Ω` is algebraic over `k`. -/
lemma mem_kbar_of_isAlgebraic {x : Ω} (hx : IsAlgebraic ℚ x) : x ∈ kbar k Ω :=
  mem_algebraicClosure_iff.2 (hx.extendScalars (algebraMap ℚ k).injective)

variable (k Ω) in
/-- `k̄` as an intermediate field of `Ω / k̄_NF`, where `k̄_NF = algebraicClosure ℚ Ω` is the
algebraic closure of `ℚ` in `Ω`. -/
def kbarNF : IntermediateField (algebraicClosure ℚ Ω) Ω :=
  (kbar k Ω).toSubfield.toIntermediateField fun x =>
    mem_kbar_of_isAlgebraic (mem_algebraicClosure_iff.1 x.2)

/-- **A descent of `X_{k̄}` (and of the cusps of `U`) to `k̄_NF`** ([AbsTopIII] Def. 1.7(i),
`U` an NF-curve), in terms of function fields inside `Ω`. -/
structure NFModel where
  /-- The function field `k̄_NF(X_NF) ⊆ F k̄`. -/
  FNF : Subfield Ω
  /-- `k̄_NF ⊆ F_NF`. -/
  algebraic_mem : ∀ x : Ω, IsAlgebraic ℚ x → x ∈ FNF
  /-- `F_NF ⊆ F k̄`. -/
  mem_F : ∀ x ∈ FNF, x ∈ F (baseChange D)
  /-- `F_NF ∩ k̄ = k̄_NF`. -/
  isAlgebraic_of_mem_kbar : ∀ x ∈ FNF, x ∈ kbar k Ω → IsAlgebraic ℚ x
  /-- `F_NF · k̄ = F k̄`. -/
  mem_closure : ∀ x ∈ F (baseChange D), x ∈ Subfield.closure ((FNF : Set Ω) ∪ kbar k Ω)
  /-- The cusps of `U` (places `W ⊇ k` with `t ∉ W`) are NF-points. -/
  cusp_nf : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t ∉ W →
    ∃ g ∈ FNF, g ∉ W
  /-- `F_NF` and `k̄` are linearly disjoint over `k̄_NF` (`IntermediateField.LinearDisjoint`):
  together with `mem_closure` this says `F_NF ⊗_{k̄_NF} k̄ ≅ k̄_NF(X_NF) ⊗_{k̄_NF} k̄` embeds into
  `F k̄` with image generating it as a field, i.e. `X_{k̄} ≅ X_NF ×_{k̄_NF} k̄` on function
  fields ([AbsTopIII] Def. 1.7(i): `X_{k̄}` is defined over `k̄_NF`). -/
  linearDisjoint : (FNF.toIntermediateField (K := algebraicClosure ℚ Ω) fun x =>
    algebraic_mem _ (mem_algebraicClosure_iff.1 x.2)).LinearDisjoint (kbarNF k Ω)

namespace NFModel

variable {D} (N : NFModel D)

/-- **NF-points** ([AbsTopIII] Def. 1.7(ii)): a place `W` of `Ω` whose restriction to `F_NF` is
nontrivial, i.e. whose point of `X(k̄)` descends to a `k̄_NF`-point of `X_NF`. -/
def IsNFPoint (W : ValuationSubring Ω) : Prop := ∃ g ∈ N.FNF, g ∉ W

/-- **NF-rational functions** ([AbsTopIII] Def. 1.7(ii)): the elements of `F_NF`. -/
def IsNFFunction (f : Ω) : Prop := f ∈ N.FNF

end NFModel

/-- **NF-constants** ([AbsTopIII] Def. 1.7(ii)): the constants `c ∈ k` which descend to `k̄_NF`. -/
def IsNFConstant (Ω : Type*) [Field Ω] [Algebra k Ω] [CharZero Ω] (c : k) : Prop :=
  IsAlgebraic ℚ (algebraMap k Ω c)

section Lift

variable {Ω' : Type*} [Field Ω'] [IsAlgClosed Ω'] (W : ValuationSubring Ω')

/-- **Lifting roots of unity**: if `x ∈ W` has `x̄ⁿ = 1`, then `x ≡ ζ mod 𝔪_W` for an `n`-th root
of unity `ζ ∈ Ω'`. -/
lemma exists_pow_eq_one_valuation_sub_lt_one {x : Ω'} (hx : x ∈ W) {n : ℕ} (hn : 0 < n)
    (h : residue W ⟨x, hx⟩ ^ n = 1) :
    ∃ ζ : Ω', ζ ^ n = 1 ∧ W.valuation (x - ζ) < 1 := by
  set p : Ω'[X] := X ^ n - C 1
  have hmonic : p.Monic := monic_X_pow_sub_C 1 hn.ne'
  have hprod : p = (p.roots.map (X - C ·)).prod := by
    have := (IsAlgClosed.splits p).eq_prod_roots
    rwa [hmonic.leadingCoeff, C_1, one_mul] at this
  have hlt : W.valuation (x ^ n - 1) < 1 := by
    have hmem : x ^ n - 1 ∈ W := sub_mem (pow_mem hx n) (one_mem W)
    have : residue W ⟨_, hmem⟩ = 0 := by
      have e : (⟨_, hmem⟩ : W) = ⟨x, hx⟩ ^ n - 1 := Subtype.ext (by simp)
      rw [e, map_sub, map_pow, h, map_one, sub_self]
    exact (W.valuation_lt_one_iff ⟨_, hmem⟩).1 ((residue_eq_zero_iff _).1 this)
  have heval : x ^ n - 1 = (p.roots.map fun r => x - r).prod := by
    have := congrArg (eval x) hprod
    rw [eval_multiset_prod, Multiset.map_map] at this
    simpa [p] using this
  by_contra hne
  push Not at hne
  rw [heval, map_multiset_prod, Multiset.map_map] at hlt
  refine absurd hlt (not_lt.mpr (le_of_eq (Multiset.prod_eq_one fun v hv => ?_).symm))
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hv
  have hrn : r ^ n = 1 := by
    have := (mem_roots hmonic.ne_zero).1 hr
    simpa [p, sub_eq_zero] using this
  have hrW : r ∈ W := W.mem_of_pow_mem hn.ne' (by rw [hrn]; exact W.one_mem)
  exact le_antisymm ((W.valuation_le_one_iff _).2 (sub_mem hx hrW)) (hne r hrn)

end Lift

namespace NFModel

variable {D} (N : NFModel D)

/-- A place `W` at which a nonzero element of `F_NF` has positive valuation is an NF-point. -/
lemma isNFPoint_of_valuation_lt_one (W : ValuationSubring Ω) {x : Ω} (hx : x ∈ N.FNF)
    (hx0 : x ≠ 0) (hxW : W.valuation x < 1) : N.IsNFPoint W := by
  refine ⟨x⁻¹, N.FNF.inv_mem hx, fun hinv => ?_⟩
  have h1 : W.valuation x * W.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have h2 := (W.valuation_le_one_iff _).2 hinv
  have : W.valuation x * W.valuation x⁻¹ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h2) hxW
  rw [h1] at this
  exact lt_irrefl _ this

variable [IsAlgClosed Ω]

/-- **[AbsTopIII] Prop. 1.8(i), "only if", for NF-curves** (T3 l.2078–2087, proof
l.2099–2106): for `k` torally Kummer-faithful and a nonconstant NF-rational function
`f ∈ Γ(U, 𝒪^×)`, there are `M ≥ 1` and NF-points `x₁, x₂ ∈ U(k_x)` (`[k_{x_i} : k] < ∞`) with
`κ_U(f^M)|x₁ = 0` (all restrictions along `D_{x₁} → Π_U` vanish) and `κ_U(f^M)|x₂ ≠ 0`. -/
theorem exists_restrict_kummerMap_of_isNF (htf : IsTorallyKummerFaithful k) (f : units D)
    (hf : Transcendental k ((f : (F D)ˣ) : F D)) (hNF : N.IsNFFunction ((f : (F D)ˣ) : F D)) :
    ∃ M : ℕ, 0 < M ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
        N.IsNFPoint A ∧
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
            (kummerMap D n (f ^ M)) = 1) ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A), t ∈ A ∧
        N.IsNFPoint A ∧
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
            (kummerMap D n (f ^ M)) = 1) := by
  have hfΩ : Transcendental k (algebraMap (F D) Ω ((f : (F D)ˣ) : F D)) :=
    (transcendental_algebraMap_iff (algebraMap (F D) Ω).injective).2 hf
  obtain ⟨M, hM, W, hk, ht, hint, hfin, hfW, hprim⟩ := exists_point_isPrimitiveRoot D _ hf
  obtain ⟨m, W₂, hk₂, ht₂, hint₂, hfin₂, hfW₂, hval⟩ := exists_point_natCast D _ hf
  refine ⟨M, hM, ⟨W, hk, ht, ?_, hint, hfin, fun n _ => ?_⟩,
    ⟨W₂, hk₂, ht₂, ?_, hint₂, hfin₂, ?_⟩⟩
  · -- `f(x₁) = ζ` with `ζᴹ = 1`: `f - ζ ∈ F_NF` vanishes at `x₁`
    obtain ⟨ζ, hζ, hlt⟩ := exists_pow_eq_one_valuation_sub_lt_one W hfW hM hprim.pow_eq_one
    have hζℚ : IsAlgebraic ℚ ζ := ⟨X ^ M - C 1, X_pow_sub_C_ne_zero hM 1, by simp [hζ]⟩
    have hζk : IsAlgebraic k ζ := ⟨X ^ M - C 1, X_pow_sub_C_ne_zero hM 1, by simp [hζ]⟩
    refine N.isNFPoint_of_valuation_lt_one W
      (sub_mem hNF (N.algebraic_mem ζ hζℚ)) (fun h0 => hfΩ ?_) hlt
    rw [show algebraMap (F D) Ω ((f : (F D)ˣ) : F D) = ζ from sub_eq_zero.1 h0]
    exact hζk
  · letI := Decomposition.residueAlgebra W hk
    exact restrict_eq_one_of_isPrimitiveRoot D W hk
      (Decomposition.residue_algebraMap_residueAlgebra W hk) ht f hfW hprim n
  · -- `f(x₂) = m + 2`: `f - (m + 2) ∈ F_NF` vanishes at `x₂`
    letI := Decomposition.residueAlgebra W₂ hk₂
    have hc : algebraMap k Ω ((m + 2 : ℕ) : k) = ((m + 2 : ℕ) : Ω) := map_natCast _ _
    have hmem : algebraMap (F D) Ω ((f : (F D)ˣ) : F D) - ((m + 2 : ℕ) : Ω) ∈ W₂ := by
      rw [← hc]
      exact sub_mem hfW₂ (hk₂ _)
    have hres : residue W₂ ⟨_, hmem⟩ = 0 := by
      have e : (⟨_, hmem⟩ : W₂) = ⟨_, hfW₂⟩ - ⟨_, hk₂ ((m + 2 : ℕ) : k)⟩ :=
        Subtype.ext (by change _ = _ - algebraMap k Ω _; rw [hc])
      rw [e, map_sub, hval, Decomposition.residue_algebraMap_residueAlgebra, sub_self]
    refine N.isNFPoint_of_valuation_lt_one W₂
      (sub_mem hNF (natCast_mem N.FNF _)) (fun h0 => hfΩ ?_)
      ((W₂.valuation_lt_one_iff ⟨_, hmem⟩).1 ((residue_eq_zero_iff _).1 hres))
    rw [show algebraMap (F D) Ω ((f : (F D)ˣ) : F D) = ((m + 2 : ℕ) : Ω) from sub_eq_zero.1 h0,
      ← hc]
    exact isAlgebraic_algebraMap _
  · letI := Decomposition.residueAlgebra W₂ hk₂
    haveI := hint₂
    haveI := hfin₂
    exact not_restrict_eq_one_of_natCast D W₂ hk₂
      (Decomposition.residue_algebraMap_residueAlgebra W₂ hk₂) ht₂ htf f hM hfW₂ hval

end NFModel

end CurvesJacobian.Kummer
