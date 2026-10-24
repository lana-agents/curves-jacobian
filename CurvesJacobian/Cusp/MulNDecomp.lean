/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.MulNSubgroup
import CurvesJacobian.Cusp.DupDecomp

/-!
# The `[N]`-subgroup `Π_U ⊆ Π_{E∖O}` is preserved by isomorphisms ([AbsTopII] Cor 3.4, step G2)

The general-`N` version of `Cusp/DupDecomp.lean` (`N = 2`). Let `E` be an elliptic curve over a
number field `K` with `#E(K)[N] = N²` (`TorsionCardN E N`), `X = E ∖ {O}`, `Π = Π_X ↠ G_K` with
kernel `Δ`, and `Π_U = mulNPiU` the image of `π₁(E ∖ E[N])` under `[N]` (`MulNSubgroup.lean`,
where `Π_U ⊓ Δ = Δ^N [Δ, Δ]` is proved). Here:

* `CuspidalExt.Iso.map_eq_of_cuspDecompN`: group theory (G2c): `Π_U = D · Δ^N [Δ, Δ]` for a
  cuspidal decomposition group `D` surjecting onto `G`, and an isomorphism of cuspidal extensions
  maps cusps to cusps, commensurators to commensurators and `Δ^N [Δ, Δ]` to `Δ^N [Δ, Δ]`.
* `ordInfty_mulByNEndo_genX_neg`: `x ∘ [N]` has a pole at infinity
  (`x(N • P) = Φ_N(x) / Ψ_N²(x)`, of order `2 (N² - 1) - 2 N² = -2`).
* `exists_sigmaN_eq`: the fibre of `[N]` has exactly the `N²` translates `ε ∘ σ_T`, `T ∈ E[N]`
  (a degree count `[K(E) : [N]^* K(E)] = N²`).
* `apply_eq_of_preservesN`: an automorphism fixing `ε([N]^* K[E])` and a place over the place at
  infinity of the source fixes `ε(B_N)` (translation by an affine point makes `x` regular at
  infinity, `eq_zero_of_translateAut_preserves₂`).
* **`commensurator_le_mulNPiU`** (G2b): every cuspidal decomposition group lies in `Π_U`;
* **`map_mulNPiU`**: every isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal extensions maps
  `Π_{U₁}` onto `Π_{U₂}`.

`Topics in Absolute Anabelian Geometry II.txt` l.4540–4600 (Cor 3.4).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### The group-theoretic step (G2c) for `Δ^N [Δ, Δ]` -/

/-- **(G2c) for `[N]`, one inclusion.** Let `H_A ⊆ Π_A` with `H_A ⊓ Δ_A = Δ_A^N [Δ_A, Δ_A]`,
containing the commensurator `D` of a cuspidal inertia group `I₀` with `pr(D) = G_A`, and let
`H_B ⊆ Π_B` contain `Δ_B^N [Δ_B, Δ_B]` and the commensurators of all cuspidal inertia groups.
Then `Φ(H_A) ⊆ H_B`. -/
theorem _root_.Belyi.Anabelian.CuspidalExt.Iso.map_le_of_cuspDecompN {A B : CuspidalExt.{u}}
    (Φ : A.Iso B) (N : ℕ) {HA : Subgroup A.Pi} {HB : Subgroup B.Pi}
    (hA : HA ⊓ A.Delta = mulNClosure A.Delta N) (hB : mulNClosure B.Delta N ≤ HB)
    {I₀ : Subgroup A.Pi} (hI₀ : I₀ ∈ A.cusps)
    (hsurj : ∀ y : A.G, ∃ d ∈ Subgroup.Commensurable.commensurator I₀, A.pr d = y)
    (hdA : Subgroup.Commensurable.commensurator I₀ ≤ HA)
    (hdB : ∀ I ∈ B.cusps, Subgroup.Commensurable.commensurator I ≤ HB) :
    HA.map Φ.pi.toMulEquiv.toMonoidHom ≤ HB := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdx⟩ := hsurj (A.pr x)
  have hxd : x * d⁻¹ ∈ mulNClosure A.Delta N := by
    rw [← hA]
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (hdA hd)), ?_⟩
    change A.pr (x * d⁻¹) = 1
    rw [map_mul, map_inv, hdx, mul_inv_cancel]
  have h1' : Φ.pi (x * d⁻¹) ∈ mulNClosure B.Delta N := by
    rw [← Φ.map_mulNClosure₂ N]
    exact ⟨_, hxd, rfl⟩
  have h2 : Φ.pi d ∈ HB := by
    refine hdB _ ((Φ.cusps_map I₀).1 hI₀) ?_
    rw [← commensurator_map_mulEquiv]
    exact ⟨d, hd, rfl⟩
  have e : Φ.pi x = Φ.pi (x * d⁻¹) * Φ.pi d := by rw [← map_mul, inv_mul_cancel_right]
  change Φ.pi x ∈ HB
  rw [e]
  exact mul_mem (hB h1') h2

/-- **(G2c) for `[N]`**: if on both sides `H ⊓ Δ = Δ^N [Δ, Δ]`, `H` contains the commensurators of
all cuspidal inertia groups, and one of these commensurators surjects onto `G`, then
`Φ(H_A) = H_B`. -/
theorem _root_.Belyi.Anabelian.CuspidalExt.Iso.map_eq_of_cuspDecompN {A B : CuspidalExt.{u}}
    (Φ : A.Iso B) (N : ℕ) {HA : Subgroup A.Pi} {HB : Subgroup B.Pi}
    (hA : HA ⊓ A.Delta = mulNClosure A.Delta N) (hB : HB ⊓ B.Delta = mulNClosure B.Delta N)
    {I₀ : Subgroup A.Pi} (hI₀ : I₀ ∈ A.cusps)
    (hsurjA : ∀ y : A.G, ∃ d ∈ Subgroup.Commensurable.commensurator I₀, A.pr d = y)
    {J₀ : Subgroup B.Pi} (hJ₀ : J₀ ∈ B.cusps)
    (hsurjB : ∀ y : B.G, ∃ d ∈ Subgroup.Commensurable.commensurator J₀, B.pr d = y)
    (hdA : ∀ I ∈ A.cusps, Subgroup.Commensurable.commensurator I ≤ HA)
    (hdB : ∀ I ∈ B.cusps, Subgroup.Commensurable.commensurator I ≤ HB) :
    HA.map Φ.pi.toMulEquiv.toMonoidHom = HB := by
  refine le_antisymm (Φ.map_le_of_cuspDecompN N hA (hB.symm.le.trans inf_le_left) hI₀ hsurjA
    (hdA _ hI₀) hdB) ?_
  have h := Φ.symm.map_le_of_cuspDecompN N hB (hA.symm.le.trans inf_le_left) hJ₀ hsurjB
    (hdB _ hJ₀) hdA
  intro y hy
  exact ⟨Φ.pi.symm y, h ⟨y, hy, rfl⟩, Φ.pi.apply_symm_apply y⟩

/-! ### (G2b), field-theoretic part: the fibre of `[N]` over the place at infinity -/

section FibreN

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [CharZero K] {E : WeierstrassCurve K} [E.IsElliptic] {N : ℕ}
  [NeZero N]

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField
local notation "ι" => algebraMap (coverRingN E N) E.toAffine.FunctionField

/-- **`x ∘ [N]` has a pole at infinity**: `x(N • P) = Φ_N(x) / Ψ_N²(x)` has order
`2 (N² - 1) - 2 N² = -2` at the place at infinity. -/
lemma ordInfty_mulByNEndo_genX_neg :
    ordInfty E.toAffine (mulByNEndo N (transcendental_N E N) (genX E.toAffine)) < 0 := by
  have hN : ((N : ℤ) : K) ≠ 0 := intCast_N_ne_zero N
  have h1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [mulByNEndo_genX, xCoord_nsmul_genericPoint two_ne_zero hN, aeval_def, aeval_def,
    ← Polynomial.eval_map, ← Polynomial.eval_map,
    ordInfty_div (eval_map_genX_ne_zero₂ (E.Φ_ne_zero _)) (eval_map_genX_ne_zero₂
      (E.ΨSq_ne_zero hN)),
    ordInfty_eval_map_genX₂ (E.Φ_ne_zero _), ordInfty_eval_map_genX₂ (E.ΨSq_ne_zero hN),
    E.natDegree_Φ, E.natDegree_ΨSq hN, Int.natAbs_natCast]
  push_cast [Nat.cast_sub h1]
  omega

/-- A map `ρ : B_N = K[E][1/ψ_N] → L` into a field which is injective on `[N]^* K[E]` is
injective. -/
lemma injective_of_comp_mulByNHom {L : Type*} [Field L] (ρ : coverRingN E N →+* L)
    (h : Function.Injective (ρ.comp (mulByNHom E N))) : Function.Injective ρ :=
  injective_of_isIntegral (mulByNHom E N) (mulByNHom_isIntegral E N) ρ h

/-- Two maps `B_N → L` agreeing on `[N]^* K[E]` have extensions to `K(E)` agreeing on
`[N]^* K(E)`. -/
lemma lift_mulByNEndoN {L : Type*} [Field L] (ρ ρ' : coverRingN E N →+* L)
    (hρ : Function.Injective (ρ.comp (mulByNHom E N)))
    (hρ' : Function.Injective (ρ'.comp (mulByNHom E N)))
    (h : ρ.comp (mulByNHom E N) = ρ'.comp (mulByNHom E N)) (u : FF) :
    IsFractionRing.lift (injective_of_comp_mulByNHom ρ hρ)
        (mulByNEndo N (transcendental_N E N) u) =
      IsFractionRing.lift (injective_of_comp_mulByNHom ρ' hρ')
        (mulByNEndo N (transcendental_N E N) u) := by
  have : (IsFractionRing.lift (injective_of_comp_mulByNHom ρ hρ)).comp
      (mulByNEndo (W := E.toAffine) N (transcendental_N E N)) =
      (IsFractionRing.lift (injective_of_comp_mulByNHom ρ' hρ')).comp
        (mulByNEndo (W := E.toAffine) N (transcendental_N E N)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← algebraMap_mulByNHom E N a, IsFractionRing.lift_algebraMap,
        IsFractionRing.lift_algebraMap]
      exact RingHom.congr_fun h a)
  exact RingHom.congr_fun this u

open Classical in
/-- **The fibre of `[N]` has exactly the `N²` translates**: if `ρ, ε : B_N → L` agree on
`[N]^* K[E]` (and are injective there), then `ρ = ε ∘ σ_T` for a translation `σ_T` by
`T ∈ E[N]` (`#E(K)[N] = N²`). -/
theorem exists_sigmaN_eq (hcard : TorsionCardN E N) {L : Type*} [Field L]
    (ε ρ : coverRingN E N →+* L) (hε : Function.Injective (ε.comp (mulByNHom E N)))
    (h : ρ.comp (mulByNHom E N) = ε.comp (mulByNHom E N)) :
    ∃ P : E.toAffine.torsion N, ρ = ε.comp (sigmaN P).toRingHom := by
  set L' := (mulByNEndoAlgHom (W := E.toAffine) N (transcendental_N E N)).fieldRange
  have hεi := injective_of_comp_mulByNHom ε hε
  letI : Algebra L' L := ((IsFractionRing.lift hεi).comp (algebraMap L' FF)).toAlgebra
  have hdeg : Module.finrank L' FF = N ^ 2 :=
    finrank_mulByNFieldRange_eq_sq_of_isCoprime_ΨSq_adjacent two_ne_zero (intCast_N_ne_zero N)
      (isCoprime_ΨSq_adjacent two_ne_zero _)
  haveI : Module.Free L' FF := Module.Free.of_divisionRing L' FF
  haveI : Module.Finite L' FF := Module.finite_of_finrank_pos (by
    rw [hdeg]; exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 2)
  have hSinj : ∀ ρ' : {ρ' : coverRingN E N →+* L //
      ρ'.comp (mulByNHom E N) = ε.comp (mulByNHom E N)},
      Function.Injective (ρ'.1.comp (mulByNHom E N)) := fun ρ' ↦ by rw [ρ'.2]; exact hε
  let Φ : {ρ' : coverRingN E N →+* L // ρ'.comp (mulByNHom E N) = ε.comp (mulByNHom E N)} →
      (FF →ₐ[L'] L) := fun ρ' ↦
    { IsFractionRing.lift (injective_of_comp_mulByNHom ρ'.1 (hSinj ρ')) with
      commutes' := fun l ↦ by
        obtain ⟨u, hu⟩ := AlgHom.mem_fieldRange.1 l.2
        change IsFractionRing.lift (injective_of_comp_mulByNHom ρ'.1 (hSinj ρ')) (l : FF) =
          IsFractionRing.lift hεi (l : FF)
        rw [← hu]
        exact lift_mulByNEndoN ρ'.1 ε (hSinj ρ') hε ρ'.2 u }
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ hg
    refine Subtype.ext (RingHom.ext fun b ↦ ?_)
    have h' := DFunLike.congr_fun hg (ι b)
    have e : ∀ g, (Φ g) (ι b) = g.1 b := fun g ↦
      IsFractionRing.lift_algebraMap (injective_of_comp_mulByNHom g.1 (hSinj g)) b
    rwa [e, e] at h'
  haveI : Finite {ρ' : coverRingN E N →+* L //
      ρ'.comp (mulByNHom E N) = ε.comp (mulByNHom E N)} :=
    Finite.of_injective Φ hΦ
  have hcardS : Nat.card {ρ' : coverRingN E N →+* L //
      ρ'.comp (mulByNHom E N) = ε.comp (mulByNHom E N)} ≤ N ^ 2 :=
    (Nat.card_le_card_of_injective Φ hΦ).trans
      ((card_algHom_le_finrank L' FF L).trans hdeg.le)
  let ψ : E.toAffine.torsion N →
      {ρ' : coverRingN E N →+* L // ρ'.comp (mulByNHom E N) = ε.comp (mulByNHom E N)} :=
    fun P ↦ ⟨ε.comp (sigmaN P).toRingHom, RingHom.ext fun a ↦ by
      change ε (sigmaN P (mulByNHom E N a)) = ε (mulByNHom E N a)
      rw [sigmaN_mulByNHom]⟩
  have hψ : Function.Injective ψ := fun P Q hPQ ↦ sigmaN_injective
    (RingEquiv.ext fun b ↦ hεi (RingHom.congr_fun (congrArg Subtype.val hPQ) b))
  have hT : N ^ 2 = Nat.card (E.toAffine.torsion N) := hcard.symm
  obtain ⟨P, hP⟩ := (hψ.bijective_of_nat_card_le (hcardS.trans hT.le)).2 ⟨ρ, h⟩
  exact ⟨P, (congrArg Subtype.val hP).symm⟩

open Classical in
/-- **(G2b) for `[N]`, field form.** Let `ε : B_N → L` be injective on `[N]^* K[E]`, `W ⊆ L` a
valuation subring lying over the place at infinity of the source `K(E)` (via the extension `εL` of
`ε`), and `τ` an automorphism of `L` fixing `ε([N]^* K[E])` and preserving `W`. Then `τ` fixes
`ε(B_N)`: the place at infinity splits completely in `[N]` (`E[N]` is rational). -/
theorem apply_eq_of_preservesN (hcard : TorsionCardN E N) {L : Type*} [Field L]
    (ε : coverRingN E N →+* L) (hε : Function.Injective (ε.comp (mulByNHom E N)))
    (εL : FF →+* L) (hεL : ∀ b, εL (ι b) = ε b) (τ : L ≃+* L)
    (hτ : ∀ a, τ (ε (mulByNHom E N a)) = ε (mulByNHom E N a)) (W : ValuationSubring L)
    (hW : W.comap εL = ordInftyVS₂ E.toAffine)
    (hτW : ∀ z, τ z ∈ W ↔ z ∈ W) (b : coverRingN E N) : τ (ε b) = ε b := by
  obtain ⟨P, hP⟩ := exists_sigmaN_eq hcard ε (τ.toRingHom.comp ε) hε
    (RingHom.ext fun a ↦ hτ a)
  have hL : τ.toRingHom.comp εL = εL.comp (tauN P).toRingEquiv.toRingHom :=
    IsLocalization.ringHom_ext (nonZeroDivisors (coverRingN E N)) (RingHom.ext fun c ↦ by
      have e1 := RingHom.congr_fun hP c
      have e2 := algebraMap_sigmaN P c
      change τ (εL (ι c)) = εL ((tauN P) (ι c))
      rw [← e2, hεL, hεL]
      exact e1)
  have hpres : ∀ f : FF, translateAut (P : E.toAffine.Point) f ∈ ordInftyVS₂ E.toAffine ↔
      f ∈ ordInftyVS₂ E.toAffine := fun f ↦ by
    have e3 : τ (εL f) = εL (tauN P f) := RingHom.congr_fun hL f
    rw [← hW, ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hτW (εL f), e3]
    rfl
  have hP0 : P = 0 := Subtype.ext ((eq_zero_of_translateAut_preserves₂ _ hpres).trans
    (ZeroMemClass.coe_zero _).symm)
  subst hP0
  have e4 := RingHom.congr_fun hP b
  change τ (ε b) = ε (sigmaN 0 b) at e4
  rw [e4, sigmaN_zero]

end FibreN

/-! ### (G2b) The cuspidal decomposition groups of `Π_{E∖O}` lie in `Π_U` for `[N]` -/

section G2bN

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K) [E.IsElliptic]
  (N : ℕ) [NeZero N]

attribute [local instance] isAlgClosure_of_isAlgebraic

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField
local notation "ι" => algebraMap (coverRingN E N) E.toAffine.FunctionField

/-- `σ : K(X̄_Ω)^alg ≅ K(V̄_Ω)^alg` over `[N]^* : L₀(X) → L₀(V)`, `V = E ∖ E[N]`. -/
abbrev mulNσ :
    FFClosure (geomCurve Ω (hypCurveX E)) ≃+* FFClosure (geomCurve Ω (hypCurveVN E N)) :=
  coverσ Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N) (compl_VNE_nonempty E N)
    (mulByNXMor E N)

/-- `ε : B_N = Γ(E ∖ E[N]) → K(X̄_Ω)^alg`, the embedding through `σ⁻¹`. -/
def mulNEps : coverRingN E N →+* FFClosure (geomCurve Ω (hypCurveX E)) :=
  (mulNσ Ω E N).symm.toRingHom.comp ((secEmb Ω (hypCurveVN E N)
    (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N))).comp
      (sectionsVNEEquiv E N).symm.toRingHom)

lemma coverRing_mulByNXMor :
    coverRing (hypCurveX E) (hypCurveVN E N) (mulByNXMor E N) = mulByNXHom E N := by
  have h : CommRingCat.ofHom (coverRing (hypCurveX E) (hypCurveVN E N) (mulByNXMor E N)) =
      CommRingCat.ofHom (mulByNXHom E N) :=
    Spec.map_injective (specMap_coverRing (hypCurveX E) (hypCurveVN E N) (mulByNXMor E N))
  exact congrArg CommRingCat.Hom.hom h

lemma mulNEps_mulByNHom (a : A) : mulNEps Ω E N (mulByNHom E N a) = dupKappa₂ Ω E a := by
  have h := coverσ_secEmb Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
    (compl_VNE_nonempty E N) (mulByNXMor E N) ((sectionsXEAlgEquiv E).symm a)
  have hr : coverRing (hypCurveX E) (hypCurveVN E N) (mulByNXMor E N)
      ((sectionsXEAlgEquiv E).symm a) = (sectionsVNEEquiv E N).symm (mulByNHom E N a) := by
    rw [coverRing_mulByNXMor]
    change (sectionsVNEEquiv E N).symm (mulByNHom E N (sectionsXEAlgEquiv E
      ((sectionsXEAlgEquiv E).symm a))) = _
    rw [AlgEquiv.apply_symm_apply]
  change (mulNσ Ω E N).symm (secEmb Ω (hypCurveVN E N)
    (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N))
    ((sectionsVNEEquiv E N).symm (mulByNHom E N a))) = secEmb Ω (hypCurveX E)
      (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E)) ((sectionsXEAlgEquiv E).symm a)
  rw [← hr, ← h, RingEquiv.symm_apply_apply]

lemma mulNEps_comp_injective : Function.Injective ((mulNEps Ω E N).comp (mulByNHom E N)) := by
  have h : (mulNEps Ω E N).comp (mulByNHom E N) = dupKappa₂ Ω E :=
    RingHom.ext (mulNEps_mulByNHom Ω E N)
  rw [h]
  exact dupKappa_injective₂ Ω E

/-- The automorphism `σ τ σ⁻¹` of `K(V̄_Ω)^alg` over `L₀(V)`, for `τ` fixing `σ⁻¹(L₀(V))`. -/
def mulNConjAut
    (τ : FFClosure (geomCurve Ω (hypCurveX E)) ≃ₐ[arithFF Ω (hypCurveX E) (compl_XE_nonempty E)]
      FFClosure (geomCurve Ω (hypCurveX E)))
    (hfix : ∀ c : arithFF Ω (hypCurveVN E N) (compl_VNE_nonempty E N),
      τ ((mulNσ Ω E N).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveVN E N))) c)) =
        (mulNσ Ω E N).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveVN E N))) c)) :
    FFClosure (geomCurve Ω (hypCurveVN E N)) ≃ₐ[arithFF Ω (hypCurveVN E N)
      (compl_VNE_nonempty E N)] FFClosure (geomCurve Ω (hypCurveVN E N)) :=
  { ((mulNσ Ω E N).symm.trans τ.toRingEquiv).trans (mulNσ Ω E N) with
    commutes' := fun c ↦ by
      change mulNσ Ω E N (τ ((mulNσ Ω E N).symm (algebraMap _ _ c))) = _
      rw [hfix, RingEquiv.apply_symm_apply] }

variable {E N} in
/-- **`τ ∈ Gal(K(X̄_Ω)^alg / L₀)` fixing `ε(B_N)` acts through `Π_U`.** -/
theorem arithAction_mem_mulNPiU_of_fix (hcard : TorsionCardN E N)
    (τ : FFClosure (geomCurve Ω (hypCurveX E)) ≃ₐ[arithFF Ω (hypCurveX E) (compl_XE_nonempty E)]
      FFClosure (geomCurve Ω (hypCurveX E)))
    (hτ : ∀ b, τ (mulNEps Ω E N b) = mulNEps Ω E N b) :
    arithAction Ω (hypCurveX E) (compl_XE_nonempty E) τ ∈ mulNPiU Ω E N := by
  have hV : ∀ a : Γ(curveE E, VNE E N), τ ((mulNσ Ω E N).symm (secEmb Ω (hypCurveVN E N)
      (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N)) a)) =
        (mulNσ Ω E N).symm (secEmb Ω (hypCurveVN E N)
          (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N)) a) := fun a ↦ by
    have h := hτ (sectionsVNEEquiv E N a)
    change τ ((mulNσ Ω E N).symm (secEmb Ω (hypCurveVN E N)
      (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N))
      ((sectionsVNEEquiv E N).symm (sectionsVNEEquiv E N a)))) = (mulNσ Ω E N).symm (secEmb Ω
        (hypCurveVN E N) (isAffineOpen_U (hypCurveVN E N) (compl_VNE_nonempty E N))
          ((sectionsVNEEquiv E N).symm (sectionsVNEEquiv E N a))) at h
    rwa [RingEquiv.symm_apply_apply] at h
  have hfix : ∀ c : arithFF Ω (hypCurveVN E N) (compl_VNE_nonempty E N),
      τ ((mulNσ Ω E N).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveVN E N))) c)) =
        (mulNσ Ω E N).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveVN E N))) c) :=
    fun c ↦ by
      obtain ⟨a, b, rfl⟩ := exists_eq_div_secToArithFF Ω (hypCurveVN E N)
        (compl_VNE_nonempty E N) c
      rw [map_div₀, map_div₀, map_div₀]
      exact congrArg₂ (· / ·) (hV a) (hV b)
  obtain ⟨t₀, ht₀⟩ := exists_coverPiHom_arithAction Ω (hypCurveX E) (compl_XE_nonempty E)
    (hypCurveVN E N) (compl_VNE_nonempty E N) (mulByNXMor E N) (mulNσ Ω E N)
    (coverσ_algebraMap Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
      (compl_VNE_nonempty E N) (mulByNXMor E N))
  have hconj : arithConj Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
      (compl_VNE_nonempty E N) (mulByNXMor E N) (mulNσ Ω E N)
      (coverσ_algebraMap Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
        (compl_VNE_nonempty E N) (mulByNXMor E N)) (mulNConjAut Ω E N τ hfix) = τ :=
    AlgEquiv.ext fun x ↦ by
      rw [arithConj_apply]
      change (mulNσ Ω E N).symm (mulNσ Ω E N (τ ((mulNσ Ω E N).symm (mulNσ Ω E N x)))) = τ x
      rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  have h1 := ht₀ (mulNConjAut Ω E N τ hfix)
  rw [hconj] at h1
  have hmem : coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
      (compl_VNE_nonempty E N) (mulByNXMor E N) (arithAction Ω (hypCurveVN E N)
        (compl_VNE_nonempty E N) (mulNConjAut Ω E N τ hfix)) ∈ mulNPiU Ω E N := ⟨_, rfl⟩
  rw [h1] at hmem
  have h2 := (mulNPiU_normal Ω hcard).conj_mem _ hmem t₀⁻¹
  rwa [show ∀ y, t₀⁻¹ * (t₀ * y * t₀⁻¹) * t₀⁻¹⁻¹ = y from fun y ↦ by group] at h2

/-- The extension `K(E) → K(X̄_Ω)^alg` of `ε`. -/
abbrev mulNEpsL : FF →+* FFClosure (geomCurve Ω (hypCurveX E)) :=
  IsFractionRing.lift (injective_of_comp_mulByNHom (mulNEps Ω E N) (mulNEps_comp_injective Ω E N))

lemma mulNEpsL_algebraMap (b : coverRingN E N) : mulNEpsL Ω E N (ι b) = mulNEps Ω E N b :=
  IsFractionRing.lift_algebraMap _ _

lemma mulNEpsL_mulByNEndo (a : A) :
    mulNEpsL Ω E N (mulByNEndo N (transcendental_N E N) (algebraMap A FF a)) =
      dupKappa₂ Ω E a := by
  rw [← algebraMap_mulByNHom E N a, mulNEpsL_algebraMap, mulNEps_mulByNHom]

/-- **A place over the cusp of `X` lying over the place at infinity of the source of `[N]`.** -/
theorem exists_isCuspPlace_comap_mulNEpsL :
    ∃ W, IsCuspPlace Ω (hypCurveX E) (compl_XE_nonempty E) W ∧
      W.comap (mulNEpsL Ω E N) = ordInftyVS₂ E.toAffine := by
  obtain ⟨W, hW⟩ := exists_valuationSubring_comap_eq₂ (mulNEpsL Ω E N) (ordInftyVS₂ E.toAffine)
  have hmem : ∀ f, mulNEpsL Ω E N f ∈ W ↔ f ∈ ordInftyVS₂ E.toAffine := fun f ↦ by
    rw [← hW]
    rfl
  have hK : ∀ k : K, algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) (algebraMap K Ω k) ∈
      W := fun k ↦ by
    have e1 : algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) (algebraMap K Ω k) =
        dupKappa₂ Ω E (algebraMap K A k) := by
      change _ = secEmb Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))
        ((sectionsXEAlgEquiv E).symm (algebraMap K A k))
      rw [AlgEquiv.commutes]
      exact (secEmb_algebraMap Ω (hypCurveX E)
        (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E)) k).symm
    rw [e1, ← mulNEpsL_mulByNEndo Ω E N, ← IsScalarTower.algebraMap_apply,
      mulByNEndo_algebraMap_base, hmem]
    exact algebraMap_mem_ordInftyVS₂ k
  refine ⟨W, ⟨fun c ↦ ?_, fun h ↦ ?_⟩, hW⟩
  · let φ : K →+* W := ((algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E)))).comp
      (algebraMap K Ω)).codRestrict W hK
    have hint : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
    have h2 : IsIntegral W (algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) c) :=
      hint.map_of_comp_eq φ (algebraMap Ω _) (RingHom.ext fun _ ↦ rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]
    exact y.2
  · have h3 := h ((sectionsXEAlgEquiv E).symm (mk E.toAffine (C X)))
    have e2 : secEmb Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))
        ((sectionsXEAlgEquiv E).symm (mk E.toAffine (C X))) =
          mulNEpsL Ω E N (mulByNEndo N (transcendental_N E N) (genX E.toAffine)) :=
      (mulNEpsL_mulByNEndo Ω E N (mk E.toAffine (C X))).symm
    rw [e2, hmem, mem_ordInftyVS₂] at h3
    exact absurd h3 (not_le.2 ordInfty_mulByNEndo_genX_neg)

variable {E N} in
/-- **(G2b) for one place**: the decomposition group of the place `W₀` (over the cusp of `X`, over
the place at infinity of the source of `[N]`) lies in `Π_U`. -/
theorem arithDecomp_le_mulNPiU (hcard : TorsionCardN E N)
    {W : ValuationSubring (FFClosure (geomCurve Ω (hypCurveX E)))}
    (hW : W.comap (mulNEpsL Ω E N) = ordInftyVS₂ E.toAffine) :
    arithDecomp Ω (hypCurveX E) (compl_XE_nonempty E) W ≤ mulNPiU Ω E N := by
  rintro _ ⟨τ, hτ, rfl⟩
  refine arithAction_mem_mulNPiU_of_fix Ω hcard τ fun b ↦ ?_
  exact apply_eq_of_preservesN hcard (mulNEps Ω E N) (mulNEps_comp_injective Ω E N)
    (mulNEpsL Ω E N) (mulNEpsL_algebraMap Ω E N) τ.toRingEquiv
    (fun a ↦ by
      change τ (mulNEps Ω E N (mulByNHom E N a)) = mulNEps Ω E N (mulByNHom E N a)
      rw [mulNEps_mulByNHom]
      exact τ.commutes ⟨_, dupKappa_mem₂ Ω E a⟩)
    W hW (fun z ↦ hτ z) b

variable {E N} in
/-- **[AbsTopII] Cor 3.4 (G2b) for `[N]`**: for `E` with `#E(K)[N] = N²`, the commensurator
(cuspidal decomposition group) of every cuspidal inertia group of `Π_{E∖O}` lies in `Π_U`. -/
theorem commensurator_le_mulNPiU (hcard : TorsionCardN E N)
    {I} (hI : I ∈ (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).cusps) :
    Subgroup.Commensurable.commensurator I ≤ mulNPiU Ω E N := by
  haveI := mulNPiU_normal Ω hcard
  obtain ⟨W₀, hW₀, hW₀c⟩ := exists_isCuspPlace_comap_mulNEpsL Ω E N
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω (hypCurveX E) (compl_XE_nonempty E)).1 hI
  have h1 := subsingleton_compl_geomOpen_XE₂ Ω E
  obtain ⟨n, -, hn⟩ := exists_comap_eq_of_isCuspPlace₂ Ω (hypCurveX E) (compl_XE_nonempty E) h1
    hW₀ hW
  subst hn
  rw [arithInertia_comap, ← commensurator_map_mulEquiv,
    commensurator_arithInertia Ω (hypCurveX E) (compl_XE_nonempty E) hW₀]
  rintro _ ⟨d, hd, rfl⟩
  exact (mulNPiU_normal Ω hcard).conj_mem d (arithDecomp_le_mulNPiU Ω hcard hW₀c hd) _

end G2bN

/-! ### Transport along isomorphisms of cuspidal extensions -/

section TransportN

variable {K₁ : Type u} [Field K₁] [NumberField K₁] (Ω₁ : Type u) [Field Ω₁] [Algebra K₁ Ω₁]
  [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁] [CharZero Ω₁] {E₁ : WeierstrassCurve K₁}
  [E₁.IsElliptic]
  {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {E₂ : WeierstrassCurve K₂}
  [E₂.IsElliptic] {N : ℕ} [NeZero N]

/-- **[AbsTopII] Cor 3.4, step G2 for `[N]`: the `[N]`-subgroup is preserved by every
isomorphism.** For elliptic curves `E_i` over number fields with `#E_i(K_i)[N] = N²`, every
isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal extensions maps `Π_{U₁}` onto `Π_{U₂}`
(`Π_{U_i}` = image of `π₁(E_i ∖ E_i[N])` under `[N]`). -/
theorem map_mulNPiU
    (Φ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Iso
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)))
    (hE₁ : TorsionCardN E₁ N) (hE₂ : TorsionCardN E₂ N) :
    (mulNPiU Ω₁ E₁ N).map Φ.pi.toMulEquiv.toMonoidHom = mulNPiU Ω₂ E₂ N := by
  obtain ⟨I₀, hI₀, hs₁⟩ := exists_cusp_commensurator_surj₂ Ω₁ E₁
  obtain ⟨J₀, hJ₀, hs₂⟩ := exists_cusp_commensurator_surj₂ Ω₂ E₂
  exact Φ.map_eq_of_cuspDecompN N (mulNPiU_inf_Delta Ω₁ hE₁) (mulNPiU_inf_Delta Ω₂ hE₂)
    hI₀ hs₁ hJ₀ hs₂ (fun _ hI ↦ commensurator_le_mulNPiU Ω₁ hE₁ hI)
    (fun _ hI ↦ commensurator_le_mulNPiU Ω₂ hE₂ hI)

end TransportN

end CurvesJacobian.Cusp
