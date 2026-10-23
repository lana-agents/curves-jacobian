/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspChern
import CurvesJacobian.Kummer.H2Map

/-!
# Compatibility of the Chern class of `𝒪_X(x)` with the transition maps `μ_{nm} → μ_n`

In the setting of `Kummer/CuspChern.lean` ([AbsTopIII] Prop. 1.4(ii)): a representative `f` of
`𝒪_X(x)` modulo `nm` is also one modulo `n` (`σ f = f g^{nm} = f (g^m)ⁿ`; an `n`-th root of `f`
is the `m`-th power of an `nm`-th root), and the Chern cocycles are related by
`ζ ↦ ζ^m : μ_{nm} → μ_n` (`Mu.transition`), the transition map of `Ẑ(1) = lim μ_n`:

* `IsChernRep.of_mul`: a representative modulo `nm` is a representative modulo `n`;
* `isAdm_pow`, `chernVal_pow_eq`: the admissible choice `g ↦ g^m` and
  `a_{g^m} = (a_g)^m`;
* `chernCocycles_pow`: on locally constant cocycles, the cocycle of `f` modulo `n` (choice
  `g^m`) is the image of the one modulo `nm` (choice `g`) under `Mu.transition`;
* **`chernClassX_of_mul`**: `chernClassX` modulo `n` is the image of `chernClassX` modulo `nm`
  under the coefficient map `TopClass.h2Map (Mu.transition _) : H²(Δ_X, μ_{nm}) → H²(Δ_X, μ_n)`;
* `chiN_transition`: `χ_n = (ζ ↦ ζ^m) ∘ χ_{nm}` (`ZHatOne.transition_proj`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen

namespace CurvesJacobian.ChernClass

universe u

/-! ### Changing `n` in the Chern cocycle (group theory) -/

section Generic

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω] {ρ : G →* Q}
  {s : Q → G} {n m : ℕ}

lemma IsFix.pow {x : Ω} (hx : IsFix ρ x) (m : ℕ) : IsFix ρ (x ^ m) := fun σ hσ ↦ by
  rw [smul_pow', hx σ hσ]

/-- An admissible choice `g` for `f` modulo `nm` gives the admissible choice `g^m` modulo `n`. -/
lemma isAdm_pow {f : Ω} {g : Q → Ω} (hg : IsAdm ρ (n * m) s f g) :
    IsAdm ρ n s f fun γ ↦ g γ ^ m :=
  ⟨fun γ ↦ (hg.fix γ).pow m, fun γ ↦ pow_ne_zero m (hg.ne γ), fun γ ↦ by
    rw [hg.eq γ, ← pow_mul, mul_comm m n]⟩

/-- `a_{g^m} = (a_g)^m`. -/
lemma chernVal_pow_eq (g : Q → Ω) (x : Q × Q) :
    chernVal s (fun γ ↦ g γ ^ m) x = chernVal s g x ^ m := by
  simp only [chernVal, div_pow, mul_pow, smul_pow']

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hs : ∀ γ, ρ (s γ) = γ)
  (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ (n * m) = 1 → σ • ζ = ζ)
  (hμ' : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

/-- The trivial action of `Q` on `μ_n` (as in `Kummer/ChernClass.lean`). -/
local instance instTrivMuQ (n : ℕ) : MulDistribMulAction Q (Mu n Ω) :=
  Pi1.SurfaceGroup.trivialAction Q (Mu n Ω)

/-- **The Chern cocycle modulo `n` is the image of the one modulo `nm`** under
`ζ ↦ ζ^m : μ_{nm} → μ_n` (choices `g` modulo `nm`, `g^m` modulo `n`). -/
lemma chernCocycles_pow [NeZero n] {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ (n * m) s f g) (hglc : IsLocallyConstant g) (x : Q × Q) :
    (chernCocycles hs hμ' hstab hq hf hfix (isAdm_pow hg) (hglc.comp (· ^ m))).1 x =
      Mu.transition (dvd_mul_right n m) ((chernCocycles hs hμ hstab hq hf hfix hg hglc).1 x) := by
  refine Mu.ext (Units.ext ?_)
  rw [Mu.val_transition, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne n)),
    Units.val_pow_eq_pow_val]
  exact chernVal_pow_eq g x

end Generic

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL} [Nonempty (⊤ : X.Opens)]
  {n m : ℕ} {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {ϖ : Ω}

omit [IsAlgClosed k] [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- **A representative of `𝒪_X(x)` modulo `nm` is a representative modulo `n`**:
`σ f = f g^{nm} = f (g^m)ⁿ`, and the `n`-th roots of `f` are the `m`-th powers of its `nm`-th
roots, so they are unramified on `U` and ramified at `W₀` like the `n`-th roots of `ϖ`. -/
theorem IsChernRep.of_mul [NeZero m] {f : Ω} (hf : IsChernRep D eL hH (n * m) U W₀ ϖ f) :
    IsChernRep D eL hH n U W₀ ϖ f := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (m : Ω) := NeZero.charZero
  refine ⟨⟨hf.ne, hf.fix, fun σ ↦ ?_⟩, fun W hW σ hσ β hβ ↦ ?_, fun σ hσ β β₀ hβ hβ₀ ↦ ?_⟩
  · obtain ⟨g, hg, h⟩ := hf.inv σ
    exact ⟨g ^ m, hg.pow m, by rw [h, ← pow_mul, mul_comm m n]⟩
  · obtain ⟨β', rfl⟩ := IsSepClosed.exists_pow_nat_eq β m
    rw [smul_pow', hf.unram W hW σ hσ β' (by rw [pow_mul', hβ])]
  · obtain ⟨β', rfl⟩ := IsSepClosed.exists_pow_nat_eq β m
    obtain ⟨β₀', rfl⟩ := IsSepClosed.exists_pow_nat_eq β₀ m
    rw [smul_pow', smul_pow', ← div_pow, ← div_pow,
      hf.cusp σ hσ β' β₀' (by rw [pow_mul', hβ]) (by rw [pow_mul', hβ₀])]

variable (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

attribute [local instance] instTrivMu

include hk hτ in
/-- `chernClassX` modulo `nm` and modulo `n` computed from one locally constant admissible
choice: `g` modulo `nm`, `g^m` modulo `n`. -/
lemma exists_chernClassX_pow [NeZero n] [NeZero m] {f : Ω}
    (hf : IsChernRep D eL hH (n * m) U W₀ ϖ f) :
    ∃ g, ∃ (hg : IsAdm (rhoX D eL hH) (n * m) (sX hH hk hτ) f g) (hglc : IsLocallyConstant g),
      chernClassX hk hτ hf = chernClassOf (rhoX_sX hH hk hτ)
        (fun σ _ hζ ↦ smul_eq_of_pow_eq_one D (n * m) σ hζ) (isOpen_stabilizer D)
        (isOpen_of_rhoX hk hτ) hf.ne hf.fix hg hglc ∧
      chernClassX hk hτ hf.of_mul = chernClassOf (rhoX_sX hH hk hτ)
        (fun σ _ hζ ↦ smul_eq_of_pow_eq_one D n σ hζ) (isOpen_stabilizer D)
        (isOpen_of_rhoX hk hτ) hf.ne hf.fix (isAdm_pow hg) (hglc.comp (· ^ m)) := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm (rhoX_sX hH hk hτ) (isOpen_stabilizer D)
    (isOpen_of_rhoX hk hτ) hf.toKummerInv
  exact ⟨g, hg, hglc, (chernClassOf_eq_chernClass _ _ _ _ _ _ _).symm,
    (chernClassOf_eq_chernClass _ _ _ _ hf.of_mul.toKummerInv _ _).symm⟩

include hk hτ in
/-- **The first Chern class of `𝒪_X(x)` modulo `n` is the image of the one modulo `nm`** under
the coefficient map `μ_{nm} → μ_n`, `ζ ↦ ζ^m` (`Mu.transition`): for a representative `f`
modulo `nm` (so also modulo `n`, `IsChernRep.of_mul`),
`c₁(𝒪_X(x)) mod n = (ζ ↦ ζ^m)_* (c₁(𝒪_X(x)) mod nm)` in `H²(Δ_X, μ_n)`. -/
theorem chernClassX_of_mul [NeZero n] [NeZero m] {f : Ω}
    (hf : IsChernRep D eL hH (n * m) U W₀ ϖ f) :
    chernClassX hk hτ hf.of_mul =
      TopClass.h2Map (Mu.transition (dvd_mul_right n m)) (fun _ _ ↦ rfl)
        (chernClassX hk hτ hf) := by
  obtain ⟨g, hg, hglc, h1, h2⟩ := exists_chernClassX_pow hk hτ hf
  rw [h1, h2, chernClassOf, chernClassOf, TopClass.h2Map_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext (funext fun x ↦ ?_))
  exact chernCocycles_pow _ _ _ _ _ hf.ne hf.fix hg hglc x

variable {x : X} {π : (F D)ˣ}

/-- **`χ_n = (ζ ↦ ζ^m) ∘ χ_{nm}`**: the tame characters `I_x ≅ Ẑ(1) ↠ μ_n` are compatible with
the transition maps of `Ẑ(1) = lim μ_n`. -/
lemma chiN_transition [NeZero n] [NeZero m] (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (i : cuspInertia D X eL hH U W₀) :
    Mu.transition (dvd_mul_right n m) (chiN hH hk hτ (n * m) U hgen hUx hW₀ hW₀U hπW hπ i) =
      chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ i :=
  ZHatOne.transition_proj (i := kIdx D n) (j := kIdx D (n * m)) (dvd_mul_right n m) _

end Curve

end CurvesJacobian.ChernClass
