/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SemiAb
import CurvesJacobian.Kummer.ChernArith
import CurvesJacobian.Kummer.ConstantExtension

/-!
# The arithmetic Chern class `c^{ar} : Div(X_{k̄})^{G_k} → H²(Π_X, μ_n)` (JAC D-d, C1)

Galois model `D : GaloisData k t` of a curve over a field `k` of characteristic `0`
(`Ω` algebraically closed, `H = Gal(Ω/F)`, `Π_X = H ⧸ ⟨⟨inertia⟩⟩ = PiX D`, acting on
`μ_n(Ω)` through `Π_X ↠ G_k`, `SemiAb.mulDistribMulAction_piX_mu`). The Kummer–Chern class of
`Kummer/ChernArith.lean` (`ChernClass.chernClassA`, for a non-trivial action on `μ_n`) applied to
`ρ : H ↠ Π_X` gives, for `f ∈ Ω^{ker ρ}` invariant modulo `n`-th powers (`KummerInv ρ n f`, i.e.
`f` is a function on the profinite universal cover `X̃` with `σ f / f ∈ (Ω^{ker ρ})^{×n}`):

* **`chernArith hf ∈ ContH2 (PiX D) (Mu n Ω)`**, the class of `a(γ, δ) = g_γ · s_γ(g_δ) / g_{γδ}`,
  `s_γ f = f g_γⁿ` (the boundary of the Kummer sequence on `X̃`, [Mzk7] Def. 4.1 over `k`), with
  `chernArith_mul` and `chernArith_mul_pow` (`f ↦ f bⁿ`);
* **`IsArithRep D n E f`**: `f` represents the divisor `E` of `F k̄ = F (baseChange D)` (the
  function field of `X_{k̄}`) modulo `n`, in the Kummer form of `ChernDivisor.IsChernRepDiv`
  (the Kummer characters of `f` and of a local equation of `E` agree on the inertia groups of
  the places of `Ω` over `k̄`). For a `G_k`-invariant `E` (a `k`-rational divisor) the class
  `chernArith` of such an `f` is the arithmetic first Chern class `c^{ar}(𝒪(E)) mod n`.

Existence of representatives for every `G_k`-invariant divisor (from MR5's
`exists_isChernRepDiv` on `X_{k̄}` and `IsChernRepDiv.exists_eq_mul_pow`), uniqueness of the
class, and `res_{Δ_X} c^{ar}(E) = c₁(E_{k̄})` are the remaining parts of milestone C1
(`JAC-plan.md`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField
open CurvesJacobian.Kummer CurvesJacobian.LocAn.SemiAb CurvesJacobian.ChernClass

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.ArithChern

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance 2000] Kummer.group_piX

/-- `ρ : H ↠ Π_X`. -/
noncomputable abbrev rhoPi : D.H →* PiX D := QuotientGroup.mk' _

theorem rhoPi_surjective : Function.Surjective (rhoPi D) := QuotientGroup.mk'_surjective _

/-- A set-theoretic section of `ρ`. -/
noncomputable def sPi : PiX D → D.H := Function.surjInv (rhoPi_surjective D)

theorem rhoPi_sPi (γ : PiX D) : rhoPi D (sPi D γ) = γ := Function.surjInv_eq _ γ

theorem isOpen_stabilizer_H (x : Ω) : IsOpen (MulAction.stabilizer D.H x : Set D.H) :=
  (stabilizer_isOpen_of_isIntegral (K := K₀ k t) x).preimage continuous_subtype_val

theorem isOpen_of_rhoPi (S : Set (PiX D)) (h : IsOpen (rhoPi D ⁻¹' S)) : IsOpen S :=
  (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 h

variable {n : ℕ} [NeZero n]

theorem rhoPi_smul_mu (σ : D.H) (ζ : Mu n Ω) :
    ((Mu.val (rhoPi D σ • ζ) : Ωˣ) : Ω) = σ • ((Mu.val ζ : Ωˣ) : Ω) :=
  hToGk_smul_mu D n σ ζ

variable {D}

/-- **The arithmetic Kummer–Chern class** of `f ∈ Ω^{ker ρ}` invariant modulo `n`-th powers:
the boundary of the Kummer sequence on the profinite universal cover, in `H²(Π_X, μ_n)` with
the cyclotomic action. -/
noncomputable def chernArith {f : Ω} (hf : KummerInv (rhoPi D) n f) : ContH2 (PiX D) (Mu n Ω) :=
  chernClassA (rhoPi_sPi D) (rhoPi_smul_mu D) (isOpen_stabilizer_H D) (isOpen_of_rhoPi D) hf

/-- `c(f f') = c(f) c(f')`. -/
theorem chernArith_mul {f f' : Ω} (hf : KummerInv (rhoPi D) n f)
    (hf' : KummerInv (rhoPi D) n f') (hff' : KummerInv (rhoPi D) n (f * f')) :
    chernArith hff' = chernArith hf * chernArith hf' :=
  chernClassA_mul _ _ _ _ hf hf' hff'

/-- `c(f bⁿ) = c(f)` for `b ∈ (Ω^{ker ρ})ˣ`. -/
theorem chernArith_mul_pow {f b : Ω} (hf : KummerInv (rhoPi D) n f) (hb : IsFix (rhoPi D) b)
    (hb0 : b ≠ 0) (hf' : KummerInv (rhoPi D) n (f * b ^ n)) :
    chernArith hf' = chernArith hf := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm (rhoPi_sPi D) (isOpen_stabilizer_H D) (isOpen_of_rhoPi D) hf
  unfold chernArith
  rw [← chernClassOfA_eq_chernClassA (rhoPi_sPi D) (rhoPi_smul_mu D) (isOpen_stabilizer_H D)
      (isOpen_of_rhoPi D) hf hg hglc,
    ← chernClassOfA_eq_chernClassA (rhoPi_sPi D) (rhoPi_smul_mu D) (isOpen_stabilizer_H D)
      (isOpen_of_rhoPi D) hf' (isAdm_mul_pow hg hb hb0)
      ((hglc.comp₂ (isLocallyConstant_smul (rhoPi_sPi D) (isOpen_stabilizer_H D)
        (isOpen_of_rhoPi D) hb) (· * ·)).comp₂ (IsLocallyConstant.const b) (· / ·))]
  exact chernClassOfA_mul_pow _ _ _ _ hf.ne hf.fix hg hglc hb hb0

attribute [local instance] isFunctionField_F

variable (D n) in
/-- **`f` represents the divisor `E` of `F k̄` modulo `n`** (`E` a divisor of the function field
of `X_{k̄}`): `f ∈ Ω^{ker ρ}` is invariant modulo `n`-th powers under `H` (`KummerInv`), and
`div f ≡ E (mod n)` on `X̃` in Kummer form (as in `ChernClass.IsChernRepDiv`): for every place
`P` of `F k̄`, every place `W` of `Ω` over `P`, every `u ∈ F k̄` with `ord_P u = E(P)` and every
`σ` in the inertia group of `W`, `σ(β)/β = σ(γ)/γ` for `βⁿ = f`, `γⁿ = u`. -/
structure IsArithRep (E : Divisor (kbar k Ω) (F (baseChange D))) (f : Ω) : Prop
    extends KummerInv (rhoPi D) n f where
  loc : ∀ (P : Place (kbar k Ω) (F (baseChange D))) (W : ValuationSubring Ω),
    (∀ x : F (baseChange D), ((x : F (baseChange D)) : Ω) ∈ W ↔ x ∈ P.1) →
    ∀ u : F (baseChange D), u ≠ 0 → P.ord u = E P →
    ∀ σ : (baseChange D).H, (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ∈ GaloisPi1.inertia W →
    ∀ β γ : Ω, β ^ n = f → γ ^ n = (u : Ω) → σ • β / β = σ • γ / γ

/-- The arithmetic Chern class of a representative. -/
noncomputable def IsArithRep.chern {E : Divisor (kbar k Ω) (F (baseChange D))} {f : Ω}
    (hf : IsArithRep D n E f) : ContH2 (PiX D) (Mu n Ω) :=
  chernArith hf.toKummerInv

end CurvesJacobian.LocAn.ArithChern
