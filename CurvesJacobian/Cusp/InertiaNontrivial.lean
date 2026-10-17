/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Galois.PiCharacters
import ContinuousKummerTheory.Curve.TameChar

/-!
# Nontriviality of cuspidal inertia groups via Kummer covers (MR8.3)

Setting of `CurvesJacobian/Cusp/Inertia.lean`. Let `W ⊇ k` be a place of `Ω` and `v ∈ F` a
uniformiser at `W` which is a unit at every place centred on the open `U`. Then the Kummer cover
`F(v^{1/n})/F` is unramified over `U` but totally (tamely) ramified at `W`
([AbsTopIII] Prop. 1.4 (i), continuous-kummer-theory `Curve.evalTriv_kummer_surjective`), so the
Kummer character `χ_v : H → μ_n` factors through `π₁ᵉᵗ(U) = H ⧸ ⟨⟨S_U⟩⟩` and maps `I_W ∩ H` onto
`μ_n`. Hence the cuspidal inertia group of `W` in `π₁ᵉᵗ(U)` is nontrivial, and even surjects onto
`μ_n` through the Kummer cover:

* `CurvesJacobian.Cusp.kernel_SU_le_ker_charOfH`: a character of `H` killing the inertia elements
  of the places centred on `U` kills `⟨⟨S_U⟩⟩`;
* `CurvesJacobian.Cusp.chartHom_ne_one_of_charOfH`: hence `σ ∈ H` with `χ(σ) ≠ 1` acts
  nontrivially on `π₁ᵉᵗ(U)`;
* `CurvesJacobian.Cusp.exists_mem_cuspInertia_kummer`: for `v` as above and every `ζ ∈ μ_n`,
  some element of `cuspInertia U W` is the image of `σ ∈ I_W ∩ H` with `χ_v(σ) = ζ`;
* `CurvesJacobian.Cusp.cuspInertia_ne_bot_of_kummer`: `cuspInertia U W ≠ ⊥`.

The existence of such a `v` for a given cusp is a statement about divisors (`div v = P + n E` on
`U`), i.e. about `n`-divisibility in `Pic⁰`; without it, abelian covers cannot detect the inertia
at a single puncture of `X ∖ {x}` (it is a product of commutators there).
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve KummerTheory Curve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] (n : ℕ) [NeZero n]

set_option maxHeartbeats 1000000 in
-- closure computations in the Krull topology of `Gal(Ω/k(t))` are slow to elaborate
omit [X.Over (Spec (CommRingCat.of k))] in
/-- A character of `H` killing the inertia elements of the places centred on `U` kills the closed
normal subgroup `⟨⟨S_U⟩⟩` of `H`. -/
lemma kernel_SU_le_ker_charOfH (U : X.Opens) [Nonempty U]
    (χ : ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω))
    (hχ : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ SU D X eL U → charOfH D n χ σ = 1) :
    GaloisPi1.kernel D.H (SU D X eL U) ≤ (charOfH D n χ).ker := by
  intro σ hσ
  let K : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := (charOfH D n χ).ker.map D.H.subtype
  have hKclosed : IsClosed (K : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    have h1 : IsClosed ((charOfH D n χ).ker : Set D.H) :=
      (isClosed_discrete ({1} : Set (Mu n Ω))).preimage (continuous_charOfH D n χ)
    have h2 := (D.isClosed_H.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.1 h1
    have hK : (K : Set (Ω ≃ₐ[K₀ k t] Ω)) = Subtype.val '' ((charOfH D n χ).ker : Set D.H) := by
      rw [Subgroup.coe_map]; rfl
    rw [hK]
    exact h2
  have hconj : GaloisPi1.conjSet D.H (SU D X eL U) ⊆ K := by
    rintro _ ⟨h, hh, s, hs, rfl⟩
    refine ⟨⟨h, hh⟩ * ⟨s, hs.1⟩ * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv,
      inv_mul_cancel, one_mul]
    exact hχ ⟨s, hs.1⟩ hs
  have hle : GaloisPi1.ambientKernel D.H (SU D X eL U) ≤ K :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le K).2 hconj) hKclosed
  have hσ' : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.ambientKernel D.H (SU D X eL U) :=
    Subgroup.mem_subgroupOf.1 hσ
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 (hle hσ')
  have : τ = σ := Subtype.ext hτσ
  rw [MonoidHom.mem_ker, ← this]
  exact hτ

variable [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
/-- An element `σ ∈ H` on which a character killing `S_U` is nontrivial acts nontrivially on
`π₁ᵉᵗ(U)`. -/
theorem chartHom_ne_one_of_charOfH (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Finite)
    (χ : ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω))
    (hχ : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ SU D X eL U → charOfH D n χ σ = 1)
    {σ : D.H} (hσ : charOfH D n χ σ ≠ 1) : D.chartHom hH (genericL D X eL U) σ ≠ 1 := by
  intro h1
  have hmem : σ ∈ (D.chartHom hH (genericL D X eL U)).ker := h1
  rw [(genericL_spec D X eL hk hH hτ U hU).1] at hmem
  exact hσ (kernel_SU_le_ker_charOfH D X eL n U χ hχ hmem)

include hk hτ in
/-- **The tame character of a cusp through the Kummer cover**: if `v ∈ F` is a uniformiser at the
place `W ⊇ k` and a unit at every place centred on `U`, then for every `ζ ∈ μ_n` there is
`σ ∈ I_W ∩ H` with Kummer character `χ_v(σ) = ζ`, whose image lies in `cuspInertia U W`; for
`ζ ≠ 1` this image is nontrivial. -/
theorem exists_mem_cuspInertia_kummer (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Finite)
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (v : (F D)ˣ)
    (hvW : W.valuation ((v : F D) : Ω) < 1)
    (hv : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((v : F D) : Ω))
    (hunit : ∀ W', IsCentredOn D X eL U W' →
      ((v : F D) : Ω) ∈ W' ∧ (((v⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W')
    (ζ : Mu n Ω) :
    ∃ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W ∧
      charOfH D n (kummer n (F D) Ω v) σ = ζ ∧
      D.chartHom hH (genericL D X eL U) σ ∈ cuspInertia D X eL hH U W ∧
      (ζ ≠ 1 → D.chartHom hH (genericL D X eL U) σ ≠ 1) := by
  obtain ⟨σ, hσW, hζ⟩ := evalTriv_kummer_surjective (D := D) hkW v hvW hv n ζ
  have hχ : ∀ σ' : D.H, (σ' : Ω ≃ₐ[K₀ k t] Ω) ∈ SU D X eL U →
      charOfH D n (kummer n (F D) Ω v) σ' = 1 := by
    intro σ' hσ'
    obtain ⟨-, W', hW', hσ'W'⟩ := (mem_SU_iff D X eL U _).1 hσ'
    exact evalTriv_res_kummer_of_unit hW'.1 hσ'W' n v (hunit W' hW').1 (hunit W' hW').2
  refine ⟨σ, hσW, hζ, Subgroup.subset_closure ⟨σ, hσW, rfl⟩, fun hζ1 ↦ ?_⟩
  exact chartHom_ne_one_of_charOfH D X eL hH n hk hτ U hU _ hχ (hζ.symm ▸ hζ1)

include hk hτ in
/-- **Cuspidal inertia groups are nontrivial** (given a Kummer function for the cusp): if `v ∈ F`
is a uniformiser at the place `W ⊇ k` and a unit at every place centred on `U`, then
`cuspInertia U W ≠ ⊥`. -/
theorem cuspInertia_ne_bot_of_kummer (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Finite)
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (v : (F D)ˣ)
    (hvW : W.valuation ((v : F D) : Ω) < 1)
    (hv : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((v : F D) : Ω))
    (hunit : ∀ W', IsCentredOn D X eL U W' →
      ((v : F D) : Ω) ∈ W' ∧ (((v⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W') :
    cuspInertia D X eL hH U W ≠ ⊥ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero ((2 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 two_ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω 2
  have hz1 : z ≠ 1 := hz.ne_one (by norm_num)
  let ζ : Mu 2 Ω := Mu.mk (hz.isUnit (by norm_num)).unit (by ext; simp [hz.pow_eq_one])
  have hζ1 : ζ ≠ 1 := fun h ↦ hz1 (by
    have := congrArg (fun x : Mu 2 Ω ↦ ((Mu.val x : Ωˣ) : Ω)) h
    simpa [ζ] using this)
  obtain ⟨σ, -, -, hmem, hne⟩ :=
    exists_mem_cuspInertia_kummer D X eL hH 2 hk hτ U hU hkW v hvW hv hunit ζ
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne hζ1 hmem

end CurvesJacobian.Cusp
