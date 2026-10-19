/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.DeltaAbKummer

/-!
# Separation and duality for the Kummer characters of `Δ_X^{ab}`

Continuation of `Kummer/DeltaAbKummer.lean` (Galois model `D`, `Δ_X^{ab} = DeltaAb D`, Kummer
characters `kCharAb a : Δ_X^{ab} → k̄ˣ` of `a ∈ J(k̄)[n] = Pic(F k̄)[n]`):

* `smul_deltaTildeToAb`, **`kCharAb_smul`**: `χ_{h a}(g δ) = h(χ_a(δ))` for `h ∈ H` over
  `g ∈ G_k` (`G_k`-equivariance of `Δ_X^{ab} → Hom(J[n], μ_n)`);
* `exists_kCharAb_eq`: a character of `Δ_X^{ab}` of exponent `N`, trivial on the image of an open
  subgroup of `Δ̃`, is some `χ_a`, `a ∈ J(k̄)[N]` (Kummer theory, `picTorsionEquivPiChars`);
* **`eq_one_of_forall_kCharAb`**, `iInf_kerAb_eq_bot`: the `χ_a` separate the points of
  `Δ_X^{ab}` (profiniteness of `Δ̃` and finite duality);
* `kCharAb_injective` (`χ_a = 1 ⇒ a = 0`), `kDual`, **`kDual_surjective`**:
  `Δ_X^{ab} ↠ Hom(J(k̄)[n], k̄ˣ)` (via the general `CommGroup.surjective_of_separating`).

Together with the perfect Weil pairing (`weilDual_bijective_baseChange`) this identifies
`Δ_X^{ab}/(⋂_a ker χ_a)` with `J(k̄)[n]`, `G_k`-equivariantly ([Cusp] Prop. 2.3(i), the
"general nonsense" isomorphism; MR5 J4).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

section Duality

variable {n : ℕ} [NeZero n]

/-- `g • [s] = [h s h⁻¹]` in `Δ_X^{ab}` for `h ∈ H` over `g ∈ G_k`. -/
lemma smul_deltaTildeToAb [Fact (Function.Surjective (piJ1ToGk D))] (h : D.H)
    (s : deltaTilde D) :
    hToGk D h • deltaTildeToAb s = deltaTildeToAb (conjDT h s) := by
  apply deltaAbToPiJ1_injective D
  rw [deltaAbToPiJ1_smul D _ _ (p := piXToPiJ1 D (h : PiX D))
    (by rw [piJ1ToGk_piXToPiJ1, piXToGk_mk])]
  change _ * deltaAbToPiJ1 D (deltaAbMk D _) * _ = deltaAbToPiJ1 D (deltaAbMk D _)
  rw [deltaAbToPiJ1_deltaAbMk, deltaAbToPiJ1_deltaAbMk, ← map_inv, ← map_mul, ← map_mul]
  rfl

/-- **`G_k`-equivariance of the Kummer characters**: `χ_{h a}(g δ) = h(χ_a(δ))` for `h` over
`g`. -/
lemma kCharAb_smul [Fact (Function.Surjective (piJ1ToGk D))] (h : D.H)
    (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (δ : DeltaAb D) :
    (((kCharAb ⟨picAct D h a, picAct_mem_picTorsion D h a.2⟩ (hToGk D h • δ) :
      (kbar k Ω)ˣ) : kbar k Ω) : Ω) =
      (h : Ω ≃ₐ[K₀ k t] Ω) (((kCharAb a δ : (kbar k Ω)ˣ) : kbar k Ω) : Ω) := by
  obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
  rw [smul_deltaTildeToAb, kCharAb_deltaTildeToAb, kCharAb_deltaTildeToAb, coe_kChar, coe_kChar]
  exact kVal_conj h a s

set_option maxHeartbeats 400000 in
-- instance synthesis for the quotients `PiX (baseChange D)`, `DeltaAb D` and `Mu N Ω` is slow
/-- **Every character of `Δ_X^{ab}` of exponent `N` which is trivial on (the image of) an open
subgroup of `Δ̃` is a Kummer character `χ_a`, `a ∈ J(k̄)[N]`** (Kummer theory for `Π_{X_{k̄}}`,
`picTorsionEquivPiChars`). -/
theorem exists_kCharAb_eq [Fact (Function.Surjective (piJ1ToGk D))] (N : ℕ) [NeZero N]
    (φ : DeltaAb D →* (kbar k Ω)ˣ) (hφN : ∀ x, φ x ^ N = 1) (U : Subgroup (deltaTilde D))
    (hUo : IsOpen (U : Set (deltaTilde D))) (hU : ∀ s ∈ U, φ (deltaTildeToAb s) = 1) :
    ∃ a : picTorsion (kbar k Ω) (F (baseChange D)) N, ∀ δ, kCharAb a δ = φ δ := by
  let φ0 : (baseChange D).H →* Mu N Ω :=
    { toFun := fun σ => Mu.mk (Units.map (algebraMap (kbar k Ω) Ω).toMonoidHom
        (φ (deltaTildeToAb (bcToDeltaTilde D σ)))) (by rw [← map_pow, hφN, map_one])
      map_one' := Mu.ext (by simp)
      map_mul' := fun σ τ => Mu.ext (by simp) }
  have hker : GaloisPi1.kernel (baseChange D).H (SAll (baseChange D)) ≤ φ0.ker := by
    intro σ hσ
    have h1 : deltaTildeToAb (bcToDeltaTilde D σ) = 1 := by
      have := bcToDeltaTilde_mem_kernel hσ
      change deltaAbMk D (deltaTildeToDeltaX _) = 1
      rw [show deltaTildeToDeltaX (bcToDeltaTilde D σ) = 1 from
        Subtype.ext ((QuotientGroup.eq_one_iff _).2 this), map_one]
    rw [MonoidHom.mem_ker]
    apply Mu.ext
    simp [φ0, h1]
  have hopen : IsOpen ((φ0.ker : Subgroup (baseChange D).H) : Set (baseChange D).H) := by
    refine Subgroup.isOpen_mono (H₁ := U.comap (bcToDeltaTilde D)) ?_
      (hUo.preimage continuous_bcToDeltaTilde)
    intro σ hσ
    rw [MonoidHom.mem_ker]
    apply Mu.ext
    simp [φ0, hU _ hσ]
  have hcont0 : Continuous φ0 := by
    refine continuous_of_continuousAt_one φ0 ?_
    rw [ContinuousAt, map_one, nhds_discrete (Mu N Ω), Filter.tendsto_pure]
    exact Filter.mem_of_superset (hopen.mem_nhds (one_mem _)) fun x hx => hx
  let ψ' : ContinuousMonoidHom (PiX (baseChange D)) (Mu N Ω) :=
    { QuotientGroup.lift _ φ0 hker with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hcont0 }
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨(picTorsionEquivPiChars (baseChange D) N hNpos).symm (Additive.ofMul ψ'), fun δ => ?_⟩
  set a := (picTorsionEquivPiChars (baseChange D) N hNpos).symm (Additive.ofMul ψ')
  have ha : Additive.toMul (picTorsionEquivPiChars (baseChange D) N hNpos a) = ψ' := by
    simp [a]
  obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
  obtain ⟨σ, rfl⟩ := bcToDeltaTilde_surjective s
  have hF := val_picTorsionEquivPiChars hNpos a σ
  rw [ha] at hF
  rw [kCharAb_deltaTildeToAb]
  apply Units.ext
  apply Subtype.ext
  rw [coe_kChar, ← hF]
  rfl

/-- **Separation**: the Kummer characters `χ_a` (`a ∈ J(k̄)[n]`, all `n ≥ 1`) separate the points
of `Δ_X^{ab}`. -/
theorem eq_one_of_forall_kCharAb [Fact (Function.Surjective (piJ1ToGk D))] (δ : DeltaAb D)
    (hδ : ∀ (m : ℕ) [NeZero m] (a : picTorsion (kbar k Ω) (F (baseChange D)) m),
      kCharAb a δ = 1) : δ = 1 := by
  by_contra hne
  obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
  have hsK : s ∉ (deltaTildeToAb (D := D)).ker := hne
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨_, isClosed_ker_deltaTildeToAb (D := D)⟩
  change (deltaTildeToAb (D := D)).ker = _ at key
  rw [key, Subgroup.mem_sInf] at hsK
  push Not at hsK
  obtain ⟨U, ⟨hUo, hKU⟩, hsU⟩ := hsK
  let V : Subgroup (DeltaAb D) := U.map deltaTildeToAb
  have hcomap : V.comap deltaTildeToAb = U := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y⁻¹ * x ∈ (deltaTildeToAb (D := D)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      simpa using U.mul_mem hy (hKU this)
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI : Finite (deltaTilde D ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUo
  haveI : V.FiniteIndex := ⟨by
    rw [← Subgroup.index_comap_of_surjective (H := V) deltaTildeToAb_surjective, hcomap]
    exact Subgroup.index_ne_zero_of_finite⟩
  have hq : (QuotientGroup.mk (deltaTildeToAb s) : DeltaAb D ⧸ V) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => hsU (by rw [← hcomap]; exact h)
  haveI : NeZero ((Monoid.exponent (DeltaAb D ⧸ V) : ℕ) : kbar k Ω) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨ψ, hψ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (DeltaAb D ⧸ V) (kbar k Ω) hq
  haveI : NeZero (Monoid.exponent (DeltaAb D ⧸ V)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨a, ha⟩ := exists_kCharAb_eq (Monoid.exponent (DeltaAb D ⧸ V))
    (ψ.comp (QuotientGroup.mk' V))
    (fun x => by rw [MonoidHom.comp_apply, ← map_pow, Monoid.pow_exponent_eq_one, map_one]) U hUo
    (fun x hx => by
      change ψ (QuotientGroup.mk _) = 1
      rw [(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_map_of_mem _ hx), map_one])
  exact hψ ((ha _).symm.trans (hδ _ a))

/-- `⋂_{n ≥ 1} ⋂_{a ∈ J[n]} ker χ_a = 1` in `Δ_X^{ab}`. -/
theorem iInf_kerAb_eq_bot [Fact (Function.Surjective (piJ1ToGk D))] :
    ⨅ m : {m : ℕ // 0 < m}, (haveI : NeZero m.1 := ⟨m.2.ne'⟩; kerAb (D := D) m.1) = ⊥ := by
  rw [eq_bot_iff]
  intro δ hδ
  rw [Subgroup.mem_iInf] at hδ
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_kCharAb δ fun m _ a => ?_
  have := hδ ⟨m, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  exact mem_kerAb.1 this a

/-- **`χ_a = 1` only for `a = 0`**. -/
theorem kCharAb_injective (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (ha : ∀ δ, kCharAb a δ = 1) : a = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  apply (picTorsionEquivPiChars (baseChange D) n hn).injective
  rw [map_zero]
  apply Additive.toMul.injective
  refine ContinuousMonoidHom.ext fun x => ?_
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  apply Mu.ext
  apply Units.ext
  rw [val_picTorsionEquivPiChars hn a σ]
  have := ha (deltaTildeToAb (bcToDeltaTilde D σ))
  rw [kCharAb_deltaTildeToAb, kChar_eq_one_iff_kVal] at this
  rw [this]
  simp

variable (D n) in
/-- **The duality map** `Δ_X^{ab} → Hom(J(k̄)[n], k̄ˣ)`, `δ ↦ (a ↦ χ_a(δ))`. -/
noncomputable def kDual :
    DeltaAb D →* (Multiplicative (picTorsion (kbar k Ω) (F (baseChange D)) n) →* (kbar k Ω)ˣ)
    where
  toFun δ :=
    { toFun := fun a => kCharAb (Multiplicative.toAdd a) δ
      map_one' := kCharAb_zero δ
      map_mul' := fun _ _ => kCharAb_add _ _ δ }
  map_one' := MonoidHom.ext fun a => map_one (kCharAb (Multiplicative.toAdd a))
  map_mul' _ _ := MonoidHom.ext fun a => map_mul (kCharAb (Multiplicative.toAdd a)) _ _

set_option maxHeartbeats 400000 in
-- unfolding the coercion of the bundled hom into `Hom(J[n], k̄ˣ)` is slow
@[simp]
lemma kDual_apply (δ : DeltaAb D)
    (a : Multiplicative (picTorsion (kbar k Ω) (F (baseChange D)) n)) :
    kDual D n δ a = kCharAb (Multiplicative.toAdd a) δ := rfl

/-- **Finite duality**: a homomorphism `Θ : A → Hom(G, κˣ)` (`G` finite commutative, `κ`
algebraically closed of characteristic `0`) whose values separate the points of `G` is
surjective. -/
theorem _root_.CommGroup.surjective_of_separating {G A κ : Type*} [CommGroup G] [Finite G]
    [CommGroup A] [Field κ] [IsAlgClosed κ] [CharZero κ] (Θ : A →* (G →* κˣ))
    (hsep : ∀ g : G, (∀ δ, Θ δ g = 1) → g = 1) : Function.Surjective Θ := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : κ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  set e := CommGroup.subgroupOrderIsoSubgroupMonoidHom G κ
  have hbot : e.symm (OrderDual.toDual Θ.range) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff] at hg
    rw [Subgroup.mem_bot]
    exact hsep g fun δ => hg _ ⟨δ, rfl⟩
  have htop' : e.symm (OrderDual.toDual (⊤ : Subgroup (G →* κˣ))) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff] at hg
    rw [Subgroup.mem_bot, ← CommGroup.forall_apply_eq_apply_iff G (M := κ)]
    intro φ
    rw [hg φ (Subgroup.mem_top φ), map_one]
  have htop : Θ.range = ⊤ := e.symm.injective (hbot.trans htop'.symm)
  exact MonoidHom.range_eq_top.1 htop

/-- **Duality**: every character of `J(k̄)[n]` is `a ↦ χ_a(δ)` for some `δ ∈ Δ_X^{ab}`. -/
theorem kDual_surjective [Finite (picTorsion (kbar k Ω) (F (baseChange D)) n)] :
    Function.Surjective (kDual D n) :=
  CommGroup.surjective_of_separating _ fun g hg => by
    have : Multiplicative.toAdd g = 0 := kCharAb_injective _ hg
    rw [← ofAdd_toAdd g, this, ofAdd_zero]

end Duality

end CurvesJacobian.Kummer
