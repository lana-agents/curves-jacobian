/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspCentralCurve
import ContinuousKummerTheory.Curve.InertiaZHat

/-!
# The cuspidal inertia group `I_x ⊆ Δ_{U_x}` is `Ẑ(1)` ([AbsTopIII] Prop. 1.4 (i))

[AbsTopIII] Proposition 1.4 (i) (`Topics in Absolute Anabelian Geometry III.txt` l.1752–1770):
"the inertia group `I_x` of `x` in `Δ_U` is naturally isomorphic to `Ẑ(1)`".

Setting of `CurvesJacobian/Kummer/CuspCentralCurve.lean`: `k` algebraically closed of
characteristic `0`, `X` a proper curve over `k` of genus `g ≥ 1` (Galois model `(D, eL)`), `x ∈ X`,
`U = X ∖ {x}`, `W₀` a place of `Ω` over `x` and `I_x = cuspInertia U W₀ ⊆ π₁ᵉᵗ(U)`, the closure
of the image of `I_{W₀} ∩ H` under the Galois action `H → π₁ᵉᵗ(U)` at the generic point.
continuous-kummer-theory identifies `I_{W₀} ∩ H` with `Ẑ(1)` by the tame character `θ_π` of a
uniformiser `π` (`KummerTheory.Curve.inertiaZHatEquiv`). Here we show that `I_{W₀} ∩ H → I_x` is
an isomorphism:

* `CurvesJacobian.CuspCentral.inertiaToCusp`: the continuous surjection `I_{W₀} ∩ H ↠ I_x`;
* `CurvesJacobian.CuspCentral.inertiaToCusp_injective`: it is injective. Proof ("`ℤ̂` is
  Hopfian"): by `exists_cuspCentral_equiv`, `I_x ≅ ℤ̂` (genus `≥ 1`), so for every `m ≥ 1` the
  group `I_{W₀} ∩ H` surjects onto `ℤ/m` through `I_x`. The kernel of such a surjection contains
  all `m`-th powers, which form the kernel of `θ_π mod m` (of index `≤ |μ_m| ≤ m`); hence the two
  kernels agree, and an element killed in `I_x` has `θ_π(σ) ≡ 1 mod m` for all `m`, i.e. `σ = 1`;
* `CurvesJacobian.CuspCentral.inertiaCuspEquiv : I_{W₀} ∩ H ≃ₜ* I_x`;
* `CurvesJacobian.CuspCentral.cuspInertiaZHatEquiv : I_x ≃ₜ* Ẑ(1)`, sending the image of
  `σ ∈ I_{W₀} ∩ H` to `θ_π(σ)`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1.Profinite Pi1 Pi1.SurfaceGroup CurvesJacobian.Cusp
open KummerTheory KummerTheory.Curve

universe u

noncomputable section

namespace CurvesJacobian.CuspCentral

section Group

/-- **`m`-th roots in `Ẑ(1)`**: an element of `Ẑ(1)` with trivial `μ_m`-component is an `m`-th
power. -/
theorem ZHatOne.exists_pow_eq_of_proj_eq_one {K Ω : Type*} [Field K] [Field Ω]
    (m : KummerIndex K) (x : ZHatOne K Ω) (hx : ZHatOne.proj m x = 1) :
    ∃ y : ZHatOne K Ω, y ^ m.n = x := by
  have hm : 0 < m.n := Nat.pos_of_ne_zero m.n_ne_zero
  let j : KummerIndex K → KummerIndex K := fun i ↦
    ⟨i.n * m.n, by push_cast; exact mul_ne_zero i.ne_zero m.ne_zero⟩
  have hmj : ∀ i, m ≤ j i := fun i ↦ dvd_mul_left m.n i.n
  have hij : ∀ i, i ≤ j i := fun i ↦ dvd_mul_right i.n m.n
  have hpow : ∀ i, Mu.val (ZHatOne.proj (j i) x) ^ i.n = 1 := fun i ↦ by
    have h := congrArg Mu.val ((ZHatOne.transition_proj (hmj i) x).trans hx)
    rwa [Mu.val_transition, map_one, show (j i).n / m.n = i.n from Nat.mul_div_cancel _ hm] at h
  refine ⟨⟨fun i ↦ Mu.mk _ (hpow i), fun i i' h ↦ Mu.ext ?_⟩, Subtype.ext (funext fun i ↦ ?_)⟩
  · have hjj : j i ≤ j i' := Nat.mul_dvd_mul_right h m.n
    rw [Mu.val_transition, Mu.val_mk, Mu.val_mk, ← ZHatOne.transition_proj hjj,
      Mu.val_transition, show (j i').n / (j i).n = i'.n / i.n from Nat.mul_div_mul_right _ _ hm]
  · refine Mu.ext ?_
    rw [Subgroup.coe_pow, Pi.pow_apply, map_pow, Mu.val_mk, ← ZHatOne.proj_apply,
      ← ZHatOne.transition_proj (hij i) x, Mu.val_transition,
      show (j i).n / i.n = m.n from Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero i.n_ne_zero)]

/-- **Index argument**: let `φ : A → M` be a homomorphism to a group of order `≤ m` whose kernel
consists of `m`-th powers. Then the kernel of every surjection `ρ : A ↠ ℤ/m` lies in `ker φ`. -/
theorem ker_le_ker_of_forall_pow {A M : Type*} [Group A] [Group M] [Finite M] (m : ℕ) [NeZero m]
    (φ : A →* M) (hφ : Nat.card M ≤ m) (hpow : ∀ a ∈ φ.ker, ∃ b, b ^ m = a)
    (ρ : A →* Multiplicative (ZMod m)) (hρ : Function.Surjective ρ) : ρ.ker ≤ φ.ker := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hle : φ.ker ≤ ρ.ker := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := hpow a ha
    rw [MonoidHom.mem_ker, map_pow]
    simpa using pow_card_eq_one' (G := Multiplicative (ZMod m)) (x := ρ b)
  have hρi : ρ.ker.index = m := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top]
    simp
  have hφi : φ.ker.index ≤ m := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hφ
  have hφ0 : φ.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have h := Subgroup.relIndex_mul_index hle
  rw [hρi] at h
  have h1 : φ.ker.relIndex ρ.ker ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by rw [one_mul, h]; exact hφi) hm
  have h0 : φ.ker.relIndex ρ.ker ≠ 0 := fun h0 ↦ hφ0 (by rw [← h, h0, zero_mul])
  exact Subgroup.relIndex_eq_one.1 (by omega)

/-- `ℤ̂ ↠ ℤ/n` is surjective. -/
lemma zmodChar_surjective (n : ℕ) [NeZero n] : Function.Surjective (zmodChar n) := fun z ↦
  ⟨zhatOne ^ (Multiplicative.toAdd z).val, by
    rw [map_pow, zmodChar_zhatOne, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
    rfl⟩

end Group

section Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  [IsGalois (K₀ k t) Ω] (D : GaloisData k t) {X : Scheme.{u}} [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)

/-- `cuspInertia U W` is the image of `I_W ∩ H` (the subgroup generated by the image of a
subgroup is that image). -/
lemma cuspInertia_eq_map (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    cuspInertia D X eL hH U W = (inertiaH D W).map (D.chartHom hH (genericL D X eL U)) := by
  rw [Cusp.cuspInertia, show (Subtype.val ⁻¹' GaloisPi1.inertia W : Set D.H) =
    (inertiaH D W : Set _) from rfl, ← Subgroup.coe_map, Subgroup.closure_eq]

/-- **`I_W ∩ H ↠ I_x`**: the Galois action `H → π₁ᵉᵗ(U)` at the generic point, restricted to
the inertia group of `W`, onto the cuspidal inertia group `cuspInertia U W`. -/
def inertiaToCusp (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    inertiaH D W →* cuspInertia D X eL hH U W :=
  ((D.chartHom hH (genericL D X eL U)).comp (inertiaH D W).subtype).codRestrict _ fun σ ↦ by
    rw [cuspInertia_eq_map]
    exact Subgroup.mem_map_of_mem _ σ.2

@[simp]
lemma coe_inertiaToCusp (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω)
    (σ : inertiaH D W) :
    (inertiaToCusp D eL hH U W σ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) =
      D.chartHom hH (genericL D X eL U) σ := rfl

lemma continuous_inertiaToCusp (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    Continuous (inertiaToCusp D eL hH U W) :=
  ((D.continuous_chartHom hH _).comp continuous_subtype_val).subtype_mk _

lemma inertiaToCusp_surjective (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    Function.Surjective (inertiaToCusp D eL hH U W) := by
  rintro ⟨g, hg⟩
  rw [cuspInertia_eq_map] at hg
  obtain ⟨σ, hσ, rfl⟩ := hg
  exact ⟨⟨σ, hσ⟩, rfl⟩

variable [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  [Nonempty (⊤ : X.Opens)]

variable {D eL hH} {π : (F D)ˣ}

include hk hτ in
/-- **`I_{W₀} ∩ H → I_x` is injective** ([AbsTopIII] Prop. 1.4 (i)) for `X` of genus `≥ 1`,
`U = X ∖ {x}` and `W₀` a place over `x`: `I_x ≅ ℤ̂` (`exists_cuspCentral_equiv`), and a
surjection from `Ẑ(1)` onto `ℤ̂` is injective (the index argument
`ker_le_ker_of_forall_pow`, using `I_{W₀} ∩ H ≅ Ẑ(1)` via the tame character). -/
theorem inertiaToCusp_injective (hg : 0 < (curveGenus k X).toNat) (U : X.Opens) [Nonempty U]
    {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    Function.Injective (inertiaToCusp D eL hH U W₀) := by
  obtain ⟨Θ, -, hI, -⟩ := exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  have hmem : ∀ c : cuspInertia D X eL hH U W₀,
      Θ c ∈ inertia (g := (curveGenus k X).toNat) (r := 1) 0 :=
    fun c ↦ hI ▸ Subgroup.mem_map_of_mem Θ.toMulEquiv.toMonoidHom c.2
  -- `ψ₀ : I_x → ℤ̂` (an isomorphism) and `ψ : I_{W₀} ∩ H ↠ ℤ̂`
  let e := cuspInertiaEquiv (g := (curveGenus k X).toNat) (Or.inr hg) (0 : Fin 1)
  let ψ₀ : cuspInertia D X eL hH U W₀ →* ZHat := e.symm.toMulEquiv.toMonoidHom.comp
    ((Θ.toMulEquiv.toMonoidHom.comp (cuspInertia D X eL hH U W₀).subtype).codRestrict _ hmem)
  have hψ₀ : Function.Surjective ψ₀ := by
    refine e.symm.surjective.comp ?_
    rintro ⟨z, hz⟩
    rw [← hI] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    exact ⟨⟨c, hc⟩, rfl⟩
  let ψ := ψ₀.comp (inertiaToCusp D eL hH U W₀)
  have hψ : Function.Surjective ψ := hψ₀.comp (inertiaToCusp_surjective D eL hH U W₀)
  set θ := tameChar (D := D) hW₀.1 π
  have hθi : Function.Injective θ := tameChar_injective hW₀.1 hπW hπ
  have hθs : Function.Surjective θ := tameChar_surjective hW₀.1 hπW hπ
  rw [injective_iff_map_eq_one]
  intro a ha
  have hψa : ψ a = 1 := by
    change ψ₀ _ = 1
    rw [ha, map_one]
  refine hθi ?_
  rw [map_one]
  refine Subtype.ext (funext fun i ↦ ?_)
  change ZHatOne.proj i (θ a) = 1
  have key := ker_le_ker_of_forall_pow i.n ((ZHatOne.proj i).comp θ)
    (card_rootsOfUnity Ω i.n) (fun b hb ↦ by
      obtain ⟨y, hy⟩ := ZHatOne.exists_pow_eq_of_proj_eq_one i (θ b) hb
      obtain ⟨c, rfl⟩ := hθs y
      exact ⟨c, hθi (by rw [map_pow, hy])⟩)
    ((zmodChar i.n).comp ψ) ((zmodChar_surjective i.n).comp hψ)
  exact key (by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hψa, map_one])

/-- **[AbsTopIII] Prop. 1.4 (i): `I_{W₀} ∩ H ≃ₜ* I_x`** for `X` of genus `≥ 1`, `U = X ∖ {x}` and
`W₀` a place over `x` (`inertiaToCusp` as a topological isomorphism). -/
def inertiaCuspEquiv (hg : 0 < (curveGenus k X).toNat) (U : X.Opens) [Nonempty U]
    {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    inertiaH D W₀ ≃ₜ* cuspInertia D X eL hH U W₀ :=
  let e : inertiaH D W₀ ≃* cuspInertia D X eL hH U W₀ :=
    MulEquiv.ofBijective (inertiaToCusp D eL hH U W₀)
      ⟨inertiaToCusp_injective hk hτ hg U hUx hW₀ hW₀U hπW hπ,
        inertiaToCusp_surjective D eL hH U W₀⟩
  { e with
    continuous_toFun := continuous_inertiaToCusp D eL hH U W₀
    continuous_invFun := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
      (continuous_inertiaToCusp D eL hH U W₀)).symm.continuous }

@[simp]
lemma inertiaCuspEquiv_apply (hg : 0 < (curveGenus k X).toNat) (U : X.Opens) [Nonempty U]
    {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (σ : inertiaH D W₀) :
    inertiaCuspEquiv hk hτ hg U hUx hW₀ hW₀U hπW hπ σ = inertiaToCusp D eL hH U W₀ σ := rfl

/-- **[AbsTopIII] Prop. 1.4 (i): the cuspidal inertia group `I_x ⊆ Δ_{U_x}` is isomorphic to
`Ẑ(1)`** as a topological group, for `X` of genus `≥ 1`, `U_x = X ∖ {x}` and `W₀` a place over
`x`: the image of `σ ∈ I_{W₀} ∩ H` goes to `θ_π(σ)`, `θ_π` the tame character of a uniformiser
`π` of `W₀ ∩ F` (`cuspInertiaZHatEquiv_inertiaToCusp`). -/
def cuspInertiaZHatEquiv (hg : 0 < (curveGenus k X).toNat) (U : X.Opens) [Nonempty U]
    {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    cuspInertia D X eL hH U W₀ ≃ₜ* ZHatOne (F D) Ω :=
  (inertiaCuspEquiv hk hτ hg U hUx hW₀ hW₀U hπW hπ).symm.trans
    (inertiaZHatEquiv hW₀.1 hπW hπ)

@[simp]
lemma cuspInertiaZHatEquiv_inertiaToCusp (hg : 0 < (curveGenus k X).toNat) (U : X.Opens)
    [Nonempty U] {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (σ : inertiaH D W₀) :
    cuspInertiaZHatEquiv hk hτ hg U hUx hW₀ hW₀U hπW hπ (inertiaToCusp D eL hH U W₀ σ) =
      tameChar hW₀.1 π σ := by
  rw [cuspInertiaZHatEquiv, ContinuousMulEquiv.trans_apply,
    ← inertiaCuspEquiv_apply hk hτ hg U hUx hW₀ hW₀U hπW hπ σ,
    ContinuousMulEquiv.symm_apply_apply, inertiaZHatEquiv_apply]

end Curve

end CurvesJacobian.CuspCentral
