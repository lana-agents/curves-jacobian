/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PicAction
import ContinuousKummerTheory.Curve.CuspResidue

/-!
# [AbsTopIII] Prop. 1.6(iii): middle exactness

Setting of `pi1` / continuous-kummer-theory: `D : GaloisData k t`, `char k = 0`, `Ω` algebraically
closed and Galois over `k(t)`, `Π_U = Pi D`, `M_X = Ẑ(1)`, `G_k = Gal(k̄/k)`.

[AbsTopIII] Prop. 1.6(iii) (T3 l.2001–2025) states that
`1 → (kˣ)^∧ → H¹(Π_U, M_X) → ⊕_{x ∈ S} Ẑ` is exact, the second map being restriction to the inertia
groups `I_x` of the cusps. Its proof (l.2032–2039) reduces this, "just as in [Cusp] Prop. 2.1(ii)",
to `H⁰(G_k, Δ_X^{ab}) = 0`, which follows from Kummer-faithfulness for the Jacobian `J`.

Main result: `CurvesJacobian.Kummer.mem_range_constMapZHat`: if `k` is algebraically closed in `F`
and `IsKummerFaithfulJac D` (`⋂_N N · J(k) = 0`, see `Kummer/PicAction.lean`), then every
`η ∈ H¹(Π_U, Ẑ(1))` which vanishes on the inertia groups `I_W ∩ H` of all places `W ⊇ k` of `Ω`
lies in the image of `(kˣ)^∧ → H¹(Π_U, Ẑ(1))` (`constMapZHat`). (For a curve, `H_L = H`, the
inertia groups of the places of `U` already die in `Π_U`, so only the cusps matter; for an
orbicurve the hypothesis also covers the orbifold points.) Together with the injectivity
`constMapZHat_injective` and `evalTriv_constMapZHat` (continuous-kummer-theory) this is the exact
sequence.

Proof, at each level `n`: the restriction of a cocycle `c_n` of `η` to `Gal(Ω/F k̄) = Δ`
(`galToPi`) is a homomorphism `Δ → μ_n`, so by Kummer theory over `F k̄` it is `σ ↦ σα/α` with
`α^n = a ∈ (F k̄)ˣ` (`exists_root`); `a` is unramified (`isUnramifiedKummer_of`), so
`div a = n E` (Milne, *Abelian Varieties*, III.9.2; `isUnramifiedKummer_iff`); the class
`[E] ∈ Pic(X_{k̄})[n]` is `G_k`-invariant since `c_n` is a cocycle on all of `Π_U`
(`picAct_mk_E`), and `[E_n] = N · [E_{nN}]` (`mk_E_eq_nsmul`). So `[E_n] ∈ ⋂_N N · J(k) = 0`,
whence `a` is an `n`-th power and `c_n|_Δ = 1`. Hence the `Ẑ(1)`-cocycle vanishes on
`Δ = ker(Π_U → G_k)` and descends to `G_k` (`ContH1.exists_map_eq_mk`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

namespace CurvesJacobian.Kummer

universe u

section Cocycle

/-- For a cocycle `c` and `ν` acting trivially: `c(g⁻¹ ν g) = g⁻¹ • c(ν)`. -/
theorem cocycle_conj {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {c : G → M} (hc : groupCohomology.IsMulCocycle₁ c) (g ν : G) (hν : ∀ m : M, ν • m = m) :
    c (g⁻¹ * ν * g) = g⁻¹ • c ν := by
  have h1 : c 1 = 1 := by
    have := hc 1 1
    rw [one_mul, one_smul] at this
    exact left_eq_mul.1 this
  have e3 := hc g⁻¹ g
  rw [inv_mul_cancel, h1] at e3
  rw [hc (g⁻¹ * ν) g, hc g⁻¹ ν, mul_smul, hν, mul_left_comm, ← e3, mul_one]

end Cocycle

namespace ContH1

variable {G H M N : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]
  [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [MulDistribMulAction H N]

/-- **Descent along a surjection**: a continuous cocycle on `H` which is trivial on the kernel of a
continuous surjection `φ : H ↠ G` (`H` compact, `G` Hausdorff) is the pull-back of a cocycle on
`G`, for an injective coefficient map `f : M → N` with a continuous right inverse `g`. -/
theorem exists_map_eq_mk [CompactSpace H] [T2Space G] (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (f : M →* N) (hf : Continuous f)
    (hfi : Function.Injective f) (g : N → M) (hg : Continuous g) (hfg : ∀ n, f (g n) = n)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) (c : ContH1.cocycles H N)
    (hc : ∀ x, φ x = 1 → c x = 1) :
    ∃ y, ContH1.map φ hφ f hf hcomp y = ContH1.mk c := by
  have hconst : ∀ x y, φ x = φ y → c x = c y := by
    intro x y hxy
    have hk : φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    rw [show y = x * (x⁻¹ * y) by group, ContH1.isMulCocycle₁ c, hc _ hk, smul_one, one_mul]
  set s := Function.surjInv hsurj
  have hs : ∀ g, φ (s g) = g := Function.surjInv_eq hsurj
  set z : G → M := fun x => g (c (s x))
  have hz : ∀ x, z (φ x) = g (c x) := fun x => by
    simp only [z]
    rw [hconst _ _ (hs (φ x))]
  have hzc : Continuous z := by
    have hq := Topology.IsQuotientMap.of_surjective_continuous hsurj hφ
    rw [hq.continuous_iff]
    have : z ∘ φ = g ∘ c := funext hz
    rw [this]
    exact hg.comp (ContH1.continuous c)
  have hzcoc : groupCohomology.IsMulCocycle₁ z := by
    intro a b
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨x', rfl⟩ := hsurj b
    apply hfi
    rw [← map_mul, hz, hz, hz, map_mul, hfg, hcomp, hfg, hfg, ContH1.isMulCocycle₁ c]
  refine ⟨ContH1.mk (ContH1.mkCocycle z hzc hzcoc), ?_⟩
  rw [ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext x
  change f (z (φ x)) = c x
  rw [hz, hfg]

end ContH1

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

instance charZero_kbar : CharZero (kbar k Ω) :=
  charZero_of_injective_algebraMap (algebraMap k (kbar k Ω)).injective

attribute [local instance] isFunctionField_F

/-- `Gal(Ω/F k̄) → Π_U` (onto `Δ = ker(Π_U → G_k)`). -/
noncomputable def galToPi : (Ω ≃ₐ[F (baseChange D)] Ω) →* Pi D :=
  (QuotientGroup.mk' _).comp (galToH D)

omit [CharZero k] [IsAlgClosed Ω] in
lemma continuous_galToPi : Continuous (galToPi D) :=
  QuotientGroup.continuous_mk.comp (continuous_galToH D)

variable {D}

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- Roots of unity lie in `k̄ ⊆ F k̄`. -/
lemma mu_mem_kbar {n : ℕ} [NeZero n] (ζ : Mu n Ω) : ((Mu.val ζ : Ωˣ) : Ω) ∈ kbar k Ω := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hζ : ((Mu.val ζ : Ωˣ) : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  exact mem_algebraicClosure_iff.mpr
    ⟨Polynomial.X ^ n - 1, Polynomial.X_pow_sub_C_ne_zero hn 1, by simp [hζ]⟩

omit [CharZero k] [IsAlgClosed Ω] in
lemma gal_smul_mu {n : ℕ} [NeZero n] (τ : Ω ≃ₐ[F (baseChange D)] Ω) (ζ : Mu n Ω) : τ • ζ = ζ :=
  Mu.ext (Units.ext (galToH_fix_kbar D τ (mu_mem_kbar ζ)))

omit [IsAlgClosed Ω] in
lemma galToPi_smul_mu {n : ℕ} [NeZero n] (τ : Ω ≃ₐ[F (baseChange D)] Ω) (ζ : Mu n Ω) :
    galToPi D τ • ζ = τ • ζ := rfl

omit [IsAlgClosed Ω] in
lemma galToPi_smul_mu_eq {n : ℕ} [NeZero n] (τ : Ω ≃ₐ[F (baseChange D)] Ω) (ζ : Mu n Ω) :
    galToPi D τ • ζ = ζ := by
  rw [galToPi_smul_mu, gal_smul_mu]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- Kummer theory for a cocycle with values in `μ_n` on which the Galois group acts trivially:
it is `σ ↦ σα/α` for some `α` with `αⁿ ∈ K`. -/
theorem exists_root_of_triv {K : Type*} [Field K] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    {n : ℕ} [NeZero n] [NeZero (n : K)] (χ : ContH1.cocycles Gal(Ω/K) (Mu n Ω))
    (htriv : ∀ (τ : Gal(Ω/K)) (ζ : Mu n Ω), τ • ζ = ζ) :
    ∃ a : Kˣ, ∃ α : Ωˣ, α ^ n = Units.map (algebraMap K Ω : K →* Ω) a ∧
      ∀ τ : Gal(Ω/K), ((Mu.val (χ τ) : Ωˣ) : Ω) * α = τ α := by
  obtain ⟨a, ha⟩ := kummer_surjective n K Ω (ContH1.mk χ)
  set α := kummerRoot n K Ω a
  refine ⟨a, α, kummerRoot_pow n _ Ω a, fun τ => ?_⟩
  rw [kummer_eq a α (kummerRoot_pow n _ Ω a), ContH1.mk_eq_mk_iff] at ha
  obtain ⟨m, hm⟩ := ha
  have h := hm τ
  rw [htriv, div_self'] at h
  have h' : kummerCocycle α _ τ = χ τ := (div_eq_one.1 h.symm)
  rw [← h', kummerCocycle_apply, val_kummerFun, Units.val_div_eq_div_val, div_mul_cancel₀ _
    α.ne_zero]
  rfl

/-- **Kummer theory over `F k̄`**: the restriction of a `μ_n`-cocycle of `Π_U` to `Gal(Ω/F k̄)` is
`σ ↦ σα/α` for some `α` with `αⁿ ∈ F k̄`. -/
theorem exists_root {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω)) :
    ∃ a : (F (baseChange D))ˣ, ∃ α : Ωˣ,
      α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a ∧
      ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α :=
  exists_root_of_triv (ContH1.cocyclesMap (galToPi D) (continuous_galToPi D)
    (MonoidHom.id (Mu n Ω)) continuous_id (fun τ ζ => galToPi_smul_mu τ ζ) c) gal_smul_mu

omit [CharZero k] [IsAlgClosed Ω] in
/-- An element of `Ω` fixed by `Gal(Ω/F k̄)` lies in `F k̄`. -/
lemma exists_unit_of_fixed {β : Ω} (hβ : β ≠ 0)
    (h : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, τ β = β) :
    ∃ b : (F (baseChange D))ˣ, ((b : F (baseChange D)) : Ω) = β := by
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F (baseChange D)) β).2 h
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← hb, map_zero])
  exact ⟨Units.mk0 b hb0, hb⟩

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- A Kummer function `a = αⁿ` is unramified if `α` is fixed by all inertia groups. -/
lemma isUnramifiedKummer_of_fix {κ : Type u} [Field κ] [Algebra κ Ω] [CharZero κ]
    {E : Pi1.Orbifold.GaloisData κ t} [IsGalois (K₀ κ t) Ω] [IsSepClosed Ω] {n : ℕ} [NeZero n]
    (a : (F E)ˣ) (α : Ωˣ) (hα : α ^ n = Units.map (algebraMap (F E) Ω : F E →* Ω) a)
    (hfix : ∀ (W : ValuationSubring Ω), (∀ c : κ, algebraMap κ Ω c ∈ W) → ∀ σ : E.H,
      (σ : Ω ≃ₐ[K₀ κ t] Ω) ∈ GaloisPi1.inertia W → (σ : Ω ≃ₐ[K₀ κ t] Ω) α = α) :
    IsUnramifiedKummer E n a := by
  intro W hk σ hσ
  rw [kummer_eq a α hα]
  change kummerCocycle α (smul_pow_of_pow_eq hα) (toGalF E σ) = 1
  apply Mu.ext
  apply Units.ext
  rw [kummerCocycle_apply, val_kummerFun, Units.val_div_eq_div_val, map_one, Units.val_one]
  change (σ : Ω ≃ₐ[K₀ κ t] Ω) (α : Ω) / α = 1
  rw [hfix W hk σ hσ, div_self α.ne_zero]

/-- **The Kummer function is unramified**: if `c` vanishes on the inertia groups `I_W ∩ H` of all
places `W ⊇ k` of `Ω`, the function `a` of `exists_root` is unramified over `F k̄`. -/
theorem isUnramifiedKummer_of {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω))
    (hc : ∀ (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) → ∀ σ : D.H,
      (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W → c (σ : Pi D) = 1)
    (a : (F (baseChange D))ˣ) (α : Ωˣ)
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a)
    (hca : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α) :
    IsUnramifiedKummer (baseChange D) n a := by
  refine isUnramifiedKummer_of_fix a α hα fun W hk σ hσ => ?_
  have hk' : ∀ x : k, algebraMap k Ω x ∈ W := fun x => by
    rw [IsScalarTower.algebraMap_apply k (kbar k Ω) Ω]
    exact hk _
  set τ := toGalF (baseChange D) σ
  have h1 := hc W hk' (galToH D τ) fun x hx => hσ x hx
  have e := hca τ
  rw [show galToPi D τ = ((galToH D τ : D.H) : Pi D) from rfl, h1, map_one, Units.val_one,
    one_mul] at e
  exact e.symm

omit [IsAlgClosed Ω] in
/-- The cocycle on a conjugate: `c(h⁻¹ τ h) = h⁻¹ • c(τ)` on `Gal(Ω/F k̄)`. -/
lemma cocycle_galToPi_conj {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω)) (h : D.H)
    (τ τ' : Ω ≃ₐ[F (baseChange D)] Ω) (hτ' : galToH D τ' = h⁻¹ * galToH D τ * h) :
    c (galToPi D τ') = (h : Pi D)⁻¹ • c (galToPi D τ) := by
  have hconj : galToPi D τ' = (h : Pi D)⁻¹ * galToPi D τ * (h : Pi D) := by
    change ((galToH D τ' : D.H) : Pi D) = _
    rw [hτ']
    rfl
  rw [hconj, cocycle_conj (ContH1.isMulCocycle₁ c) _ _ (galToPi_smul_mu_eq τ)]

omit [IsAlgClosed Ω] in
/-- `h(α)/α` is fixed by `Gal(Ω/F k̄)`, for `h ∈ H`. -/
theorem apply_div_fixed {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω)) (α : Ωˣ)
    (hca : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α)
    (h : D.H) (τ : Ω ≃ₐ[F (baseChange D)] Ω) :
    τ ((h : Ω ≃ₐ[K₀ k t] Ω) α / α) = (h : Ω ≃ₐ[K₀ k t] Ω) α / α := by
  obtain ⟨τ', hτ'⟩ := exists_galToH_conj D h τ
  have e1 := hca τ'
  rw [cocycle_galToPi_conj c h τ τ' hτ'] at e1
  have e2 := hca τ
  have hτ'α := congrArg (fun g : D.H => (g : Ω ≃ₐ[K₀ k t] Ω) (α : Ω)) hτ'
  simp only [galToH_apply, Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply,
    AlgEquiv.aut_inv] at hτ'α
  have hsm : ∀ ζ : Mu n Ω, (((Mu.val ((h : Pi D)⁻¹ • ζ)) : Ωˣ) : Ω) =
      (h : Ω ≃ₐ[K₀ k t] Ω).symm ((Mu.val ζ : Ωˣ) : Ω) := fun ζ => rfl
  rw [hsm, hτ'α] at e1
  have e3 := congrArg (h : Ω ≃ₐ[K₀ k t] Ω) e1
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at e3
  have hζ0 := (Mu.val (c (galToPi D τ))).ne_zero
  rw [map_div₀, ← e3, ← e2, mul_div_mul_left _ _ hζ0]

omit [CharZero k] [IsAlgClosed Ω] in
lemma coe_eq_pow_of {n : ℕ} {a : (F (baseChange D))ˣ} {α : Ωˣ}
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a) :
    ((a : F (baseChange D)) : Ω) = (α : Ω) ^ n := by
  have := congrArg (fun u : Ωˣ => (u : Ω)) hα
  simpa using this.symm

omit [IsAlgClosed Ω] in
/-- **`G_k`-invariance of the Kummer function up to `n`-th powers**: for `h ∈ H`,
`h(a) = a · bⁿ` with `b ∈ (F k̄)ˣ`. -/
theorem exists_apply_eq_mul_pow {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω))
    (a : (F (baseChange D))ˣ) (α : Ωˣ)
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a)
    (hca : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α)
    (h : D.H) :
    ∃ b : (F (baseChange D))ˣ, (h : Ω ≃ₐ[K₀ k t] Ω) ((a : F (baseChange D)) : Ω) =
      (a : F (baseChange D)) * ((b : F (baseChange D)) : Ω) ^ n := by
  have hα0 : (α : Ω) ≠ 0 := α.ne_zero
  have hβ0 : (h : Ω ≃ₐ[K₀ k t] Ω) α / α ≠ 0 :=
    div_ne_zero ((map_ne_zero _).2 hα0) hα0
  obtain ⟨b, hb⟩ := exists_unit_of_fixed hβ0 (apply_div_fixed c α hca h)
  refine ⟨b, ?_⟩
  rw [hb, div_pow, coe_eq_pow_of hα, ← map_pow, mul_div_cancel₀ _ (pow_ne_zero _ hα0)]

/-- The divisor of an unramified Kummer function is divisible by `n`. -/
lemma exists_nsmul_eq_div {n : ℕ} [NeZero n] {a : (F (baseChange D))ˣ}
    (hun : IsUnramifiedKummer (baseChange D) n a) :
    ∃ E : Divisor (kbar k Ω) (F (baseChange D)),
      n • E = Divisor.div (kbar k Ω) (a : F (baseChange D)) :=
  (mem_nsmulDivisors_div_iff (baseChange D) n _).2 ((isUnramifiedKummer_iff _ n a).1 hun)

omit [IsAlgClosed Ω] in
/-- `[E] ∈ Pic(X_{k̄})^{G_k}` for the divisor `E` with `n E = div a`. -/
lemma mk_mem_picInv {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω))
    (a : (F (baseChange D))ˣ) (α : Ωˣ)
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a)
    (hca : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α)
    (E : Divisor (kbar k Ω) (F (baseChange D)))
    (hE : n • E = Divisor.div (kbar k Ω) (a : F (baseChange D))) :
    (E : Pic (kbar k Ω) (F (baseChange D))) ∈ picInv D := by
  intro h
  obtain ⟨b, hb⟩ := exists_apply_eq_mul_pow c a α hα hca h
  exact picMap_mk_eq_of (NeZero.ne n) (autF D h) a.ne_zero b.ne_zero hE (Subtype.ext hb)

set_option maxHeartbeats 1000000 in
-- elaborating statements about `F (baseChange D)` (units, divisors) needs deep unfolding
omit [IsAlgClosed Ω] in
/-- **Compatibility of the Kummer functions of two levels** `n ∣ m`: `a_m = a_n gⁿ`. -/
lemma exists_eq_mul_pow_of_dvd {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (cn : ContH1.cocycles (Pi D) (Mu n Ω)) (cm : ContH1.cocycles (Pi D) (Mu m Ω))
    (hc : ∀ x, Mu.transition hnm (cm x) = cn x)
    (an : (F (baseChange D))ˣ) (αn : Ωˣ)
    (hαn : αn ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) an)
    (hcan : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (cn (galToPi D τ)) : Ωˣ) : Ω) * αn = τ αn)
    (am : (F (baseChange D))ˣ) (αm : Ωˣ)
    (hαm : αm ^ m = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) am)
    (hcam : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (cm (galToPi D τ)) : Ωˣ) : Ω) * αm = τ αm) :
    ∃ g : (F (baseChange D))ˣ, ((am : F (baseChange D)) : Ω) =
      (an : F (baseChange D)) * ((g : F (baseChange D)) : Ω) ^ n := by
  have hαn0 : (αn : Ω) ≠ 0 := αn.ne_zero
  have hαm0 : (αm : Ω) ≠ 0 := αm.ne_zero
  have hfix : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω,
      τ ((αm : Ω) ^ (m / n) / αn) = (αm : Ω) ^ (m / n) / αn := by
    intro τ
    have e := hc (galToPi D τ)
    have e' := congrArg (fun z : Mu n Ω => ((Mu.val z : Ωˣ) : Ω)) e
    simp only [Mu.val_transition, Units.val_pow_eq_pow_val] at e'
    rw [map_div₀, map_pow, ← hcam τ, ← hcan τ, ← e', mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero _ (Mu.val (cm (galToPi D τ))).ne_zero)]
  obtain ⟨g, hg⟩ := exists_unit_of_fixed (div_ne_zero (pow_ne_zero _ hαm0) hαn0) hfix
  refine ⟨g, ?_⟩
  rw [hg, coe_eq_pow_of hαm, coe_eq_pow_of hαn, div_pow, ← pow_mul,
    Nat.div_mul_cancel hnm, mul_div_cancel₀ _ (pow_ne_zero _ hαn0)]

set_option maxHeartbeats 1000000 in
-- elaborating statements about `F (baseChange D)` (units, divisors) needs deep unfolding
/-- A Kummer function whose divisor class is trivial is an `n`-th power (`k̄` algebraically
closed). -/
lemma exists_pow_eq_of_mk_eq_zero {n : ℕ} [NeZero n] (a : (F (baseChange D))ˣ)
    (E : Divisor (kbar k Ω) (F (baseChange D)))
    (hE : n • E = Divisor.div (kbar k Ω) (a : F (baseChange D)))
    (h0 : (E : Pic (kbar k Ω) (F (baseChange D))) = 0) :
    ∃ w : (F (baseChange D))ˣ, a = w ^ n := by
  obtain ⟨f, hf, hfE⟩ := (mem_principal (k := kbar k Ω)).1 ((QuotientAddGroup.eq_zero_iff E).1 h0)
  set fu := Units.mk0 f hf
  have hu : divHom (kbar k Ω) (F (baseChange D)) (Additive.ofMul (a * (fu ^ n)⁻¹)) = 0 := by
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_pow, map_nsmul]
    change Divisor.div (kbar k Ω) (a : F (baseChange D)) + -(n • Divisor.div (kbar k Ω) f) = 0
    rw [hfE, hE, add_neg_cancel]
  obtain ⟨v, hv⟩ := mem_nsmul_range_of_div_eq_zero (baseChange D) n
    (Nat.pos_of_ne_zero (NeZero.ne n)) _ hu
  refine ⟨Additive.toMul v * fu, ?_⟩
  have := congrArg Additive.toMul hv
  simp only [nsmulAddMonoidHom_apply, toMul_nsmul, toMul_ofMul] at this
  rw [mul_pow, this, inv_mul_cancel_right]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
lemma mem_kbar_of_pow_eq_one {z : Ω} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ kbar k Ω :=
  mem_algebraicClosure_iff.mpr
    ⟨Polynomial.X ^ n - 1, Polynomial.X_pow_sub_C_ne_zero hn 1, by simp [hz]⟩

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- If `αⁿ = wⁿ` with `w ∈ K` and `τ ∈ Gal(Ω/K)` fixes the `n`-th roots of unity, `τ α = α`. -/
lemma apply_eq_of_pow_eq {K : Type*} [Field K] [Algebra K Ω] (τ : Ω ≃ₐ[K] Ω) (α : Ωˣ) (w : Kˣ)
    {n : ℕ} (hαw : (α : Ω) ^ n = (algebraMap K Ω w) ^ n)
    (hfix : ∀ z : Ω, z ^ n = 1 → τ z = z) : τ α = α := by
  have hw0 : algebraMap K Ω w ≠ 0 := (map_ne_zero _).2 w.ne_zero
  have hz : ((α : Ω) / algebraMap K Ω w) ^ n = 1 := by
    rw [div_pow, hαw, div_self (pow_ne_zero _ hw0)]
  have h1 := hfix _ hz
  rw [map_div₀, AlgEquiv.commutes] at h1
  exact (div_left_inj' hw0).1 h1

omit [CharZero k] [IsAlgClosed Ω] in
lemma pow_eq_of_eq_pow {n : ℕ} {a w : (F (baseChange D))ˣ} {α : Ωˣ}
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a)
    (hw : a = w ^ n) :
    (α : Ω) ^ n = (algebraMap (F (baseChange D)) Ω w) ^ n := by
  rw [← coe_eq_pow_of hα, hw, Units.val_pow_eq_pow_val, IntermediateField.coe_pow]
  rfl

set_option maxHeartbeats 1000000 in
-- elaborating statements about `F (baseChange D)` (units, divisors) needs deep unfolding
/-- **If the Kummer divisor class is trivial, the cocycle is trivial on `Gal(Ω/F k̄)`.** -/
lemma eq_one_of_mk_eq_zero {n : ℕ} [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω))
    (a : (F (baseChange D))ˣ) (α : Ωˣ)
    (hα : α ^ n = Units.map (algebraMap (F (baseChange D)) Ω : F (baseChange D) →* Ω) a)
    (hca : ∀ τ : Ω ≃ₐ[F (baseChange D)] Ω, ((Mu.val (c (galToPi D τ)) : Ωˣ) : Ω) * α = τ α)
    (E : Divisor (kbar k Ω) (F (baseChange D)))
    (hE : n • E = Divisor.div (kbar k Ω) (a : F (baseChange D)))
    (h0 : (E : Pic (kbar k Ω) (F (baseChange D))) = 0) (τ : Ω ≃ₐ[F (baseChange D)] Ω) :
    c (galToPi D τ) = 1 := by
  obtain ⟨w, hw⟩ := exists_pow_eq_of_mk_eq_zero a E hE h0
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hτα := apply_eq_of_pow_eq τ α w (pow_eq_of_eq_pow hα hw)
    (fun z hz => galToH_fix_kbar D τ (mem_kbar_of_pow_eq_one hn hz))
  have e := hca τ
  rw [hτα] at e
  apply Mu.ext
  apply Units.ext
  rw [map_one, Units.val_one]
  exact (mul_eq_right₀ α.ne_zero).1 e

/-- The level-`n` component `proj_i ∘ c` of a `Ẑ(1)`-cocycle. -/
noncomputable def cn (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω)) (i : KummerIndex (F D)) :
    ContH1.cocycles (Pi D) (Mu i.n Ω) :=
  ContH1.cocyclesMap (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i)
    (ZHatOne.continuous_proj i) (fun g x => proj_pi_smul i g x) c

omit [IsAlgClosed Ω] in
lemma cn_apply (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω)) (i : KummerIndex (F D))
    (x : Pi D) : cn c i x = ZHatOne.proj i (c x) := rfl

/-- The index `n N`. -/
def KummerIndex.mulNat (i : KummerIndex (F D)) (N : ℕ) (hN : 0 < N) : KummerIndex (F D) :=
  ⟨i.n * N, by
    rw [Nat.cast_ne_zero]
    exact mul_ne_zero i.n_ne_zero hN.ne'⟩

/-- **The level-`n` components vanish on `Gal(Ω/F k̄)`** (Kummer-faithfulness for `J`). -/
theorem cn_galToPi_eq_one (hJ : IsKummerFaithfulJac D)
    (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω))
    (hc : ∀ (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) → ∀ σ : D.H,
      (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W → c (σ : Pi D) = 1)
    (i : KummerIndex (F D)) (τ : Ω ≃ₐ[F (baseChange D)] Ω) : cn c i (galToPi D τ) = 1 := by
  have hc' : ∀ j : KummerIndex (F D), ∀ (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) →
      ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W → cn c j (σ : Pi D) = 1 :=
    fun j W hk σ hσ => by rw [cn_apply, hc W hk σ hσ, map_one]
  choose a α hα hca using fun j : KummerIndex (F D) => exists_root (cn c j)
  choose E hE using fun j : KummerIndex (F D) =>
    exists_nsmul_eq_div (isUnramifiedKummer_of (cn c j) (hc' j) (a j) (α j) (hα j) (hca j))
  have hinv : ∀ j, (E j : Pic (kbar k Ω) (F (baseChange D))) ∈ picInv D := fun j =>
    mk_mem_picInv (cn c j) (a j) (α j) (hα j) (hca j) (E j) (hE j)
  have hcompat : ∀ (N : ℕ) (hN : 0 < N), N • (E (KummerIndex.mulNat i N hN) :
      Pic (kbar k Ω) (F (baseChange D))) = E i := by
    intro N hN
    set j := KummerIndex.mulNat i N hN
    have hij : i.n ∣ j.n := ⟨N, rfl⟩
    obtain ⟨g, hg⟩ := exists_eq_mul_pow_of_dvd hij (cn c i) (cn c j)
      (fun x => ZHatOne.transition_proj (show i ≤ j from hij) (c x)) (a i) (α i) (hα i) (hca i)
      (a j) (α j) (hα j) (hca j)
    exact nsmul_mk_eq_of (NeZero.ne i.n) (a i).ne_zero g.ne_zero (hE i) (hE j) (Subtype.ext hg)
  have h0 := hJ _ fun N hN => ⟨_, hinv _, hcompat N hN⟩
  exact eq_one_of_mk_eq_zero (cn c i) (a i) (α i) (hα i) (hca i) (E i) (hE i) h0 τ

/-- **The cocycle vanishes on `Δ = ker(Π_U → G_k)`.** -/
theorem eq_one_of_piToGk_eq_one (hJ : IsKummerFaithfulJac D)
    (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω))
    (hc : ∀ (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) → ∀ σ : D.H,
      (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W → c (σ : Pi D) = 1)
    (x : Pi D) (hx : piToGk D x = 1) : c x = 1 := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨τ, hτ⟩ := exists_galToH_eq D ((hToGk_eq_one_iff D h).1 hx)
  have hxτ : (h : Pi D) = galToPi D τ := by
    change _ = ((galToH D τ : D.H) : Pi D)
    rw [hτ]
  rw [hxτ]
  apply Subtype.ext
  funext i
  exact cn_galToPi_eq_one hJ c hc i τ

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- `Ẑ(1)_{k̄} → Ẑ(1)_Ω` has a continuous inverse. -/
lemma exists_continuous_zHatMap_inv (K : Type*) [Field K] [CharZero K] :
    ∃ g : ZHatOne K Ω → ZHatOne k (kbar k Ω), Continuous g ∧
      ∀ x, zHatMap (k := k) (Ω := Ω) K (g x) = x := by
  have hpre : ∀ (j : KummerIndex k) (ζ : Mu j.n Ω), ∃ η, muMap j.n (kbar k Ω) Ω η = ζ :=
    fun j ζ => haveI : NeZero j.n := ⟨j.n_ne_zero⟩; muMap_surjective (k := k) j.n ζ
  choose g hg using hpre
  let toK : KummerIndex k → KummerIndex K := fun j => ⟨j.n, Nat.cast_ne_zero.mpr j.n_ne_zero⟩
  refine ⟨fun x => ⟨fun j => g j ((x : ∀ i, Mu i.n Ω) (toK j)), fun i j h => ?_⟩, ?_, ?_⟩
  · apply muMap_injective (k := k) (Ω := Ω) i.n
    rw [muMap_transition, hg, hg]
    exact x.2 (toK i) (toK j) h
  · refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    exact continuous_of_discreteTopology.comp
      ((continuous_apply (toK j)).comp continuous_subtype_val)
  · intro x
    apply Subtype.ext
    funext i
    exact hg (toIndex (k := k) i) _

/-- **[AbsTopIII] Prop. 1.6(iii), middle exactness** (T3 l.2001–2012, proof l.2032–2039): if `k` is
algebraically closed in `F` and Kummer-faithful for the Jacobian (`IsKummerFaithfulJac D`), a class
`η ∈ H¹(Π_U, Ẑ(1))` vanishing on the inertia groups `I_W ∩ H` of all places `W ⊇ k` of `Ω` lies in
the image of `(kˣ)^∧ → H¹(Π_U, Ẑ(1))`. -/
theorem mem_range_constMapZHat (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω))
    (hη : ∀ (W : ValuationSubring Ω) (hW : ∀ x : k, algebraMap k Ω x ∈ W) (σ : D.H)
      (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W),
      ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_zHatOne hW hσ (F D)) η = 1) :
    η ∈ (constMapZHat D).range := by
  induction η using ContH1.induction_on with
  | h c =>
  have hc : ∀ (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) → ∀ σ : D.H,
      (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W → c (σ : Pi D) = 1 :=
    fun W hW σ hσ => hη W hW σ hσ
  obtain ⟨g, hgc, hg⟩ := exists_continuous_zHatMap_inv (k := k) (Ω := Ω) (F D)
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  haveI : CompactSpace (Pi D) := Quotient.compactSpace
  obtain ⟨y, hy⟩ := ContH1.exists_map_eq_mk (piToGk D) (continuous_piToGk D)
    (piToGk_surjective D hk) (zHatMap (F D)) (continuous_zHatMap (F D))
    (zHatMap_injective (F D)) g hgc hg (zHatMap_piToGk_smul D (F D)) c
    (eq_one_of_piToGk_eq_one hJ c hc)
  refine ⟨kummerZHatEquiv k (kbar k Ω) y, ?_⟩
  rw [constMapZHat_apply, MulEquiv.symm_apply_apply, hy]

end CurvesJacobian.Kummer
