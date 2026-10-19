/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianPi1

/-!
# Classes in `H¹(G_k, Δ_X^{ab})` are detected modulo `N`; Kummer classes of a divisible module

Inputs of [Cusp] Prop. 2.3(i) ("`D` principal ⟺ `η_D = 0`", proof via the Kummer sequences
`0 → J[N] → J(k̄) → J(k̄) → 0`, [Cusp] txt l.2084–2102) which need neither divisibility of `J(k̄)`
(JAC-4a) nor the Weil pairing (JAC-4b):

* `ContH1.mk_eq_one_of_forall_mem`: for a compact Hausdorff coefficient group `M` and a directed
  family of closed subgroups `U i` with `⋂ U i = 1`, a continuous cocycle that is a coboundary
  modulo every `U i` is a coboundary (compactness: the closed sets of `m` with
  `c(σ) ≡ σm/m mod U i` have the finite intersection property);
* `CurvesJacobian.Kummer.eq_one_of_forall_exists_pow_eq`: in an abelian quotient of a profinite
  group, an element with `N`-th roots for all `N ≥ 1` is trivial (open subgroups have finite
  index);
* **`CurvesJacobian.Kummer.eq_one_of_forall_exists_pow_eq_deltaAb`**: `⋂_{N ≥ 1} (Δ_X^{ab})^N = 1`
  (through `Δ̃ = deltaTilde D`, the preimage of `Δ_X` in the profinite group `H`), and
  **`CurvesJacobian.Kummer.mk_eq_one_iff_forall_pow`**: a class `c ∈ H¹(G_k, Δ_X^{ab})` (e.g.
  `η_D`) vanishes iff `c` is a coboundary modulo `(Δ_X^{ab})^N` for every `N ≥ 1`, i.e. iff its
  images in `H¹(G_k, Δ_X^{ab}/N)` vanish;
* `kummer_mem_nsmul_iff`: for a `G`-module `M`, `x ∈ M^G` and `y` with
  `N • y = x`, the Kummer cocycle `σ ↦ σ y - y ∈ M[N]` is a coboundary with values in `M[N]` iff
  `x ∈ N · M^G` (the injectivity of `M^G/N → H¹(G, M[N])`, used for `M = J(k̄)`).

With JAC-4b (`Δ_X^{ab}/N ≅ J[N]`, `η_D mod N ↦` the Kummer cocycle of `[D]`) and J1
(`⋂_N N · J(k) = 0`) these give [Cusp] Prop. 2.3(i).
-/

open KummerTheory Curve AffOrbicurve groupCohomology

set_option linter.unusedSectionVars false

universe u

namespace ContH1

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M] [CompactSpace M] [ContinuousConstSMul G M]

/-- **A cocycle which is a coboundary modulo every member of a directed family of closed subgroups
with trivial intersection is a coboundary** (coefficients compact). -/
theorem mk_eq_one_of_forall_mem {ι : Type*} [Nonempty ι] (U : ι → Subgroup M)
    (hU : ∀ i, IsClosed (U i : Set M)) (hdir : Directed (· ≥ ·) U) (hbot : ⨅ i, U i = ⊥)
    (c : cocycles G M) (hc : ∀ i, ∃ m : M, ∀ σ : G, c σ / (σ • m / m) ∈ U i) : mk c = 1 := by
  rw [mk_eq_one_iff]
  let S : ι → Set M := fun i => {m | ∀ σ : G, c σ / (σ • m / m) ∈ U i}
  have hScl : ∀ i, IsClosed (S i) := fun i => by
    have : S i = ⋂ σ : G, (fun m => c σ / (σ • m / m)) ⁻¹' (U i : Set M) := by
      ext m
      simp [S]
    rw [this]
    exact isClosed_iInter fun σ => (hU i).preimage
      (continuous_const.div' ((continuous_const_smul σ).div' continuous_id))
  have hSdir : Directed (· ⊇ ·) S := by
    intro i j
    obtain ⟨l, hli, hlj⟩ := hdir i j
    exact ⟨l, fun m hm σ => hli (hm σ), fun m hm σ => hlj (hm σ)⟩
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hSdir
    hc (fun i => (hScl i).isCompact) hScl
  refine ⟨m, fun σ => ?_⟩
  have h1 : c σ / (σ • m / m) ∈ ⨅ i, U i :=
    Subgroup.mem_iInf.2 fun i => Set.mem_iInter.1 hm i σ
  rw [hbot, Subgroup.mem_bot, div_eq_one] at h1
  exact h1.symm

end ContH1

namespace CurvesJacobian.Kummer

section Profinite

variable {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P] [CommGroup Q]

/-- **Infinitely divisible elements of an abelian quotient of a profinite group are trivial**:
if `π : P ↠ Q` has closed kernel and `Q` is commutative, then `q ∈ ⋂_{N ≥ 1} Q^N` forces `q = 1`.
(An element `h ∉ ker π` avoids an open subgroup `U ⊇ ker π`; `U` is normal, of finite index `n`,
and `q = y^n` would put `h` into `U`.) -/
theorem eq_one_of_forall_exists_pow_eq (π : P →* Q) (hπ : Function.Surjective π)
    (hK : IsClosed (π.ker : Set P)) (q : Q) (hq : ∀ N : ℕ, 0 < N → ∃ y, y ^ N = q) : q = 1 := by
  by_contra hne
  obtain ⟨h, rfl⟩ := hπ q
  have hh : h ∉ π.ker := fun hk => hne hk
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨π.ker, hK⟩
  change π.ker = _ at key
  rw [key, Subgroup.mem_sInf] at hh
  push Not at hh
  obtain ⟨U, ⟨hUo, hKU⟩, hhU⟩ := hh
  haveI hUn : U.Normal := ⟨fun u hu g => by
    have hc : u⁻¹ * (g * u * g⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (π g)]
      group
    simpa using U.mul_mem hu (hKU hc)⟩
  haveI := Subgroup.quotient_finite_of_isOpen U hUo
  set n := Nat.card (P ⧸ U)
  have hn : 0 < n := Nat.card_pos
  obtain ⟨y, hy⟩ := hq n hn
  obtain ⟨p, rfl⟩ := hπ y
  have hpn : p ^ n ∈ U := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hdiff : (p ^ n)⁻¹ * h ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hy, inv_mul_cancel]
  exact hhU (by simpa using U.mul_mem hpn (hKU hdiff))

end Profinite

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- The preimage `Δ̃ ⊆ H` of `Δ_X`. -/
noncomputable def deltaTilde (D : Pi1.Orbifold.GaloisData k t) : Subgroup D.H :=
  (DeltaX D).comap (QuotientGroup.mk' _)

theorem isClosed_deltaTilde : IsClosed (deltaTilde D : Set D.H) :=
  (isClosed_deltaX D).preimage QuotientGroup.continuous_mk

instance compactSpace_deltaTilde : CompactSpace (deltaTilde D) :=
  isCompact_iff_compactSpace.mp isClosed_deltaTilde.isCompact

/-- `Δ̃ → Δ_X`. -/
noncomputable def deltaTildeToDeltaX : deltaTilde D →* DeltaX D :=
  ((QuotientGroup.mk' (GaloisPi1.kernel D.H (SAll D))).comp (deltaTilde D).subtype).codRestrict
    (DeltaX D) fun x => x.2

/-- `Δ̃ ↠ Δ_X ↠ Δ_X^{ab}`. -/
noncomputable def deltaTildeToAb : deltaTilde D →* DeltaAb D :=
  (deltaAbMk D).comp deltaTildeToDeltaX

theorem deltaTildeToAb_surjective : Function.Surjective (deltaTildeToAb (D := D)) := by
  intro a
  obtain ⟨δ, rfl⟩ := deltaAbMk_surjective D a
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (δ : PiX D)
  have hmem : h ∈ deltaTilde D := by
    change (QuotientGroup.mk' _ h : PiX D) ∈ DeltaX D
    rw [QuotientGroup.mk'_apply, hh]
    exact δ.2
  refine ⟨⟨h, hmem⟩, ?_⟩
  change deltaAbMk D (deltaTildeToDeltaX _) = _
  congr 1
  exact Subtype.ext hh

theorem isClosed_ker_deltaTildeToAb :
    IsClosed ((deltaTildeToAb (D := D)).ker : Set (deltaTilde D)) := by
  have : ((deltaTildeToAb (D := D)).ker : Set (deltaTilde D)) =
      (fun x : deltaTilde D => (QuotientGroup.mk (x : D.H) : PiX D)) ⁻¹'
        (commClosure D : Set (PiX D)) := by
    ext x
    exact deltaAbMk_eq_one_iff D _
  rw [this]
  exact (isClosed_commClosure D).preimage (QuotientGroup.continuous_mk.comp continuous_subtype_val)

/-- **`⋂_{N ≥ 1} (Δ_X^{ab})^N = 1`**: an element of `Δ_X^{ab}` with `N`-th roots for all `N ≥ 1` is
trivial (`Δ_X^{ab}` is an abelian quotient of the profinite group `Δ̃ ⊆ H`). -/
theorem eq_one_of_forall_exists_pow_eq_deltaAb (x : DeltaAb D)
    (hx : ∀ N : ℕ, 0 < N → ∃ y, y ^ N = x) : x = 1 :=
  eq_one_of_forall_exists_pow_eq deltaTildeToAb deltaTildeToAb_surjective
    isClosed_ker_deltaTildeToAb x hx

variable [Fact (Function.Surjective (piJ1ToGk D))]

/-- **Classes in `H¹(G_k, Δ_X^{ab})` are detected modulo `N`**: a continuous cocycle `c` (e.g. a
representative of `η_D`) is a coboundary iff for every `N ≥ 1` it is a coboundary modulo
`(Δ_X^{ab})^N`, i.e. iff all its images in `H¹(G_k, Δ_X^{ab}/N)` vanish. -/
theorem mk_eq_one_iff_forall_pow (c : ContH1.cocycles (Gk k Ω) (DeltaAb D)) :
    ContH1.mk c = 1 ↔
      ∀ N : ℕ, 0 < N → ∃ m : DeltaAb D, ∀ σ : Gk k Ω,
        c σ / (σ • m / m) ∈ (powMonoidHom N).range := by
  constructor
  · intro h N _
    obtain ⟨m, hm⟩ := (ContH1.mk_eq_one_iff c).1 h
    exact ⟨m, fun σ => ⟨1, by rw [powMonoidHom_apply, one_pow, hm σ, div_self']⟩⟩
  · intro h
    haveI : Nonempty {N : ℕ // 0 < N} := ⟨⟨1, one_pos⟩⟩
    refine ContH1.mk_eq_one_of_forall_mem (fun N : {N : ℕ // 0 < N} => (powMonoidHom N.1).range)
      (fun N => ?_) (fun N M => ?_) ?_ c (fun N => h N.1 N.2)
    · rw [MonoidHom.coe_range]
      exact (isCompact_range (continuous_pow N.1)).isClosed
    · refine ⟨⟨N.1 * M.1, Nat.mul_pos N.2 M.2⟩, ?_, ?_⟩
      · rintro _ ⟨y, rfl⟩
        exact ⟨y ^ M.1, by simp only [powMonoidHom_apply, ← pow_mul, mul_comm]⟩
      · rintro _ ⟨y, rfl⟩
        exact ⟨y ^ N.1, by simp only [powMonoidHom_apply, ← pow_mul]⟩
    · rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_iInf] at hx
      exact eq_one_of_forall_exists_pow_eq_deltaAb x fun N hN => hx ⟨N, hN⟩

end CurvesJacobian.Kummer

section KummerSequence

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- **Kummer sequence, injectivity of `M^G / N → H¹(G, M[N])`**: for `y ∈ M` with `N • y = x`,
the Kummer cocycle `σ ↦ σ • y - y` (with values in `M[N]` when `x` is invariant) is a coboundary
of an element of `M[N]` iff `x ∈ N · M^G`. -/
theorem kummer_mem_nsmul_iff (x y : M) (N : ℕ) (hy : N • y = x) :
    (∃ m : M, N • m = 0 ∧ ∀ σ : G, σ • y - y = σ • m - m) ↔
      ∃ x' : M, (∀ σ : G, σ • x' = x') ∧ N • x' = x := by
  constructor
  · rintro ⟨m, hm, hσ⟩
    refine ⟨y - m, fun σ => ?_, by rw [nsmul_sub, hy, hm, sub_zero]⟩
    rw [smul_sub]
    have := hσ σ
    rw [sub_eq_sub_iff_sub_eq_sub] at this
    exact this
  · rintro ⟨x', hx', hN⟩
    refine ⟨y - x', by rw [nsmul_sub, hy, hN, sub_self], fun σ => ?_⟩
    rw [smul_sub, hx' σ]
    abel

end KummerSequence
