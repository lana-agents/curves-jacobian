/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Assembly
import CurvesJacobian.Cusp.FillElemOp
import CurvesJacobian.Cusp.CuspInertiaQuotient
import CurvesJacobian.Cusp.CuspInertiaFacts


/-!
# The cusp groups of `Δ_U` form a cusp set (inputs of [AbsTopI] Lemma 4.5 (v))

For an affine hyperbolic curve `U = C` over a number field `K` with a cusp (`hc`) and an algebraic
closure `Ω`, let `Δ_U = ker(Π_U ↠ G_K)` (`CurvesJacobian.CuspChar.deltaU`) and let
`deltaCusps Ω C hc` be the cuspidal inertia groups `arithCusps Ω C hc` of `Π_U`, viewed in `Δ_U`
(`mem_arithCusps_iff_mem_deltaCusps` is the bridge). We verify the hypotheses of
`CurvesJacobian.CuspChar.mem_iff_map_mem_of_cuspWeightIdentity` for `(Π_U, Δ_U, deltaCusps)`:

* (T1) `Δ_U` is compact, Hausdorff, totally disconnected and normal in `Π_U`;
* (T2) `card_charSpace_two_deltaU`: `Δ_U` has `2 ^ (χ₀ + 1)` continuous `ℤ/2`-characters, where
  `χ₀ = 2g - 2 + r` (`eulerU`), and `eulerU_pos : 0 < χ₀` (hyperbolicity);
* (T3) `exists_cuspCount_mul_le_deltaU`: for every `m` there is an open `H ⊆ Δ_U` with
  `r(H) · m ≤ r · [Δ_U : H]`;
* (T4) `isCuspSet_deltaCusps`: `deltaCusps` is a cusp set (`IsCuspSet`), given as an explicit
  hypothesis `hcent` the centraliser property of the cusp groups `Iⱼ ⊆ Π̂_{g,r}`.

`mem_deltaCusps_iff_of_cuspWeightIdentity` combines these with
`mem_iff_map_mem_of_cuspWeightIdentity`.

The route: `Θ : π₁ᵉᵗ(U_Ω) ≃ₜ* Π̂_{g,r}`
(`exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed`) gives `Φ : Δ_U ≃ₜ* Π̂_{g,r}`
under which every cusp group of `Δ_U` is a `Δ_U`-conjugate of some
`Φ⁻¹(Iⱼ)` (`exists_equiv_deltaCusps_subset`). The group-theoretic properties are then proved for
any set of subgroups contained in the conjugates of the `Φ⁻¹(Iⱼ)` (sections `Count`, `Cusps`):
finiteness of cusps and the cusp count via cosets, `cⱼ ∉ cl⟨cⱼ^p⟩` and the cusp bound via the finite
quotients of `Π_{g,r}` in which `cⱼ` has prescribed order (`exists_finite_orderOf_cusp`), and
finiteness of characters via the dense finitely generated subgroup `Π_{g,r}`.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite

namespace CurvesJacobian.CuspChar

/-! ### Counting the conjugates of finitely many subgroups -/

section Count

variable {D : Type*} [Group D] {r : ℕ} (A : Fin r → Subgroup D)

lemma conjSub_eq_self {a : D} {I : Subgroup D} (ha : a ∈ I) : conjSub a I = I := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := I.mul_mem (I.mul_mem ha hx) (I.inv_mem ha)
    simpa [mul_assoc] using this
  · intro hx
    exact I.mul_mem (I.mul_mem (I.inv_mem ha) hx) ha

/-- The set of all conjugates of the subgroups `A j`. -/
def conjFamily : Set (Subgroup D) := {J | ∃ j δ, J = conjSub δ (A j)}

lemma conjStable_conjFamily : ConjStable (conjFamily A) := by
  rintro _ ⟨j, δ, rfl⟩ g
  exact ⟨j, g * δ, (conjSub_mul g δ (A j)).symm⟩

/-- For `S ⊆ T`, the map from the cusps of `H` in `S` to those in `T`. -/
def cuspIncl {S T : Set (Subgroup D)} (hST : S ⊆ T) (H : Subgroup D) :
    CuspQuot S H → CuspQuot T H :=
  Quotient.map' (Set.inclusion hST) fun _ _ h ↦ h

lemma cuspIncl_injective {S T : Set (Subgroup D)} (hST : S ⊆ T) (H : Subgroup D) :
    Function.Injective (cuspIncl hST H) := by
  rintro ⟨I⟩ ⟨J⟩ h
  have h' : Quotient.mk (cuspSetoid T H) (Set.inclusion hST I) =
      Quotient.mk _ (Set.inclusion hST J) := h
  have h'' := Quotient.exact h'
  exact Quotient.sound h''

/-- The cusp `δ⁻¹ A_j δ` of `H`, as a function of the coset `δ H`. -/
def cuspOfCoset (H : Subgroup D) : (Σ _ : Fin r, D ⧸ H) → CuspQuot (conjFamily A) H :=
  fun x ↦ Quotient.liftOn' x.2 (fun δ ↦ Quotient.mk _ ⟨conjSub δ⁻¹ (A x.1), x.1, δ⁻¹, rfl⟩)
    fun δ δ' hδ ↦ by
      have hk := QuotientGroup.leftRel_apply.1 hδ
      apply Quotient.sound
      refine ⟨(δ⁻¹ * δ')⁻¹, H.inv_mem hk, ?_⟩
      change conjSub (δ⁻¹ * δ')⁻¹ (conjSub δ⁻¹ (A x.1)) = conjSub δ'⁻¹ (A x.1)
      rw [← conjSub_mul]
      congr 1
      group

lemma cuspOfCoset_surjective (H : Subgroup D) : Function.Surjective (cuspOfCoset A H) := by
  rintro ⟨⟨J, j, δ, rfl⟩⟩
  refine ⟨⟨j, QuotientGroup.mk δ⁻¹⟩, ?_⟩
  change Quotient.mk _ _ = Quotient.mk _ _
  congr 2
  rw [inv_inv]

/-- The cusp `δ A_j δ⁻¹` of `H`, as a function of the coset `δ K_j`, provided `δ K_j ⊆ H δ A_j`. -/
def cuspOfCosetK (H : Subgroup D) (K : Fin r → Subgroup D)
    (hK : ∀ j (δ k : D), k ∈ K j → ∃ h ∈ H, ∃ a ∈ A j, δ * k = h * δ * a) :
    (Σ j, D ⧸ K j) → CuspQuot (conjFamily A) H := fun x ↦
  Quotient.liftOn' x.2 (fun δ ↦ Quotient.mk _ ⟨conjSub δ (A x.1), x.1, δ, rfl⟩) fun δ δ' hδ ↦ by
    obtain ⟨h, hh, a, ha, e⟩ := hK x.1 δ (δ⁻¹ * δ') (QuotientGroup.leftRel_apply.1 hδ)
    apply Quotient.sound
    refine ⟨h, hh, ?_⟩
    have : δ' = h * δ * a := by rw [← e]; group
    change conjSub h (conjSub δ (A x.1)) = conjSub δ' (A x.1)
    rw [this, conjSub_mul, conjSub_mul, conjSub_eq_self ha]

lemma cuspOfCosetK_surjective (H : Subgroup D) (K : Fin r → Subgroup D)
    (hK : ∀ j (δ k : D), k ∈ K j → ∃ h ∈ H, ∃ a ∈ A j, δ * k = h * δ * a) :
    Function.Surjective (cuspOfCosetK A H K hK) := by
  rintro ⟨⟨J, j, δ, rfl⟩⟩
  exact ⟨⟨j, QuotientGroup.mk δ⟩, rfl⟩

/-- Finitely many cusps for a subgroup of finite index. -/
theorem finite_cuspQuot_of_subset {S : Set (Subgroup D)} (hS : S ⊆ conjFamily A)
    (H : Subgroup D) [Finite (D ⧸ H)] : Finite (CuspQuot S H) := by
  haveI : Finite (CuspQuot (conjFamily A) H) := Finite.of_surjective _ (cuspOfCoset_surjective A H)
  exact Finite.of_injective _ (cuspIncl_injective hS H)

theorem cuspCount_le_sum {S : Set (Subgroup D)} (hS : S ⊆ conjFamily A) (H : Subgroup D)
    (K : Fin r → Subgroup D) (hK : ∀ j (δ k : D), k ∈ K j → ∃ h ∈ H, ∃ a ∈ A j, δ * k = h * δ * a)
    [∀ j, Finite (D ⧸ K j)] : cuspCount S H ≤ ∑ j, (K j).index := by
  haveI : Finite (CuspQuot (conjFamily A) H) :=
    Finite.of_surjective _ (cuspOfCosetK_surjective A H K hK)
  calc cuspCount S H ≤ cuspCount (conjFamily A) H :=
        Nat.card_le_card_of_injective _ (cuspIncl_injective hS H)
    _ ≤ Nat.card (Σ j, D ⧸ K j) :=
        Nat.card_le_card_of_surjective _ (cuspOfCosetK_surjective A H K hK)
    _ = ∑ j, (K j).index := by rw [Nat.card_sigma]; rfl

omit [Group D] in
lemma index_comap_map_mul_le {D : Type*} [Group D] {F : Type*} [Group F] [Finite F] (φ : D →* F)
    (B : Subgroup D) {x : D} (hx : x ∈ B) {n : ℕ} (hn : n ∣ orderOf (φ x)) :
    ((B.map φ).comap φ).index * n ≤ φ.ker.index := by
  set L := B.map φ
  have hLR : L ≤ φ.range := Subgroup.map_le_range φ B
  rw [Subgroup.index_comap, Subgroup.index_ker]
  have h1 : Nat.card (L.subgroupOf φ.range) * L.relIndex φ.range = Nat.card φ.range :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (L.subgroupOf φ.range) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLR).toEquiv
  have h3 : n ∣ Nat.card L := hn.trans (L.orderOf_dvd_natCard ⟨x, hx, rfl⟩)
  have h4 : 0 < Nat.card L := Nat.card_pos
  rw [h2] at h1
  rw [← h1, mul_comm (Nat.card L)]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd h4 h3)

end Count
/-! ### Transport along isomorphisms with `Π̂_{g,r}` -/

section Transport

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G']

/-- A continuous homomorphism maps `cl⟨y⟩` into `cl⟨f y⟩`. -/
lemma map_mem_closure_zpowers (f : G →* G') (hf : Continuous f) {x y : G}
    (hx : x ∈ (Subgroup.zpowers y).topologicalClosure) :
    f x ∈ (Subgroup.zpowers (f y)).topologicalClosure := by
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hx ⊢
  have h2 : f '' (Subgroup.zpowers y : Set G) ⊆ (Subgroup.zpowers (f y) : Set G') := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow f y k).symm⟩
  exact closure_mono h2 (image_closure_subset_closure_image hf ⟨x, hx, rfl⟩)

/-- Conjugation as a topological group automorphism. -/
def conjCME (δ : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj δ
  continuous_toFun := by
    change Continuous fun x ↦ δ * x * δ⁻¹
    fun_prop
  continuous_invFun := by
    have : ((MulAut.conj δ).symm : G → G) = fun x ↦ δ⁻¹ * x * δ := by
      ext x
      simp
    change Continuous ((MulAut.conj δ).symm : G → G)
    rw [this]
    fun_prop

omit [IsTopologicalGroup G'] in
lemma conjSub_comap (δ : G) (B : Subgroup G') (E : G ≃ₜ* G') :
    conjSub δ (B.comap E.toMulEquiv.toMonoidHom) =
      B.comap ((conjCME δ⁻¹).trans E).toMulEquiv.toMonoidHom := by
  ext x
  rw [mem_conjSub_iff]
  change E (δ⁻¹ * x * δ) ∈ B ↔ E (δ⁻¹ * x * δ⁻¹⁻¹) ∈ B
  rw [inv_inv]

lemma comap_closure_zpowers (E : G ≃ₜ* G') (c : G') :
    ((Subgroup.zpowers c).topologicalClosure).comap E.toMulEquiv.toMonoidHom =
      (Subgroup.zpowers (E.symm c)).topologicalClosure := by
  ext x
  constructor
  · intro hx
    have := map_mem_closure_zpowers E.symm.toMulEquiv.toMonoidHom E.symm.continuous hx
    change E.symm (E x) ∈ _ at this
    rwa [ContinuousMulEquiv.symm_apply_apply] at this
  · intro hx
    have := map_mem_closure_zpowers E.toMulEquiv.toMonoidHom E.continuous hx
    change E x ∈ (Subgroup.zpowers (E (E.symm c))).topologicalClosure at this
    rwa [ContinuousMulEquiv.apply_symm_apply] at this

end Transport

section Surface

open Pi1.SurfaceGroup

variable {g r : ℕ}

/-- The cusp generator `cⱼ ∈ Π̂_{g,r}`. -/
noncomputable abbrev cuspGen (j : Fin r) : Pi1.ProfiniteSurfaceGroup g r :=
  etaFn (GrpCat.of (Pi1.SurfaceGroup g r)) (Pi1.SurfaceGroup.cusp j)

lemma cuspGen_mem_inertia (j : Fin r) : cuspGen (g := g) j ∈ inertia (g := g) j :=
  Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)

/-- A homomorphism to a finite group maps `cl⟨y⟩` into `⟨ψ y⟩`. -/
lemma liftFinite_mem_zpowers {P : Type} [Group P] [Finite P]
    (ρ : Pi1.SurfaceGroup g r →* P) {y z : Pi1.ProfiniteSurfaceGroup g r}
    (hz : z ∈ (Subgroup.zpowers y).topologicalClosure) :
    liftFinite ρ z ∈ Subgroup.zpowers (liftFinite ρ y) := by
  set M := (Subgroup.zpowers (liftFinite ρ y)).comap (liftFinite ρ)
  have hker : IsOpen ((liftFinite ρ).ker : Set (Pi1.ProfiniteSurfaceGroup g r)) :=
    isOpen_liftFinite_fiber ρ 1
  have hM : IsOpen (M : Set (Pi1.ProfiniteSurfaceGroup g r)) :=
    Subgroup.isOpen_mono (H₁ := (liftFinite ρ).ker) (H₂ := M) (fun x hx ↦ by
      change liftFinite ρ x ∈ Subgroup.zpowers (liftFinite ρ y)
      rw [MonoidHom.mem_ker.1 hx]
      exact (Subgroup.zpowers _).one_mem) hker
  have hle : Subgroup.zpowers y ≤ M := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers _
  exact Subgroup.topologicalClosure_minimal _ hle (Subgroup.isClosed_of_isOpen _ hM) hz

/-- **The generator of a cusp group of `Π̂_{g,r}` is not a `p`-th power in it.** -/
theorem not_mem_closure_zpowers_pow (hr : 1 < r ∨ 0 < g) (j : Fin r)
    {b : Pi1.ProfiniteSurfaceGroup g r}
    (hb : inertia (g := g) j = (Subgroup.zpowers b).topologicalClosure)
    {p : ℕ} (hp : p.Prime) : b ∉ (Subgroup.zpowers (b ^ p)).topologicalClosure := by
  intro hbp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨P, _, _, ρ, hρ⟩ := CurvesJacobian.Cusp.exists_finite_orderOf_cusp hr j p
  set ψ := liftFinite ρ
  have h1 : ψ (cuspGen j) ∈ Subgroup.zpowers (ψ b) :=
    liftFinite_mem_zpowers ρ (hb ▸ cuspGen_mem_inertia j)
  have hbI : b ∈ inertia (g := g) j := by
    rw [hb]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  have h2 : ψ b ∈ Subgroup.zpowers (ψ (cuspGen j)) := liftFinite_mem_zpowers ρ hbI
  have h3 : ψ b ∈ Subgroup.zpowers (ψ b ^ p) := by
    rw [← map_pow]
    exact liftFinite_mem_zpowers ρ hbp
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 h1
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 h2
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.1 h3
  have hψc : ψ (cuspGen j) = ρ (Pi1.SurfaceGroup.cusp j) := liftFinite_eta ρ _
  set q := ψ (cuspGen j)
  have key : q ^ (t * p * u * s - 1) = 1 := by
    have e : q = q ^ (t * p * u * s) := by
      calc q = ψ b ^ s := hs.symm
        _ = ((ψ b ^ p) ^ u) ^ s := by rw [hu]
        _ = (((q ^ t) ^ p) ^ u) ^ s := by rw [ht]
        _ = q ^ (t * p * u * s) := by
          rw [← zpow_natCast (q ^ t) p, ← zpow_mul, ← zpow_mul, ← zpow_mul]
          congr 1
          ring
    rw [zpow_sub_one, ← e, mul_inv_cancel]
  rw [← orderOf_dvd_iff_zpow_eq_one, hψc, hρ] at key
  have hd : (p : ℤ) ∣ 1 := by
    have : (p : ℤ) ∣ t * p * u * s := ⟨t * u * s, by ring⟩
    simpa using this.sub key
  have := Int.natCast_dvd_natCast.1 (by simpa using hd : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

end Surface
/-! ### Cusp groups transported from `Π̂_{g,r}` -/

section Cusps

open Pi1.SurfaceGroup

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {g r : ℕ}

/-- The preimages `Φ⁻¹(Iⱼ)` of the cusp groups of `Π̂_{g,r}`. -/
noncomputable abbrev surfInertia (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r) (j : Fin r) :
    Subgroup D :=
  (inertia (g := g) j).comap Φ.toMulEquiv.toMonoidHom

lemma exists_equiv_of_mem_conjFamily {Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r} {J : Subgroup D}
    (hJ : J ∈ conjFamily (surfInertia Φ)) :
    ∃ (j : Fin r) (E : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r),
      J = (inertia (g := g) j).comap E.toMulEquiv.toMonoidHom := by
  obtain ⟨j, δ, rfl⟩ := hJ
  exact ⟨j, _, conjSub_comap δ _ Φ⟩

variable {j : Fin r} {E : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r} {J : Subgroup D}

lemma eq_closure_of_eq_comap (hJ : J = (inertia (g := g) j).comap E.toMulEquiv.toMonoidHom) :
    J = (Subgroup.zpowers (E.symm (cuspGen j))).topologicalClosure := by
  rw [hJ]
  exact comap_closure_zpowers E _

lemma not_mem_closure_pow_of_eq_comap (hr : 1 < r ∨ 0 < g)
    (hJ : J = (inertia (g := g) j).comap E.toMulEquiv.toMonoidHom) {a : D}
    (ha : J = (Subgroup.zpowers a).topologicalClosure) {p : ℕ} (hp : p.Prime) :
    a ∉ (Subgroup.zpowers (a ^ p)).topologicalClosure := by
  intro hap
  have hb : inertia (g := g) j = (Subgroup.zpowers (E a)).topologicalClosure := by
    ext y
    constructor
    · intro hy
      have h1 : E.symm y ∈ J := by
        rw [hJ]
        change E (E.symm y) ∈ inertia (g := g) j
        rwa [ContinuousMulEquiv.apply_symm_apply]
      rw [ha] at h1
      have := map_mem_closure_zpowers E.toMulEquiv.toMonoidHom E.continuous h1
      change E (E.symm y) ∈ (Subgroup.zpowers (E a)).topologicalClosure at this
      rwa [ContinuousMulEquiv.apply_symm_apply] at this
    · intro hy
      have := map_mem_closure_zpowers E.symm.toMulEquiv.toMonoidHom E.symm.continuous hy
      change E.symm y ∈ (Subgroup.zpowers (E.symm (E a))).topologicalClosure at this
      rw [ContinuousMulEquiv.symm_apply_apply, ← ha, hJ] at this
      change E (E.symm y) ∈ inertia (g := g) j at this
      rwa [ContinuousMulEquiv.apply_symm_apply] at this
  have := map_mem_closure_zpowers E.toMulEquiv.toMonoidHom E.continuous hap
  change E a ∈ (Subgroup.zpowers (E (a ^ p))).topologicalClosure at this
  rw [map_pow] at this
  exact not_mem_closure_zpowers_pow hr j hb hp this

omit [TopologicalSpace D] [IsTopologicalGroup D] in
lemma mem_of_commute_of_eq_comap
    (hcent : ∀ x z : Pi1.ProfiniteSurfaceGroup g r, x ∈ inertia (g := g) j → x ≠ 1 →
      z * x = x * z → z ∈ inertia (g := g) j)
    {E : D ≃* Pi1.ProfiniteSurfaceGroup g r}
    (hJ : J = (inertia (g := g) j).comap E.toMonoidHom) {x : D} (hx : x ∈ J) (hx1 : x ≠ 1)
    {z : D} (hz : z * x = x * z) : z ∈ J := by
  rw [hJ] at hx ⊢
  refine hcent (E x) (E z) hx (fun h ↦ hx1 (E.injective (h.trans (map_one E).symm))) ?_
  rw [← map_mul, ← map_mul, hz]

/-- `Π_{g,r}` is finitely generated. -/
lemma fg_surfaceGroup : Group.FG (Pi1.SurfaceGroup g r) := by
  haveI : Finite (Pi1.SurfaceGen g r) :=
    Finite.of_equiv _ (CurvesJacobian.Cusp.surfaceGenEquiv g r).symm
  exact Group.fg_of_surjective (PresentedGroup.mk_surjective _)

/-- **Finitely many continuous `ℤ/p`-characters** on an open subgroup of finite index of a group
with a dense finitely generated subgroup. -/
theorem finite_charSpace_of_denseRange {G : Type*} [Group G] [Group.FG G] (ψ : G →* D)
    (hψ : DenseRange ψ) (p : ℕ) [NeZero p] (H : OpenSubgroup D)
    (hH : (H : Subgroup D).index ≠ 0) : Finite (charSpace p H) := by
  set G₀ := (H : Subgroup D).comap ψ
  haveI : (H : Subgroup D).FiniteIndex := ⟨hH⟩
  haveI := Subgroup.isFiniteRelIndex_of_finiteIndex (H := (H : Subgroup D)) (K := ψ.range)
  haveI : G₀.FiniteIndex := ⟨by rw [Subgroup.index_comap]; exact Subgroup.relIndex_ne_zero⟩
  haveI : Group.FG G₀ := Subgroup.fg_of_index_ne_zero G₀
  obtain ⟨s, hs⟩ := (Group.fg_def.1 ‹Group.FG G₀›)
  let f : charSpace p H → (s → ZMod p) := fun ξ x ↦ ξ.1 (Additive.ofMul ⟨ψ x.1.1, x.1.2⟩)
  refine Finite.of_injective f fun ξ η hξη ↦ ?_
  set ζ := ξ - η
  have hζs : ∀ x ∈ (s : Set G₀), ψ x.1 ∈ kerSub (H : Subgroup D) ζ.1 := fun x hx ↦ by
    refine ⟨x.2, ?_⟩
    have := congrFun hξη ⟨x, hx⟩
    change ξ.1 _ = η.1 _ at this
    change (ξ.1 - η.1) _ = 0
    rw [AddMonoidHom.sub_apply, this, sub_self]
  have hG₀ : ∀ x : G₀, ψ x.1 ∈ kerSub (H : Subgroup D) ζ.1 := by
    have hle : Subgroup.closure (s : Set G₀) ≤
        (kerSub (H : Subgroup D) ζ.1).comap (ψ.comp G₀.subtype) := (Subgroup.closure_le _).2 hζs
    rw [hs] at hle
    exact fun x ↦ hle (Subgroup.mem_top x)
  have hopen : IsOpen (kerSub (H : Subgroup D) ζ.1 : Set D) := ζ.2
  have hcl : IsClosed (kerSub (H : Subgroup D) ζ.1 : Set D) := Subgroup.isClosed_of_isOpen _ hopen
  have hHle : ∀ h ∈ (H : Subgroup D), h ∈ kerSub (H : Subgroup D) ζ.1 := by
    intro h hh
    by_contra hk
    have hU : IsOpen ((H : Set D) ∩ (kerSub (H : Subgroup D) ζ.1 : Set D)ᶜ) :=
      H.isOpen.inter hcl.isOpen_compl
    obtain ⟨x, hx⟩ := hψ.exists_mem_open hU ⟨h, hh, hk⟩
    exact hx.2 (hG₀ ⟨x, hx.1⟩)
  have hζ : ζ = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun a ↦ ?_)
    obtain ⟨_, h0⟩ := hHle _ (Additive.toMul a).2
    exact h0
  exact sub_eq_zero.1 hζ

/-- The dense subgroup `Π_{g,r} → Π̂_{g,r} ≃ D`. -/
noncomputable def surfDense (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r) :
    Pi1.SurfaceGroup g r →* D :=
  Φ.symm.toMulEquiv.toMonoidHom.comp (eta (GrpCat.of (Pi1.SurfaceGroup g r))).hom

omit [IsTopologicalGroup D] in
lemma denseRange_surfDense (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r) :
    DenseRange (surfDense Φ) :=
  Φ.symm.surjective.denseRange.comp (denseRange _) Φ.symm.continuous

theorem finite_charSpace_of_equiv [CompactSpace D] (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r)
    (p : ℕ) [NeZero p] (H : OpenSubgroup D) : Finite (charSpace p H) := by
  haveI := fg_surfaceGroup (g := g) (r := r)
  haveI : Finite (D ⧸ (H : Subgroup D)) := Subgroup.quotient_finite_of_isOpen _ H.isOpen
  exact finite_charSpace_of_denseRange _ (denseRange_surfDense Φ) p H
    Subgroup.index_ne_zero_of_finite

/-- **Few cusps relative to the index** (the input `hfam` of
`CurvesJacobian.CuspChar.isNumCusp_of_cuspWeightIdentity`): for every `m` there is an open
normal `H` in which every cusp generator has order `≥ m` modulo `H`, so that there are at most
`r [D : H] / m` cusps of `H`. -/
theorem exists_cuspCount_mul_le [CompactSpace D] (Φ : D ≃ₜ* Pi1.ProfiniteSurfaceGroup g r)
    (hr : 1 < r ∨ 0 < g) {S : Set (Subgroup D)} (hS : S ⊆ conjFamily (surfInertia Φ)) :
    ∃ C, ∀ m : ℕ, ∃ H : OpenSubgroup D,
      cuspCount S (H : Subgroup D) * m ≤ C * (H : Subgroup D).index := by
  refine ⟨r, fun m ↦ ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨⊤, by simp⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  choose P _ _ ρ hρ using fun j : Fin r ↦ CurvesJacobian.Cusp.exists_finite_orderOf_cusp hr j m
  let ρ' : Pi1.SurfaceGroup g r →* ((j : Fin r) → P j) := MonoidHom.pi ρ
  let φ : D →* ((j : Fin r) → P j) := (liftFinite ρ').comp Φ.toMulEquiv.toMonoidHom
  have hopen : IsOpen (φ.ker : Set D) := (isOpen_liftFinite_fiber ρ' 1).preimage Φ.continuous
  let H : OpenSubgroup D := ⟨φ.ker, hopen⟩
  refine ⟨H, ?_⟩
  set K : Fin r → Subgroup D := fun j ↦ ((surfInertia Φ j).map φ).comap φ
  have hK : ∀ j (δ k : D), k ∈ K j →
      ∃ h ∈ (H : Subgroup D), ∃ a ∈ surfInertia Φ j, δ * k = h * δ * a := by
    rintro j δ k ⟨a, ha, hak⟩
    refine ⟨δ * k * a⁻¹ * δ⁻¹, ?_, a, ha, by group⟩
    change φ (δ * k * a⁻¹ * δ⁻¹) = 1
    simp only [map_mul, map_inv, hak, mul_inv_cancel_right, mul_inv_cancel]
  have hHK : ∀ j, (H : Subgroup D) ≤ K j := fun j x hx ↦
    ⟨1, (surfInertia Φ j).one_mem, by rw [map_one]; exact (MonoidHom.mem_ker.1 hx).symm⟩
  haveI : ∀ j, Finite (D ⧸ K j) := fun j ↦
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (hHK j) H.isOpen)
  have hle := cuspCount_le_sum (surfInertia Φ) hS H K hK
  have hidx : ∀ j, (K j).index * m ≤ (H : Subgroup D).index := fun j ↦ by
    refine index_comap_map_mul_le φ (surfInertia Φ j) (x := Φ.symm (cuspGen j)) ?_ ?_
    · change Φ (Φ.symm (cuspGen j)) ∈ inertia (g := g) j
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact cuspGen_mem_inertia j
    · have e : φ (Φ.symm (cuspGen j)) = ρ' (Pi1.SurfaceGroup.cusp j) := by
        change liftFinite ρ' (Φ (Φ.symm _)) = _
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact liftFinite_eta ρ' _
      rw [e, ← hρ j]
      exact orderOf_map_dvd (Pi.evalMonoidHom P j) (ρ' _)
  calc cuspCount S H * m ≤ (∑ j, (K j).index) * m := Nat.mul_le_mul_right _ hle
    _ = ∑ j, (K j).index * m := Finset.sum_mul _ _ _
    _ ≤ ∑ _j : Fin r, (H : Subgroup D).index := Finset.sum_le_sum fun j _ ↦ hidx j
    _ = r * (H : Subgroup D).index := by simp

end Cusps
/-! ### Characters of the whole group -/

section Top

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]

/-- The continuous `ℤ/p`-characters of `⊤` are the homomorphisms `D → ℤ/p` with open kernel. -/
noncomputable def charSpaceTopEquiv (p : ℕ) :
    charSpace p (⊤ : OpenSubgroup D) ≃
      {φ : D →* Multiplicative (ZMod p) // IsOpen (φ.ker : Set D)} where
  toFun ξ := ⟨{ toFun := fun x ↦
                  Multiplicative.ofAdd (ξ.1 (Additive.ofMul ⟨x, OpenSubgroup.mem_top x⟩))
                map_one' := by
                  change Multiplicative.ofAdd (ξ.1 (Additive.ofMul 1)) = 1
                  simp
                map_mul' := fun x y ↦ by
                  change Multiplicative.ofAdd (ξ.1 (Additive.ofMul ⟨x, OpenSubgroup.mem_top x⟩ +
                    Additive.ofMul ⟨y, OpenSubgroup.mem_top y⟩)) = _
                  rw [map_add, ofAdd_add] }, by
      have h : IsOpen (kerSub ((⊤ : OpenSubgroup D) : Subgroup D) ξ.1 : Set D) := ξ.2
      convert h using 1
      ext x
      exact ⟨fun hx ↦ ⟨OpenSubgroup.mem_top x, ofAdd_eq_one.1 hx⟩,
        fun ⟨_, hx⟩ ↦ ofAdd_eq_one.2 hx⟩⟩
  invFun φ := ⟨{ toFun := fun a ↦ Multiplicative.toAdd (φ.1 (Additive.toMul a).1)
                 map_zero' := by simp
                 map_add' := fun a b ↦ by simp }, by
      change IsOpen ((kerSub ((⊤ : OpenSubgroup D) : Subgroup D) _ : Subgroup D) : Set D)
      convert φ.2 using 1
      ext x
      exact ⟨fun ⟨_, hx⟩ ↦ toAdd_eq_zero.1 hx,
        fun hx ↦ ⟨OpenSubgroup.mem_top x, toAdd_eq_zero.2 hx⟩⟩⟩
  left_inv ξ := rfl
  right_inv φ := rfl

lemma card_charSpace_top (p : ℕ) :
    Nat.card (charSpace p (⊤ : OpenSubgroup D)) =
      Nat.card {φ : D →* Multiplicative (ZMod p) // IsOpen (φ.ker : Set D)} :=
  Nat.card_congr (charSpaceTopEquiv p)

end Top
/-! ### The cusp groups of `Δ_U` -/

section Arith

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian CurvesJacobian.Cusp
  Pi1.SurfaceGroup
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `Δ_U = ker(Π_U ↠ G_K)`. -/
noncomputable abbrev deltaU : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (projGk Ω C hc).toMonoidHom.ker

instance compactSpace_deltaU : CompactSpace (deltaU Ω C hc) :=
  isCompact_iff_compactSpace.mp
    ((isClosed_singleton.preimage (projGk Ω C hc).continuous :
      IsClosed ((projGk Ω C hc : _ → _) ⁻¹' {1}))).isCompact

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `(T1)` `Δ_U` is Hausdorff. -/
lemma t2Space_deltaU : T2Space (deltaU Ω C hc) := inferInstance

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `(T1)` `Δ_U` is totally disconnected. -/
lemma totallyDisconnectedSpace_deltaU : TotallyDisconnectedSpace (deltaU Ω C hc) := inferInstance

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `(T1)` `Δ_U` is normal in `Π_U`. -/
lemma normal_deltaU : (deltaU Ω C hc).Normal := inferInstance

/-- **The cusp groups of `Δ_U`**: the cuspidal inertia groups of `Π_U`, viewed in `Δ_U`. -/
def deltaCusps : Set (Subgroup (deltaU Ω C hc)) :=
  {J | J.map (deltaU Ω C hc).subtype ∈ arithCusps Ω C hc}

/-- The bridge between `arithCusps` and `deltaCusps`. -/
theorem mem_arithCusps_iff_mem_deltaCusps
    {I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hI : I ≤ deltaU Ω C hc) :
    I ∈ arithCusps Ω C hc ↔ I.subgroupOf (deltaU Ω C hc) ∈ deltaCusps Ω C hc := by
  change _ ↔ (I.subgroupOf (deltaU Ω C hc)).map (deltaU Ω C hc).subtype ∈ arithCusps Ω C hc
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hI]

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma map_conjSub_deltaU (J : Subgroup (deltaU Ω C hc)) (δ : deltaU Ω C hc) :
    (conjSub δ J).map (deltaU Ω C hc).subtype =
      conjSub (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
        (J.map (deltaU Ω C hc).subtype) := by
  simp only [conjSub, Subgroup.map_map]
  congr 1

/-- `(T4)` The cusp groups of `Δ_U` are stable under conjugation. -/
theorem conjStable_deltaCusps : ConjStable (deltaCusps Ω C hc) := by
  intro J hJ δ
  change (conjSub δ J).map (deltaU Ω C hc).subtype ∈ arithCusps Ω C hc
  rw [map_conjSub_deltaU]
  exact map_conj_mem_arithCusps Ω C hc hJ _

/-- `(T4)` The cusp groups of `Δ_U` are self-normalising in `Δ_U`. -/
theorem mem_of_conjSub_eq_deltaCusps {J : Subgroup (deltaU Ω C hc)} (hJ : J ∈ deltaCusps Ω C hc)
    {δ : deltaU Ω C hc} (h : conjSub δ J = J) : δ ∈ J := by
  set I := J.map (deltaU Ω C hc).subtype
  have hI : conjSub (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) I = I := by
    rw [← map_conjSub_deltaU, h]
  have hconj : ConjAct.toConjAct
      (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) • I = I := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    have := mem_conjSub_iff (g := (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))))
      (x := x) (I := I)
    rw [hI] at this
    exact this.symm
  have hcomm : (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
      Subgroup.Commensurable.commensurator I := by
    rw [Subgroup.Commensurable.commensurator_mem_iff, hconj]
  have hJ' : I ∈ arithCusps Ω C hc := hJ
  have hmem : (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈ I := by
    rw [← commensurator_inf_of_mem_arithCusps Ω C hc hJ']
    exact ⟨hcomm, δ.2⟩
  obtain ⟨y, hy, hyδ⟩ := hmem
  rwa [← Subtype.ext hyδ]

/-- The genus `g` of `X̄_Ω`. -/
noncomputable abbrev genusU : ℕ := (curveGenus Ω (geomCurve Ω C)).toNat

/-- The number `r` of cusps of `U_Ω`. -/
noncomputable abbrev cuspsU : ℕ :=
  Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))

/-- The Euler characteristic `χ₀ = 2g - 2 + r` of `U_Ω` (as a natural number). -/
noncomputable abbrev eulerU : ℕ := 2 * genusU Ω C + cuspsU Ω C - 2

omit [Algebra.IsAlgebraic K Ω] in
lemma isHyperbolic_genusU : IsHyperbolic (genusU Ω C) (cuspsU Ω C) :=
  isHyperbolic_baseChange Ω C

omit [CharZero K] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
include hc in
lemma cuspsU_pos : 0 < cuspsU Ω C :=
  haveI := (compl_finite_baseChangeOpen K Ω C.nonempty).to_subtype
  Nat.card_pos_iff.2 ⟨(compl_nonempty_baseChangeOpen K Ω hc).to_subtype, inferInstance⟩

omit [Algebra.IsAlgebraic K Ω] in
include hc in
lemma one_lt_cuspsU_or : 1 < cuspsU Ω C ∨ 0 < genusU Ω C := by
  have h := isHyperbolic_genusU Ω C
  have h0 := cuspsU_pos Ω C hc
  unfold IsHyperbolic at h
  omega

omit [Algebra.IsAlgebraic K Ω] in
/-- `(T2)` `0 < χ₀`. -/
theorem eulerU_pos : 0 < eulerU Ω C := by
  unfold eulerU
  have h := isHyperbolic_genusU Ω C
  unfold IsHyperbolic at h
  omega

/-- `(T2)` **`Δ_U` has `2 ^ (χ₀ + 1)` continuous `ℤ/2`-characters** (`Δ_U ≅ Π̂_{g,r}` is free
profinite of rank `2g + r - 1 = χ₀ + 1`). -/
theorem card_charSpace_two_deltaU :
    Nat.card (charSpace 2 (⊤ : OpenSubgroup (deltaU Ω C hc))) = 2 ^ (eulerU Ω C + 1) := by
  rw [card_charSpace_top]
  change numChar2 _ = _
  obtain ⟨e⟩ := nonempty_kerProjGk_equiv Ω C hc
  rw [numChar2_congr e]
  have hhyp := isHyperbolic_genusU Ω C
  have hr0 := cuspsU_pos Ω C hc
  unfold IsHyperbolic at hhyp
  change numChar2 (completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (genusU Ω C)
    (cuspsU Ω C))))) = 2 ^ (2 * genusU Ω C + cuspsU Ω C - 2 + 1)
  generalize genusU Ω C = g at hhyp ⊢
  generalize cuspsU Ω C = n at hhyp hr0 ⊢
  obtain ⟨r', rfl⟩ : ∃ r', n = r' + 1 := ⟨n - 1, by omega⟩
  rw [numChar2_surfaceCompletion]
  congr 1
  omega

/-- Every cuspidal inertia group of `Π_U` is the image of one of `π₁ᵉᵗ(U_Ω)` (no conjugation
needed). -/
lemma exists_geomCusps_of_mem_arithCusps
    {I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hI : I ∈ arithCusps Ω C hc) : ∃ I₀ ∈ geomCusps Ω C, I = I₀.map (geomToPi Ω C hc) := by
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω C hc).1 hI
  exact ⟨_, ⟨W, hW.1, fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2, rfl⟩,
    (map_geomCuspInertia Ω C hc hW.1).symm⟩

/-- `Δ_U ≃ₜ* π₁ᵉᵗ(U_Ω, generic point)`. -/
noncomputable def deltaGeomEquiv : deltaU Ω C hc ≃ₜ*
    π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)) :=
  (kerProjGkEquivGeom Ω C hc).trans (basePointEquiv Ω C hc).symm

lemma geomToPi_eq_deltaGeomEquiv (γ) :
    geomToPi Ω C hc γ = ((deltaGeomEquiv Ω C hc).symm γ :
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) := rfl

/-- **`Δ_U ≃ₜ* Π̂_{g,r}` with every cusp group of `Δ_U` a `Δ_U`-conjugate of the preimage of
some `Iⱼ`.** -/
theorem exists_equiv_deltaCusps_subset :
    ∃ Φ : deltaU Ω C hc ≃ₜ* Pi1.ProfiniteSurfaceGroup (genusU Ω C) (cuspsU Ω C),
      deltaCusps Ω C hc ⊆ conjFamily (surfInertia Φ) := by
  obtain ⟨Θ, hΘ⟩ := exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed (geomData Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (geomOpen Ω C)
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
  set Ψ := deltaGeomEquiv Ω C hc
  refine ⟨Ψ.trans Θ, fun J hJ ↦ ?_⟩
  obtain ⟨I₀, ⟨W, hkW, hWU, rfl⟩, hI⟩ := exists_geomCusps_of_mem_arithCusps Ω C hc hJ
  obtain ⟨j, σ, hj⟩ := hΘ W hkW hWU
  have hmem : ∀ x : deltaU Ω C hc, x ∈ J ↔ Ψ x ∈ cuspInertia (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
      (geomOpen Ω C) W := by
    intro x
    constructor
    · intro hx
      have h1 : (x : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
          J.map (deltaU Ω C hc).subtype := ⟨x, hx, rfl⟩
      rw [hI] at h1
      obtain ⟨γ, hγ, hγx⟩ := h1
      rw [geomToPi_eq_deltaGeomEquiv] at hγx
      rw [← Subtype.ext hγx, ContinuousMulEquiv.apply_symm_apply]
      exact hγ
    · intro hx
      have h1 : (x : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
          J.map (deltaU Ω C hc).subtype := by
        rw [hI]
        exact ⟨Ψ x, hx, by rw [geomToPi_eq_deltaGeomEquiv, ContinuousMulEquiv.symm_apply_apply]⟩
      obtain ⟨y, hy, hyx⟩ := h1
      rwa [← Subtype.ext hyx]
  refine ⟨j, Ψ.symm σ⁻¹, ?_⟩
  ext x
  rw [mem_conjSub_iff, hmem]
  change _ ↔ Θ (Ψ ((Ψ.symm σ⁻¹)⁻¹ * x * Ψ.symm σ⁻¹)) ∈ inertia (g := genusU Ω C) j
  rw [← hj]
  simp only [map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply, inv_inv]
  constructor
  · intro h
    refine ⟨Ψ x, h, ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨γ, hγ, e⟩
    simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv, mul_left_inj, mul_right_inj] at e
    have e3 : γ = Ψ x := Θ.injective e
    rwa [← e3]

/-- `(T3)` **Few cusps relative to the index** for `Δ_U` (the input `hfam`). -/
theorem exists_cuspCount_mul_le_deltaU :
    ∃ C₀, ∀ m : ℕ, ∃ H : OpenSubgroup (deltaU Ω C hc),
      cuspCount (deltaCusps Ω C hc) (H : Subgroup (deltaU Ω C hc)) * m ≤
        C₀ * (H : Subgroup (deltaU Ω C hc)).index := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_deltaCusps_subset Ω C hc
  exact exists_cuspCount_mul_le Φ (one_lt_cuspsU_or Ω C hc) hΦ

/-- `(T4)` **The cusp groups of `Δ_U` form a cusp set**, given the centraliser property of the
cuspidal inertia groups of `Π̂_{g,r}` (an explicit hypothesis, proved separately). -/
theorem isCuspSet_deltaCusps
    (hcent : ∀ (g r : ℕ), 0 < r → Pi1.SurfaceGroup.IsHyperbolic g r → ∀ (j : Fin r)
      (x z : Pi1.ProfiniteSurfaceGroup g r), x ∈ Pi1.SurfaceGroup.inertia (g := g) j → x ≠ 1 →
        z * x = x * z → z ∈ Pi1.SurfaceGroup.inertia (g := g) j) :
    IsCuspSet (deltaCusps Ω C hc) := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_deltaCusps_subset Ω C hc
  have hr := one_lt_cuspsU_or Ω C hc
  refine ⟨conjStable_deltaCusps Ω C hc, fun I hI δ h ↦ mem_of_conjSub_eq_deltaCusps Ω C hc hI h,
    fun I hI ↦ ?_, fun I hI a ha p hp ↦ ?_, fun I hI x hx hx1 z hz ↦ ?_, fun H ↦ ?_,
    fun p hp H ↦ ?_⟩
  · obtain ⟨j, E, hE⟩ := exists_equiv_of_mem_conjFamily (hΦ hI)
    exact ⟨_, eq_closure_of_eq_comap hE⟩
  · obtain ⟨j, E, hE⟩ := exists_equiv_of_mem_conjFamily (hΦ hI)
    exact not_mem_closure_pow_of_eq_comap hr hE ha hp
  · obtain ⟨j, E, hE⟩ := exists_equiv_of_mem_conjFamily (hΦ hI)
    exact mem_of_commute_of_eq_comap (hcent _ _ (cuspsU_pos Ω C hc) (isHyperbolic_genusU Ω C) j)
      (E := E.toMulEquiv) hE hx hx1 hz
  · haveI : Finite (deltaU Ω C hc ⧸ (H : Subgroup (deltaU Ω C hc))) :=
      Subgroup.quotient_finite_of_isOpen _ H.isOpen
    exact finite_cuspQuot_of_subset _ hΦ _
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    exact finite_charSpace_of_equiv Φ p H

end Arith

section Final

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian CurvesJacobian.Cusp
  Pi1.SurfaceGroup

universe u

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopI] Lemma 4.5 (v) for affine hyperbolic curves over number fields**, from the cusp
weight identities: an isomorphism `Π_U ≃ₜ* Π_{U'}` mapping `Δ_U` onto `Δ_{U'}` maps the cusp
groups of `Δ_U` exactly onto those of `Δ_{U'}`. The centraliser property of the cusp groups of
`Π̂_{g,r}` (`hcent`) and the cusp weight identities (`hW`, `hW'`, `hinf`) are explicit inputs. -/
theorem mem_deltaCusps_iff_of_cuspWeightIdentity
    {K : Type u} [Field K] [CharZero K] {Ω : Type u} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
    {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
    {K' : Type u} [Field K'] [CharZero K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
    [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
    {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
    (hcent : ∀ (g r : ℕ), 0 < r → Pi1.SurfaceGroup.IsHyperbolic g r → ∀ (j : Fin r)
      (x z : Pi1.ProfiniteSurfaceGroup g r), x ∈ Pi1.SurfaceGroup.inertia (g := g) j → x ≠ 1 →
        z * x = x * z → z ∈ Pi1.SurfaceGroup.inertia (g := g) j)
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc') {l : ℕ}
    {χ : ∀ k : ℕ, π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →*
      (ZMod (l ^ k))ˣ}
    {χ' : ∀ k : ℕ, π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)) →*
      (ZMod (l ^ k))ˣ}
    (hW : CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) l (eulerU Ω C) χ)
    (hW' : CuspWeightIdentity (deltaU Ω' C' hc') (deltaCusps Ω' C' hc') l (eulerU Ω' C') χ')
    (hinf : ∀ A B : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      IsOpen (A : Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) →
      IsOpen (B : Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) →
      ∀ N : ℕ, (∀ σ ∈ A ⊓ B, ∀ k, χ k σ ^ N = 1) → N = 0)
    (I : Subgroup (deltaU Ω C hc)) :
    I ∈ deltaCusps Ω C hc ↔ I.map (resD Φ hD).toMulEquiv.toMonoidHom ∈ deltaCusps Ω' C' hc' :=
  mem_iff_map_mem_of_cuspWeightIdentity Φ hD (isCuspSet_deltaCusps Ω C hc hcent)
    (isCuspSet_deltaCusps Ω' C' hc' hcent) hW hW' hinf (eulerU_pos Ω C)
    (card_charSpace_two_deltaU Ω C hc) (card_charSpace_two_deltaU Ω' C' hc')
    (exists_cuspCount_mul_le_deltaU Ω C hc) (exists_cuspCount_mul_le_deltaU Ω' C' hc') I

end Final

end CurvesJacobian.CuspChar
