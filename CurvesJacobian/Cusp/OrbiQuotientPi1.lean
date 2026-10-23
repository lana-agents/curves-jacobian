/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbifold.EtaleGalois

/-!
# `π₁` of a quotient orbifold as an extension (MR8, bridge for [AbsTopII] Cor. 3.3)

Let `D : GaloisData k t` (`H_L ≤ H ≤ Gal(Ω / k(t))`, `L = Ω^{H_L}`, `R` the integral closure of
`k[t]` in `L`, `A = H ⧸ H_L` acting on `R`, `S ⊆ H_L` the inertia elements). We compare the
fundamental group `etalePi1 R A Ω ≅ H ⧸ ⟨⟨S⟩⟩` of the orbifold `[Spec R / A]` with
`π₁ᵉᵗ(Spec R) ≅ H_L ⧸ ⟨⟨S⟩⟩`:

* `CurvesJacobian.Cusp.galoisDataHL D`: the Galois data with `H := H_L` (same `H_L`, so the same
  `L`, `R` and `S`: `galoisDataHL_S`);
* `CurvesJacobian.Cusp.conj_mem_S`: `S` is stable under conjugation by `H` (an element `h ∈ H`
  maps the inertia group of `W` to that of `h(W)`); hence the closed normal closures of `S` in `H`
  and in `H_L` agree (`ambientKernel_HL_eq`);
* `CurvesJacobian.Cusp.orbiIncl D : H_L ⧸ ⟨⟨S⟩⟩ →ₜ* H ⧸ ⟨⟨S⟩⟩`, an open embedding
  (`isOpenEmbedding_orbiIncl`) with normal image (`range_orbiIncl_normal`) of index `[H : H_L]`
  (`index_range_orbiIncl`) and quotient `A` (`orbiQuotEquiv`, via `orbiProj`, `ker_orbiProj`);
  for `H = Gal(Ω / k(t))` (e.g. `galoisDataTop`) the index is `[L : k(t)]`
  (`index_range_orbiIncl_of_H_eq_top`);
* `CurvesJacobian.Cusp.orbiEmb D : π₁ᵉᵗ(Spec R) →ₜ* etalePi1 R A Ω`, an open embedding
  (`isOpenEmbedding_orbiEmb`), mapping the intrinsic Galois action of `σ ∈ H_L` on the fibres of
  `Spec R` to the action of `σ` on the fibres of `A`-equivariant covers (`orbiEmb_galoisHom`);
* the restriction to the constants `galResConst : Gal(Ω / k(t)) →* Gal(k̄ / k)` (`k̄` the
  algebraic closure of `k` in `Ω`), continuous (`continuous_galResConst`) and trivial on inertia
  groups of places containing `k` (`galResConst_eq_one_of_mem_inertia`), hence the projections
  `piConst H S : H ⧸ ⟨⟨S⟩⟩ →* Gal(k̄ / k)`, compatible with `orbiIncl`
  (`piConst_comp_orbiIncl`), with `Δ_C ∩ range ι = ι(Δ_X)` (`ker_piConst_inf_range_orbiIncl`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Orbifold AffOrbicurve
open Topology

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

section GroupTheory

/-- `ker f ⊓ range g = g(ker (f ∘ g))`. -/
lemma ker_inf_range_eq_map₂ {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) : f.ker ⊓ g.range = (f.comp g).ker.map g := by
  ext y
  constructor
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x, rfl⟩

end GroupTheory

section Valuation

/-- Valuations `< 1` under `comap` along a ring automorphism. -/
lemma valuation_comap_lt_one_iff₂ (W : ValuationSubring Ω) (f : Ω ≃+* Ω) (x : Ω) :
    (W.comap f.toRingHom).valuation x < 1 ↔ W.valuation (f x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  simp

/-- An element of `Ω` integral over `k` lies in every valuation subring containing `k`. -/
lemma mem_valuationSubring_of_isIntegral₂ (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {a : Ω} (ha : IsIntegral k a) : a ∈ W := by
  letI : Algebra k W := ((algebraMap k Ω).codRestrict W.toSubring hk).toAlgebra
  haveI : IsScalarTower k W Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hW : IsIntegral W a := ha.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := Ω)).1 hW
  rw [← hy]
  exact y.2

end Valuation

section Constants

variable (k Ω) in
/-- The algebraic closure `k̄` of `k` in `Ω`. -/
abbrev ConstField₂ : IntermediateField k Ω := algebraicClosure k Ω

variable (t) in
/-- **Restriction to the constants**: `Gal(Ω / k(t)) → Gal(k̄ / k)`, `k̄` the algebraic closure of
`k` in `Ω`. -/
def galResConst : (Ω ≃ₐ[K₀ k t] Ω) →* (ConstField₂ k Ω ≃ₐ[k] ConstField₂ k Ω) where
  toFun σ := AlgEquiv.algebraicClosure (σ.restrictScalars k)
  map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => Subtype.ext rfl

@[simp] lemma galResConst_apply (σ : Ω ≃ₐ[K₀ k t] Ω) (x : ConstField₂ k Ω) :
    ((galResConst t σ x : ConstField₂ k Ω) : Ω) = σ x := rfl

/-- **Inertia acts trivially on the constants**: an element of the inertia group of a valuation
subring `W ⊇ k` of `Ω` restricts to the identity of `k̄`. -/
theorem galResConst_eq_one_of_mem_inertia (W : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.inertia W) : galResConst t σ = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  change σ (x : Ω) = x
  have hxW : (x : Ω) ∈ W :=
    mem_valuationSubring_of_isIntegral₂ W hk (mem_algebraicClosure_iff'.1 x.2)
  have hlt : W.valuation (σ x - x) < 1 := hσ _ hxW
  by_contra hne
  have hσx : σ (x : Ω) ∈ ConstField₂ k Ω :=
    (map_mem_algebraicClosure_iff ((σ.restrictScalars k).toAlgHom)).2 x.2
  have hc : σ (x : Ω) - x ∈ ConstField₂ k Ω := sub_mem hσx x.2
  have hcinv : (σ (x : Ω) - x)⁻¹ ∈ W :=
    mem_valuationSubring_of_isIntegral₂ W hk
      (mem_algebraicClosure_iff'.1 ((ConstField₂ k Ω).inv_mem hc))
  have hn := (W.mem_nonunits_iff_or).1 ((W.mem_nonunits_iff).2 hlt)
  rcases hn with h0 | hinv
  · exact hne (sub_eq_zero.1 h0)
  · exact hinv hcinv

variable (t) in
/-- The restriction to the constants is continuous for the Krull topologies. -/
theorem continuous_galResConst : Continuous (galResConst (k := k) t) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 hs
  have hfg : E.toSubalgebra.FG := Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.1 hE)
  obtain ⟨T, hTfin, hT⟩ := IntermediateField.fg_def.1 (E.fg_of_fg_toSubalgebra hfg)
  let T' : Set Ω := Subtype.val '' T
  haveI : Finite T' := (hTfin.image _).to_subtype
  have hint : ∀ x ∈ T', IsIntegral (K₀ k t) x := by
    rintro _ ⟨y, -, rfl⟩
    exact (mem_algebraicClosure_iff'.1 y.2).tower_top
  haveI := IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin (K₀ k t) T', inferInstance, fun σ hσ => hEs ?_⟩
  have hσ' : σ ∈ (IntermediateField.adjoin (K₀ k t) T').fixingSubgroup := hσ
  change galResConst t σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ' ⊢
  intro x hx
  rw [← hT] at hx
  have key := (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := k) (S := T)
    (galResConst t σ)).2 (fun y hy => Subtype.ext
      (hσ' _ (IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩))) x hx
  exact key

end Constants

variable (D : GaloisData k t)

section Restrict

/-- **The Galois data of `Spec R`**: `H := H_L`, same `H_L` (hence the same `L`, `R`, `S`). -/
def galoisDataHL : GaloisData k t where
  H := D.HL
  HL := D.HL
  le := le_rfl
  isOpen_HL := D.isOpen_HL
  conj_mem := fun _ hh _ hn => D.HL.mul_mem (D.HL.mul_mem hh hn) (D.HL.inv_mem hh)
  transcendental := D.transcendental

lemma galoisDataHL_H : (galoisDataHL D).H = D.HL := rfl

lemma galoisDataHL_HL : (galoisDataHL D).HL = D.HL := rfl

lemma galoisDataHL_L : (galoisDataHL D).L = D.L := rfl

/-- The inertia elements of `galoisDataHL D` are those of `D`. -/
lemma galoisDataHL_S : (galoisDataHL D).S = D.S := rfl

lemma galoisDataHL_H_le : (galoisDataHL D).H ≤ (galoisDataHL D).HL := le_rfl

/-- The Galois data with `H := Gal(Ω / k(t))` and the same `H_L`, for `H_L` normal (e.g. `L / k(t)`
Galois): the orbifold `[Spec R / Gal(L / k(t))]`. -/
def galoisDataTop (hn : D.HL.Normal) : GaloisData k t where
  H := ⊤
  HL := D.HL
  le := le_top
  isOpen_HL := D.isOpen_HL
  conj_mem := fun _ _ _ hn' => hn.conj_mem _ hn' _
  transcendental := D.transcendental

lemma galoisDataTop_H (hn : D.HL.Normal) : (galoisDataTop D hn).H = ⊤ := rfl

lemma galoisDataTop_S (hn : D.HL.Normal) : (galoisDataTop D hn).S = D.S := rfl

/-- **The inertia elements are stable under conjugation by `H`**: `h ∈ H` maps the inertia group
of `W` to that of `h(W)`, and fixes `k` and `t`. -/
theorem conj_mem_S {h : Ω ≃ₐ[K₀ k t] Ω} (hh : h ∈ D.H) {s : Ω ≃ₐ[K₀ k t] Ω} (hs : s ∈ D.S) :
    h * s * h⁻¹ ∈ D.S := by
  obtain ⟨hsL, W, hk, ht, hI⟩ := hs
  refine ⟨D.conj_mem h hh s hsL, W.comap (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv.toRingHom,
    fun c => ?_, ?_, fun a ha => ?_⟩
  · rw [ValuationSubring.mem_comap]
    have hc : (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) = algebraMap k Ω c :=
      (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω).commutes ⟨_, (K₀ k t).algebraMap_mem c⟩
    change (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) ∈ W
    rw [hc]
    exact hk c
  · rw [ValuationSubring.mem_comap]
    have htt : (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) t = t :=
      (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω).commutes ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
    change (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) t ∈ W
    rw [htt]
    exact ht
  · rw [valuation_comap_lt_one_iff₂]
    rw [ValuationSubring.mem_comap] at ha
    have he : (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ((h * s * h⁻¹) a - a) =
        s ((h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) a) - (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) a := by
      change (h⁻¹ : Ω ≃ₐ[K₀ k t] Ω) ((h * s * h⁻¹) a - a) = _
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply h⁻¹ h,
        inv_mul_cancel, AlgEquiv.one_apply]
    rw [he]
    exact hI _ ha

lemma conjSet_S_eq {K : Subgroup (Ω ≃ₐ[K₀ k t] Ω)} (hK : K ≤ D.H) :
    GaloisPi1.conjSet K D.S = D.S := by
  ext x
  constructor
  · rintro ⟨h, hh, s, hs, rfl⟩
    exact (conj_mem_S D) (hK hh) hs
  · intro hx
    exact ⟨1, K.one_mem, x, hx, by simp⟩

/-- **The closed normal closures of `S` in `H_L` and in `H` agree.** -/
theorem ambientKernel_HL_eq :
    GaloisPi1.ambientKernel D.HL D.S = GaloisPi1.ambientKernel D.H D.S := by
  simp only [GaloisPi1.ambientKernel, (conjSet_S_eq D) D.le, (conjSet_S_eq D) le_rfl]

lemma kernel_HL_eq :
    GaloisPi1.kernel D.HL D.S = (GaloisPi1.kernel D.H D.S).comap (Subgroup.inclusion D.le) := by
  ext x
  simp only [GaloisPi1.kernel, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
    Subgroup.coe_inclusion, (ambientKernel_HL_eq D)]

/-- `⟨⟨S⟩⟩ ≤ H_L`. -/
lemma ambientKernel_le_HL : GaloisPi1.ambientKernel D.H D.S ≤ D.HL := by
  refine Subgroup.topologicalClosure_minimal _ ?_ D.isClosed_HL
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  exact D.conj_mem h hh s (D.S_subset_HL hs)

lemma kernel_le_subgroupOf : GaloisPi1.kernel D.H D.S ≤ D.HL.subgroupOf D.H := by
  intro x hx
  rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_subgroupOf]
  exact (ambientKernel_le_HL D) hx

end Restrict

section Extension

variable [IsGalois (K₀ k t) Ω]

/-- **The orbifold extension** `ι : H_L ⧸ ⟨⟨S⟩⟩ → H ⧸ ⟨⟨S⟩⟩`, induced by `H_L ≤ H`. -/
def orbiIncl :
    GaloisPi1.pi1 D.HL D.S D.isClosed_HL →ₜ* GaloisPi1.pi1 D.H D.S D.isClosed_H where
  toMonoidHom := GaloisPi1.pi1Map D.isClosed_HL D.isClosed_H D.le (subset_refl D.S)
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ _

lemma orbiIncl_mk (x : D.HL) :
    orbiIncl D (QuotientGroup.mk x : D.HL ⧸ GaloisPi1.kernel D.HL D.S) =
      (QuotientGroup.mk (Subgroup.inclusion D.le x) : D.H ⧸ GaloisPi1.kernel D.H D.S) := rfl

/-- `ι` is an open embedding. -/
theorem isOpenEmbedding_orbiIncl : IsOpenEmbedding (orbiIncl D) :=
  GaloisPi1.isOpenEmbedding_pi1Map D.isClosed_HL D.isClosed_H D.le D.isOpen_HL
    fun _ hh _ hs => (conj_mem_S D) hh hs

lemma injective_orbiIncl : Function.Injective (orbiIncl D) :=
  (isOpenEmbedding_orbiIncl D).injective

/-- The image of `ι` is `(H_L ⧸ ⟨⟨S⟩⟩)` inside `H ⧸ ⟨⟨S⟩⟩`. -/
theorem range_orbiIncl :
    (orbiIncl D).toMonoidHom.range =
      (D.HL.subgroupOf D.H).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨Subgroup.inclusion D.le x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk (⟨x, Subgroup.mem_subgroupOf.1 hx⟩ : D.HL), rfl⟩

/-- The projection `H ⧸ ⟨⟨S⟩⟩ → A = H ⧸ H_L`. -/
def orbiProj : GaloisPi1.pi1 D.H D.S D.isClosed_H →* D.A :=
  QuotientGroup.lift (GaloisPi1.kernel D.H D.S) (QuotientGroup.mk' (D.HL.subgroupOf D.H)) (by
    rw [QuotientGroup.ker_mk']
    exact kernel_le_subgroupOf D)

lemma orbiProj_mk (x : D.H) :
    orbiProj D (QuotientGroup.mk x : D.H ⧸ GaloisPi1.kernel D.H D.S) = (x : D.A) := rfl

lemma orbiProj_surjective : Function.Surjective (orbiProj D) := by
  intro a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- **Exactness**: `ker (H ⧸ ⟨⟨S⟩⟩ → A) = range ι`. -/
theorem ker_orbiProj : (orbiProj D).ker = (orbiIncl D).toMonoidHom.range := by
  rw [range_orbiIncl]
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := GaloisPi1.kernel D.H D.S) y
  rw [MonoidHom.mem_ker]
  refine (QuotientGroup.eq_one_iff (N := D.HL.subgroupOf D.H) x).trans ?_
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have hk : z⁻¹ * x ∈ GaloisPi1.kernel D.H D.S := QuotientGroup.eq.1 hzx
    have hm := (D.HL.subgroupOf D.H).mul_mem hz (kernel_le_subgroupOf D hk)
    simpa using hm

/-- The image of `ι` is normal. -/
instance range_orbiIncl_normal : (orbiIncl D).toMonoidHom.range.Normal := by
  rw [← ker_orbiProj]
  infer_instance

/-- The image of `ι` is open. -/
lemma isOpen_range_orbiIncl :
    IsOpen ((orbiIncl D).toMonoidHom.range : Set (GaloisPi1.pi1 D.H D.S D.isClosed_H)) := by
  rw [MonoidHom.coe_range]
  exact (isOpenEmbedding_orbiIncl D).isOpen_range

/-- **The quotient of the orbifold extension**: `(H ⧸ ⟨⟨S⟩⟩) ⧸ range ι ≃ A = H ⧸ H_L`. -/
def orbiQuotEquiv : GaloisPi1.pi1 D.H D.S D.isClosed_H ⧸ (orbiIncl D).toMonoidHom.range ≃* D.A :=
  (QuotientGroup.quotientMulEquivOfEq (ker_orbiProj D).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (orbiProj_surjective D))

/-- **The index of the orbifold extension** is `[H : H_L]`. -/
theorem index_range_orbiIncl : (orbiIncl D).toMonoidHom.range.index = D.HL.relIndex D.H :=
  Nat.card_congr (orbiQuotEquiv D).toEquiv

lemma index_range_orbiIncl_ne_zero : (orbiIncl D).toMonoidHom.range.index ≠ 0 := by
  rw [index_range_orbiIncl, Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

/-- For `H = Gal(Ω / k(t))`, the index of the orbifold extension is the degree `[L : k(t)]` (e.g.
`2` for `L = K(E) ⊇ K(x)`, `E` an elliptic curve). -/
theorem index_range_orbiIncl_of_H_eq_top (hH : D.H = ⊤) :
    (orbiIncl D).toMonoidHom.range.index = Module.finrank (K₀ k t) D.L := by
  rw [index_range_orbiIncl, hH, Subgroup.relIndex_top_right,
    IntermediateField.finrank_eq_fixingSubgroup_index, D.fixingSubgroup_L]

variable [CharZero k] [IsSepClosed Ω]

/-- **The open embedding `π₁ᵉᵗ(Spec R) ↪ π₁ᵉᵗ([Spec R / A])`**: `equivPi1Spec` (for `H_L`), then
`ι`, then `equivPi1` (for `D`). -/
def orbiEmb : π₁ᵉᵗ(specPoint D.R Ω) →ₜ* etalePi1 D.R D.A Ω :=
  ((ContinuousMonoidHom.toContinuousMonoidHom D.equivPi1.symm).comp (orbiIncl D)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)))

theorem isOpenEmbedding_orbiEmb : IsOpenEmbedding (orbiEmb D) :=
  D.equivPi1.symm.toHomeomorph.isOpenEmbedding.comp ((isOpenEmbedding_orbiIncl D).comp
    ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).toHomeomorph.isOpenEmbedding)

/-- `orbiEmb` maps the intrinsic Galois action of `σ ∈ H_L` on the fibres of `Spec R` to the
action of `σ` on the fibres of the `A`-equivariant covers. -/
theorem orbiEmb_galoisHom (σ : D.HL) :
    orbiEmb D ((galoisDataHL D).galoisHom (galoisDataHL_H_le D) σ) =
      D.toEtalePi1 (Subgroup.inclusion D.le σ) := by
  have h : ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D))
      ((galoisDataHL D).galoisHom (galoisDataHL_H_le D) σ) =
      (QuotientGroup.mk σ : D.HL ⧸ GaloisPi1.kernel D.HL D.S) := by
    rw [ContinuousMulEquiv.apply_eq_iff_symm_apply]
    exact ((galoisDataHL D).equivPi1Spec_symm_mk (galoisDataHL_H_le D) σ).symm
  change D.equivPi1.symm (orbiIncl D (((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D))
    ((galoisDataHL D).galoisHom (galoisDataHL_H_le D) σ))) = _
  rw [h, orbiIncl_mk]
  rfl

end Extension

section ConstProj

variable [IsGalois (K₀ k t) Ω]

/-- **The projection to the Galois group of the constants**: `H ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / k)`, for any
set `S` of elements restricting trivially to `k̄`. -/
def piConst (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (S : Set (Ω ≃ₐ[K₀ k t] Ω))
    (hH : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω))) (hS : ∀ s ∈ S, galResConst t s = 1) :
    GaloisPi1.pi1 H S hH →* (ConstField₂ k Ω ≃ₐ[k] ConstField₂ k Ω) :=
  QuotientGroup.lift (GaloisPi1.kernel H S) ((galResConst t).comp H.subtype) (by
    intro x hx
    rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker]
    have hcl : IsClosed (((galResConst (k := k) t).ker : Subgroup _) : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (continuous_galResConst t)
    refine Subgroup.topologicalClosure_minimal _ ?_ hcl hx
    rw [Subgroup.closure_le]
    rintro _ ⟨h, -, s, hs, rfl⟩
    change galResConst t (h * s * h⁻¹) = 1
    rw [map_mul, map_mul, hS s hs, mul_one, map_inv, mul_inv_cancel])

lemma piConst_mk (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (S : Set (Ω ≃ₐ[K₀ k t] Ω))
    (hH : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω))) (hS : ∀ s ∈ S, galResConst t s = 1) (x : H) :
    piConst H S hH hS (QuotientGroup.mk x : H ⧸ GaloisPi1.kernel H S) = galResConst t x := rfl

lemma continuous_piConst (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (S : Set (Ω ≃ₐ[K₀ k t] Ω))
    (hH : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω))) (hS : ∀ s ∈ S, galResConst t s = 1) :
    Continuous (piConst H S hH hS) := by
  change Continuous (QuotientGroup.lift (GaloisPi1.kernel H S) ((galResConst t).comp H.subtype) _)
  rw [(QuotientGroup.isQuotientMap_mk (GaloisPi1.kernel H S)).continuous_iff]
  exact (continuous_galResConst t).comp continuous_subtype_val

omit [IsGalois (K₀ k t) Ω] in
/-- The inertia elements restrict trivially to the constants. -/
lemma galResConst_S {s : Ω ≃ₐ[K₀ k t] Ω} (hs : s ∈ D.S) : galResConst t s = 1 := by
  obtain ⟨-, W, hk, -, hI⟩ := hs
  exact galResConst_eq_one_of_mem_inertia W hk hI

/-- `Π_C = H ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / k)`. -/
abbrev piConstC : GaloisPi1.pi1 D.H D.S D.isClosed_H →* (ConstField₂ k Ω ≃ₐ[k] ConstField₂ k Ω) :=
  piConst D.H D.S D.isClosed_H fun _ hs => (galResConst_S D) hs

/-- `Π_X = H_L ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / k)`. -/
abbrev piConstX :
    GaloisPi1.pi1 D.HL D.S D.isClosed_HL →* (ConstField₂ k Ω ≃ₐ[k] ConstField₂ k Ω) :=
  piConst D.HL D.S D.isClosed_HL fun _ hs => (galResConst_S D) hs

/-- **Compatibility with `ι`**: `piConstC ∘ ι = piConstX`. -/
theorem piConst_comp_orbiIncl : (piConstC D).comp (orbiIncl D).toMonoidHom = piConstX D := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- **`Δ_C ∩ range ι = ι(Δ_X)`**, where `Δ_C`, `Δ_X` are the kernels of the projections to
`Gal(k̄ / k)`. -/
theorem ker_piConst_inf_range_orbiIncl :
    (piConstC D).ker ⊓ (orbiIncl D).toMonoidHom.range =
      (piConstX D).ker.map (orbiIncl D).toMonoidHom := by
  rw [ker_inf_range_eq_map₂, piConst_comp_orbiIncl]

/-- `ι⁻¹(Δ_C) = Δ_X`. -/
theorem comap_ker_piConst_orbiIncl :
    (piConstC D).ker.comap (orbiIncl D).toMonoidHom = (piConstX D).ker := by
  rw [MonoidHom.comap_ker, piConst_comp_orbiIncl]

end ConstProj

end CurvesJacobian.Cusp
