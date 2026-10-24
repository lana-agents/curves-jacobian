/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ConstantExtension
import CurvesJacobian.Cusp.OrbiQuotientPi1
import CurvesJacobian.LocAn.ThmC

/-!
# Algebraic constant extensions `U_K` of the Galois model

Setting of `pi1` / continuous-kummer-theory: `D : GaloisData k t`, `Ω ⊇ K₀ = k(t)` Galois,
`char k = 0`. For an algebraic extension `k ⊆ K ⊆ Ω` (e.g. a finite extension `k'` of `k` inside
`Ω`) we build the Galois model of `U_K` and identify its fundamental group with the preimage of
`G_K` in `Π_U`:

* `CurvesJacobian.Kummer.resK : Gal(Ω/K(t)) →* Gal(Ω/k(t))`, continuous and injective, with image
  the automorphisms fixing `K` (`exists_resK_eq`);
* `CurvesJacobian.Kummer.constExt K D : GaloisData K t` (`H' = H ∩ Gal(Ω/K(t))`), whose
  function field contains `F` and `K` (`le_F_constExt`, `algebraMap_mem_F_constExt`);
* `CurvesJacobian.Kummer.map_S_constExt`, `exists_S_constExt`: the inertia elements of `D'` are
  exactly the inertia elements of `D` (these fix `k̄ ⊇ K` pointwise);
* `CurvesJacobian.Kummer.ambientKernel_constExt`: `⟨⟨S⟩⟩_H = res(⟨⟨S'⟩⟩_{H'})` (the `H`-normal
  closure of `S` equals the `H'`-normal closure, as `S` is stable under conjugation by `H`);
* **`CurvesJacobian.Kummer.piRes : Π_{U_K} →* Π_U`**, continuous (`continuous_piRes`), injective
  (`piRes_injective`), a closed embedding (`isClosedEmbedding_piRes`), with image `π⁻¹(G_K)`
  (`mem_range_piRes_iff`): `Π_{U_K} = Π_U ×_{G_k} G_K`;
* `CurvesJacobian.Kummer.RatPoint.constExt K x`: a rational point of `U` (place `x.A`) is a
  rational point of `U_K` (`exists_residue_eq_constExt`: residues of `F K` at `x` lie in `K`,
  by lifting `G_K` into the decomposition group of `x`);
* `CurvesJacobian.Kummer.exists_resGk`: the restriction `G_K → G_k`;
* **`CurvesJacobian.Kummer.piRes_ratSectionGk`**: the section of `x` over `K` is the restriction
  of the section of `x` to `G_K`: `piRes (s_{x_K}(g')) = s_x(g)` whenever `g'|_{k̄} = g`.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing
open scoped Pointwise

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω} {t : Ω}

/-- `k(t) ⊆ K(t)` as an algebra (local instance). -/
@[reducible] noncomputable def algebraK₀K : Algebra (K₀ k t) (K₀ K t) :=
  (K₀Map (K := K) t).toAlgebra

attribute [local instance] algebraK₀K

instance isScalarTower_K₀K : IsScalarTower (K₀ k t) (K₀ K t) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (k K t) in
/-- Restriction `Gal(Ω/K(t)) → Gal(Ω/k(t))`. -/
noncomputable def resK : (Ω ≃ₐ[K₀ K t] Ω) →* (Ω ≃ₐ[K₀ k t] Ω) :=
  AlgEquiv.restrictScalarsHom (K₀ k t)

@[simp]
lemma resK_apply (σ : Ω ≃ₐ[K₀ K t] Ω) (x : Ω) : resK k K t σ x = σ x := rfl

lemma resK_injective : Function.Injective (resK k K t) := by
  intro σ τ h
  ext x
  exact DFunLike.congr_fun h x

/-- Elements of `Gal(Ω/K(t))` fix `K`. -/
lemma resK_fix (σ : Ω ≃ₐ[K₀ K t] Ω) (c : K) : resK k K t σ (algebraMap K Ω c) = algebraMap K Ω c :=
  σ.commutes ⟨_, (K₀ K t).algebraMap_mem c⟩

/-- **The image of `resK`**: an automorphism over `k(t)` fixing `K` pointwise is an automorphism
over `K(t)`. -/
lemma exists_resK_eq {h : Ω ≃ₐ[K₀ k t] Ω} (hh : ∀ c : K, h (algebraMap K Ω c) = algebraMap K Ω c) :
    ∃ σ : Ω ≃ₐ[K₀ K t] Ω, resK k K t σ = h := by
  let h' : Ω ≃ₐ[K] Ω := AlgEquiv.ofRingEquiv (f := h.toRingEquiv) fun c => hh c
  have hle : K₀ K t ≤ IntermediateField.fixedField (Subgroup.zpowers h') := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro g hg
    have ht : h' ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) t :=
      h.commutes ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
    exact (Subgroup.zpowers_le.2 ht) hg
  refine ⟨AlgEquiv.ofRingEquiv (f := h.toRingEquiv) fun x => ?_, by ext; rfl⟩
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) h' (Subgroup.mem_zpowers h')

variable [IsGalois (K₀ k t) Ω]

instance isGalois_K₀K : IsGalois (K₀ K t) Ω :=
  IsGalois.tower_top_of_isGalois (K₀ k t) (K₀ K t) Ω

lemma continuous_resK : Continuous (resK k K t) :=
  continuous_of_apply_eq _ fun _ _ => rfl

/-- `resK` is a closed map (compact source, Hausdorff target). -/
lemma isClosedMap_resK : IsClosedMap (resK k K t) :=
  (continuous_resK (k := k) (K := K) (t := t)).isClosedMap

variable [Algebra.IsAlgebraic k K] (D : Pi1.Orbifold.GaloisData k t)

omit [IsGalois (K₀ k t) Ω] in
include D in
lemma transcendental_K : Transcendental K t :=
  Transcendental.extendScalars K D.transcendental

variable (K) in
/-- **The Galois model of `U_K`** for an algebraic extension `k ⊆ K ⊆ Ω`:
`H' = H ∩ Gal(Ω/K(t))`, `H'_L = H_L ∩ Gal(Ω/K(t))`. -/
@[irreducible] noncomputable def constExt : Pi1.Orbifold.GaloisData K t where
  H := D.H.comap (resK k K t)
  HL := D.HL.comap (resK k K t)
  le σ hσ := by
    rw [Subgroup.mem_comap] at hσ ⊢
    exact D.le hσ
  isOpen_HL := D.isOpen_HL.preimage (continuous_resK (k := k) (K := K) (t := t))
  conj_mem h hh n hn := by
    rw [Subgroup.mem_comap] at hh hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact D.conj_mem _ hh _ hn
  transcendental := transcendental_K (K := K) D

@[simp]
lemma mem_constExt_H {σ : Ω ≃ₐ[K₀ K t] Ω} :
    σ ∈ (constExt K D).H ↔ resK k K t σ ∈ D.H := by
  unfold constExt
  exact Subgroup.mem_comap

@[simp]
lemma mem_constExt_HL {σ : Ω ≃ₐ[K₀ K t] Ω} :
    σ ∈ (constExt K D).HL ↔ resK k K t σ ∈ D.HL := by
  unfold constExt
  exact Subgroup.mem_comap

/-- `F ⊆ F K`. -/
lemma le_F_constExt {x : Ω} (hx : x ∈ F D) : x ∈ F (constExt K D) := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  exact hx _ ((mem_constExt_H D).1 hσ)

/-- `K ⊆ F K`. -/
lemma algebraMap_mem_F_constExt (c : K) : algebraMap K Ω c ∈ F (constExt K D) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact σ.commutes ⟨_, (K₀ K t).algebraMap_mem c⟩

variable (K) in
/-- The restriction `H' → H`. -/
noncomputable def hRes : (constExt K D).H →* D.H :=
  ((resK k K t).comp (constExt K D).H.subtype).codRestrict D.H fun σ =>
    (mem_constExt_H D).1 σ.2

@[simp]
lemma coe_hRes (σ : (constExt K D).H) :
    ((hRes K D σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) = resK k K t σ := rfl

lemma hRes_injective : Function.Injective (hRes K D) := by
  intro σ τ h
  exact Subtype.ext (resK_injective (k := k) (congrArg Subtype.val h :))

lemma continuous_hRes : Continuous (hRes K D) :=
  Continuous.subtype_mk ((continuous_resK (k := k) (K := K) (t := t)).comp
    continuous_subtype_val) _

/-- An element of `H` fixing `K` lies in the image of `H'`. -/
lemma exists_hRes_eq {h : D.H} (hh : ∀ c : K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) =
    algebraMap K Ω c) : ∃ σ : (constExt K D).H, hRes K D σ = h := by
  obtain ⟨σ, hσ⟩ := exists_resK_eq hh
  exact ⟨⟨σ, (mem_constExt_H D).2 (hσ ▸ h.2)⟩, Subtype.ext hσ⟩

/-- Inertia elements of `U_K` restrict to inertia elements of `U`. -/
lemma map_S_constExt {s : Ω ≃ₐ[K₀ K t] Ω} (hs : s ∈ (constExt K D).S) :
    resK k K t s ∈ D.S := by
  obtain ⟨hsL, W, hK, ht, hI⟩ := hs
  refine ⟨(mem_constExt_HL D).1 hsL, W, fun c => ?_, ht, fun a ha => hI a ha⟩
  rw [IsScalarTower.algebraMap_apply k K Ω]
  exact hK _

/-- **Inertia elements of `U` come from `U_K`** (they fix `k̄ ⊇ K` pointwise). -/
lemma exists_S_constExt [CharZero k] {s : Ω ≃ₐ[K₀ k t] Ω} (hs : s ∈ D.S) :
    ∃ s' ∈ (constExt K D).S, resK k K t s' = s := by
  obtain ⟨hsL, W, hk, ht, hI⟩ := hs
  have halg : ∀ c : K, IsAlgebraic k (algebraMap K Ω c) := fun c =>
    (Algebra.IsAlgebraic.isAlgebraic c).algebraMap
  obtain ⟨s', rfl⟩ := exists_resK_eq (K := K) fun c => inertia_fix_algebraic hk hI (halg c)
  refine ⟨s', ⟨(mem_constExt_HL D).2 hsL, W,
    fun c => KummerTheory.Curve.mem_of_isIntegral hk (halg c).isIntegral,
    ht, fun a ha => hI a ha⟩, rfl⟩

/-- `res(⟨⟨S'⟩⟩_{H'}) ⊆ ⟨⟨S⟩⟩_H`. -/
lemma ambientKernel_constExt_le_comap :
    GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S ≤
      (GaloisPi1.ambientKernel D.H D.S).comap (resK k K t) := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((GaloisPi1.isClosed_ambientKernel _ _).preimage (continuous_resK (k := k) (K := K) (t := t)))
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_)
  refine ⟨resK k K t h, (mem_constExt_H D).1 hh, resK k K t s, map_S_constExt D hs, ?_⟩
  simp only [map_mul, map_inv]

/-- `⟨⟨S⟩⟩_H ⊆ res(⟨⟨S'⟩⟩_{H'})`: `S` is stable under conjugation by `H` and comes from `S'`. -/
lemma ambientKernel_le_map_constExt [CharZero k] :
    GaloisPi1.ambientKernel D.H D.S ≤
      (GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S).map (resK k K t) := by
  refine Subgroup.topologicalClosure_minimal _ ?_ (isClosedMap_resK _
    (GaloisPi1.isClosed_ambientKernel _ _))
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  obtain ⟨s', hs', he⟩ := exists_S_constExt (K := K) D (CurvesJacobian.Cusp.conj_mem_S D hh hs)
  refine ⟨s', Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_), he⟩
  exact ⟨1, (constExt K D).H.one_mem, s', hs', by simp⟩

/-- **`⟨⟨S⟩⟩_H = res(⟨⟨S'⟩⟩_{H'})`.** -/
lemma ambientKernel_constExt [CharZero k] :
    (GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S).map (resK k K t) =
      GaloisPi1.ambientKernel D.H D.S :=
  le_antisymm (Subgroup.map_le_iff_le_comap.2 (ambientKernel_constExt_le_comap D))
    (ambientKernel_le_map_constExt D)

/-- `res⁻¹(⟨⟨S⟩⟩_H) = ⟨⟨S'⟩⟩_{H'}`. -/
lemma comap_ambientKernel_constExt [CharZero k] :
    (GaloisPi1.ambientKernel D.H D.S).comap (resK k K t) =
      GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S := by
  rw [← ambientKernel_constExt (K := K) D,
    Subgroup.comap_map_eq_self_of_injective resK_injective]

lemma mem_comap_of_mem_ambientKernel_constExt (σ : Ω ≃ₐ[K₀ K t] Ω)
    (h1 : σ ∈ GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S) :
    σ ∈ (GaloisPi1.ambientKernel D.H D.S).comap (resK k K t) := by
  have := ambientKernel_constExt_le_comap (K := K) D
  exact this h1

lemma hRes_mem_kernel (σ : (constExt K D).H)
    (hσ : σ ∈ GaloisPi1.kernel (constExt K D).H (constExt K D).S) :
    hRes K D σ ∈ GaloisPi1.kernel D.H D.S := by
  have h1 : (σ : Ω ≃ₐ[K₀ K t] Ω) ∈
      GaloisPi1.ambientKernel (constExt K D).H (constExt K D).S := hσ
  exact Subgroup.mem_comap.1 (mem_comap_of_mem_ambientKernel_constExt D _ h1)

lemma kernel_le_comap_hRes :
    GaloisPi1.kernel (constExt K D).H (constExt K D).S ≤
      (GaloisPi1.kernel D.H D.S).comap (hRes K D) :=
  fun σ hσ => Subgroup.mem_comap.2 (hRes_mem_kernel D σ hσ)

variable (K) in
/-- **The map `Π_{U_K} → Π_U`.** -/
noncomputable def piRes : Pi (constExt K D) →* Pi D :=
  QuotientGroup.map _ _ (hRes K D) (kernel_le_comap_hRes D)

@[simp]
lemma piRes_mk (σ : (constExt K D).H) :
    piRes K D (σ : Pi (constExt K D)) = (hRes K D σ : Pi D) := rfl

lemma continuous_piRes : Continuous (piRes K D) := by
  change Continuous (QuotientGroup.map _ _ (hRes K D) (kernel_le_comap_hRes D))
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_hRes D)

/-- **`Π_{U_K} → Π_U` is injective.** -/
theorem piRes_injective [CharZero k] : Function.Injective (piRes K D) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  induction p using QuotientGroup.induction_on with
  | H σ =>
    rw [piRes_mk, QuotientGroup.eq_one_iff, GaloisPi1.kernel, Subgroup.mem_subgroupOf,
      coe_hRes, ← Subgroup.mem_comap, comap_ambientKernel_constExt] at hp
    exact (QuotientGroup.eq_one_iff σ).2
      (by rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf]; exact hp)

variable [CharZero k] [IsAlgClosed Ω]

omit [CharZero k] [IsAlgClosed Ω] in
/-- The image of `K` lies in `k̄`. -/
lemma algebraMap_mem_kbar (c : K) : algebraMap K Ω c ∈ kbar k Ω :=
  mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic c).algebraMap

/-- **The image of `Π_{U_K}` in `Π_U` is the preimage of `G_K`** (the elements of `G_k` fixing
`K`): `Π_{U_K} = Π_U ×_{G_k} G_K`. -/
theorem mem_range_piRes_iff (p : Pi D) :
    p ∈ (piRes K D).range ↔
      ∀ c : K, piToGk D p ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ =
        ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ := by
  constructor
  · rintro ⟨q, rfl⟩ c
    induction q using QuotientGroup.induction_on with
    | H σ =>
      apply Subtype.ext
      change algebraMap (kbar k Ω) Ω (hToGk D (hRes K D σ) _) = _
      rw [algebraMap_hToGk_apply, coe_hRes]
      exact resK_fix σ.1 c
  · induction p using QuotientGroup.induction_on with
    | H h =>
    intro hc
    have hh : ∀ c : K, (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) = algebraMap K Ω c := by
      intro c
      have := congrArg (algebraMap (kbar k Ω) Ω) (hc c)
      rw [piToGk_mk, algebraMap_hToGk_apply] at this
      exact this
    obtain ⟨σ, rfl⟩ := exists_hRes_eq (K := K) D hh
    exact ⟨σ, rfl⟩

omit [IsAlgClosed Ω] in
/-- **`Π_{U_K} → Π_U` is a closed embedding.** -/
theorem isClosedEmbedding_piRes : Topology.IsClosedEmbedding (piRes K D) := by
  haveI : CompactSpace (constExt K D).H :=
    GaloisPi1.compactSpace_of_isClosed _ (constExt K D).isClosed_H
  haveI : CompactSpace (Pi (constExt K D)) := Quotient.compactSpace
  haveI : IsClosed (GaloisPi1.kernel D.H D.S : Set D.H) := GaloisPi1.isClosed_kernel _ _
  exact (continuous_piRes D).isClosedEmbedding (piRes_injective D)

/-! ### Rational points of `U` are rational points of `U_K` -/

instance charZero_constExt : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap k K).injective

variable {D}

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma algebraMap_mem_A_constExt {A : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (c : K) :
    algebraMap K Ω c ∈ A :=
  KummerTheory.Curve.mem_of_isIntegral hk
    (Algebra.IsAlgebraic.isAlgebraic c).algebraMap.isIntegral

omit [IsGalois (K₀ k t) Ω] in
/-- The constants of `k̄` fixed by `G_K` are the elements of `K`. -/
lemma exists_eq_of_forall_fix_constExt (β : kbar k Ω)
    (hβ : ∀ g : Gk k Ω, (∀ c : K, g ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ =
      ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩) → g β = β) :
    ∃ c : K, algebraMap K Ω c = β := by
  have hle : K ≤ kbar k Ω := fun y hy => algebraMap_mem_kbar (K := K) ⟨y, hy⟩
  have hmem : β ∈ IntermediateField.restrict hle := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.restrict hle),
      IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    refine hβ g fun c => hg _ ((IntermediateField.mem_restrict hle _).2 c.2)
  exact ⟨⟨β, (IntermediateField.mem_restrict hle β).1 hmem⟩, rfl⟩

/-- **A rational point of `U` stays rational over `K`**: the residue of a function of `F K` at `x`
lies in `K`. (Lift `g ∈ G_K` to the decomposition group of `x`; it fixes `F K`.) -/
theorem exists_residue_eq_constExt (x : RatPoint D) (a : F (constExt K D)) (ha : (a : Ω) ∈ x.A) :
    ∃ c : K, residue x.A ⟨_, ha⟩ = residue x.A ⟨_, algebraMap_mem_A_constExt x.hk c⟩ := by
  obtain ⟨β, hβ⟩ := kbarResidue_surjective x.A x.hk x.hkres (residue x.A ⟨_, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_of_forall_fix_constExt (K := K) β fun g hg => by
    obtain ⟨σ, hσ⟩ := x.decompositionMap_surjective
      ((kbarEquiv x.A x.hk x.hkres).symm.trans (g.trans (kbarEquiv x.A x.hk x.hkres)))
    have hG : ∀ y, piToGk D (decompToPi D x.A σ) y = g y := fun y =>
      (kbarResidue x.A x.hk).injective (by
        rw [kbarResidue_piToGk_decompToPi D x.A x.hk x.hkres, hσ,
          ← kbarEquiv_apply x.A x.hk x.hkres,
          ← kbarEquiv_apply x.A x.hk x.hkres]
        simp)
    have hfix : ∀ c : K, ((ofGalF D σ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) =
        algebraMap K Ω c := by
      intro c
      have h1 := algebraMap_hToGk_apply D (ofGalF D σ.1) ⟨_, algebraMap_mem_kbar c⟩
      have h2 := hG ⟨_, algebraMap_mem_kbar c⟩
      have h3 := hg c
      rw [← h1]
      change algebraMap (kbar k Ω) Ω (piToGk D (decompToPi D x.A σ) _) = _
      rw [h2, h3]
      rfl
    obtain ⟨σ', hσ'⟩ := exists_hRes_eq (K := K) D hfix
    have hσa : σ.1 (a : Ω) = a := by
      rw [← ofGalF_apply D σ.1, ← hσ', coe_hRes, resK_apply]
      exact (IntermediateField.mem_fixedField_iff _ _).1 a.2 _ σ'.2
    apply (kbarResidue x.A x.hk).injective
    rw [← hG, kbarResidue_piToGk_decompToPi D x.A x.hk x.hkres, hβ,
      Decomposition.decompositionMap_residue]
    congr 1
    exact Subtype.ext hσa
  refine ⟨c, ?_⟩
  rw [← hβ, kbarResidue_apply]
  congr 1
  exact Subtype.ext hc.symm

variable (K) in
/-- **A rational point of `U` as a rational point of `U_K`** (same place `x.A`). -/
noncomputable def RatPoint.constExt (x : RatPoint D) : RatPoint (constExt K D) where
  A := x.A
  hk := algebraMap_mem_A_constExt x.hk
  isIntegral := by
    letI := resAlg x.A (algebraMap_mem_A_constExt (K := K) x.hk)
    haveI : IsScalarTower k K (ResidueField x.A) := IsScalarTower.of_algebraMap_eq fun c => rfl
    exact ⟨fun y => (Algebra.IsIntegral.isIntegral (R := k) y).tower_top⟩
  hrat a ha := exists_residue_eq_constExt x a ha

@[simp]
lemma RatPoint.constExt_A (x : RatPoint D) : (x.constExt K).A = x.A := rfl

/-! ### Sections of rational points and restriction to `G_K` -/

omit [CharZero k] [IsAlgClosed Ω] in
variable (D) in
lemma constExt_HL_eq (hHL : D.HL = D.H) : (constExt K D).HL = (constExt K D).H := by
  ext σ
  rw [mem_constExt_HL, mem_constExt_H, hHL]

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k K] in
/-- `k̄ ⊆ K̄` (algebraic closures of `k` and `K` in `Ω`). -/
lemma mem_kbarK (y : kbar k Ω) : (y : Ω) ∈ kbar K Ω :=
  mem_algebraicClosure_iff.2
    ((mem_algebraicClosure_iff.1 y.2).extendScalars (algebraMap k K).injective)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k K] in
/-- `G_K` maps `k̄ ⊆ K̄` into itself. -/
lemma resGk_mem (g' : Gk K Ω) (y : kbar k Ω) :
    ((g' ⟨y, mem_kbarK y⟩ : kbar K Ω) : Ω) ∈ kbar k Ω := by
  obtain ⟨p, hp0, hp⟩ := mem_algebraicClosure_iff.1 y.2
  refine mem_algebraicClosure_iff.2 ⟨p, hp0, ?_⟩
  set pK := p.map (algebraMap k K)
  have h0 : Polynomial.aeval (⟨y, mem_kbarK y⟩ : kbar K Ω) pK = 0 := by
    apply (algebraMap (kbar K Ω) Ω).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    change Polynomial.aeval (y : Ω) pK = 0
    rw [Polynomial.aeval_map_algebraMap, hp]
  have h1 : Polynomial.aeval (g' ⟨y, mem_kbarK y⟩) pK = 0 := by
    rw [← AlgEquiv.coe_toAlgHom, Polynomial.aeval_algHom_apply, h0, map_zero]
  have h2 := congrArg (algebraMap (kbar K Ω) Ω) h1
  rw [← Polynomial.aeval_algebraMap_apply, map_zero, Polynomial.aeval_map_algebraMap] at h2
  exact h2

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k K] in
/-- **The restriction `G_K → G_k`**: every `g' ∈ G_K` acts on `k̄ ⊆ K̄` as an element of `G_k`. -/
lemma exists_resGk (g' : Gk K Ω) :
    ∃ g : Gk k Ω, ∀ y : kbar k Ω, ((g y : kbar k Ω) : Ω) = g' ⟨y, mem_kbarK y⟩ := by
  let φ : kbar k Ω →ₐ[k] kbar k Ω :=
    { toFun y := ⟨_, resGk_mem g' y⟩
      map_one' := Subtype.ext (by
        change ((g' 1 : kbar K Ω) : Ω) = 1
        rw [map_one]; rfl)
      map_mul' a b := Subtype.ext (by
        change ((g' (⟨a, mem_kbarK a⟩ * ⟨b, mem_kbarK b⟩) : kbar K Ω) : Ω) = _
        rw [map_mul]; rfl)
      map_zero' := Subtype.ext (by
        change ((g' 0 : kbar K Ω) : Ω) = 0
        rw [map_zero]; rfl)
      map_add' a b := Subtype.ext (by
        change ((g' (⟨a, mem_kbarK a⟩ + ⟨b, mem_kbarK b⟩) : kbar K Ω) : Ω) = _
        rw [map_add]; rfl)
      commutes' c := Subtype.ext (by
        change ((g' (algebraMap K (kbar K Ω) (algebraMap k K c)) : kbar K Ω) : Ω) = _
        rw [AlgEquiv.commutes]; rfl) }
  exact ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun _ => rfl⟩

omit [CharZero k] [IsAlgClosed Ω] in
lemma ofGalF_toGalF (h : D.H) : ofGalF D (toGalF D h) = h :=
  toGalF_injective D (toGalF_ofGalF D _)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k K] in
lemma residue_congr_constExt {A : ValuationSubring Ω} (a b : A) (h : (a : Ω) = b) :
    residue A a = residue A b := by
  rw [Subtype.ext h]

/-- An element of the decomposition group of `x` over `F K`, viewed in `Gal(Ω/F)`, lies in the
decomposition group of `x` over `F`. -/
lemma toGalF_hRes_mem_decompositionSubgroup (x : RatPoint D)
    (σ' : (x.constExt K).A.decompositionSubgroup (F (constExt K D))) :
    toGalF D (hRes K D (ofGalF (constExt K D) σ'.1)) ∈ x.A.decompositionSubgroup (F D) := by
  have hρapp : ∀ z, toGalF D (hRes K D (ofGalF (constExt K D) σ'.1)) z = σ'.1 z :=
    fun z => ofGalF_apply (constExt K D) σ'.1 z
  have hσA : σ'.1 • x.A = x.A := MulAction.mem_stabilizer_iff.1 σ'.2
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hσA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have : (toGalF D (hRes K D (ofGalF (constExt K D) σ'.1)))⁻¹ • z = σ'.1⁻¹ • z := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.aut_inv, AlgEquiv.aut_inv]
    apply (toGalF D (hRes K D (ofGalF (constExt K D) σ'.1))).injective
    rw [AlgEquiv.apply_symm_apply, hρapp, AlgEquiv.apply_symm_apply]
  rw [this]

/-- The decomposition maps of `x` over `F K` and over `F` are compatible with `G_K → G_k`. -/
lemma decompositionMap_toGalF_hRes (x : RatPoint D)
    (σ' : (x.constExt K).A.decompositionSubgroup (F (constExt K D))) (g' : Gk K Ω)
    (g : Gk k Ω) (hg : ∀ y : kbar k Ω, ((g y : kbar k Ω) : Ω) = g' ⟨y, mem_kbarK y⟩)
    (hσ' : Decomposition.decompositionMap (F (constExt K D)) (x.constExt K).A (x.constExt K).hk
      (x.constExt K).hkres σ' =
      AlgEquiv.autCongr (kbarEquiv (x.constExt K).A (x.constExt K).hk (x.constExt K).hkres) g') :
    Decomposition.decompositionMap (F D) x.A x.hk x.hkres
      ⟨_, toGalF_hRes_mem_decompositionSubgroup x σ'⟩ =
      AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g := by
  ext r
  obtain ⟨y, rfl⟩ := (kbarEquiv x.A x.hk x.hkres).surjective r
  have h1 := congrArg (fun φ => φ (kbarEquiv (x.constExt K).A (x.constExt K).hk
    (x.constExt K).hkres ⟨y, mem_kbarK y⟩)) hσ'
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at h1
  rw [kbarEquiv_apply, kbarResidue_apply, Decomposition.decompositionMap_residue,
    kbarEquiv_apply, kbarResidue_apply] at h1
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, kbarEquiv_apply, kbarResidue_apply,
    Decomposition.decompositionMap_residue, kbarEquiv_apply, kbarResidue_apply]
  refine ((residue_congr_constExt _ _ ?_).trans h1).trans (residue_congr_constExt _ _ ?_)
  · exact ofGalF_apply (constExt K D) σ'.1 y
  · exact (hg y).symm

/-- **Compatibility of the sections of a rational point with `Π_{U_K} → Π_U`**: if `g ∈ G_k` and
`g' ∈ G_K` agree on `k̄`, then `s_x(g) = s_{x_K}(g')` in `Π_U`. -/
theorem piRes_ratSectionGk (x : RatPoint D) (hHL : D.HL = D.H) (ht : t ∈ x.A) (g' : Gk K Ω)
    (g : Gk k Ω) (hg : ∀ y : kbar k Ω, ((g y : kbar k Ω) : Ω) = g' ⟨y, mem_kbarK y⟩) :
    piRes K D (LocAn.ratSectionGk (x.constExt K) (constExt_HL_eq D hHL) ht g') =
      LocAn.ratSectionGk x hHL ht g := by
  obtain ⟨σ', hσ'⟩ := (x.constExt K).decompositionMap_surjective
    (AlgEquiv.autCongr (kbarEquiv (x.constExt K).A (x.constExt K).hk (x.constExt K).hkres) g')
  have e1 : LocAn.ratSectionGk (x.constExt K) (constExt_HL_eq D hHL) ht g' =
      decompToPi (constExt K D) (x.constExt K).A σ' := by
    change ratSectionMap (constExt K D) (x.constExt K).A (x.constExt K).hk (x.constExt K).hkres
      (x.constExt K).hrat (constExt_HL_eq D hHL) ht
      (AlgEquiv.autCongr (kbarEquiv (x.constExt K).A (x.constExt K).hk (x.constExt K).hkres) g')
      = _
    rw [← hσ', ratSectionMap_decompositionMap]
  have e3 : LocAn.ratSectionGk x hHL ht g =
      decompToPi D x.A ⟨_, toGalF_hRes_mem_decompositionSubgroup x σ'⟩ := by
    change ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht
      (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g) = _
    rw [← decompositionMap_toGalF_hRes x σ' g' g hg hσ', ratSectionMap_decompositionMap]
  rw [e1, e3]
  change ((hRes K D (ofGalF (constExt K D) σ'.1) : D.H) : Pi D) =
    ((ofGalF D (toGalF D (hRes K D (ofGalF (constExt K D) σ'.1))) : D.H) : Pi D)
  rw [ofGalF_toGalF]

end CurvesJacobian.Kummer
