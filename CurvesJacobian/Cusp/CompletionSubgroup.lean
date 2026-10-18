/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FixedPointConj
import Pi1.Profinite.Completion

/-!
# Open subgroups and quotients of profinite completions

Let `G` be a group with profinite completion `Ĝ` (`η : G → Ĝ`).

* `CurvesJacobian.Cusp.completionComapEquiv`: for an open subgroup `O ⊆ Ĝ` and `H = η⁻¹(O)`
  (a subgroup of finite index), the map `Ĥ → Ĝ` induced by `H ⊆ G` is an isomorphism of
  topological groups `Ĥ ≃ₜ* O` (`completionComapEquiv_eta`: it extends `η|_H`). Injectivity: a
  finite quotient `H ↠ P` factors through the finite quotient `G ↠ G ⧸ N` by the normal core of
  its kernel.
* `CurvesJacobian.Cusp.ker_completionMap`: for a surjection `φ : H ↠ Q` the induced
  `Ĥ ↠ Q̂` (`completionMap_surjective`) has kernel the closure of `η(ker φ)`.
* `CurvesJacobian.Cusp.exists_continuousMulEquiv_of_ker_eq`: two continuous surjections from a
  compact group to Hausdorff groups with the same kernel differ by an isomorphism of topological
  groups.
* `CurvesJacobian.Cusp.topologicalClosure_zpowers_inf_le`: `⟨c⟩‾ ∩ O ⊆ (⟨c⟩ ∩ O)‾` for `O` open.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology Pi1.Profinite

universe u

namespace CurvesJacobian.Cusp

section Procyclic

variable {P : Type*} [Group P] [TopologicalSpace P]

/-- `⟨c⟩‾ ∩ O ⊆ (⟨c⟩ ∩ O)‾` for an open subgroup `O`. -/
lemma topologicalClosure_zpowers_inf_le [IsTopologicalGroup P] {O : Subgroup P}
    (hO : IsOpen (O : Set P)) (c : P) :
    (Subgroup.zpowers c).topologicalClosure ⊓ O ≤ (Subgroup.zpowers c ⊓ O).topologicalClosure := by
  rintro x ⟨hx1, hx2⟩
  have h := hO.inter_closure (t := (Subgroup.zpowers c : Set P)) ⟨hx2, hx1⟩
  change x ∈ closure _
  rw [Subgroup.coe_inf, Set.inter_comm]
  exact h

end Procyclic

section Quotient

variable {P A B : Type*} [Group P] [TopologicalSpace P] [CompactSpace P] [Group A]
  [TopologicalSpace A] [T2Space A] [Group B] [TopologicalSpace B] [T2Space B]

/-- **Two continuous surjections with the same kernel** from a compact group to Hausdorff groups
differ by an isomorphism of topological groups. -/
theorem exists_continuousMulEquiv_of_ker_eq (p : P →* A) (q : P →* B) (hpc : Continuous p)
    (hqc : Continuous q) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : p.ker = q.ker) : ∃ e : A ≃ₜ* B, ∀ x, e (p x) = q x := by
  let eA := QuotientGroup.quotientKerEquivOfSurjective p hp
  let eB := QuotientGroup.quotientKerEquivOfSurjective q hq
  let e₀ : A ≃* B := eA.symm.trans ((QuotientGroup.quotientMulEquivOfEq h).trans eB)
  have he₀ : ∀ x, e₀ (p x) = q x := by
    intro x
    have h1 : eA.symm (p x) = (x : P ⧸ p.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change eB ((QuotientGroup.quotientMulEquivOfEq h) (eA.symm (p x))) = q x
    rw [h1]
    rfl
  have he₀' : ∀ x, e₀.symm (q x) = p x := fun x ↦ by
    rw [MulEquiv.symm_apply_eq, he₀]
  have hpq : IsQuotientMap p := (hpc.isClosedMap).isQuotientMap hpc hp
  have hqq : IsQuotientMap q := (hqc.isClosedMap).isQuotientMap hqc hq
  refine ⟨{ e₀ with
    continuous_toFun := ?_
    continuous_invFun := ?_ }, he₀⟩
  · rw [hpq.continuous_iff]
    have : (e₀ : A → B) ∘ p = q := funext he₀
    simpa only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, MulEquiv.coe_toEquiv, this]
      using hqc
  · rw [hqq.continuous_iff]
    have : (e₀.symm : B → A) ∘ q = p := funext he₀'
    simpa only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm, this]
      using hpc

end Quotient


section Action

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- Conjugation maps `⟨b⟩‾` to `⟨a b a⁻¹⟩‾`. -/
lemma map_conj_topologicalClosure_zpowers (a b : P) :
    (Subgroup.zpowers b).topologicalClosure.map (MulAut.conj a).toMonoidHom =
      (Subgroup.zpowers (a * b * a⁻¹)).topologicalClosure := by
  let h : P ≃ₜ P := (Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)
  have hh : ∀ x, h x = MulAut.conj a x := fun x ↦ by simp [h, MulAut.conj_apply]
  have hz : (Subgroup.zpowers b).map (MulAut.conj a).toMonoidHom =
      Subgroup.zpowers (a * b * a⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe,
    ← hz, Subgroup.coe_map]
  have e1 : ((MulAut.conj a).toMonoidHom : P → P) = h := funext fun x ↦ (hh x).symm
  rw [e1, h.image_closure]

variable {Fb : Type*} [MulAction P Fb]

/-- **Procyclic subgroups and stabilisers.** For `d = γ⁻¹ x γ` and `m` the period of `x` at
`γ • ω₀`, `⟨d⟩‾ ∩ Stab(ω₀) = ⟨dᵐ⟩‾` (stabilisers open). -/
lemma topologicalClosure_zpowers_conj_inf_stabilizer {ω₀ : Fb}
    (hO : IsOpen (MulAction.stabilizer P ω₀ : Set P)) (x γ : P) :
    (Subgroup.zpowers (γ⁻¹ * x * γ)).topologicalClosure ⊓ MulAction.stabilizer P ω₀ =
      (Subgroup.zpowers
        (γ⁻¹ * x ^ Function.minimalPeriod (x • ·) (γ • ω₀) * γ)).topologicalClosure := by
  set m := Function.minimalPeriod (x • ·) (γ • ω₀)
  have hpow : ∀ n : ℤ, (γ⁻¹ * x * γ) ^ n = γ⁻¹ * x ^ n * γ := fun n ↦ by
    simpa using conj_zpow (a := γ⁻¹) (b := x) (i := n)
  have key : ∀ n : ℤ, (γ⁻¹ * x * γ) ^ n ∈ MulAction.stabilizer P ω₀ ↔ (m : ℤ) ∣ n := by
    intro n
    rw [hpow, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
    exact MulAction.zpow_smul_eq_iff_minimalPeriod_dvd
  have hdm : γ⁻¹ * x ^ m * γ = (γ⁻¹ * x * γ) ^ (m : ℤ) := by
    rw [hpow, zpow_natCast]
  have hO' : IsClosed (MulAction.stabilizer P ω₀ : Set P) :=
    Subgroup.isClosed_of_isOpen _ hO
  apply le_antisymm
  · refine (topologicalClosure_zpowers_inf_le hO _).trans
      (Subgroup.topologicalClosure_mono ?_)
    rintro y ⟨hy1, hy2⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
    obtain ⟨q, rfl⟩ := (key n).1 hy2
    rw [hdm, zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  · refine le_inf (Subgroup.topologicalClosure_mono ?_) ?_
    · rw [Subgroup.zpowers_le, hdm]
      exact Subgroup.zpow_mem_zpowers _ _
    · refine Subgroup.topologicalClosure_minimal _ ?_ hO'
      rw [Subgroup.zpowers_le, hdm]
      exact (key m).2 dvd_rfl

end Action

section Completion

variable {G : Type u} [Group G]

/-- `η : G →* Ĝ`. -/
noncomputable abbrev etaHom (G : Type u) [Group G] : G →* completion (GrpCat.of G) :=
  (eta (GrpCat.of G)).hom

@[simp] lemma etaHom_apply (x : G) : etaHom G x = etaFn (GrpCat.of G) x := rfl

lemma denseRange_etaHom : DenseRange (etaHom G) := denseRange (GrpCat.of G)

/-- A continuous map from `Ĝ` to a Hausdorff space is determined by its values on `η(G)`. -/
lemma completion_ext {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : completion (GrpCat.of G) → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : G, f (etaFn (GrpCat.of G) x) = g (etaFn (GrpCat.of G) x)) : f = g :=
  (denseRange (GrpCat.of G)).equalizer hf hg (funext h)

/-- **`completionMap` of a surjection is surjective.** -/
theorem completionMap_surjective {Q : Type u} [Group Q] {φ : G →* Q}
    (hφ : Function.Surjective φ) : Function.Surjective (completionMap φ) := by
  have hc := continuous_completionMap φ
  have hcl : IsClosed (Set.range (completionMap φ)) := (isCompact_range hc).isClosed
  have hd : Dense (Set.range (completionMap φ)) := by
    refine (denseRange (GrpCat.of Q)).mono ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨etaFn (GrpCat.of G) x, completionMap_eta φ x⟩
  intro z
  have : z ∈ closure (Set.range (completionMap φ)) := hd.closure_eq ▸ Set.mem_univ z
  rwa [hcl.closure_eq] at this

/-- In a profinite group, an element outside a closed normal subgroup `M` lies outside an open
normal subgroup containing `M`. -/
lemma exists_open_normal_notMem {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TotallyDisconnectedSpace K] {M : Subgroup K} [M.Normal]
    (hM : IsClosed (M : Set K)) {z : K} (hz : z ∉ M) :
    ∃ T : Subgroup K, T.Normal ∧ IsOpen (T : Set K) ∧ M ≤ T ∧ z ∉ T := by
  obtain ⟨N, hN⟩ := exists_openNormalSubgroup_notMem_sup hM hz
  exact ⟨(N : Subgroup K) ⊔ M, Subgroup.sup_normal _ _,
    Subgroup.isOpen_mono le_sup_left N.isOpen, le_sup_right, hN⟩

/-- The closure of `η(N)` for a normal subgroup `N ⊴ G` is normal in `Ĝ`. -/
lemma normal_topologicalClosure_map_etaHom (N : Subgroup G) [N.Normal] :
    ((N.map (etaHom G)).topologicalClosure).Normal := by
  set M := (N.map (etaHom G)).topologicalClosure
  have hMcl : IsClosed (M : Set (completion (GrpCat.of G))) :=
    Subgroup.isClosed_topologicalClosure _
  have hS : IsClosed {x : completion (GrpCat.of G) | ∀ m ∈ M, x * m * x⁻¹ ∈ M} := by
    have : {x : completion (GrpCat.of G) | ∀ m ∈ M, x * m * x⁻¹ ∈ M} =
        ⋂ m ∈ M, (fun x ↦ x * m * x⁻¹) ⁻¹' (M : Set _) := by
      ext x; simp
    rw [this]
    exact isClosed_biInter fun m _ ↦ hMcl.preimage
      ((continuous_id.mul continuous_const).mul continuous_inv)
  have hη : ∀ g : G, ∀ m ∈ M, etaFn (GrpCat.of G) g * m * (etaFn (GrpCat.of G) g)⁻¹ ∈ M := by
    intro g m hm
    have hc : Continuous fun x : completion (GrpCat.of G) ↦
        etaFn (GrpCat.of G) g * x * (etaFn (GrpCat.of G) g)⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hmaps : Set.MapsTo (fun x : completion (GrpCat.of G) ↦
        etaFn (GrpCat.of G) g * x * (etaFn (GrpCat.of G) g)⁻¹)
        ((N.map (etaHom G) : Subgroup _) : Set _) ((N.map (etaHom G) : Subgroup _) : Set _) := by
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨g * n * g⁻¹, Subgroup.Normal.conj_mem inferInstance n hn g, ?_⟩
      simp only [etaHom_apply, map_mul, map_inv]
    have := map_mem_closure hc hm hmaps
    exact this
  have hall : ∀ x, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    intro x
    have hx : x ∈ closure (Set.range (etaFn (GrpCat.of G))) := by
      rw [(denseRange (GrpCat.of G)).closure_range]; trivial
    exact closure_minimal (s := Set.range (etaFn (GrpCat.of G)))
      (t := {x | ∀ m ∈ M, x * m * x⁻¹ ∈ M}) (by rintro _ ⟨g, rfl⟩; exact hη g) hS hx
  exact ⟨fun m hm x ↦ hall x m hm⟩

/-- **The kernel of `Ĥ ↠ Q̂`** for a surjection `φ : H ↠ Q` is the closure of `η(ker φ)`. -/
theorem ker_completionMap {Q : Type u} [Group Q] {φ : G →* Q} (hφ : Function.Surjective φ) :
    (completionMap φ).ker = (φ.ker.map (etaHom G)).topologicalClosure := by
  set M := (φ.ker.map (etaHom G)).topologicalClosure with hM
  have hMcl : IsClosed (M : Set (completion (GrpCat.of G))) :=
    Subgroup.isClosed_topologicalClosure _
  apply le_antisymm
  · haveI : M.Normal := normal_topologicalClosure_map_etaHom φ.ker
    intro z hz
    by_contra hzM
    obtain ⟨T, hTn, hTo, hMT, hzT⟩ := exists_open_normal_notMem hMcl hzM
    haveI := hTn
    haveI : Finite (completion (GrpCat.of G) ⧸ T) := Subgroup.quotient_finite_of_isOpen T hTo
    let ρ : G →* completion (GrpCat.of G) ⧸ T := (QuotientGroup.mk' T).comp (etaHom G)
    have hρ : φ.ker ≤ ρ.ker := by
      intro k hk
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hMT (Subgroup.le_topologicalClosure _ (Subgroup.mem_map_of_mem _ hk))
    let ρ' : Q →* completion (GrpCat.of G) ⧸ T :=
      (QuotientGroup.lift φ.ker ρ hρ).comp
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
    have hρ' : ρ'.comp φ = ρ := by
      ext x
      change QuotientGroup.lift φ.ker ρ hρ
        ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x)) = ρ x
      have : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) =
          (x : G ⧸ φ.ker) := by
        rw [MulEquiv.symm_apply_eq]; rfl
      rw [this]
      rfl
    have hlift : liftFinite ρ z = (z : completion (GrpCat.of G) ⧸ T) := by
      obtain ⟨w, hw, hwz⟩ := exists_etaFn_eq ρ (isOpen_setOf_mk_eq T hTo z) (z := z) rfl
      rw [← hwz]
      exact hw
    have h1 : liftFinite ρ z = 1 := by
      rw [← hρ', ← liftFinite_completionMap, MonoidHom.mem_ker.1 hz, map_one]
    rw [hlift, QuotientGroup.eq_one_iff] at h1
    exact hzT h1
  · refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      rw [MonoidHom.mem_ker, etaHom_apply, completionMap_eta, MonoidHom.mem_ker.1 hk]
      exact map_one (etaHom Q)
    · exact isClosed_singleton.preimage (continuous_completionMap φ)

variable (O : Subgroup (completion (GrpCat.of G)))
  (hO : IsOpen (O : Set (completion (GrpCat.of G))))

include hO in
/-- `η⁻¹(O)` has finite index for an open subgroup `O ⊆ Ĝ`. -/
lemma finiteIndex_comap_etaHom : (O.comap (etaHom G)).FiniteIndex := by
  haveI : Finite (completion (GrpCat.of G) ⧸ O) := Subgroup.quotient_finite_of_isOpen O hO
  have h := Subgroup.relIndex_comap_ne_zero (etaHom G) (J := O) (K := ⊤)
    (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  rw [Subgroup.comap_top, Subgroup.relIndex_top_right] at h
  exact ⟨h⟩

include hO in
lemma completionMap_subtype_mem (z : completion (GrpCat.of (O.comap (etaHom G)))) :
    completionMap (O.comap (etaHom G)).subtype z ∈ O := by
  have hcl : IsClosed ((completionMap (O.comap (etaHom G)).subtype) ⁻¹' (O : Set _)) :=
    (Subgroup.isClosed_of_isOpen O hO).preimage (continuous_completionMap _)
  have hz : z ∈ closure (Set.range (etaFn (GrpCat.of (O.comap (etaHom G))))) := by
    rw [(denseRange _).closure_range]; trivial
  refine closure_minimal ?_ hcl hz
  rintro _ ⟨h, rfl⟩
  change completionMap _ (etaFn _ h) ∈ O
  rw [completionMap_eta]
  exact h.2

include hO in
lemma completionMap_subtype_injective :
    Function.Injective (completionMap (O.comap (etaHom G)).subtype) := by
  set H := O.comap (etaHom G)
  haveI := finiteIndex_comap_etaHom O hO
  rw [injective_iff_map_eq_one]
  intro z hz
  refine eq_one_of_forall_liftFinite fun P _ _ ρ ↦ ?_
  haveI : Finite ρ.range := inferInstance
  haveI hK : ρ.ker.FiniteIndex := inferInstance
  have hK' : (ρ.ker.map H.subtype).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hK.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  set N := (ρ.ker.map H.subtype).normalCore
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let f₁ : H →* (π.comp H.subtype).range := (π.comp H.subtype).rangeRestrict
  have hle : (π.comp H.subtype).ker ≤ ρ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hh
    obtain ⟨k, hk, hkh⟩ := Subgroup.normalCore_le _ hh
    have : k = h := Subtype.ext hkh
    exact this ▸ hk
  let e := QuotientGroup.quotientKerEquivRange (π.comp H.subtype)
  let φ : (π.comp H.subtype).range →* P :=
    (QuotientGroup.lift _ ρ hle).comp e.symm.toMonoidHom
  have hφ : φ.comp f₁ = ρ := by
    ext h
    change QuotientGroup.lift _ ρ hle (e.symm (f₁ h)) = ρ h
    have : e.symm (f₁ h) = (h : H ⧸ (π.comp H.subtype).ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this]
    rfl
  have h1 : liftFinite (π.comp H.subtype) z = 1 := by
    rw [← liftFinite_completionMap, hz, map_one]
  have h2 : liftFinite f₁ z = 1 := by
    apply Subtype.ext
    rw [← Subgroup.coe_subtype, ← liftFinite_comp, MonoidHom.subtype_comp_rangeRestrict, h1]
    rfl
  rw [← hφ, liftFinite_comp, h2, map_one]

include hO in
lemma completionMap_subtype_surjective (o : O) :
    ∃ z, completionMap (O.comap (etaHom G)).subtype z = o := by
  set f := completionMap (O.comap (etaHom G)).subtype
  have hcl : IsClosed (Set.range f) := (isCompact_range (continuous_completionMap _)).isClosed
  suffices (o : completion (GrpCat.of G)) ∈ closure (Set.range f) by
    rw [hcl.closure_eq] at this
    exact this
  rw [mem_closure_iff]
  intro V hV hoV
  obtain ⟨g, hg⟩ := (denseRange (GrpCat.of G)).exists_mem_open (hV.inter hO) ⟨o, hoV, o.2⟩
  refine ⟨_, hg.1, etaFn _ (⟨g, hg.2⟩ : O.comap (etaHom G)), ?_⟩
  rw [completionMap_eta]
  rfl

/-- **`Ĥ ≃ₜ* O`** for an open subgroup `O ⊆ Ĝ` and `H = η⁻¹(O)`. -/
noncomputable def completionComapEquiv :
    completion (GrpCat.of (O.comap (etaHom G))) ≃ₜ* O := by
  let ψ : completion (GrpCat.of (O.comap (etaHom G))) →* O :=
    (completionMap (O.comap (etaHom G)).subtype).codRestrict O (completionMap_subtype_mem O hO)
  have hbij : Function.Bijective ψ := by
    refine ⟨fun a b hab ↦ completionMap_subtype_injective O hO (congrArg Subtype.val hab),
      fun o ↦ ?_⟩
    obtain ⟨z, hz⟩ := completionMap_subtype_surjective O hO o
    exact ⟨z, Subtype.ext hz⟩
  have hcont : Continuous ψ := (continuous_completionMap _).subtype_mk _
  let e := MulEquiv.ofBijective ψ hbij
  exact
    { e with
      continuous_toFun := hcont
      continuous_invFun := (hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

lemma coe_completionComapEquiv (z : completion (GrpCat.of (O.comap (etaHom G)))) :
    (completionComapEquiv O hO z : completion (GrpCat.of G)) =
      completionMap (O.comap (etaHom G)).subtype z := rfl

lemma completionComapEquiv_eta (h : O.comap (etaHom G)) :
    (completionComapEquiv O hO (etaFn _ h) : completion (GrpCat.of G)) =
      etaFn (GrpCat.of G) (h : G) := by
  rw [coe_completionComapEquiv, completionMap_eta]
  rfl

end Completion

end CurvesJacobian.Cusp
