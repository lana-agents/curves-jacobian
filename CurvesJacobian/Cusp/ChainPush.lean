/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.BelyiChain
import Belyi.Anabelian.ChainOpen

/-!
# Building `Π`-chains across `⋏` and `⋎` (MR8.5, group-theoretic half)

[AbsTopI] Definition 4.2 (iii) (`Topics in Absolute Anabelian Geometry I.txt` l.2950–3030): the
objects of a `Π`-chain are slim profinite groups `Π_j` with rigidifying homomorphisms
`ρ_j : Π ⊇ H_j → Π_j`, and each elementary operation is compatible with the `ρ_j`. In the Belyi
chain `X ⇝ V ⇝ Q ⇝ … ⇝ P ⇝ W ⇝ … ⇝ V ⇝ X` of [AbsTopII] Example 3.6 (ii)
(`Topics in Absolute Anabelian Geometry II.txt` l.4669–4680) the rigidifying homomorphism of
each object is *defined* from the previous one and the operation homomorphism (in the scheme
version: `ρ_W` is a lift of `ρ_P` through the finite étale `β : W → P`). This file provides these
constructions for an abstract cuspidal extension `E`:

* `ChainObj.domOf`, `ChainObj.rhoOn`: the part of `ρ_A` landing in an open subgroup of `Π_A`;
* `ChainObj.coverObj`: the target of an operation of type `⋏` along an open immersion
  `φ : G' ↪ Π_A` (`ρ = φ⁻¹ ∘ ρ_A`), with `ElemOp.ofCover`;
* `ChainObj.postObj`: the target of an operation of type `⋎` or `•` along `φ : Π_A → G'`
  (`ρ = φ ∘ ρ_A`), with `ElemOp.ofQuot`, `ElemOp.ofDecusp`;
* `ChainObj.push`: a chain object `B'` of another cuspidal extension `E'`, attached to a chain
  object `A` of `E` by an open immersion `j : Π_A ↪ Π_{E'}` over an open immersion
  `ι : G_{E'} ↪ G_E` (`ρ = ρ_{B'} ∘ j ∘ ρ_A`); `ElemOp.push` transports operations, where for
  `•` the cuspidal decomposition groups are matched by the hypothesis `CuspMatch A j`
  (every cusp of `E'` is commensurable with the image of a cusp of `E`);
* `OpPath`, `OpPath.toPiChain`: chains assembled by concatenating operations (`OpPath.append`),
  with their type-chains (`OpPath.kind_opN_append_left`, `OpPath.kind_opN_append_right`);
  `OpPath.belyiPath`, `OpPath.isBelyiType_belyiPath`: the type-chain `⋏, ⋎, •^l, ⋏, •^r, ⋎`;
  `OpPath.pushRun`: a whole `Π`-chain of `E'` (e.g. a run of `•`'s, `fillChain`) pushed to `E`.

Auxiliary group theory: `isOpen_map_of_isOpen_range` (image of an open subgroup under a
continuous homomorphism of a compact group with open range is open),
`isSlim_of_injective`, `Subgroup.Commensurable.map'`, `Subgroup.Commensurable.comap'`.
-/

open Pi1.Profinite
open scoped Pointwise

universe u

noncomputable section

namespace Belyi.Anabelian

section GroupTheory

variable {G H : Type*} [Group G] [Group H]

/-- If `J` has finite index in `K`, then `f(J)` has finite index in `f(K)`. -/
theorem Subgroup.relIndex_map_ne_zero (f : G →* H) {J K : Subgroup G} (h : J.relIndex K ≠ 0) :
    (J.map f).relIndex (K.map f) ≠ 0 := by
  have hJK : (J ⊓ K).relIndex K ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
  let fK : K →* K.map f := f.subgroupMap K
  have hsurj : Function.Surjective fK := f.subgroupMap_surjective K
  have hle : ((J ⊓ K).subgroupOf K).map fK ≤ (J.map f).subgroupOf (K.map f) := by
    rintro ⟨y, hy⟩ ⟨⟨x, hxK⟩, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf]
    have hx' : x ∈ J ⊓ K := hx
    have : f x = y := congrArg Subtype.val hxy
    exact ⟨x, hx'.1, this⟩
  have h1 : (((J ⊓ K).subgroupOf K).map fK).index ≠ 0 := fun h0 ↦
    hJK (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_map_dvd _ hsurj))
  exact fun h0 ↦ h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hle))

/-- Commensurability is preserved by images under homomorphisms. -/
theorem Subgroup.Commensurable.map' (f : G →* H) {J K : Subgroup G} (h : J.Commensurable K) :
    (J.map f).Commensurable (K.map f) :=
  ⟨Subgroup.relIndex_map_ne_zero f h.1, Subgroup.relIndex_map_ne_zero f h.2⟩

/-- Commensurability is preserved by preimages under homomorphisms. -/
theorem Subgroup.Commensurable.comap' (f : G →* H) {J K : Subgroup H} (h : J.Commensurable K) :
    (J.comap f).Commensurable (K.comap f) :=
  ⟨Subgroup.relIndex_comap_ne_zero f h.1, Subgroup.relIndex_comap_ne_zero f h.2⟩

/-- A subgroup commensurable with `⊥` is finite. -/
theorem Subgroup.finite_of_commensurable_bot {J : Subgroup G}
    (h : J.Commensurable ⊥) : (J : Set G).Finite := by
  have h1 : (⊥ : Subgroup G).relIndex J ≠ 0 := h.2
  rw [Subgroup.relIndex_bot_left] at h1
  haveI := Nat.finite_of_card_ne_zero h1
  exact Set.toFinite _

end GroupTheory

section Topology

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- An open subgroup of a compact group has finite index. -/
theorem finiteIndex_of_isOpen {O : Subgroup G} (hO : IsOpen (O : Set G)) : O.FiniteIndex := by
  haveI : DiscreteTopology (G ⧸ O) := QuotientGroup.discreteTopology_iff.2 hO
  haveI : Finite (G ⧸ O) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The image of an open subgroup under a continuous homomorphism of a compact group with open
range is open** (it is closed of finite index in the open range). -/
theorem isOpen_map_of_isOpen_range (f : G →ₜ* H) (hf : IsOpen (Set.range f)) {O : Subgroup G}
    (hO : IsOpen (O : Set G)) : IsOpen ((O.map (f : G →* H) : Subgroup H) : Set H) := by
  set R := (f : G →* H).range with hRdef
  have hR : IsOpen (R : Set H) := by
    rw [hRdef, MonoidHom.coe_range]
    exact hf
  haveI := finiteIndex_of_isOpen hO
  let f' : G →* R := (f : G →* H).rangeRestrict
  have hsurj : Function.Surjective f' := MonoidHom.rangeRestrict_surjective _
  have hM : (O.map (f : G →* H)).subgroupOf R = O.map f' := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  haveI : ((O.map (f : G →* H)).subgroupOf R).FiniteIndex := by
    rw [hM]
    exact ⟨fun h ↦ O.index_ne_zero_of_finite
      (Nat.eq_zero_of_zero_dvd (h ▸ O.index_map_dvd hsurj))⟩
  have hcl : IsClosed (((O.map (f : G →* H)) : Subgroup H) : Set H) := by
    have hc : IsCompact (O : Set G) :=
      (Subgroup.isClosed_of_isOpen O hO).isCompact
    have := (hc.image f.continuous).isClosed
    simpa using this
  have hopen : IsOpen (((O.map (f : G →* H)).subgroupOf R : Subgroup R) : Set R) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (hcl.preimage continuous_subtype_val)
  have := hR.isOpenMap_subtype_val _ hopen
  convert this using 1
  ext y
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hy
    obtain ⟨x, hxO, rfl⟩ := hy
    exact ⟨⟨f x, x, rfl⟩, ⟨x, hxO, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- An injective continuous homomorphism of a compact group into a slim group with open range has
slim source. -/
theorem isSlim_of_injective (f : G →ₜ* H) (hinj : Function.Injective f)
    (hf : IsOpen (Set.range f)) (hH : IsSlim H) : IsSlim G := by
  intro U z hz
  have hU := isOpen_map_of_isOpen_range f hf U.isOpen
  refine hinj ((hH ⟨_, hU⟩ (f z) ?_).trans (map_one f).symm)
  rintro _ ⟨x, hx, rfl⟩
  change f z * f x = f x * f z
  rw [← map_mul, ← map_mul, hz x hx]

/-- A continuous bijective homomorphism of a compact group onto a Hausdorff group is an
isomorphism of topological groups. -/
def continuousMulEquivOfBijective (f : G →ₜ* H) (hf : Function.Bijective f) : G ≃ₜ* H :=
  ContinuousMulEquiv.mk' (f.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hf)) (fun a b ↦ map_mul f a b)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
lemma continuousMulEquivOfBijective_apply (f : G →ₜ* H) (hf : Function.Bijective f) (x : G) :
    continuousMulEquivOfBijective f hf x = f x := rfl

/-- `G ≃ₜ*` the range of an injective continuous homomorphism of a compact group. -/
def rangeEquiv (f : G →ₜ* H) (hinj : Function.Injective f) : G ≃ₜ* (f : G →* H).range :=
  continuousMulEquivOfBijective
    ⟨(f : G →* H).rangeRestrict, f.continuous.subtype_mk _⟩
    ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective _⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
lemma coe_rangeEquiv_apply (f : G →ₜ* H) (hinj : Function.Injective f) (x : G) :
    (rangeEquiv f hinj x : H) = f x := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
lemma apply_rangeEquiv_symm (f : G →ₜ* H) (hinj : Function.Injective f)
    (y : (f : G →* H).range) : f ((rangeEquiv f hinj).symm y) = y := by
  conv_rhs => rw [← (rangeEquiv f hinj).apply_symm_apply y]
  rfl

end Topology

/-! ### Chain objects defined from a previous one -/

namespace ChainObj

variable {E : CuspidalExt.{u}} (A : ChainObj E)

lemma le_commensurator_self' {G : Type*} [Group G] (H : Subgroup G) :
    H ≤ Subgroup.Commensurable.commensurator H := by
  intro γ hγ
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have e : ConjAct.toConjAct γ • H = H := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv]
    constructor
    · intro hx
      have := mul_mem (mul_mem hγ hx) (inv_mem hγ)
      simpa [mul_assoc] using this
    · intro hx
      exact mul_mem (mul_mem (inv_mem hγ) hx) hγ
  rw [e]

/-- The image of `I ⊆ Π` lies in `Δ_A` if `I ⊆ Δ`. -/
lemma image_le_Delta {I : Subgroup E.Pi} (hI : I ≤ E.Delta) : A.image I ≤ A.Delta := by
  rintro _ ⟨h, hh, rfl⟩
  change A.toG (A.rho h) = 1
  rw [A.toG_rho]
  exact hI hh

/-- `ρ_A` maps commensurable subgroups of `Π` to commensurable subgroups. -/
lemma image_commensurable {I J : Subgroup E.Pi} (h : I.Commensurable J) :
    (A.image I).Commensurable (A.image J) :=
  Subgroup.Commensurable.map' _ (Subgroup.Commensurable.comap' (A.dom : Subgroup E.Pi).subtype h)

/-- `{h ∈ H_A | ρ_A(h) ∈ O}` for an open subgroup `O ⊆ Π_A`: an open subgroup of `Π`. -/
def domOf (O : Subgroup A.grp) (hO : IsOpen (O : Set A.grp)) : OpenSubgroup E.Pi where
  toSubgroup := (O.comap (A.rho : (A.dom : Subgroup E.Pi) →* A.grp)).map
    (A.dom : Subgroup E.Pi).subtype
  isOpen' := by
    have h1 : IsOpen ((A.rho : ↥(A.dom : Subgroup E.Pi) → A.grp) ⁻¹' (O : Set A.grp)) :=
      hO.preimage A.rho.continuous
    have := A.dom.isOpen.isOpenMap_subtype_val _ h1
    convert this using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩

variable {A} in
lemma domOf_le {O : Subgroup A.grp} (hO : IsOpen (O : Set A.grp)) :
    (A.domOf O hO : Subgroup E.Pi) ≤ A.dom := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

variable {A} in
lemma domOf_mono {O O' : Subgroup A.grp} (hO : IsOpen (O : Set A.grp))
    (hO' : IsOpen (O' : Set A.grp)) (h : O ≤ O') :
    (A.domOf O hO : Subgroup E.Pi) ≤ A.domOf O' hO' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

variable {A} in
lemma rho_inclusion_mem {O : Subgroup A.grp} (hO : IsOpen (O : Set A.grp))
    (h : (A.domOf O hO : Subgroup E.Pi)) :
    A.rho (Subgroup.inclusion (domOf_le hO) h) ∈ O := by
  obtain ⟨x, hx, hxh⟩ := h.2
  have : Subgroup.inclusion (domOf_le hO) h = x := Subtype.ext hxh.symm
  rw [this]
  exact hx

variable {A} in
lemma mem_domOf {O : Subgroup A.grp} (hO : IsOpen (O : Set A.grp)) (x : (A.dom : Subgroup E.Pi))
    (hx : A.rho x ∈ O) : (x : E.Pi) ∈ (A.domOf O hO : Subgroup E.Pi) :=
  ⟨x, hx, rfl⟩

/-- `ρ_A` on `domOf O`, with values in `O`. -/
def rhoOn (O : Subgroup A.grp) (hO : IsOpen (O : Set A.grp)) :
    (A.domOf O hO : Subgroup E.Pi) →ₜ* O where
  toMonoidHom := ((A.rho : (A.dom : Subgroup E.Pi) →* A.grp).comp
    (Subgroup.inclusion (domOf_le hO))).codRestrict O (rho_inclusion_mem hO)
  continuous_toFun := (A.rho.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

@[simp]
lemma coe_rhoOn (O : Subgroup A.grp) (hO : IsOpen (O : Set A.grp))
    (h : (A.domOf O hO : Subgroup E.Pi)) :
    (A.rhoOn O hO h : A.grp) = A.rho (Subgroup.inclusion (domOf_le hO) h) := rfl

lemma isOpen_coe_range {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (f : G →ₜ* H) (hf : IsOpen (Set.range f)) :
    IsOpen (((f : G →* H).range : Subgroup H) : Set H) := by
  rw [MonoidHom.coe_range]
  exact hf

lemma compactSpace_ker {G H : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [Group H]
    [TopologicalSpace H] [T2Space H] (f : G →ₜ* H) : CompactSpace (f : G →* H).ker :=
  isCompact_iff_compactSpace.mp
    ((isClosed_singleton.preimage f.continuous : IsClosed ((f : G → H) ⁻¹' {1}))).isCompact

/-! #### Operations of type `⋏` -/

section Cover

variable {G' : ProfiniteGrp.{u}} (φ : G' →ₜ* A.grp) (hinj : Function.Injective φ)
  (hopen : IsOpen (Set.range φ))

/-- **The target of an operation of type `⋏`** along an open immersion `φ : G' ↪ Π_A`:
`Π' = G'`, `ρ' = φ⁻¹ ∘ ρ_A` (on `ρ_A⁻¹(φ(G'))`), `G' → Π_A → G`. -/
def coverObj : ChainObj E where
  grp := G'
  dom := A.domOf (φ : G' →* A.grp).range (isOpen_coe_range φ hopen)
  rho := (ContinuousMonoidHom.toContinuousMonoidHom (rangeEquiv φ hinj).symm).comp
    (A.rhoOn _ (isOpen_coe_range φ hopen))
  isOpen_range_rho := by
    convert A.isOpen_range_rho.preimage φ.continuous using 1
    ext g
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨Subgroup.inclusion (domOf_le _) h, ?_⟩
      change _ = φ ((rangeEquiv φ hinj).symm (A.rhoOn _ _ h))
      rw [apply_rangeEquiv_symm, coe_rhoOn]
    · rintro ⟨x, hx⟩
      refine ⟨⟨x, mem_domOf _ x ⟨g, hx.symm⟩⟩, ?_⟩
      apply hinj
      change φ ((rangeEquiv φ hinj).symm (A.rhoOn _ _ _)) = φ g
      rw [apply_rangeEquiv_symm, coe_rhoOn]
      exact hx
  toG := A.toG.comp φ
  isOpen_range_toG := by
    convert isOpen_map_of_isOpen_range A.toG A.isOpen_range_toG
      (isOpen_coe_range φ hopen) using 1
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨φ g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  toG_rho h := by
    change A.toG (φ ((rangeEquiv φ hinj).symm (A.rhoOn _ _ h))) = _
    rw [apply_rangeEquiv_symm, coe_rhoOn, A.toG_rho]
    rfl
  slim_delta := by
    haveI := compactSpace_ker (A.toG.comp φ)
    let ψ : ((A.toG.comp φ : G' →ₜ* E.G) : G' →* E.G).ker →ₜ* A.Delta :=
      { toFun := fun x ↦ ⟨φ x.1, x.2⟩
        map_one' := Subtype.ext (map_one φ)
        map_mul' := fun a b ↦ Subtype.ext (map_mul φ a.1 b.1)
        continuous_toFun := (φ.continuous.comp continuous_subtype_val).subtype_mk _ }
    refine isSlim_of_injective ψ (fun a b h ↦ Subtype.ext (hinj (congrArg Subtype.val h))) ?_
      A.slim_delta
    convert hopen.preimage (continuous_subtype_val : Continuous (Subtype.val : A.Delta → A.grp))
      using 1
    ext d
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨g, hg⟩
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      change A.toG (φ g) = 1
      rw [hg]
      exact d.2
  nontrivial_delta := by
    have hne := IsSlim.subgroupOf_ne_bot A.slim_delta A.nontrivial_delta
      (isOpen_coe_range φ hopen)
    intro hbot
    apply hne
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    rintro ⟨_, g, rfl⟩ hd
    have : g = 1 := hbot g hd
    subst this
    exact Subtype.ext (map_one φ)

lemma coverObj_grp : (A.coverObj φ hinj hopen).grp = G' := rfl

lemma coverObj_toG : (A.coverObj φ hinj hopen).toG = A.toG.comp φ := rfl

lemma apply_coverObj_rho (h) : φ ((A.coverObj φ hinj hopen).rho h) =
    A.rho (Subgroup.inclusion (domOf_le (isOpen_coe_range φ hopen)) h) := by
  change φ ((rangeEquiv φ hinj).symm (A.rhoOn _ _ h)) = _
  rw [apply_rangeEquiv_symm, coe_rhoOn]

/-- The images of subgroups of `Π` in the target of `⋏` are the preimages under `φ`. -/
lemma image_coverObj (I : Subgroup E.Pi) :
    (A.coverObj φ hinj hopen).image I = (A.image I).comap (φ : G' →* A.grp) := by
  ext g
  simp only [ChainObj.image, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨Subgroup.inclusion (domOf_le (isOpen_coe_range φ hopen)) h, hh,
      (apply_coverObj_rho A φ hinj hopen h).symm⟩
  · rintro ⟨x, hx, hxg⟩
    refine ⟨⟨x, mem_domOf (isOpen_coe_range φ hopen) x ⟨g, hxg.symm⟩⟩, hx, ?_⟩
    apply hinj
    exact (apply_coverObj_rho A φ hinj hopen _).trans hxg

end Cover

/-! #### Operations of type `⋎` and `•` -/

section Post

variable {G' : ProfiniteGrp.{u}} (φ : A.grp →ₜ* G') (hopen : IsOpen (Set.range φ))
  (toG' : G' →ₜ* E.G) (htoG : ∀ x, toG' (φ x) = A.toG x) (hG' : IsOpen (Set.range toG'))
  (hslim : IsSlim (toG' : G' →* E.G).ker) (hne : (toG' : G' →* E.G).ker ≠ ⊥)

/-- **The target of an operation of type `⋎` or `•`** along `φ : Π_A → G'` (open range):
`ρ' = φ ∘ ρ_A`, with a given projection `G' → G` compatible with `Π_A → G`. -/
def postObj : ChainObj E where
  grp := G'
  dom := A.dom
  rho := φ.comp A.rho
  isOpen_range_rho := by
    convert isOpen_map_of_isOpen_range φ hopen (isOpen_coe_range A.rho A.isOpen_range_rho)
      using 1
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨A.rho h, ⟨h, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, rfl⟩
  toG := toG'
  isOpen_range_toG := hG'
  toG_rho h := by
    change toG' (φ (A.rho h)) = _
    rw [htoG, A.toG_rho]
  slim_delta := hslim
  nontrivial_delta := hne

lemma postObj_rho : (A.postObj φ hopen toG' htoG hG' hslim hne).rho = φ.comp A.rho := rfl

lemma image_postObj (I : Subgroup E.Pi) :
    (A.postObj φ hopen toG' htoG hG' hslim hne).image I = (A.image I).map (φ : A.grp →* G') := by
  rw [ChainObj.image, ChainObj.image, Subgroup.map_map]
  rfl

end Post

/-! #### Chain objects of another cuspidal extension -/

section Push

variable {E' : CuspidalExt.{u}} (j : A.grp →ₜ* E'.Pi) (hj : IsOpen (Set.range j))
  (ι : E'.G →ₜ* E.G) (hι : Function.Injective ι) (hιo : IsOpen (Set.range ι))
  (hcomp : ∀ x, ι (E'.pr (j x)) = A.toG x)

lemma isOpen_comap_dom (B' : ChainObj E') :
    IsOpen (((B'.dom : Subgroup E'.Pi).comap (j : A.grp →* E'.Pi) : Subgroup A.grp) :
      Set A.grp) :=
  B'.dom.isOpen.preimage j.continuous

/-- `j ∘ ρ_A` on `domOf (j⁻¹ H_{B'})`, with values in `H_{B'}`. -/
def jOn (B' : ChainObj E') :
    (A.domOf _ (A.isOpen_comap_dom j B') : Subgroup E.Pi) →ₜ* (B'.dom : Subgroup E'.Pi) :=
  (⟨(j : A.grp →* E'.Pi).subgroupComap (B'.dom : Subgroup E'.Pi),
    (j.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
      ((B'.dom : Subgroup E'.Pi).comap (j : A.grp →* E'.Pi) : Subgroup A.grp) →ₜ*
        (B'.dom : Subgroup E'.Pi)).comp (A.rhoOn _ (A.isOpen_comap_dom j B'))

@[simp]
lemma coe_jOn (B' : ChainObj E') (h) :
    (A.jOn j B' h : E'.Pi) = j (A.rho (Subgroup.inclusion (domOf_le _) h)) := rfl

include hι in
lemma ker_comp_of_injective (B' : ChainObj E') :
    ((ι.comp B'.toG : B'.grp →ₜ* E.G) : B'.grp →* E.G).ker = (B'.toG : B'.grp →* E'.G).ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  change ι (B'.toG x) = 1 ↔ B'.toG x = 1
  exact map_eq_one_iff ι hι

/-- **A chain object of `E'` as a chain object of `E`**, along an open immersion-like
`j : Π_A → Π_{E'}` over `ι : G_{E'} ↪ G_E`: `ρ = ρ_{B'} ∘ j ∘ ρ_A`, `Π → G` via `ι`. -/
def push (B' : ChainObj E') : ChainObj E where
  grp := B'.grp
  dom := A.domOf _ (A.isOpen_comap_dom j B')
  rho := B'.rho.comp (A.jOn j B')
  isOpen_range_rho := by
    haveI : CompactSpace (B'.dom : Subgroup E'.Pi) :=
      isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ B'.dom.isOpen).isCompact
    -- the subgroup `H_{B'} ∩ j(ρ_A(H_A))` of `H_{B'}`
    let S : Subgroup (B'.dom : Subgroup E'.Pi) :=
      (((A.rho : (A.dom : Subgroup E.Pi) →* A.grp).range.map (j : A.grp →* E'.Pi))).comap
        (B'.dom : Subgroup E'.Pi).subtype
    have hS : IsOpen (S : Set (B'.dom : Subgroup E'.Pi)) :=
      (isOpen_map_of_isOpen_range j hj (isOpen_coe_range A.rho A.isOpen_range_rho)).preimage
        continuous_subtype_val
    convert isOpen_map_of_isOpen_range B'.rho B'.isOpen_range_rho hS using 1
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, Subgroup.mem_comap,
      MonoidHom.mem_range, S]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨A.jOn j B' h, ⟨_, ⟨_, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨_, ⟨x, rfl⟩, hxz⟩, rfl⟩
      have hx : A.rho x ∈ ((B'.dom : Subgroup E'.Pi).comap (j : A.grp →* E'.Pi)) := by
        change j (A.rho x) ∈ (B'.dom : Subgroup E'.Pi)
        rw [show j (A.rho x) = (z : E'.Pi) from hxz]
        exact z.2
      have e : A.jOn j B' ⟨x, mem_domOf (A.isOpen_comap_dom j B') x hx⟩ = z := Subtype.ext hxz
      exact ⟨⟨x, mem_domOf (A.isOpen_comap_dom j B') x hx⟩, congrArg B'.rho e⟩
  toG := ι.comp B'.toG
  isOpen_range_toG := by
    convert isOpen_map_of_isOpen_range ι hιo (isOpen_coe_range B'.toG B'.isOpen_range_toG)
      using 1
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨B'.toG g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  toG_rho h := by
    change ι (B'.toG (B'.rho (A.jOn j B' h))) = _
    rw [B'.toG_rho, coe_jOn, hcomp, A.toG_rho]
    rfl
  slim_delta := (ker_comp_of_injective ι hι B').symm ▸ B'.slim_delta
  nontrivial_delta := (ker_comp_of_injective ι hι B').symm ▸ B'.nontrivial_delta

lemma push_Delta (B' : ChainObj E') :
    (A.push j hj ι hι hιo hcomp B').Delta = B'.Delta :=
  ker_comp_of_injective ι hι B'

lemma push_deltaNormalClosure (B' : ChainObj E') (C : Subgroup B'.grp) :
    (A.push j hj ι hι hιo hcomp B').deltaNormalClosure C = B'.deltaNormalClosure C := by
  unfold deltaNormalClosure
  rw [push_Delta]
  rfl

lemma push_rho_apply (B' : ChainObj E') (h) :
    (A.push j hj ι hι hιo hcomp B').rho h = B'.rho (A.jOn j B' h) := rfl

lemma image_push (B' : ChainObj E') (I : Subgroup E.Pi) :
    (A.push j hj ι hι hιo hcomp B').image I = B'.image ((A.image I).map (j : A.grp →* E'.Pi)) := by
  ext y
  simp only [ChainObj.image, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨A.jOn j B' h, ⟨_, ⟨Subgroup.inclusion (domOf_le _) h, hh, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨_, ⟨x, hx, rfl⟩, hxz⟩, rfl⟩
    have hx' : A.rho x ∈ ((B'.dom : Subgroup E'.Pi).comap (j : A.grp →* E'.Pi)) := by
      change j (A.rho x) ∈ (B'.dom : Subgroup E'.Pi)
      rw [show j (A.rho x) = (z : E'.Pi) from hxz]
      exact z.2
    have e : A.jOn j B' ⟨x, mem_domOf (A.isOpen_comap_dom j B') x hx'⟩ = z := Subtype.ext hxz
    exact ⟨⟨x, mem_domOf (A.isOpen_comap_dom j B') x hx'⟩, hx, congrArg B'.rho e⟩

/-- **Matching of cusps**: every cuspidal decomposition group of `E'` is commensurable with the
image under `j ∘ ρ_A` of a cuspidal decomposition group of `E`. -/
def CuspMatch : Prop :=
  ∀ I' ∈ E'.cusps, ∃ I ∈ E.cusps, ((A.image I).map (j : A.grp →* E'.Pi)).Commensurable I'

variable {A j hj ι hι hιo hcomp}

lemma Compat.push {B₁ B₂ : ChainObj E'} {φ : B₁.grp →ₜ* B₂.grp} (h : Compat B₁ B₂ φ) :
    Compat (A.push j hj ι hι hιo hcomp B₁) (A.push j hj ι hι hιo hcomp B₂) φ := by
  obtain ⟨H, h₁, h₂, hφ⟩ := h
  have hH : IsOpen (((H : Subgroup E'.Pi).comap (j : A.grp →* E'.Pi) : Subgroup A.grp) :
      Set A.grp) := H.isOpen.preimage j.continuous
  refine ⟨A.domOf _ hH, domOf_mono hH (A.isOpen_comap_dom j B₁) (Subgroup.comap_mono h₁),
    domOf_mono hH (A.isOpen_comap_dom j B₂) (Subgroup.comap_mono h₂), fun h hh ↦ ?_⟩
  change φ (B₁.rho (A.jOn j B₁ _)) = B₂.rho (A.jOn j B₂ _)
  have hmem : (j (A.rho (Subgroup.inclusion (domOf_le hH) ⟨h, hh⟩))) ∈ (H : Subgroup E'.Pi) :=
    rho_inclusion_mem hH ⟨h, hh⟩
  exact hφ _ hmem

lemma InTorsionFreeNormalOpen.push {B' : ChainObj E'} {C : Subgroup B'.grp}
    (h : B'.InTorsionFreeNormalOpen C) :
    (A.push j hj ι hι hιo hcomp B').InTorsionFreeNormalOpen C := by
  unfold InTorsionFreeNormalOpen
  rw [push_Delta]
  exact h

lemma IsCuspidal.push (hc : A.CuspMatch j) {B' : ChainObj E'} {C : Subgroup B'.grp}
    (h : B'.IsCuspidal C) (tf : B'.InTorsionFreeNormalOpen C) :
    (A.push j hj ι hι hιo hcomp B').IsCuspidal C := by
  obtain ⟨I', hI', hne, rfl⟩ := h
  obtain ⟨I, hI, hcomm⟩ := hc I' hI'
  have h' : ((A.push j hj ι hι hιo hcomp B').image I).Commensurable (B'.image I') := by
    rw [image_push]
    exact B'.image_commensurable hcomm
  refine ⟨I, hI, fun hbot ↦ hne ?_, ?_⟩
  · rw [hbot] at h'
    have hfin := Subgroup.finite_of_commensurable_bot h'.symm
    obtain ⟨N, -, hCN, -, -, htf⟩ := tf
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine htf x (hCN ⟨le_commensurator_self' _ hx,
      B'.image_le_Delta (E'.cusps_le I' hI') hx⟩) ?_
    haveI : Finite (B'.image I') := hfin.to_subtype
    have := isOfFinOrder_of_finite (⟨x, hx⟩ : B'.image I')
    exact (B'.image I').subtype.isOfFinOrder this
  · rw [push_Delta, Subgroup.Commensurable.eq h']
    rfl

/-- **An operation of `E'`-chain objects as an operation of the pushed `E`-chain objects.** -/
def _root_.Belyi.Anabelian.ElemOp.push (hc : A.CuspMatch j) {B₁ B₂ : ChainObj E'} :
    ElemOp B₁ B₂ → ElemOp (A.push j hj ι hι hιo hcomp B₁) (A.push j hj ι hι hιo hcomp B₂)
  | .cover φ inj op compat => .cover φ inj op compat.push
  | .quot φ inj op compat => .quot φ inj op compat.push
  | .decusp φ surj C cusp tf ker compat =>
      .decusp φ surj C (cusp.push hc tf) tf.push
        (by rw [push_deltaNormalClosure]; exact ker) compat.push
  | .deorb φ surj F le fin ker compat =>
      .deorb φ surj F (by rw [push_Delta]; exact le) fin ker compat.push

lemma _root_.Belyi.Anabelian.ElemOp.kind_push (hc : A.CuspMatch j) {B₁ B₂ : ChainObj E'}
    (o : ElemOp B₁ B₂) : (o.push (hj := hj) (hι := hι) (hιo := hιo) (hcomp := hcomp) hc).kind =
      o.kind := by
  cases o <;> rfl

end Push

end ChainObj

/-! ### The elementary operations into the new objects -/

namespace ElemOp

variable {E : CuspidalExt.{u}} (A : ChainObj E) {G' : ProfiniteGrp.{u}}

/-- The operation `A ⇝ coverObj` of type `⋏`. -/
def ofCover (φ : G' →ₜ* A.grp) (hinj : Function.Injective φ) (hopen : IsOpen (Set.range φ)) :
    ElemOp A (A.coverObj φ hinj hopen) :=
  .cover φ hinj hopen ⟨_, le_rfl, ChainObj.domOf_le (ChainObj.isOpen_coe_range φ hopen), fun h hh ↦
    A.apply_coverObj_rho φ hinj hopen ⟨h, hh⟩⟩

lemma kind_ofCover (φ : G' →ₜ* A.grp) (hinj : Function.Injective φ)
    (hopen : IsOpen (Set.range φ)) : (ofCover A φ hinj hopen).kind = .cover := rfl

variable (φ : A.grp →ₜ* G') (hopen : IsOpen (Set.range φ))
  (toG' : G' →ₜ* E.G) (htoG : ∀ x, toG' (φ x) = A.toG x) (hG' : IsOpen (Set.range toG'))
  (hslim : IsSlim (toG' : G' →* E.G).ker) (hne : (toG' : G' →* E.G).ker ≠ ⊥)

lemma compat_postObj :
    ChainObj.Compat A (A.postObj φ hopen toG' htoG hG' hslim hne) φ :=
  ⟨A.dom, le_rfl, le_rfl, fun _ _ ↦ rfl⟩

/-- The operation `A ⇝ postObj` of type `⋎` (for injective `φ`). -/
def ofQuot (hinj : Function.Injective φ) :
    ElemOp A (A.postObj φ hopen toG' htoG hG' hslim hne) :=
  .quot φ hinj hopen (compat_postObj A φ hopen toG' htoG hG' hslim hne)

lemma kind_ofQuot (hinj : Function.Injective φ) :
    (ofQuot A φ hopen toG' htoG hG' hslim hne hinj).kind = .quot := rfl

/-- The operation `A ⇝ postObj` of type `•` (for surjective `φ` with kernel topologically
normally generated in `Δ` by a cuspidal decomposition group `C` of `A`). -/
def ofDecusp (hsurj : Function.Surjective φ) (C : Subgroup A.grp) (cusp : A.IsCuspidal C)
    (tf : A.InTorsionFreeNormalOpen C)
    (ker : (φ : A.grp →* G').ker = A.deltaNormalClosure C) :
    ElemOp A (A.postObj φ hopen toG' htoG hG' hslim hne) :=
  .decusp φ hsurj C cusp tf ker (compat_postObj A φ hopen toG' htoG hG' hslim hne)

end ElemOp

/-! ### Chains as concatenations of operations -/

/-- A finite sequence of elementary operations `A ⇝ … ⇝ C`. -/
inductive OpPath {E : CuspidalExt.{u}} : ChainObj E → ChainObj E → Type (u + 1)
  | nil (A : ChainObj E) : OpPath A A
  | cons {A B C : ChainObj E} (o : ElemOp A B) (p : OpPath B C) : OpPath A C

namespace OpPath

variable {E : CuspidalExt.{u}}

/-- The number of operations. -/
def length : {A C : ChainObj E} → OpPath A C → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ p => p.length + 1

/-- The `n`-th object (the source for `n = 0`). -/
def objN : ℕ → {A C : ChainObj E} → OpPath A C → ChainObj E
  | 0, A, _, _ => A
  | n + 1, A, _, p => match p with
    | nil _ => A
    | cons _ q => objN n q

/-- The `j`-th operation `objN j ⇝ objN (j + 1)`. -/
def opN : (j : ℕ) → {A C : ChainObj E} → (p : OpPath A C) → j < p.length →
    ElemOp (p.objN j) (p.objN (j + 1))
  | 0, _, _, cons o _, _ => o
  | j + 1, _, _, cons _ q, h => opN j q (by simp only [length] at h; omega)
  | _, _, _, nil _, h => absurd h (by simp [length])

/-- Concatenation. -/
def append : {A B C : ChainObj E} → OpPath A B → OpPath B C → OpPath A C
  | _, _, _, nil _, q => q
  | _, _, _, cons o p, q => cons o (append p q)

lemma length_append {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append, length]
  | cons o p ih => simp only [append, length, ih]; omega

lemma kind_opN_append_left {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (j : ℕ)
    (h : j < p.length) (h' : j < (p.append q).length) :
    ((p.append q).opN j h').kind = (p.opN j h).kind := by
  induction p generalizing j with
  | nil => simp [length] at h
  | cons o p ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih q j (by simp only [length] at h; omega) _

lemma kind_opN_append_right' {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (j k : ℕ)
    (hk : k = p.length + j) (h : j < q.length) (h' : k < (p.append q).length) :
    ((p.append q).opN k h').kind = (q.opN j h).kind := by
  induction p generalizing k with
  | nil =>
    obtain rfl : k = j := by simp only [length] at hk; omega
    rfl
  | cons o p ih =>
    obtain rfl : k = (p.length + j) + 1 := by simp only [length] at hk; omega
    exact ih q (p.length + j) rfl h _

lemma kind_opN_append_right {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (j : ℕ)
    (h : j < q.length) (h' : p.length + j < (p.append q).length) :
    ((p.append q).opN (p.length + j) h').kind = (q.opN j h).kind :=
  kind_opN_append_right' p q j _ rfl h h'

/-- A single operation. -/
def single {A B : ChainObj E} (o : ElemOp A B) : OpPath A B := cons o (nil B)

lemma length_single {A B : ChainObj E} (o : ElemOp A B) : (single o).length = 1 := rfl

lemma kind_opN_single {A B : ChainObj E} (o : ElemOp A B) (h : 0 < (single o).length) :
    ((single o).opN 0 h).kind = o.kind := rfl

/-- The path of a sequence of operations `f 0 ⇝ f 1 ⇝ … ⇝ f r`. -/
def ofSeq : (r : ℕ) → (f : (i : ℕ) → i ≤ r → ChainObj E) →
    (∀ i (h : i < r), ElemOp (f i h.le) (f (i + 1) h)) → OpPath (f 0 (Nat.zero_le r)) (f r le_rfl)
  | 0, f, _ => nil (f 0 le_rfl)
  | r + 1, f, g =>
    (ofSeq r (fun i h ↦ f i (h.trans (Nat.le_succ r)))
      (fun i h ↦ g i (h.trans (Nat.lt_succ_self r)))).append
      (single (g r (Nat.lt_succ_self r)))

lemma length_ofSeq : ∀ (r : ℕ) (f : (i : ℕ) → i ≤ r → ChainObj E)
    (g : ∀ i (h : i < r), ElemOp (f i h.le) (f (i + 1) h)), (ofSeq r f g).length = r
  | 0, _, _ => rfl
  | r + 1, f, g => by
    rw [ofSeq, length_append, length_ofSeq r, length_single]

lemma kind_opN_ofSeq : ∀ (r : ℕ) (f : (i : ℕ) → i ≤ r → ChainObj E)
    (g : ∀ i (h : i < r), ElemOp (f i h.le) (f (i + 1) h)) (i : ℕ) (h : i < r)
    (h' : i < (ofSeq r f g).length), ((ofSeq r f g).opN i h').kind = (g i h).kind
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | r + 1, f, g, i, h, h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hi | rfl
    · exact (kind_opN_append_left
        (ofSeq r (fun i h ↦ f i (h.trans (Nat.le_succ r)))
          (fun i h ↦ g i (h.trans (Nat.lt_succ_self r))))
        (single (g r (Nat.lt_succ_self r))) i (by rw [length_ofSeq]; exact hi) h').trans
        (kind_opN_ofSeq r _ _ i hi _)
    · exact kind_opN_append_right'
        (ofSeq i (fun k h ↦ f k (h.trans (Nat.le_succ i)))
          (fun k h ↦ g k (h.trans (Nat.lt_succ_self i))))
        (single (g i (Nat.lt_succ_self i))) 0 i (by rw [length_ofSeq, Nat.add_zero]) Nat.one_pos h'

/-- **The `Π`-chain of a path starting at the trivial object.** -/
def toPiChain {C : ChainObj E} (p : OpPath (ChainObj.base E) C) : PiChain E where
  len := p.length
  obj i := p.objN i.val
  obj_zero := ⟨ContinuousMulEquiv.refl _, ⊤, le_rfl, le_rfl, fun _ _ ↦ rfl⟩
  op j := p.opN j.val j.isLt

lemma toPiChain_len {C : ChainObj E} (p : OpPath (ChainObj.base E) C) :
    p.toPiChain.len = p.length := rfl

lemma kind_opN_toPiChain {C : ChainObj E} (p : OpPath (ChainObj.base E) C) (j : ℕ)
    (h : j < p.toPiChain.len) : (p.toPiChain.opN j h).kind = (p.opN j h).kind := rfl

lemma kind_opN_cons {A B C : ChainObj E} (o : ElemOp A B) (p : OpPath B C) (j k : ℕ)
    (hk : k = j + 1) (h : j < p.length) (h' : k < (cons o p).length) :
    ((cons o p).opN k h').kind = (p.opN j h).kind := by
  subst hk
  rfl

/-- **The Belyi path** `⋏, ⋎, (run), ⋏, (run), ⋎` ([AbsTopII] Example 3.6 (ii)). -/
def belyiPath {A₁ A₂ A₃ A₄ A₅ A₆ : ChainObj E} (o₁ : ElemOp (ChainObj.base E) A₁)
    (o₂ : ElemOp A₁ A₂) (r₁ : OpPath A₂ A₃) (o₃ : ElemOp A₃ A₄) (r₂ : OpPath A₄ A₅)
    (o₄ : ElemOp A₅ A₆) : OpPath (ChainObj.base E) A₆ :=
  cons o₁ (cons o₂ (r₁.append (cons o₃ (r₂.append (single o₄)))))

/-- The `Π`-chain of a Belyi path is of Belyi type. -/
theorem isBelyiType_belyiPath {A₁ A₂ A₃ A₄ A₅ A₆ : ChainObj E}
    (o₁ : ElemOp (ChainObj.base E) A₁) (o₂ : ElemOp A₁ A₂) (r₁ : OpPath A₂ A₃)
    (o₃ : ElemOp A₃ A₄) (r₂ : OpPath A₄ A₅) (o₄ : ElemOp A₅ A₆) (h₁ : o₁.kind = .cover)
    (h₂ : o₂.kind = .quot) (hr₁ : ∀ j (h : j < r₁.length), (r₁.opN j h).kind = .decusp)
    (h₃ : o₃.kind = .cover) (hr₂ : ∀ j (h : j < r₂.length), (r₂.opN j h).kind = .decusp)
    (h₄ : o₄.kind = .quot) :
    (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).toPiChain.IsBelyiType r₁.length r₂.length := by
  have hlen : (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).length = r₁.length + r₂.length + 4 := by
    simp only [belyiPath, length, length_append, length_single]
    omega
  have k2 : ∀ n (hn : n + 2 < (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).toPiChain.len)
      (hn' : n < (r₁.append (cons o₃ (r₂.append (single o₄)))).length),
      ((belyiPath o₁ o₂ r₁ o₃ r₂ o₄).toPiChain.opN (n + 2) hn).kind =
        ((r₁.append (cons o₃ (r₂.append (single o₄)))).opN n hn').kind :=
    fun n _ _ ↦ rfl
  have hTlen : (r₁.append (cons o₃ (r₂.append (single o₄)))).length =
      r₁.length + r₂.length + 2 := by
    simp only [length, length_append, length_single]
    omega
  have hlen' : (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).toPiChain.len = r₁.length + r₂.length + 4 := hlen
  have hl1 : (r₂.append (single o₄)).length = r₂.length + 1 := by
    rw [length_append, length_single]
  unfold PiChain.IsBelyiType
  refine ⟨hlen, h₁, h₂, fun s hs ↦ ?_, ?_, fun s hs ↦ ?_, ?_⟩
  · rw [PiChain.kind_opN_congr _ (show 2 + s = s + 2 by omega) _ (by omega),
      k2 s _ (by omega)]
    exact (kind_opN_append_left _ _ s hs _).trans (hr₁ s hs)
  · rw [PiChain.kind_opN_congr _ (show r₁.length + 2 = r₁.length + 2 by rfl) _ (by omega),
      k2 _ _ (by omega)]
    exact (kind_opN_append_right' r₁ _ 0 r₁.length (by omega)
      (by simp only [length]; omega) _).trans h₃
  · rw [PiChain.kind_opN_congr _ (show r₁.length + 3 + s = (r₁.length + 1 + s) + 2 by omega) _
      (by omega), k2 _ _ (by omega)]
    exact (kind_opN_append_right' r₁ _ (s + 1) _ (by omega) (by simp only [length]; omega)
      _).trans ((kind_opN_cons o₃ _ s (s + 1) rfl (by omega) _).trans
        ((kind_opN_append_left r₂ _ s hs _).trans (hr₂ s hs)))
  · rw [PiChain.kind_opN_congr _
      (show r₁.length + r₂.length + 3 = (r₁.length + r₂.length + 1) + 2 by omega) _ (by omega),
      k2 _ _ (by omega)]
    exact (kind_opN_append_right' r₁ _ (r₂.length + 1) _ (by omega)
      (by simp only [length]; omega) _).trans
      ((kind_opN_cons o₃ _ r₂.length (r₂.length + 1) rfl (by omega) _).trans
        ((kind_opN_append_right' r₂ (single o₄) 0 r₂.length (by omega)
          (by rw [length_single]; omega) _).trans h₄))

section PushRun

variable {E' : CuspidalExt.{u}} (A : ChainObj E) (j : A.grp →ₜ* E'.Pi) (hj : IsOpen (Set.range j))
  (ι : E'.G →ₜ* E.G) (hι : Function.Injective ι) (hιo : IsOpen (Set.range ι))
  (hcomp : ∀ x, ι (E'.pr (j x)) = A.toG x) (hc : A.CuspMatch j) (c : PiChain E')

/-- **A `Π`-chain of `E'`, pushed to `E`**: the path of the pushed operations from the pushed
first object to the pushed last object. -/
def pushRun : OpPath (A.push j hj ι hι hιo hcomp (c.obj ⟨0, Nat.succ_pos _⟩))
    (A.push j hj ι hι hιo hcomp (c.obj ⟨c.len, Nat.lt_succ_self _⟩)) :=
  ofSeq c.len (fun i h ↦ A.push j hj ι hι hιo hcomp (c.obj ⟨i, Nat.lt_succ_of_le h⟩))
    (fun i h ↦ (c.op ⟨i, h⟩).push hc)

lemma length_pushRun : (pushRun A j hj ι hι hιo hcomp hc c).length = c.len :=
  length_ofSeq _ _ _

lemma kind_opN_pushRun (i : ℕ) (h : i < c.len)
    (h' : i < (pushRun A j hj ι hι hιo hcomp hc c).length) :
    ((pushRun A j hj ι hι hιo hcomp hc c).opN i h').kind = (c.op ⟨i, h⟩).kind :=
  (kind_opN_ofSeq _ _ _ i h h').trans (ElemOp.kind_push hc _)

end PushRun

end OpPath

end Belyi.Anabelian
