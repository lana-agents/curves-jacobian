/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ChainPush

/-!
# Terminal objects of `ÉtLoc(Π)`: the group-theoretic reduction (MR8)

[AbsTopII] Cor. 3.3 (i) (`Topics in Absolute Anabelian Geometry II.txt` l.4440–4447)
characterises the chain `Π' ⇝ Π_C` attached to the `k'`-core `C` of `X_{k'}` as the length-one
chain of type `⋎` whose object of `ÉtLoc(Π')` is terminal. Here `ÉtLoc(Π) =
Chain^{iso-trm}(Π){⋏, ⋎}` ([AbsTopI] Def. 4.2 (v), `Topics in Absolute Anabelian Geometry I.txt`
l.3066–3075), whose morphisms are terminal homomorphisms of the last groups ([AbsTopI] Def. 4.2
(iv), l.3036–3045: open outer homomorphisms compatible with the maps to `G` up to an inner
automorphism of `G`).

**Lead decision (2026-10-25).** The morphisms of `ÉtLoc` are the *open outer injections over
`G`* (isomorphisms onto open subgroups); belyi's `PiChain.TerminalIso` is the bijective special
case. With bijective morphisms only, a terminal object would force all objects to be isomorphic.
Here: `OpenInjOver A B` (an injective continuous homomorphism `Π_A → Π_B` with open image, over
`G` up to conjugation) and `PiChain.TerminalInj`; two of them are identified in `ÉtLoc` when they
differ by an inner automorphism of the target.

This file proves the group-theoretic half of Cor. 3.3 (i): if the last group `Π_B` of a chain is
**self-commensurating over `G`** (`ChainObj.SelfComm`: every two open injections `P ↪ Π_B` over
`G` differ by an inner automorphism of `Π_B` — for `Π_B = Π_C` this is the group-theoretic
content of "`C` is a `k`-core", via the relative isomorphism version of the Grothendieck
conjecture), then every `⋏⋎`-chain admits an open injection into `Π_B`, unique up to `Inn(Π_B)`.
The key step is the extension across an operation of type `⋎` (`OpenInjOver.extendQuot`): an
open injection `Π_j ↪ Π_B` extends uniquely to `Π_{j+1} ⊇ Π_j`, sending `ψ ∈ Π_{j+1}` to the
element of `Π_B` inducing the transported conjugation by `ψ` on an open normal subgroup.

## Main statements

* `Belyi.Anabelian.ChainObj.isSlim_grp₄`: chain objects are slim (from `G` and `Δ_j` slim).
* `Belyi.Anabelian.ChainObj.toG_apply_of_compat₄`: homomorphisms compatible with the
  rigidifications lie over `G`.
* `Belyi.Anabelian.ChainObj.selfComm_of_open`: `SelfComm` reduces to open injections with
  image in a fixed open subgroup (e.g. `Π_X ⊆ Π_C`).
* `CurvesJacobian.Cusp.OpenInjOver.compOpen`, `OpenInjOver.extendQuot`: transport of open
  injections into a self-commensurating `Π_B` across operations of types `⋏` and `⋎`.
* `Belyi.Anabelian.PiChain.nonempty_openInjOver_last`,
  `CurvesJacobian.Cusp.OpenInjOver.exists_conj`: existence and uniqueness up to `Inn(Π_B)`.
* `Belyi.Anabelian.PiChain.isTerminalEtLoc_of_selfComm`: a chain of type `⋎ ⋯ ⋎` whose last
  group is self-commensurating is a terminal object of `ÉtLoc(Π)`;
  `PiChain.nonempty_terminalIso_of_isTerminalEtLoc`: terminal objects are unique up to terminal
  isomorphism (the "uniqueness" in Cor. 3.3 (i), up to isomorphism in `ÉtLoc(Π)`; compatibility of
  the isomorphism with the rigidifying homomorphisms, i.e. isomorphism in `Chain(Π)`, is not
  treated here).

The geometric input — `SelfComm` for `Π_C`, `C` the hemi-elliptic core — is not proved here (it
needs the relative isomorphism version of the Grothendieck conjecture for orbicurves and the core
property of `C`); see the MR8 plan.
-/

open Pi1.Profinite Belyi.Anabelian Topology

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section GroupLemmas

/-- If `a` and `c` induce the same conjugate of `b`, then `a⁻¹ c` commutes with `b`. -/
lemma inv_mul_comm_of_conj_eq₄ {G : Type*} [Group G] {a b c : G}
    (h : a * b * a⁻¹ = c * b * c⁻¹) : a⁻¹ * c * b = b * (a⁻¹ * c) := by
  calc a⁻¹ * c * b = a⁻¹ * (c * b * c⁻¹) * c := by group
    _ = a⁻¹ * (a * b * a⁻¹) * c := by rw [h]
    _ = b * (a⁻¹ * c) := by group

variable {P G : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- **Homomorphisms into a slim group agreeing on an open subgroup are equal** (when one of them
has open range). -/
theorem eq_of_eqOn_open₄ (hG : IsSlim G) (f f' : P →ₜ* G) (hf : IsOpen (Set.range f))
    {U : Subgroup P} (hU : IsOpen (U : Set P)) (h : ∀ u ∈ U, f u = f' u) (x : P) :
    f x = f' x := by
  have hc : Continuous fun v : P => x * v * x⁻¹ := by fun_prop
  let V : Subgroup P := U ⊓ U.comap (MulAut.conj x).toMonoidHom
  have hV : IsOpen (V : Set P) := hU.inter (hU.preimage hc)
  have hVo := isOpen_map_of_isOpen_range f hf hV
  refine inv_mul_eq_one.1 (hG ⟨_, hVo⟩ _ ?_)
  rintro _ ⟨v, hv, rfl⟩
  have h1 : f (x * v * x⁻¹) = f' (x * v * x⁻¹) := h _ hv.2
  have h2 : f v = f' v := h _ hv.1
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ← h2] at h1
  exact inv_mul_comm_of_conj_eq₄ h1

/-- An element commuting with the image of an open subgroup under an injective homomorphism with
open range into a slim group is trivial. -/
lemma eq_one_of_commute_open₄ (hG : IsSlim G) (f : P →ₜ* G) (hf : IsOpen (Set.range f))
    {U : Subgroup P} (hU : IsOpen (U : Set P)) {z : G} (hz : ∀ u ∈ U, z * f u = f u * z) :
    z = 1 :=
  hG ⟨_, isOpen_map_of_isOpen_range f hf hU⟩ z (by
    rintro _ ⟨u, hu, rfl⟩
    exact hz u hu)

end GroupLemmas

end CurvesJacobian.Cusp

namespace Belyi.Anabelian.ChainObj

open CurvesJacobian.Cusp

variable {E : CuspidalExt.{u}}

lemma compactSpace_dom₄ (A : ChainObj E) : CompactSpace (A.dom : Subgroup E.Pi) :=
  isCompact_iff_compactSpace.mp A.dom.isClosed.isCompact

/-- **Chain objects are slim** (`G` and `Δ_j` are slim and `Π_j → G` has open range). -/
theorem isSlim_grp₄ (A : ChainObj E) : IsSlim A.grp := by
  intro U z hz
  have h1 : A.toG z = 1 := eq_one_of_commute_open₄ E.slim_G A.toG A.isOpen_range_toG U.isOpen
    (fun u hu => by rw [← map_mul, ← map_mul, hz u hu])
  have hzΔ : z ∈ (A.toG : A.grp →* E.G).ker := h1
  have hΔ : IsOpen (((U : Subgroup A.grp).subgroupOf (A.toG : A.grp →* E.G).ker :
      Subgroup (A.toG : A.grp →* E.G).ker) : Set (A.toG : A.grp →* E.G).ker) :=
    U.isOpen.preimage continuous_subtype_val
  have := A.slim_delta ⟨_, hΔ⟩ ⟨z, hzΔ⟩ (by
    rintro ⟨u, hu⟩ hu'
    exact Subtype.ext (hz u hu'))
  exact congrArg Subtype.val this

/-- **Homomorphisms compatible with the rigidifying homomorphisms lie over `G`**:
`toG_B ∘ φ = toG_A` (both agree on `ρ_A(H)`, and `G` is slim). -/
theorem toG_apply_of_compat₄ {A B : ChainObj E} {φ : A.grp →ₜ* B.grp} (h : Compat A B φ)
    (x : A.grp) : B.toG (φ x) = A.toG x := by
  obtain ⟨H, hA, hB, hφ⟩ := h
  haveI := A.compactSpace_dom₄
  let H' : Subgroup (A.dom : Subgroup E.Pi) := (H : Subgroup E.Pi).subgroupOf A.dom
  have hH' : IsOpen (H' : Set (A.dom : Subgroup E.Pi)) :=
    H.isOpen.preimage continuous_subtype_val
  have hU := isOpen_map_of_isOpen_range A.rho A.isOpen_range_rho hH'
  refine (eq_of_eqOn_open₄ E.slim_G A.toG (B.toG.comp φ) A.isOpen_range_toG hU ?_ x).symm
  rintro _ ⟨y, hy, rfl⟩
  have e1 : φ (A.rho y) = B.rho ⟨y, hB hy⟩ := hφ (y : E.Pi) hy
  calc A.toG (A.rho y) = E.pr y := A.toG_rho y
    _ = B.toG (B.rho ⟨y, hB hy⟩) := (B.toG_rho ⟨y, hB hy⟩).symm
    _ = B.toG (φ (A.rho y)) := congrArg B.toG e1.symm

/-- `Compat` is symmetric for isomorphisms. -/
theorem compat_symm₄ {A B : ChainObj E} {e : A.grp ≃ₜ* B.grp}
    (h : Compat A B (ContinuousMonoidHom.toContinuousMonoidHom e : A.grp →ₜ* B.grp)) :
    Compat B A (ContinuousMonoidHom.toContinuousMonoidHom e.symm : B.grp →ₜ* A.grp) := by
  obtain ⟨H, hA, hB, hφ⟩ := h
  refine ⟨H, hB, hA, fun x hx => ?_⟩
  change e.symm (B.rho ⟨x, hB hx⟩) = A.rho ⟨x, hA hx⟩
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact (hφ x hx).symm

/-- **`Π_B` is self-commensurating over `G`**: any two open injections `f₁, f₂ : P ↪ Π_B` of a
compact group whose composites with `Π_B → G` differ by conjugation in `G` differ by an inner
automorphism of `Π_B`. For `Π_B = Π_C` with `C` a `k`-core this is the group-theoretic content of
the core property (an isomorphism of open subgroups over `G` comes from an isomorphism of
coverings of `C`, which commutes with the maps to the core). -/
def SelfComm (B : ChainObj E) : Prop :=
  ∀ (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (f₁ f₂ : P →ₜ* B.grp), Function.Injective f₁ → IsOpen (Set.range f₁) →
    Function.Injective f₂ → IsOpen (Set.range f₂) →
    ∀ g : E.G, (∀ x, B.toG (f₂ x) = g * B.toG (f₁ x) * g⁻¹) →
    ∃ γ : B.grp, ∀ x, f₂ x = γ * f₁ x * γ⁻¹

/-- **Reduction of `SelfComm` to an open subgroup**: it suffices to treat open injections with
image in a fixed open subgroup `O ⊆ Π_B` (for `Π_B = Π_C` and `O = Π_X`: injections whose images
are fundamental groups of curves, where the relative isomorphism version of the Grothendieck
conjecture for curves applies). -/
theorem selfComm_of_open (B : ChainObj E) (O : Subgroup B.grp) (hO : IsOpen (O : Set B.grp))
    (h : ∀ (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
      (f₁ f₂ : P →ₜ* B.grp), Function.Injective f₁ → IsOpen (Set.range f₁) →
      Function.Injective f₂ → IsOpen (Set.range f₂) → Set.range f₁ ⊆ O → Set.range f₂ ⊆ O →
      ∀ g : E.G, (∀ x, B.toG (f₂ x) = g * B.toG (f₁ x) * g⁻¹) →
      ∃ γ : B.grp, ∀ x, f₂ x = γ * f₁ x * γ⁻¹) :
    B.SelfComm := by
  intro P _ _ _ _ f₁ f₂ hi₁ ho₁ hi₂ ho₂ g hg
  let P' : Subgroup P := O.comap (f₁ : P →* B.grp) ⊓ O.comap (f₂ : P →* B.grp)
  have hP' : IsOpen (P' : Set P) := (hO.preimage f₁.continuous).inter (hO.preimage f₂.continuous)
  haveI : CompactSpace P' :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hP').isCompact
  let ι : P' →ₜ* P := ⟨P'.subtype, continuous_subtype_val⟩
  have hr : ∀ f : P →ₜ* B.grp, IsOpen (Set.range f) →
      Set.range (f.comp ι) = ((P'.map (f : P →* B.grp) : Subgroup B.grp) : Set B.grp) := by
    intro f _
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨γ, hγ⟩ := h P' (f₁.comp ι) (f₂.comp ι) (hi₁.comp Subtype.val_injective)
    (by rw [hr f₁ ho₁]; exact isOpen_map_of_isOpen_range f₁ ho₁ hP')
    (hi₂.comp Subtype.val_injective)
    (by rw [hr f₂ ho₂]; exact isOpen_map_of_isOpen_range f₂ ho₂ hP')
    (by rintro _ ⟨x, rfl⟩; exact x.2.1) (by rintro _ ⟨x, rfl⟩; exact x.2.2) g fun x => hg x
  let c : P →ₜ* B.grp := ⟨(MulAut.conj γ).toMonoidHom.comp (f₁ : P →* B.grp),
    (continuous_const.mul f₁.continuous).mul continuous_const⟩
  exact ⟨γ, fun x => eq_of_eqOn_open₄ (isSlim_grp₄ B) f₂ c ho₂ hP' (fun u hu => hγ ⟨u, hu⟩) x⟩

end Belyi.Anabelian.ChainObj

namespace CurvesJacobian.Cusp

variable {E : CuspidalExt.{u}}

/-- An **open injection over `G`** `Π_A ↪ Π_B` (lead decision 2026-10-25 for the morphisms of
`ÉtLoc`): an injective continuous homomorphism with open image, compatible with the maps to `G`
up to conjugation by `g ∈ G`. -/
structure OpenInjOver (A B : ChainObj E) where
  /-- The homomorphism `Π_A → Π_B`. -/
  hom : A.grp →ₜ* B.grp
  inj : Function.Injective hom
  isOpen_range : IsOpen (Set.range hom)
  /-- The element of `G` conjugating `Π_A → G` into `Π_B → G`. -/
  g : E.G
  toG_hom : ∀ x, B.toG (hom x) = g * A.toG x * g⁻¹

namespace OpenInjOver

/-- A compatible open immersion is an open injection over `G` (with `g = 1`). -/
def ofCompat {A B : ChainObj E} (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ)
    (hopen : IsOpen (Set.range φ)) (hc : ChainObj.Compat A B φ) : OpenInjOver A B where
  hom := φ
  inj := hinj
  isOpen_range := hopen
  g := 1
  toG_hom x := by rw [ChainObj.toG_apply_of_compat₄ hc, one_mul, inv_one, mul_one]

/-- The identity is an open injection over `G`. -/
def refl (A : ChainObj E) : OpenInjOver A A where
  hom := ContinuousMonoidHom.id A.grp
  inj := Function.injective_id
  isOpen_range := by
    change IsOpen (Set.range id)
    rw [Set.range_id]
    exact isOpen_univ
  g := 1
  toG_hom x := by
    change A.toG x = _
    group

/-- Composition of open injections over `G`. -/
def trans {A B C : ChainObj E} (i : OpenInjOver A B) (j : OpenInjOver B C) :
    OpenInjOver A C where
  hom := j.hom.comp i.hom
  inj := j.inj.comp i.inj
  isOpen_range := by
    have := isOpen_map_of_isOpen_range j.hom j.isOpen_range
      (ChainObj.isOpen_coe_range i.hom i.isOpen_range)
    convert this using 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨i.hom x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  g := j.g * i.g
  toG_hom x := by
    change C.toG (j.hom (i.hom x)) = _
    rw [j.toG_hom, i.toG_hom]
    group

/-- **Operations of type `⋏`**: precomposition with a compatible open immersion `Π_C ↪ Π_A`. -/
def compOpen {A B C : ChainObj E} (i : OpenInjOver A B) (φ : C.grp →ₜ* A.grp)
    (hinj : Function.Injective φ) (hopen : IsOpen (Set.range φ)) (hc : ChainObj.Compat C A φ) :
    OpenInjOver C B :=
  (ofCompat φ hinj hopen hc).trans i

/-- **Uniqueness**: two open injections over `G` into a self-commensurating `Π_B` differ by an
inner automorphism of `Π_B`. -/
theorem exists_conj {A B : ChainObj E} (hB : B.SelfComm) (i i' : OpenInjOver A B) :
    ∃ γ : B.grp, ∀ x, i'.hom x = γ * i.hom x * γ⁻¹ :=
  hB A.grp i.hom i'.hom i.inj i.isOpen_range i'.inj i'.isOpen_range (i'.g * i.g⁻¹) fun x => by
    rw [i'.toG_hom, i.toG_hom]
    group

section ExtendQuot

/-! ### Operations of type `⋎`: extension across an open immersion `Π_A ↪ Π_C` -/

variable {A B C : ChainObj E} (i : OpenInjOver A B) (φ : A.grp →ₜ* C.grp)
  (hinj : Function.Injective φ) (hopen : IsOpen (Set.range φ))

/-- The normal core `N` of `φ(Π_A)` in `Π_C`. -/
abbrev coreN : Subgroup C.grp := (φ : A.grp →* C.grp).range.normalCore

include hopen in
lemma isOpen_coreN : IsOpen (coreN φ : Set C.grp) := by
  have hQ := ChainObj.isOpen_coe_range φ hopen
  haveI := finiteIndex_of_isOpen hQ
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hQ))

/-- `P = φ⁻¹(N) ⊆ Π_A`, an open subgroup mapped isomorphically onto `N`. -/
abbrev coreP : Subgroup A.grp := (coreN φ).comap (φ : A.grp →* C.grp)

include hopen in
lemma isOpen_coreP : IsOpen (coreP φ : Set A.grp) :=
  (isOpen_coreN φ hopen).preimage φ.continuous

lemma mem_range_of_mem_coreN {n : C.grp} (hn : n ∈ coreN φ) :
    n ∈ (φ : A.grp →* C.grp).range :=
  Subgroup.normalCore_le _ hn

/-- `p ↦ ψ φ(p) ψ⁻¹`, `P → φ(Π_A)`. -/
def conjQ (ψ : C.grp) : coreP φ →* (φ : A.grp →* C.grp).range :=
  ((MulAut.conj ψ).toMonoidHom.comp ((φ : A.grp →* C.grp).comp (coreP φ).subtype)).codRestrict _
    fun p => mem_range_of_mem_coreN φ ((Subgroup.normalCore_normal _).conj_mem _ p.2 ψ)

/-- **Conjugation by `ψ ∈ Π_C` transported to `P`**: `κ_ψ(p) = φ⁻¹(ψ φ(p) ψ⁻¹)`. -/
def kappa (ψ : C.grp) : coreP φ →ₜ* A.grp :=
  (ContinuousMonoidHom.toContinuousMonoidHom (rangeEquiv φ hinj).symm).comp
    ⟨conjQ φ ψ, ((continuous_const.mul (φ.continuous.comp continuous_subtype_val)).mul
      continuous_const).subtype_mk _⟩

lemma phi_kappa (ψ : C.grp) (p : coreP φ) : φ (kappa φ hinj ψ p) = ψ * φ p * ψ⁻¹ :=
  apply_rangeEquiv_symm φ hinj _

lemma kappa_mem (ψ : C.grp) (p : coreP φ) : kappa φ hinj ψ p ∈ coreP φ := by
  change φ (kappa φ hinj ψ p) ∈ coreN φ
  rw [phi_kappa]
  exact (Subgroup.normalCore_normal _).conj_mem _ p.2 ψ

lemma kappa_injective (ψ : C.grp) : Function.Injective (kappa φ hinj ψ) := by
  intro p p' h
  have h1 := congrArg φ h
  rw [phi_kappa, phi_kappa, mul_left_inj, mul_right_inj] at h1
  exact Subtype.ext (hinj h1)

lemma range_kappa (ψ : C.grp) : Set.range (kappa φ hinj ψ) = (coreP φ : Set A.grp) := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    exact kappa_mem φ hinj ψ p
  · intro ha
    refine ⟨⟨kappa φ hinj ψ⁻¹ ⟨a, ha⟩, kappa_mem φ hinj _ _⟩, hinj ?_⟩
    rw [phi_kappa, phi_kappa]
    group

lemma kappa_mul (ψ ψ' : C.grp) (p : coreP φ) :
    kappa φ hinj (ψ * ψ') p = kappa φ hinj ψ ⟨kappa φ hinj ψ' p, kappa_mem φ hinj ψ' p⟩ := by
  apply hinj
  rw [phi_kappa, phi_kappa]
  change _ = ψ * φ (kappa φ hinj ψ' p) * ψ⁻¹
  rw [phi_kappa]
  group

lemma kappa_one (p : coreP φ) : kappa φ hinj 1 p = p := by
  apply hinj
  rw [phi_kappa]
  group

lemma kappa_phi (a : A.grp) (p : coreP φ) : kappa φ hinj (φ a) p = a * p * a⁻¹ := by
  apply hinj
  rw [phi_kappa, map_mul, map_mul, map_inv]

/-- `γ ∈ Π_B` **induces the transported conjugation by `ψ`** on `i(P)`. -/
def IsConjOn (ψ : C.grp) (γ : B.grp) : Prop :=
  ∀ p : coreP φ, i.hom (kappa φ hinj ψ p) = γ * i.hom p * γ⁻¹

include hopen in
lemma isConjOn_unique {ψ : C.grp} {γ γ' : B.grp} (h : IsConjOn i φ hinj ψ γ)
    (h' : IsConjOn i φ hinj ψ γ') : γ = γ' := by
  refine inv_mul_eq_one.1 (eq_one_of_commute_open₄ (ChainObj.isSlim_grp₄ B) i.hom i.isOpen_range
    (isOpen_coreP φ hopen) fun u hu => ?_)
  exact inv_mul_comm_of_conj_eq₄ ((h ⟨u, hu⟩).symm.trans (h' ⟨u, hu⟩))

variable (hc : ChainObj.Compat A C φ) (hB : B.SelfComm)

include hc in
lemma toG_kappa (ψ : C.grp) (p : coreP φ) :
    A.toG (kappa φ hinj ψ p) = C.toG ψ * A.toG p * (C.toG ψ)⁻¹ := by
  rw [← ChainObj.toG_apply_of_compat₄ hc, ← ChainObj.toG_apply_of_compat₄ hc, phi_kappa,
    map_mul, map_mul, map_inv]

include hopen hc hB in
lemma exists_isConjOn (ψ : C.grp) : ∃ γ, IsConjOn i φ hinj ψ γ := by
  haveI : CompactSpace (coreP φ) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ (isOpen_coreP φ hopen)).isCompact
  let f₁ : coreP φ →ₜ* B.grp := i.hom.comp ⟨(coreP φ).subtype, continuous_subtype_val⟩
  let f₂ : coreP φ →ₜ* B.grp := i.hom.comp (kappa φ hinj ψ)
  have hr₁ : Set.range f₁ = ((coreP φ).map (i.hom : A.grp →* B.grp) : Set B.grp) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hr₂ : Set.range f₂ = Set.range f₁ := by
    rw [hr₁]
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, kappa_mem φ hinj ψ p, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨p, hp⟩ : a ∈ Set.range (kappa φ hinj ψ) := by rw [range_kappa]; exact ha
      exact ⟨p, by rw [← hp]; rfl⟩
  have ho₁ : IsOpen (Set.range f₁) := by
    rw [hr₁]
    exact isOpen_map_of_isOpen_range i.hom i.isOpen_range (isOpen_coreP φ hopen)
  obtain ⟨γ, hγ⟩ := hB (coreP φ) f₁ f₂ (i.inj.comp Subtype.val_injective) ho₁
    (i.inj.comp (kappa_injective φ hinj ψ)) (hr₂ ▸ ho₁) (i.g * C.toG ψ * i.g⁻¹) fun p => by
      change B.toG (i.hom (kappa φ hinj ψ p)) = _ * B.toG (i.hom p) * _
      rw [i.toG_hom, i.toG_hom, toG_kappa φ hinj hc]
      group
  exact ⟨γ, hγ⟩

/-- The element `γ_ψ ∈ Π_B` inducing the transported conjugation by `ψ`. -/
def gammaQ (ψ : C.grp) : B.grp :=
  Classical.choose (exists_isConjOn i φ hinj hopen hc hB ψ)

lemma isConjOn_gammaQ (ψ : C.grp) : IsConjOn i φ hinj ψ (gammaQ i φ hinj hopen hc hB ψ) :=
  Classical.choose_spec (exists_isConjOn i φ hinj hopen hc hB ψ)

lemma gammaQ_eq {ψ : C.grp} {γ : B.grp} (h : IsConjOn i φ hinj ψ γ) :
    gammaQ i φ hinj hopen hc hB ψ = γ :=
  isConjOn_unique i φ hinj hopen (isConjOn_gammaQ i φ hinj hopen hc hB ψ) h

/-- `ψ ↦ γ_ψ` as a homomorphism `Π_C → Π_B`. -/
def gammaHom : C.grp →* B.grp where
  toFun := gammaQ i φ hinj hopen hc hB
  map_one' := gammaQ_eq i φ hinj hopen hc hB fun p => by
    rw [kappa_one]
    group
  map_mul' ψ ψ' := gammaQ_eq i φ hinj hopen hc hB fun p => by
    rw [kappa_mul, isConjOn_gammaQ i φ hinj hopen hc hB ψ, isConjOn_gammaQ i φ hinj hopen hc hB ψ']
    group

lemma gammaHom_phi (a : A.grp) : gammaHom i φ hinj hopen hc hB (φ a) = i.hom a :=
  gammaQ_eq i φ hinj hopen hc hB fun p => by
    rw [kappa_phi, map_mul, map_mul, map_inv]

lemma continuous_gammaHom : Continuous (gammaHom i φ hinj hopen hc hB) := by
  refine continuous_of_continuousAt_one _ ?_
  have hind : IsInducing φ := (φ.continuous.isClosedEmbedding hinj).isInducing
  have hmem : Set.range φ ∈ 𝓝 (φ 1) := hopen.mem_nhds ⟨1, rfl⟩
  have h1 : ContinuousAt ((gammaHom i φ hinj hopen hc hB) ∘ φ) 1 := by
    have hcomp : (gammaHom i φ hinj hopen hc hB) ∘ φ = i.hom :=
      funext (gammaHom_phi i φ hinj hopen hc hB)
    rw [hcomp]
    exact i.hom.continuous.continuousAt
  have := (hind.continuousAt_iff' hmem).1 h1
  rwa [map_one] at this

lemma injective_gammaHom : Function.Injective (gammaHom i φ hinj hopen hc hB) := by
  refine (injective_iff_map_eq_one _).2 fun ψ hψ => ?_
  have h1 : IsConjOn i φ hinj ψ 1 := by
    have := isConjOn_gammaQ i φ hinj hopen hc hB ψ
    change gammaQ i φ hinj hopen hc hB ψ = 1 at hψ
    rwa [hψ] at this
  refine eq_one_of_commute_open₄ (ChainObj.isSlim_grp₄ C)
    (ContinuousMonoidHom.id C.grp) (by simp) (isOpen_coreN φ hopen) fun n hn => ?_
  obtain ⟨a, rfl⟩ := mem_range_of_mem_coreN φ hn
  have h2 := h1 ⟨a, hn⟩
  rw [one_mul, inv_one, mul_one] at h2
  have h3 : φ (kappa φ hinj ψ ⟨a, hn⟩) = φ a := congrArg φ (i.inj h2)
  rw [phi_kappa] at h3
  change ψ * φ a = φ a * ψ
  calc ψ * φ a = ψ * φ a * ψ⁻¹ * ψ := by group
    _ = φ a * ψ := by rw [h3]

lemma isOpen_range_gammaHom : IsOpen (Set.range (gammaHom i φ hinj hopen hc hB)) := by
  have hle : (i.hom : A.grp →* B.grp).range ≤ (gammaHom i φ hinj hopen hc hB).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, gammaHom_phi i φ hinj hopen hc hB a⟩
  have := Subgroup.isOpen_mono hle (ChainObj.isOpen_coe_range i.hom i.isOpen_range)
  rwa [MonoidHom.coe_range] at this

lemma toG_gammaHom (ψ : C.grp) :
    B.toG (gammaHom i φ hinj hopen hc hB ψ) = i.g * C.toG ψ * i.g⁻¹ := by
  have key : ∀ p : coreP φ, B.toG (gammaQ i φ hinj hopen hc hB ψ) * B.toG (i.hom p) *
      (B.toG (gammaQ i φ hinj hopen hc hB ψ))⁻¹ =
      (i.g * C.toG ψ * i.g⁻¹) * B.toG (i.hom p) * (i.g * C.toG ψ * i.g⁻¹)⁻¹ := by
    intro p
    have h1 := congrArg B.toG (isConjOn_gammaQ i φ hinj hopen hc hB ψ p)
    rw [map_mul, map_mul, map_inv, i.toG_hom, toG_kappa φ hinj hc] at h1
    rw [← h1, i.toG_hom]
    group
  have hU := isOpen_map_of_isOpen_range i.hom i.isOpen_range (isOpen_coreP φ hopen)
  refine inv_mul_eq_one.1 (eq_one_of_commute_open₄ E.slim_G B.toG B.isOpen_range_toG hU
    fun u hu => ?_)
  obtain ⟨a, ha, rfl⟩ := hu
  exact inv_mul_comm_of_conj_eq₄ (key ⟨a, ha⟩)

/-- **Operations of type `⋎`**: an open injection `Π_A ↪ Π_B` over `G` into a
self-commensurating `Π_B` extends (via `ψ ↦ γ_ψ`) to an open injection `Π_C ↪ Π_B` over `G`
along a compatible open immersion `φ : Π_A ↪ Π_C`. -/
def extendQuot : OpenInjOver C B where
  hom := ⟨gammaHom i φ hinj hopen hc hB, continuous_gammaHom i φ hinj hopen hc hB⟩
  inj := injective_gammaHom i φ hinj hopen hc hB
  isOpen_range := isOpen_range_gammaHom i φ hinj hopen hc hB
  g := i.g
  toG_hom := toG_gammaHom i φ hinj hopen hc hB

lemma extendQuot_hom_phi (a : A.grp) : (extendQuot i φ hinj hopen hc hB).hom (φ a) = i.hom a :=
  gammaHom_phi i φ hinj hopen hc hB a

end ExtendQuot

end OpenInjOver

end CurvesJacobian.Cusp

namespace Belyi.Anabelian

open CurvesJacobian.Cusp

variable {E : CuspidalExt.{u}}

/-- An elementary operation of type `⋏` or `⋎` transports open injections into a
self-commensurating `Π_B`. -/
theorem nonempty_openInjOver_of_elemOp {A B C : ChainObj E} (hB : B.SelfComm) (o : ElemOp A C)
    (ho : o.kind = .cover ∨ o.kind = .quot) (i : OpenInjOver A B) :
    Nonempty (OpenInjOver C B) := by
  cases o with
  | cover φ inj op compat => exact ⟨i.compOpen φ inj op compat⟩
  | quot φ inj op compat => exact ⟨OpenInjOver.extendQuot i φ inj op compat hB⟩
  | decusp => rcases ho with h | h <;> cases h
  | deorb => rcases ho with h | h <;> cases h

namespace PiChain

/-- The **base object** of a chain embeds into any `Π_B` receiving `Π` (via `Π₀ ≅ Π`). -/
def openInjOverZero (c : PiChain E) {B : ChainObj E} (i₀ : OpenInjOver (ChainObj.base E) B) :
    OpenInjOver (c.obj 0) B :=
  i₀.compOpen _ c.obj_zero.choose.injective
    (by
      change IsOpen (Set.range c.obj_zero.choose)
      rw [c.obj_zero.choose.surjective.range_eq]
      exact isOpen_univ)
    c.obj_zero.choose_spec

/-- **Existence**: for a self-commensurating `Π_B` receiving `Π` by an open injection over `G`,
the last group of every `⋏⋎`-chain admits an open injection over `G` into `Π_B`. -/
theorem nonempty_openInjOver_last {B : ChainObj E} (hB : B.SelfComm)
    (i₀ : OpenInjOver (ChainObj.base E) B) (c : PiChain E) (hc : c.IsEtLoc) :
    Nonempty (OpenInjOver c.last B) :=
  Fin.induction (motive := fun j => Nonempty (OpenInjOver (c.obj j) B))
    ⟨c.openInjOverZero i₀⟩
    (fun j ⟨ij⟩ => nonempty_openInjOver_of_elemOp hB (c.op j)
      (hc _ (List.mem_ofFn.2 ⟨j, rfl⟩)) ij)
    (Fin.last c.len)

/-- **Terminal injections** (morphisms of `ÉtLoc(Π)` in the reading of the lead decision of
2026-10-25): open injections over `G` between the last groups. -/
abbrev TerminalInj (c c' : PiChain E) : Type u := OpenInjOver c.last c'.last

/-- `c₀` is a **terminal object of `ÉtLoc(Π)`**: it is a `⋏⋎`-chain, and every `⋏⋎`-chain admits a
terminal injection into it, unique up to an inner automorphism of the last group of `c₀`. -/
def IsTerminalEtLoc (c₀ : PiChain E) : Prop :=
  c₀.IsEtLoc ∧ ∀ c : PiChain E, c.IsEtLoc → Nonempty (c.TerminalInj c₀) ∧
    ∀ i i' : c.TerminalInj c₀, ∃ γ : c₀.last.grp, ∀ x, i'.hom x = γ * i.hom x * γ⁻¹

/-- Along a chain of operations of type `⋎` only, `Π` embeds into every object over `G`. -/
theorem nonempty_openInjOver_base_of_quot (c : PiChain E) (hq : ∀ t ∈ c.typeChain, t = .quot)
    (j : Fin (c.len + 1)) : Nonempty (OpenInjOver (ChainObj.base E) (c.obj j)) := by
  refine Fin.induction (motive := fun j => Nonempty (OpenInjOver (ChainObj.base E) (c.obj j)))
    ⟨OpenInjOver.ofCompat _ c.obj_zero.choose.symm.injective
      (by
        change IsOpen (Set.range c.obj_zero.choose.symm)
        rw [c.obj_zero.choose.symm.surjective.range_eq]
        exact isOpen_univ)
      (ChainObj.compat_symm₄ c.obj_zero.choose_spec)⟩ (fun j ⟨ij⟩ => ?_) j
  have hk := hq _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  revert hk
  cases c.op j with
  | quot φ inj op compat => exact fun _ => ⟨ij.trans (OpenInjOver.ofCompat φ inj op compat)⟩
  | cover => intro h; cases h
  | decusp => intro h; cases h
  | deorb => intro h; cases h

/-- **[AbsTopII] Cor. 3.3 (i), group-theoretic half.** A chain whose operations are all of type
`⋎` (e.g. the length-one chain `Π ⇝ Π_C`) and whose last group is self-commensurating over `G`
is a terminal object of `ÉtLoc(Π)`. -/
theorem isTerminalEtLoc_of_selfComm (c₀ : PiChain E) (hq : ∀ t ∈ c₀.typeChain, t = .quot)
    (hB : c₀.last.SelfComm) : c₀.IsTerminalEtLoc := by
  obtain ⟨i₀⟩ := nonempty_openInjOver_base_of_quot c₀ hq (Fin.last c₀.len)
  exact ⟨fun t ht => Or.inr (hq t ht), fun c hc =>
    ⟨nonempty_openInjOver_last hB i₀ c hc, fun i i' => OpenInjOver.exists_conj hB i i'⟩⟩

/-- **Terminal objects of `ÉtLoc(Π)` are unique up to terminal isomorphism**: if `c₀` and `c₁`
are both terminal, the terminal injection `c₁ → c₀` is bijective (its composites with the
terminal injection `c₀ → c₁` are inner automorphisms), i.e. a terminal isomorphism in the sense of
belyi's `PiChain.TerminalIso` ([AbsTopI] Def. 4.2 (iv)). -/
theorem nonempty_terminalIso_of_isTerminalEtLoc {c₀ c₁ : PiChain E}
    (h₀ : c₀.IsTerminalEtLoc) (h₁ : c₁.IsTerminalEtLoc) : Nonempty (c₁.TerminalIso c₀) := by
  obtain ⟨a⟩ := (h₀.2 c₁ h₁.1).1
  obtain ⟨b⟩ := (h₁.2 c₀ h₀.1).1
  obtain ⟨δ, hδ⟩ := (h₀.2 c₀ h₀.1).2 (OpenInjOver.refl _) (b.trans a)
  have hsurj : Function.Surjective a.hom := fun y => by
    refine ⟨b.hom (δ⁻¹ * y * δ), ?_⟩
    have := hδ (δ⁻¹ * y * δ)
    change a.hom (b.hom (δ⁻¹ * y * δ)) = δ * (δ⁻¹ * y * δ) * δ⁻¹ at this
    rw [this]
    group
  exact ⟨⟨continuousMulEquivOfBijective a.hom ⟨a.inj, hsurj⟩, a.g, a.toG_hom⟩⟩

end PiChain

end Belyi.Anabelian
