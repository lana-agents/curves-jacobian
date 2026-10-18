/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ChainPush

/-!
# Entering and leaving pushed chain objects; terminal isomorphisms of paths (MR8.5)

Group-theoretic glue for assembling the Belyi chain `X ⇝ V ⇝ Q ⇝ … ⇝ P ⇝ W ⇝ … ⇝ V ⇝ X` of
[AbsTopII] Example 3.6 (ii) (`Topics in Absolute Anabelian Geometry II.txt` l.4669–4680) with
`Belyi.Anabelian.OpPath.belyiPath`, for a cuspidal extension `E` (of `X`) and runs of `•`'s that
are `Π`-chains of other cuspidal extensions `E'` (of `Q`, of `W`) pushed to `E`
(`OpPath.pushRun`):

* `ChainObj.rhoTop`: the rigidifying homomorphism of a chain object defined on all of `Π`;
* `ElemOp.toPush`: the operation `A ⇝ A.push j B'` of type `⋎` (`φ = ρ_{B'} ∘ j`), entering the
  pushed run (`V ⇝ Q`);
* `ElemOp.coverPush`: the operation `A ⇝ (A.coverObj φ).push id B'` of type `⋏`
  (`φ ∘ ρ_{B'}⁻¹`), entering the second pushed run (`P ⇝ W`), for `ρ_{B'}` bijective;
* `ChainObj.cuspMatch_of_commensurable`: a criterion for `CuspMatch`;
* `OpPath.objN_length`, `ChainObj.equivOfEq`, `OpPath.terminalIso`: a terminal isomorphism of the
  `Π`-chain of a path to the trivial chain from an isomorphism of its last group with `Π` over `G`
  up to conjugation.
-/

open Pi1.Profinite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Belyi.Anabelian

section GroupTheory

variable {G H : Type*} [Group G] [Group H]

/-- A subgroup of finite index in a larger one is commensurable with it. -/
theorem Subgroup.commensurable_of_le {J K : Subgroup G} (hle : J ≤ K) (h : J.relIndex K ≠ 0) :
    J.Commensurable K :=
  ⟨h, by rw [Subgroup.relIndex_eq_one.2 hle]; exact one_ne_zero⟩

/-- Equal subgroups are commensurable. -/
theorem Subgroup.commensurable_of_eq {J K : Subgroup G} (h : J = K) : J.Commensurable K :=
  h ▸ Subgroup.Commensurable.refl J

/-- For injective `φ`, if `φ(J) ⊆ I` with finite index then `J ⊆ φ⁻¹(I)` with finite index. -/
theorem Subgroup.commensurable_comap_of_map_le {φ : G →* H} (hφ : Function.Injective φ)
    {J : Subgroup G} {I : Subgroup H} (hle : J.map φ ≤ I) (h : (J.map φ).relIndex I ≠ 0) :
    J.Commensurable (I.comap φ) := by
  have hle' : J ≤ I.comap φ := Subgroup.map_le_iff_le_comap.1 hle
  refine Subgroup.commensurable_of_le hle' ?_
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.map_comap_eq]
  have h1 : J.map φ ≤ φ.range ⊓ I := le_inf (Subgroup.map_le_range φ J) hle
  have h2 := Subgroup.relIndex_mul_relIndex (J.map φ) (φ.range ⊓ I) I h1 inf_le_right
  intro h0
  rw [h0, zero_mul] at h2
  exact h h2.symm

end GroupTheory

namespace ChainObj

variable {E E' : CuspidalExt.{u}}

/-- **A criterion for `CuspMatch`**: a family `S` of subgroups of `Π_A`, each commensurable with
the image of a cusp of `E`, whose images under `j` are commensurable with all cusps of `E'`. -/
theorem cuspMatch_of_commensurable {A : ChainObj E} {j : A.grp →ₜ* E'.Pi}
    (S : Set (Subgroup A.grp)) (hS : ∀ J ∈ S, ∃ I ∈ E.cusps, J.Commensurable (A.image I))
    (ha : ∀ I' ∈ E'.cusps, ∃ J ∈ S, (J.map (j : A.grp →* E'.Pi)).Commensurable I') :
    A.CuspMatch j := by
  intro I' hI'
  obtain ⟨J, hJ, hJI'⟩ := ha I' hI'
  obtain ⟨I, hI, hJI⟩ := hS J hJ
  exact ⟨I, hI, (Subgroup.Commensurable.map' _ hJI).symm.trans hJI'⟩

/-- The images of subgroups of `Π` in the target of a `⋏` from the trivial object. -/
lemma image_coverObj_base {G' : ProfiniteGrp.{u}} (φ : G' →ₜ* E.Pi)
    (hinj : Function.Injective φ) (hopen : IsOpen (Set.range φ)) (I : Subgroup E.Pi) :
    ((base E).coverObj φ hinj hopen).image I = I.comap (φ : G' →* E.Pi) := by
  have hb : (base E).image I = I := by
    ext x
    constructor
    · rintro ⟨⟨y, _⟩, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, trivial⟩, hx, rfl⟩
  rw [image_coverObj, hb]

/-- The rigidifying homomorphism of a chain object defined on all of `Π`. -/
def rhoTop (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi)) : E'.Pi →ₜ* B'.grp where
  toFun x := B'.rho ⟨x, hB x⟩
  map_one' := (congrArg B'.rho (Subtype.ext rfl)).trans (map_one B'.rho)
  map_mul' a b := (congrArg B'.rho (Subtype.ext rfl)).trans (map_mul B'.rho ⟨a, hB a⟩ ⟨b, hB b⟩)
  continuous_toFun := B'.rho.continuous.comp (continuous_id.subtype_mk _)

lemma rhoTop_apply (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi)) (x : E'.Pi) :
    B'.rhoTop hB x = B'.rho ⟨x, hB x⟩ := rfl

lemma isOpen_range_rhoTop (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi)) :
    IsOpen (Set.range (B'.rhoTop hB)) := by
  have e : Set.range (B'.rhoTop hB) = Set.range B'.rho := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, rfl⟩
  rw [e]
  exact B'.isOpen_range_rho

lemma isOpen_range_rhoTop_comp {A : ChainObj E} (j : A.grp →ₜ* E'.Pi) (hj : IsOpen (Set.range j))
    (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi)) :
    IsOpen (Set.range ((B'.rhoTop hB).comp j)) := by
  have e : Set.range ((B'.rhoTop hB).comp j) =
      (((j : A.grp →* E'.Pi).range.map (B'.rhoTop hB : E'.Pi →* B'.grp) : Subgroup B'.grp) :
        Set B'.grp) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨j x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  rw [e]
  exact isOpen_map_of_isOpen_range (B'.rhoTop hB) (B'.isOpen_range_rhoTop hB)
    (isOpen_coe_range j hj)

/-- An equality of chain objects gives an isomorphism of their groups. -/
def equivOfEq {A B : ChainObj E} (h : A = B) : A.grp ≃ₜ* B.grp := by
  subst h
  exact ContinuousMulEquiv.refl _

lemma toG_equivOfEq {A B : ChainObj E} (h : A = B) (x : A.grp) :
    B.toG (equivOfEq h x) = A.toG x := by
  subst h
  rfl

end ChainObj

namespace ElemOp

open ChainObj

variable {E E' : CuspidalExt.{u}} (A : ChainObj E) (j : A.grp →ₜ* E'.Pi)
  (hj : IsOpen (Set.range j)) (ι : E'.G →ₜ* E.G) (hι : Function.Injective ι)
  (hιo : IsOpen (Set.range ι)) (hcomp : ∀ x, ι (E'.pr (j x)) = A.toG x)
  (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi))

/-- **Entering a pushed run by an operation of type `⋎`**: `A ⇝ A.push j B'` with
`φ = ρ_{B'} ∘ j`, for `j` and `ρ_{B'}` injective (`B'` defined on all of `Π_{E'}`). -/
def toPush (hjinj : Function.Injective j) (hinj : Function.Injective (B'.rhoTop hB)) :
    ElemOp A (A.push j hj ι hι hιo hcomp B') :=
  .quot ((B'.rhoTop hB).comp j) (hinj.comp hjinj) (isOpen_range_rhoTop_comp j hj B' hB)
    ⟨(A.push j hj ι hι hιo hcomp B').dom, domOf_le (A.isOpen_comap_dom j B'), le_rfl,
      fun _ _ ↦ rfl⟩

lemma kind_toPush (hjinj : Function.Injective j) (hinj : Function.Injective (B'.rhoTop hB)) :
    (toPush A j hj ι hι hιo hcomp B' hB hjinj hinj).kind = .quot := rfl

end ElemOp

namespace ElemOp

open ChainObj

variable {E E' : CuspidalExt.{u}} (A : ChainObj E) (φ : E'.Pi →ₜ* A.grp)
  (hinj : Function.Injective φ) (hopen : IsOpen (Set.range φ)) (ι : E'.G →ₜ* E.G)
  (hι : Function.Injective ι) (hιo : IsOpen (Set.range ι))
  (hcomp : ∀ x, ι (E'.pr x) = A.toG (φ x))
  (B' : ChainObj E') (hB : ∀ x, x ∈ (B'.dom : Subgroup E'.Pi))
  (hbij : Function.Bijective (B'.rhoTop hB))

/-- `ContinuousMonoidHom.id` as an open map from the target of `⋏` to `Π_{E'}`. -/
lemma isOpen_range_id : IsOpen (Set.range (ContinuousMonoidHom.id E'.Pi)) := by
  rw [show Set.range (ContinuousMonoidHom.id E'.Pi) = Set.univ from
    Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩]
  exact isOpen_univ

/-- **Entering a pushed run by an operation of type `⋏`**: for an open immersion
`φ : Π_{E'} ↪ Π_A` and a chain object `B'` of `E'` with bijective `ρ_{B'}`, the operation
`A ⇝ (A.coverObj φ).push id B'` with `φ ∘ ρ_{B'}⁻¹`. -/
def coverPush :
    ElemOp A ((A.coverObj φ hinj hopen).push (E' := E') (ContinuousMonoidHom.id E'.Pi)
      (isOpen_range_id (E' := E')) ι hι hιo hcomp B') :=
  let e := continuousMulEquivOfBijective (B'.rhoTop hB) hbij
  .cover (φ.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm))
    (hinj.comp e.symm.injective)
    (by
      change IsOpen (Set.range (φ ∘ e.symm))
      rw [e.symm.surjective.range_comp]
      exact hopen)
    ⟨((A.coverObj φ hinj hopen).push (E' := E') (ContinuousMonoidHom.id E'.Pi)
        (isOpen_range_id (E' := E')) ι hι hιo hcomp B').dom,
      le_rfl, (domOf_le ((A.coverObj φ hinj hopen).isOpen_comap_dom
        (ContinuousMonoidHom.id E'.Pi) B')).trans (domOf_le (isOpen_coe_range φ hopen)),
      fun h hh ↦ by
        change φ (e.symm (B'.rho _)) = A.rho _
        have hx : B'.rho ((A.coverObj φ hinj hopen).jOn (ContinuousMonoidHom.id E'.Pi) B'
            ⟨h, hh⟩) = e ((A.coverObj φ hinj hopen).rho
              (Subgroup.inclusion (domOf_le ((A.coverObj φ hinj hopen).isOpen_comap_dom
                (ContinuousMonoidHom.id E'.Pi) B')) ⟨h, hh⟩)) := by
          change B'.rho _ = B'.rho _
          exact congrArg B'.rho (Subtype.ext rfl)
        refine (congrArg (fun z ↦ φ (e.symm z)) hx).trans ?_
        rw [e.symm_apply_apply, apply_coverObj_rho]
        rfl⟩

lemma kind_coverPush : (coverPush A φ hinj hopen ι hι hιo hcomp B' hB hbij).kind = .cover := rfl

end ElemOp

namespace OpPath

variable {E : CuspidalExt.{u}}

/-- The last object of a path is its target. -/
theorem objN_length : ∀ {A C : ChainObj E} (p : OpPath A C), p.objN p.length = C
  | _, _, nil _ => rfl
  | _, _, cons _ p => objN_length p

/-- **A terminal isomorphism to the trivial chain** from an isomorphism `Π_C ≃ Π` of the last
group with `Π`, compatible with the projections to `G` up to conjugation. -/
def terminalIso {C : ChainObj E} (p : OpPath (ChainObj.base E) C) (e : C.grp ≃ₜ* E.Pi)
    (g : E.G) (hg : ∀ x, E.pr (e x) = g * C.toG x * g⁻¹) :
    p.toPiChain.TerminalIso (PiChain.trivial E) where
  iso := (ChainObj.equivOfEq (objN_length p)).trans e
  over := ⟨g, fun x ↦ by
    change E.pr (e (ChainObj.equivOfEq (objN_length p) x)) = _
    rw [hg, ChainObj.toG_equivOfEq]
    rfl⟩

end OpPath

end Belyi.Anabelian
