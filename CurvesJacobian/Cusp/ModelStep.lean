/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GeomModel
import CurvesJacobian.Cusp.ChainPush

/-!
# Model steps across `⋏` and `⋎`: the group-theoretic part (MR8.5, option (A2), (A3))

For a geometric model `D` of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`) and an
elementary operation of type `⋏` or `⋎`, the model of the next chain object is the cover of `Y`
attached to an open normal subgroup of `Π_Y` obtained by a **normal core**; so only the
Galois correspondence for *normal* open subgroups is needed
(`CurvesJacobian.Cusp.exists_isFiniteEtale_range_eq`).

* `Belyi.Anabelian.isOpen_normalCore`: the normal core of an open subgroup of a compact group is
  open.
* **`Belyi.Anabelian.ChainObj.toG_apply_of_compat`**: an operation homomorphism compatible with
  the rigidifying homomorphisms is compatible with the projections to `G` (`G` slim;
  [AbsTopI] Def 4.2 (iii), (1Π): "uniquely determined").
* `GeomModel.quotCore`, `GeomModel.quotSub` (type `⋎`, `φ : A ↪ B`): `core_B(φ ι Π_Y)` and its
  preimage in `Π_Y`, open and normal, with `φ ι (quotSub) = quotCore`.
* `GeomModel.coverCore`, `GeomModel.coverSub`, `GeomModel.coverSubB` (type `⋏`, `φ : B ↪ A`):
  `core_A(ι Π_Y ∩ φ B)` and its preimages in `Π_Y` and in `B`, open and normal, with
  `ι (coverSub) = coverCore = φ (coverSubB)`.
-/

open Pi1.Profinite

universe u

noncomputable section

namespace Belyi.Anabelian

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **The normal core of an open subgroup of a compact group is open.** -/
theorem isOpen_normalCore {H : Subgroup G} (hH : IsOpen (H : Set G)) :
    IsOpen (H.normalCore : Set G) := by
  haveI := finiteIndex_of_isOpen hH
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (H.normalCore_isClosed (H.isClosed_of_isOpen hH))

end Core

namespace ChainObj

variable {E : CuspidalExt.{u}}

/-- **Compatibility with the rigidifying homomorphisms forces compatibility with the projections
to `G`** (`G` slim). -/
theorem toG_apply_of_compat {A B : ChainObj E} {φ : A.grp →ₜ* B.grp} (h : Compat A B φ)
    (a : A.grp) : B.toG (φ a) = A.toG a := by
  obtain ⟨H, hA, hB, hφ⟩ := h
  set V : Subgroup A.grp :=
    ((H : Subgroup E.Pi).subgroupOf (A.dom : Subgroup E.Pi)).map (A.rho : _ →* A.grp)
  haveI : CompactSpace (A.dom : Subgroup E.Pi) :=
    isCompact_iff_compactSpace.mp A.dom.isClosed.isCompact
  have hVopen : IsOpen (V : Set A.grp) :=
    isOpen_map_of_isOpen_range A.rho A.isOpen_range_rho
      (H.isOpen.preimage continuous_subtype_val)
  have hV : ∀ v ∈ V, B.toG (φ v) = A.toG v := by
    rintro _ ⟨⟨x, hxA⟩, hx, rfl⟩
    have hxH : x ∈ H := hx
    change B.toG (φ (A.rho ⟨x, hxA⟩)) = A.toG (A.rho ⟨x, hxA⟩)
    rw [hφ x hxH, B.toG_rho, A.toG_rho]
  set W := V.normalCore
  have hW : IsOpen (W : Set A.grp) := isOpen_normalCore hVopen
  have hcomm : ∀ u ∈ W.map (A.toG : A.grp →* E.G),
      ((A.toG a)⁻¹ * B.toG (φ a)) * u = u * ((A.toG a)⁻¹ * B.toG (φ a)) := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 : a * w * a⁻¹ ∈ V := V.normalCore_le ((V.normalCore_normal).conj_mem w hw a)
    have h2 := hV _ h1
    have h3 := hV w (V.normalCore_le hw)
    simp only [map_mul, map_inv] at h2
    rw [h3] at h2
    change ((A.toG a)⁻¹ * B.toG (φ a)) * A.toG w = A.toG w * ((A.toG a)⁻¹ * B.toG (φ a))
    calc ((A.toG a)⁻¹ * B.toG (φ a)) * A.toG w
        = (A.toG a)⁻¹ * (B.toG (φ a) * A.toG w * (B.toG (φ a))⁻¹) * B.toG (φ a) := by group
      _ = (A.toG a)⁻¹ * (A.toG a * A.toG w * (A.toG a)⁻¹) * B.toG (φ a) := by rw [h2]
      _ = A.toG w * ((A.toG a)⁻¹ * B.toG (φ a)) := by group
  have := E.slim_G ⟨W.map (A.toG : A.grp →* E.G),
    isOpen_map_of_isOpen_range A.toG A.isOpen_range_toG hW⟩ _ hcomm
  exact (inv_mul_eq_one.1 this).symm

end ChainObj

end Belyi.Anabelian

namespace CurvesJacobian.Cusp.GeomModel

open Belyi Belyi.Anabelian

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A B : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

/-- `ι(Π_Y)` as an open subgroup of `A`. -/
abbrev rangeι : Subgroup A.grp := (D.ι : D.Pi →* A.grp).range

lemma isOpen_rangeι : IsOpen (D.rangeι : Set A.grp) := by
  rw [MonoidHom.coe_range]
  exact D.isOpen_range

/-! ### Type `⋎`: `φ : A ↪ B` -/

/-- `core_B(φ(ι Π_Y))`. -/
def quotCore (φ : A.grp →ₜ* B.grp) : Subgroup B.grp :=
  (D.rangeι.map (φ : A.grp →* B.grp)).normalCore

instance (φ : A.grp →ₜ* B.grp) : (D.quotCore φ).Normal := Subgroup.normalCore_normal _

lemma isOpen_quotCore (φ : A.grp →ₜ* B.grp) (hφ : IsOpen (Set.range φ)) :
    IsOpen (D.quotCore φ : Set B.grp) :=
  isOpen_normalCore (isOpen_map_of_isOpen_range φ hφ D.isOpen_rangeι)

/-- The preimage of `quotCore` in `Π_Y`. -/
def quotSub (φ : A.grp →ₜ* B.grp) : Subgroup D.Pi :=
  (D.quotCore φ).comap ((φ : A.grp →* B.grp).comp (D.ι : D.Pi →* A.grp))

instance (φ : A.grp →ₜ* B.grp) : (D.quotSub φ).Normal := Subgroup.Normal.comap inferInstance _

lemma isOpen_quotSub (φ : A.grp →ₜ* B.grp) (hφ : IsOpen (Set.range φ)) :
    IsOpen (D.quotSub φ : Set D.Pi) :=
  (D.isOpen_quotCore φ hφ).preimage (φ.continuous.comp D.ι.continuous)

lemma map_quotSub (φ : A.grp →ₜ* B.grp) :
    (D.quotSub φ).map ((φ : A.grp →* B.grp).comp (D.ι : D.Pi →* A.grp)) = D.quotCore φ := by
  refine Subgroup.map_comap_eq_self ?_
  intro x hx
  obtain ⟨_, ⟨σ, rfl⟩, rfl⟩ := Subgroup.normalCore_le _ hx
  exact ⟨σ, rfl⟩

/-! ### Type `⋏`: `φ : B ↪ A` -/

/-- `core_A(ι Π_Y ∩ φ B)`. -/
def coverCore (φ : B.grp →ₜ* A.grp) : Subgroup A.grp :=
  (D.rangeι ⊓ (φ : B.grp →* A.grp).range).normalCore

instance (φ : B.grp →ₜ* A.grp) : (D.coverCore φ).Normal := Subgroup.normalCore_normal _

lemma isOpen_coverCore (φ : B.grp →ₜ* A.grp) (hφ : IsOpen (Set.range φ)) :
    IsOpen (D.coverCore φ : Set A.grp) := by
  refine isOpen_normalCore ?_
  rw [Subgroup.coe_inf, MonoidHom.coe_range]
  exact D.isOpen_rangeι.inter hφ

/-- The preimage of `coverCore` in `Π_Y`. -/
def coverSub (φ : B.grp →ₜ* A.grp) : Subgroup D.Pi :=
  (D.coverCore φ).comap (D.ι : D.Pi →* A.grp)

/-- The preimage of `coverCore` in `B`. -/
def coverSubB (φ : B.grp →ₜ* A.grp) : Subgroup B.grp :=
  (D.coverCore φ).comap (φ : B.grp →* A.grp)

instance (φ : B.grp →ₜ* A.grp) : (D.coverSub φ).Normal := Subgroup.Normal.comap inferInstance _

instance (φ : B.grp →ₜ* A.grp) : (D.coverSubB φ).Normal := Subgroup.Normal.comap inferInstance _

lemma isOpen_coverSub (φ : B.grp →ₜ* A.grp) (hφ : IsOpen (Set.range φ)) :
    IsOpen (D.coverSub φ : Set D.Pi) :=
  (D.isOpen_coverCore φ hφ).preimage D.ι.continuous

lemma isOpen_coverSubB (φ : B.grp →ₜ* A.grp) (hφ : IsOpen (Set.range φ)) :
    IsOpen (D.coverSubB φ : Set B.grp) :=
  (D.isOpen_coverCore φ hφ).preimage φ.continuous

lemma map_coverSub (φ : B.grp →ₜ* A.grp) :
    (D.coverSub φ).map (D.ι : D.Pi →* A.grp) = D.coverCore φ :=
  Subgroup.map_comap_eq_self fun _ hx ↦ (Subgroup.normalCore_le _ hx).1

lemma map_coverSubB (φ : B.grp →ₜ* A.grp) :
    (D.coverSubB φ).map (φ : B.grp →* A.grp) = D.coverCore φ :=
  Subgroup.map_comap_eq_self fun _ hx ↦ (Subgroup.normalCore_le _ hx).2

end CurvesJacobian.Cusp.GeomModel
