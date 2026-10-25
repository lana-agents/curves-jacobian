/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Assembly
import CurvesJacobian.CuspChar.Count
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The open subgroup fixing all cusps

Let `Γ` be a topological group, `D ⊆ Γ` a compact normal subgroup and `S` a set of closed
subgroups of `D` (the cusp groups) which is stable under conjugation by `Γ` and has only finitely
many `D`-conjugacy classes (`CurvesJacobian.CuspChar.CuspQuot S ⊤` finite). The subgroup
`CurvesJacobian.CuspChar.cuspStab D S` consists of the `x ∈ Γ` which map every cusp group to a
`D`-conjugate of itself (i.e. which fix every cusp of `D`). It contains `D`, and it is **open**
(`CurvesJacobian.CuspChar.isOpen_cuspStab`).

Proof: for a fixed `J ∈ S` the subgroup `cuspStabOf D J = {x | ∃ δ ∈ D, x J x⁻¹ = δ J δ⁻¹}` is the
product `D · {x | x J x⁻¹ = J}` of the compact set `D` and a closed set, hence closed; and
`x ↦ [x J x⁻¹]` injects its cosets into the finite set `CuspQuot S ⊤`, so it has finite index;
hence it is open. It only depends on the `D`-conjugacy class of `J`, so `cuspStab D S` contains the
finite intersection of the `cuspStabOf D J` over representatives `J` of the classes.
-/

namespace CurvesJacobian.CuspChar

open scoped Pointwise

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (D : Subgroup Γ)
  [D.Normal]

/-- The image `x J x⁻¹` of a subgroup `J ⊆ D` under conjugation by `x ∈ Γ`. -/
def conjDSub (x : Γ) (J : Subgroup D) : Subgroup D := J.map (conjD D x).toMulEquiv.toMonoidHom

variable {D}

lemma conjDSub_mul (x y : Γ) (J : Subgroup D) :
    conjDSub D (x * y) J = conjDSub D x (conjDSub D y J) := by
  simp only [conjDSub, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun z ↦ Subtype.ext ?_
  change x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹
  group

@[simp] lemma conjDSub_one (J : Subgroup D) : conjDSub D 1 J = J := by
  rw [conjDSub, show (conjD D 1).toMulEquiv.toMonoidHom = MonoidHom.id D from
    MonoidHom.ext fun z ↦ Subtype.ext (by change 1 * (z : Γ) * 1⁻¹ = z; group), Subgroup.map_id]

lemma conjDSub_coe (d : D) (J : Subgroup D) : conjDSub D (d : Γ) J = conjSub d J := rfl

lemma conjDSub_conjSub (x : Γ) (δ : D) (J : Subgroup D) :
    conjDSub D x (conjSub δ J) = conjSub (conjD D x δ) (conjDSub D x J) := by
  simp only [conjDSub, conjSub, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun z ↦ Subtype.ext ?_
  change x * ((δ : Γ) * z * (δ : Γ)⁻¹) * x⁻¹ = x * δ * x⁻¹ * (x * z * x⁻¹) * (x * δ * x⁻¹)⁻¹
  group

lemma conjD_mem_of_conjDSub_eq {x : Γ} {J : Subgroup D} (h : conjDSub D x J = J) {z : D}
    (hz : z ∈ J) : conjD D x z ∈ J := by
  have hz' := Subgroup.mem_map_of_mem (conjD D x).toMulEquiv.toMonoidHom hz
  rwa [← conjDSub, h] at hz'

/-- The subgroup of `x ∈ Γ` mapping `J ⊆ D` to a `D`-conjugate of itself (`D · N_Γ(J)`). -/
def cuspStabOf (J : Subgroup D) : Subgroup Γ where
  carrier := {x | ∃ δ : D, conjDSub D x J = conjSub δ J}
  one_mem' := ⟨1, by rw [conjDSub_one, conjSub_one]⟩
  mul_mem' := by
    rintro x y ⟨δx, hx⟩ ⟨δy, hy⟩
    exact ⟨conjD D x δy * δx, by rw [conjDSub_mul, hy, conjDSub_conjSub, hx, ← conjSub_mul]⟩
  inv_mem' := by
    rintro x ⟨δ, hx⟩
    have h := congrArg (conjDSub D x⁻¹) hx
    rw [← conjDSub_mul, inv_mul_cancel, conjDSub_one, conjDSub_conjSub] at h
    refine ⟨(conjD D x⁻¹ δ)⁻¹, ?_⟩
    conv_rhs => rw [h]
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

lemma mem_cuspStabOf {J : Subgroup D} {x : Γ} :
    x ∈ cuspStabOf J ↔ ∃ δ : D, conjDSub D x J = conjSub δ J := Iff.rfl

lemma le_cuspStabOf (J : Subgroup D) : D ≤ cuspStabOf J :=
  fun x hx ↦ ⟨⟨x, hx⟩, conjDSub_coe ⟨x, hx⟩ J⟩

/-- `cuspStabOf J` only depends on the `D`-conjugacy class of `J`. -/
lemma cuspStabOf_le_conjSub (J : Subgroup D) (d : D) : cuspStabOf J ≤ cuspStabOf (conjSub d J) := by
  rintro x ⟨δ, hx⟩
  refine ⟨conjD D x d * δ * d⁻¹, ?_⟩
  rw [conjDSub_conjSub, hx, ← conjSub_mul, ← conjSub_mul, inv_mul_cancel_right]

lemma coe_cuspStabOf_eq_mul (J : Subgroup D) :
    (cuspStabOf J : Set Γ) = (D : Set Γ) * {x | conjDSub D x J = J} := by
  ext x
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨δ, δ.2, (δ : Γ)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    change conjDSub D ((δ : Γ)⁻¹ * x) J = J
    rw [conjDSub_mul, hδ, show (δ : Γ)⁻¹ = ((δ⁻¹ : D) : Γ) from rfl, conjDSub_coe,
      conjSub_inv_conjSub]
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hb : conjDSub D b J = J := hb
    exact ⟨⟨a, ha⟩, by rw [conjDSub_mul, hb]; exact conjDSub_coe ⟨a, ha⟩ J⟩

lemma isClosed_setOf_conjDSub_eq {J : Subgroup D} (hJ : IsClosed (J : Set D)) :
    IsClosed {x : Γ | conjDSub D x J = J} := by
  have hc : ∀ z : D, Continuous fun x : Γ ↦ conjD D x z := fun z ↦
    continuous_induced_rng.2 (by simp only [Function.comp_def, conjD_apply_coe]; fun_prop)
  have he : {x : Γ | conjDSub D x J = J} =
      ⋂ z ∈ (J : Set D), {x : Γ | conjD D x z ∈ J ∧ conjD D x⁻¹ z ∈ J} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, SetLike.mem_coe]
    constructor
    · intro h z hz
      have h' : conjDSub D x⁻¹ J = J := by
        conv_lhs => rw [← h]
        rw [← conjDSub_mul, inv_mul_cancel, conjDSub_one]
      exact ⟨conjD_mem_of_conjDSub_eq h hz, conjD_mem_of_conjDSub_eq h' hz⟩
    · intro h
      refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun z hz ↦ (h z hz).1)
        fun z hz ↦ ⟨conjD D x⁻¹ z, (h z hz).2, Subtype.ext ?_⟩
      change x * (x⁻¹ * z * x⁻¹⁻¹) * x⁻¹ = z
      group
  rw [he]
  exact isClosed_biInter fun z _ ↦ (hJ.preimage (hc z)).inter (hJ.preimage ((hc z).comp
    continuous_inv))

lemma isClosed_cuspStabOf [CompactSpace D] {J : Subgroup D} (hJ : IsClosed (J : Set D)) :
    IsClosed (cuspStabOf J : Set Γ) := by
  rw [coe_cuspStabOf_eq_mul]
  exact (isClosed_setOf_conjDSub_eq hJ).mul_left_of_isCompact
    (isCompact_iff_compactSpace.2 ‹CompactSpace D›)

variable {S : Set (Subgroup D)}

/-- The cusp class of `x J x⁻¹`, as a function of the coset `x · cuspStabOf J`. -/
def cuspStabOfQuotMap (hS : ∀ x : Γ, ∀ J ∈ S, conjDSub D x J ∈ S) {J : Subgroup D} (hJ : J ∈ S) :
    Γ ⧸ cuspStabOf J → CuspQuot S ⊤ :=
  Quotient.lift (fun x ↦ Quotient.mk _ ⟨conjDSub D x J, hS x J hJ⟩) fun a b hab ↦ by
    obtain ⟨δ, hδ⟩ := QuotientGroup.leftRel_apply.1 hab
    refine Quotient.sound ⟨conjD D a δ, trivial, ?_⟩
    change conjSub (conjD D a δ) (conjDSub D a J) = conjDSub D b J
    rw [← conjDSub_conjSub, ← hδ, ← conjDSub_mul, mul_inv_cancel_left]

lemma cuspStabOfQuotMap_injective (hS : ∀ x : Γ, ∀ J ∈ S, conjDSub D x J ∈ S) {J : Subgroup D}
    (hJ : J ∈ S) : Function.Injective (cuspStabOfQuotMap hS hJ) := by
  rintro ⟨a⟩ ⟨b⟩ h
  have h' : (Quotient.mk (cuspSetoid S ⊤) ⟨conjDSub D a J, hS a J hJ⟩ : CuspQuot S ⊤) =
      Quotient.mk _ ⟨conjDSub D b J, hS b J hJ⟩ := h
  obtain ⟨g, -, e⟩ := Quotient.exact h'
  change conjSub g (conjDSub D a J) = conjDSub D b J at e
  change (a : Γ ⧸ cuspStabOf J) = b
  rw [QuotientGroup.eq]
  refine ⟨conjD D a⁻¹ g, ?_⟩
  rw [conjDSub_mul, ← e, conjDSub_conjSub, ← conjDSub_mul, inv_mul_cancel, conjDSub_one]

lemma finiteIndex_cuspStabOf (hS : ∀ x : Γ, ∀ J ∈ S, conjDSub D x J ∈ S)
    [Finite (CuspQuot S ⊤)] {J : Subgroup D} (hJ : J ∈ S) : (cuspStabOf J).FiniteIndex := by
  have : Finite (Γ ⧸ cuspStabOf J) := Finite.of_injective _ (cuspStabOfQuotMap_injective hS hJ)
  exact Subgroup.finiteIndex_of_finite_quotient

lemma isOpen_cuspStabOf [CompactSpace D] (hS : ∀ x : Γ, ∀ J ∈ S, conjDSub D x J ∈ S)
    [Finite (CuspQuot S ⊤)] {J : Subgroup D} (hJ : J ∈ S) (hJc : IsClosed (J : Set D)) :
    IsOpen (cuspStabOf J : Set Γ) :=
  have := finiteIndex_cuspStabOf hS hJ
  Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_cuspStabOf hJc)

variable (D S)

/-- The subgroup of `x ∈ Γ` mapping every cusp group `J ∈ S` to a `D`-conjugate of itself, i.e.
fixing every cusp of `D`. -/
def cuspStab : Subgroup Γ where
  carrier := {x | ∀ J ∈ S, ∃ δ : D, J.map (conjD D x).toMulEquiv.toMonoidHom = conjSub δ J}
  one_mem' J _ := (cuspStabOf J).one_mem
  mul_mem' hx hy J hJ := (cuspStabOf J).mul_mem (hx J hJ) (hy J hJ)
  inv_mem' hx J hJ := (cuspStabOf J).inv_mem (hx J hJ)

variable {D S}

lemma mem_cuspStab {x : Γ} : x ∈ cuspStab D S ↔
    ∀ J ∈ S, ∃ δ : D, J.map (conjD D x).toMulEquiv.toMonoidHom = conjSub δ J := Iff.rfl

lemma mem_cuspStab_iff_forall_mem_cuspStabOf {x : Γ} :
    x ∈ cuspStab D S ↔ ∀ J ∈ S, x ∈ cuspStabOf J := Iff.rfl

lemma inv_mem_cuspStab {x : Γ} (hx : x ∈ cuspStab D S) : x⁻¹ ∈ cuspStab D S :=
  (cuspStab D S).inv_mem hx

lemma le_cuspStab : D ≤ cuspStab D S := fun _ hx J _ ↦ le_cuspStabOf J hx

/-- The subgroup fixing all cusps is open: `D` is compact, the cusp groups are closed, `S` is
stable under conjugation by `Γ` and has finitely many `D`-conjugacy classes. -/
theorem isOpen_cuspStab [CompactSpace D] (hSc : ∀ J ∈ S, IsClosed (J : Set D))
    (hS : ∀ x : Γ, ∀ J ∈ S, J.map (conjD D x).toMulEquiv.toMonoidHom ∈ S)
    [Finite (CuspQuot S ⊤)] : IsOpen (cuspStab D S : Set Γ) := by
  let K : Subgroup Γ := ⨅ c : CuspQuot S ⊤, cuspStabOf (c.out : Subgroup D)
  have hK : IsOpen (K : Set Γ) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun c ↦ isOpen_cuspStabOf hS c.out.2 (hSc _ c.out.2)
  refine Subgroup.isOpen_mono (fun x hx J hJ ↦ ?_) hK
  have hc : (Quotient.mk (cuspSetoid S ⊤)
      (Quotient.mk (cuspSetoid S ⊤) ⟨J, hJ⟩ : CuspQuot S ⊤).out : CuspQuot S ⊤) =
      Quotient.mk _ ⟨J, hJ⟩ := Quotient.out_eq' _
  obtain ⟨g, -, e⟩ := Quotient.exact hc
  have hx' := cuspStabOf_le_conjSub _ g (Subgroup.mem_iInf.1 hx (Quotient.mk _ ⟨J, hJ⟩))
  rwa [e] at hx'

/-- `cuspStab D S` as an open subgroup of `Γ`. -/
def cuspStabOpen [CompactSpace D] (hSc : ∀ J ∈ S, IsClosed (J : Set D))
    (hS : ∀ x : Γ, ∀ J ∈ S, J.map (conjD D x).toMulEquiv.toMonoidHom ∈ S)
    [Finite (CuspQuot S ⊤)] : OpenSubgroup Γ :=
  ⟨cuspStab D S, isOpen_cuspStab hSc hS⟩

end CurvesJacobian.CuspChar
