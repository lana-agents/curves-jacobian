/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Final
import CurvesJacobian.CuspChar.SchreierRank
import CurvesJacobian.Cusp.CoverInstance
import CurvesJacobian.Cusp.CoverCuspComap
import CurvesJacobian.Cusp.ConjInducedCusps
import CurvesJacobian.Cusp.TwistGalois
import CurvesJacobian.Cusp.ChainPush
import CurvesJacobian.Cusp.CoverRangeOpen

/-!
# The cusp weight identity for all open `H ⊆ Δ_U` from the case `H = Δ_U`

Let `U` be an affine hyperbolic curve over a number field `K` with a cusp, `Δ_U ⊆ Π_U` its
geometric fundamental group. The cusp weight identity
`CurvesJacobian.CuspChar.CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) 3 (eulerU Ω C)
(cyc3 Ω C hc)` asks, for every open `H ⊆ Δ_U`, for an open `P ⊆ Π_U` normalising `H` on which
`det(x | Hom(H, ℤ/3^k))² = χ_k(x)^{[Δ_U : H] χ₀ + r_H}`. We reduce it to the case `H = Δ_U`
for **all** curves over number fields inside `Ω`
(**`CurvesJacobian.CuspChar.cuspWeightIdentity_of_top`**).

Proof. For `H ⊆ Δ_U` open choose an open subgroup `Q ⊆ Π_U` with `Q ∩ Δ_U = H`
(`exists_openSubgroup_inf_eq`: `Q = N · H` for an open normal `N` with `N ∩ Δ_U ⊆ H`), realise
`Q` as `π₁ᵉᵗ(V) ⊆ Π_U` for a connected finite étale cover `V → U`
(`exists_isFiniteEtale_range_eq_of_open`), and view `V` as a hyperbolic curve `U'` over its
constant field `K'` (`coverCurve`) with `ι : Π_{U'} ≃ π₁ᵉᵗ(V) ⊆ Π_U` (`coverIncl`). Then
* `ι` maps `Δ_{U'}` isomorphically onto `H` (`deltaEquiv`), compatibly with conjugation, so the
  character determinants agree (`charDet_coverIncl`, via `charDet_charRestrict`), and
  `[Δ_U : H] χ₀(U) = χ₀(U')` by counting `ℤ/2`-characters (`eulerU_cover`);
* the cyclotomic characters agree: `pr ∘ ι = conj(c) ∘ res ∘ pr'` and `res` is the inclusion
  `Gal(Ω/K') ⊆ Gal(Ω/K)` (`cyc3_coverIncl`);
* `J ↦ ι⁻¹(J)` is a bijection from the `H`-classes of cusp groups of `Δ_U` to the classes of cusp
  groups of `Δ_{U'}` (`cuspCount_cover`, via the abstract `cuspCount_eq_of_comap`): preimages of
  cusp groups are cusp groups (`comap_coverPiEquiv_mem_arithCusps`), every cusp group of `Δ_{U'}`
  is one (`eq_comap_of_map_le`), and two cusp groups with the same intersection with `H` agree
  (commensurators, `eq_of_inf_eq_arithCusps`).
-/

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

/-! ### Characters of an open subgroup and of a group isomorphic to it -/

section Restrict

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {D' : Type*} [Group D'] [TopologicalSpace D'] [IsTopologicalGroup D']
  (H : OpenSubgroup D) (Θ : D' ≃ₜ* (H : Subgroup D)) (p : ℕ)

omit [IsTopologicalGroup D'] in
lemma topMem (y : D') : y ∈ ((⊤ : OpenSubgroup D') : Subgroup D') := OpenSubgroup.mem_top y

/-- `⊤ ⊆ D' → H` along `Θ`, additively. -/
def topToSub : Additive ((⊤ : OpenSubgroup D') : Subgroup D') →+ Additive (H : Subgroup D) :=
  MonoidHom.toAdditive (Θ.toMulEquiv.toMonoidHom.comp
    ((⊤ : OpenSubgroup D') : Subgroup D').subtype)

/-- `H → ⊤ ⊆ D'` along `Θ⁻¹`, additively. -/
def subToTop : Additive (H : Subgroup D) →+ Additive ((⊤ : OpenSubgroup D') : Subgroup D') :=
  MonoidHom.toAdditive ((MonoidHom.codRestrict (MonoidHom.id D')
    ((⊤ : OpenSubgroup D') : Subgroup D') fun y ↦ topMem y).comp Θ.symm.toMulEquiv.toMonoidHom)

lemma topToSub_subToTop (a : Additive (H : Subgroup D)) :
    topToSub H Θ (subToTop H Θ a) = a := by
  change Additive.ofMul (Θ (Θ.symm (Additive.toMul a))) = a
  rw [ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]

lemma subToTop_topToSub (a : Additive ((⊤ : OpenSubgroup D') : Subgroup D')) :
    subToTop H Θ (topToSub H Θ a) = a := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change Θ.symm (Θ (Additive.toMul a).1) = (Additive.toMul a).1
  exact Θ.symm_apply_apply _

lemma comp_topToSub_mem (ζ : charSpace p H) :
    ζ.1.comp (topToSub H Θ) ∈ charSpace p (⊤ : OpenSubgroup D') := by
  change IsOpen (kerSub ((⊤ : OpenSubgroup D') : Subgroup D') (ζ.1.comp (topToSub H Θ)) : Set D')
  have e : (kerSub ((⊤ : OpenSubgroup D') : Subgroup D') (ζ.1.comp (topToSub H Θ)) : Set D') =
      (fun y ↦ (Θ y : D)) ⁻¹' (kerSub (H : Subgroup D) ζ.1 : Set D) := by
    ext y
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, mem_kerSub_iff, mem_kerSub_iff,
      ξv_of_mem (topMem y), ξv_of_mem (Θ y).2]
    exact ⟨fun h ↦ ⟨(Θ y).2, h.2⟩, fun h ↦ ⟨topMem y, h.2⟩⟩
  rw [e]
  exact ζ.2.preimage (continuous_subtype_val.comp Θ.continuous)

lemma comp_subToTop_mem (ζ : charSpace p (⊤ : OpenSubgroup D')) :
    ζ.1.comp (subToTop H Θ) ∈ charSpace p H := by
  change IsOpen (kerSub (H : Subgroup D) (ζ.1.comp (subToTop H Θ)) : Set D)
  have e : (kerSub (H : Subgroup D) (ζ.1.comp (subToTop H Θ)) : Set D) =
      Subtype.val '' (Θ.symm ⁻¹'
        (kerSub ((⊤ : OpenSubgroup D') : Subgroup D') ζ.1 : Set D')) := by
    ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, mem_kerSub_iff] at hx
      obtain ⟨hxH, hx0⟩ := hx
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      rw [Set.mem_preimage, SetLike.mem_coe, mem_kerSub_iff, ξv_of_mem (topMem _)]
      rw [ξv_of_mem hxH] at hx0
      exact ⟨topMem _, hx0⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_preimage, SetLike.mem_coe, mem_kerSub_iff, ξv_of_mem (topMem _)] at hz
      rw [SetLike.mem_coe, mem_kerSub_iff, ξv_of_mem z.2]
      exact ⟨z.2, hz.2⟩
  rw [e]
  have hHo : IsOpen ((H : Subgroup D) : Set D) := H.isOpen
  exact hHo.isOpenMap_subtype_val _ (ζ.2.preimage Θ.symm.continuous)

/-- **The continuous characters of `H` and of `D' ≅ H`**: `ξ ↦ ξ ∘ Θ`. -/
def charRestrict : charSpace p H ≃ₗ[ZMod p] charSpace p (⊤ : OpenSubgroup D') where
  toFun ζ := ⟨ζ.1.comp (topToSub H Θ), comp_topToSub_mem H Θ p ζ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ζ := ⟨ζ.1.comp (subToTop H Θ), comp_subToTop_mem H Θ p ζ⟩
  left_inv ζ := Subtype.ext (AddMonoidHom.ext fun a ↦ congrArg ζ.1 (topToSub_subToTop H Θ a))
  right_inv ζ := Subtype.ext (AddMonoidHom.ext fun a ↦ congrArg ζ.1 (subToTop_topToSub H Θ a))

lemma ξv_charRestrict (ζ : charSpace p H) (y : D') :
    ξv ((⊤ : OpenSubgroup D') : Subgroup D') (charRestrict H Θ p ζ).1 y =
      ξv (H : Subgroup D) ζ.1 (Θ y) := by
  rw [ξv_of_mem (topMem y), ξv_of_mem (Θ y).2]
  rfl

lemma ξv_charRestrict_symm (ζ : charSpace p (⊤ : OpenSubgroup D')) (z : (H : Subgroup D)) :
    ξv (H : Subgroup D) ((charRestrict H Θ p).symm ζ).1 z =
      ξv ((⊤ : OpenSubgroup D') : Subgroup D') ζ.1 (Θ.symm z) := by
  rw [ξv_of_mem z.2, ξv_of_mem (topMem _)]
  rfl

/-- **Transport of the character determinant to an open subgroup**: if `Θ : D' ≅ H` intertwines
`τ'` on `D'` and `τ` on `D` (with `τ(H) = H`), then `det(τ' | Hom(D', ℤ/p))` equals
`det(τ | Hom(H, ℤ/p))`. -/
theorem charDet_charRestrict (τ : D ≃ₜ* D) (hτ : mapOpenSub τ H = H) (τ' : D' ≃ₜ* D')
    (hτ' : mapOpenSub τ' ⊤ = ⊤) (hc : ∀ y, (Θ (τ' y) : D) = τ (Θ y)) :
    charDet (p := p) τ' ⊤ hτ' = charDet τ H hτ := by
  unfold charDet
  have hA : pullEquivOf (p := p) τ' ⊤ ⊤ hτ' = (((charRestrict H Θ p).symm.trans
      (pullEquivOf τ H H hτ)).trans (charRestrict H Θ p)) := by
    ext1 ζ
    apply charSpace_ext
    intro y
    rw [ξv_pullEquivOf, LinearEquiv.trans_apply, ξv_charRestrict, LinearEquiv.trans_apply,
      ξv_pullEquivOf, ← hc, ξv_charRestrict_symm, ContinuousMulEquiv.symm_apply_apply]
  rw [hA, LinearEquiv.det_conj]

include Θ in
/-- `D' ≅ H` have the same number of continuous `ℤ/p`-characters. -/
lemma natCard_charSpace_top_eq :
    Nat.card (charSpace p (⊤ : OpenSubgroup D')) = Nat.card (charSpace p H) :=
  (Nat.card_congr (charRestrict H Θ p).toEquiv).symm

end Restrict

/-! ### Conjugation by elements of an open subgroup `Q` with `Q ∩ D = H` -/

section Normalise

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {D : Subgroup Γ}
  [D.Normal]

/-- Elements of `Q` normalise `H = Q ∩ D`. -/
lemma mapOpenSub_conjD_of_mem (H : OpenSubgroup D) (Q : Subgroup Γ)
    (hkey : ∀ z : D, (z : Γ) ∈ Q ↔ z ∈ H) {x : Γ} (hx : x ∈ Q) :
    mapOpenSub (conjD D x) H = H := by
  ext y
  obtain ⟨z, rfl⟩ := (conjD D x).surjective y
  change conjD D x z ∈ (mapOpenSub (conjD D x) H : Subgroup D) ↔ conjD D x z ∈ (H : Subgroup D)
  rw [mem_mapOpenSub]
  change z ∈ H ↔ conjD D x z ∈ H
  rw [← hkey, ← hkey, conjD_apply_coe]
  constructor
  · intro hz
    exact Q.mul_mem (Q.mul_mem hx hz) (Q.inv_mem hx)
  · intro hz
    have h1 := Q.mul_mem (Q.mul_mem (Q.inv_mem hx) hz) hx
    have e : x⁻¹ * (x * (z : Γ) * x⁻¹) * x = z := by group
    rwa [e] at h1

/-- **An open subgroup `Q` of a profinite group with `Q ∩ D = H`** for `H ⊆ D` open: `Q = N · H`
for an open normal `N` with `N ∩ D ⊆ H`. -/
theorem exists_openSubgroup_inf_eq [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (D : Subgroup Γ) (H : OpenSubgroup D) :
    ∃ Q : OpenSubgroup Γ, ∀ z : D, (z : Γ) ∈ Q ↔ z ∈ H := by
  obtain ⟨O, hO, hOH⟩ := isOpen_induced_iff.1 H.isOpen
  have h1 : (1 : Γ) ∈ O := by
    have : (1 : D) ∈ (H : Set D) := H.one_mem
    rw [← hOH] at this
    exact this
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  let H' : Subgroup Γ := (H : Subgroup D).map D.subtype
  have hNo : IsOpen (N.toSubgroup : Set Γ) := N.toOpenSubgroup.isOpen
  have hQo : IsOpen ((N.toSubgroup ⊔ H' : Subgroup Γ) : Set Γ) :=
    Subgroup.isOpen_mono le_sup_left hNo
  refine ⟨⟨N.toSubgroup ⊔ H', hQo⟩, fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩⟩
  · have hz' : (z : Γ) ∈ ((N.toSubgroup ⊔ H' : Subgroup Γ) : Set Γ) := hz
    rw [Subgroup.normal_mul] at hz'
    obtain ⟨n, hn, w', hw', hnw⟩ := hz'
    obtain ⟨w, hw, rfl⟩ := hw'
    have hnz : n = (z : Γ) * (w : Γ)⁻¹ := eq_mul_inv_of_mul_eq hnw
    have hnD : n ∈ D := by
      rw [hnz]
      exact D.mul_mem z.2 (D.inv_mem w.2)
    have hnO : n ∈ O := hN hn
    have hnH : (⟨n, hnD⟩ : D) ∈ H := by
      have : (⟨n, hnD⟩ : D) ∈ Subtype.val ⁻¹' O := hnO
      rw [hOH] at this
      exact this
    have e : z = ⟨n, hnD⟩ * w := Subtype.ext hnw.symm
    rw [e]
    exact H.mul_mem hnH hw
  · change (z : Γ) ∈ N.toSubgroup ⊔ H'
    exact Subgroup.mem_sup_right ⟨z, hz, rfl⟩

end Normalise

/-! ### Cusp counts along an embedding onto `H` -/

section CuspTransport

variable {D : Type*} [Group D] {D' : Type*} [Group D'] (φ : D' →* D)

lemma comap_conjSub (d : D') (J : Subgroup D) :
    (conjSub (φ d) J).comap φ = conjSub d (J.comap φ) := by
  ext x
  rw [Subgroup.mem_comap, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_comap, map_mul, map_mul,
    map_inv]

lemma inf_eq_of_comap_eq {H : Subgroup D} (hφ : φ.range = H) {J₁ J₂ : Subgroup D}
    (e : J₁.comap φ = J₂.comap φ) : J₁ ⊓ H = J₂ ⊓ H := by
  have k : ∀ J : Subgroup D, J ⊓ H = (J.comap φ).map φ := fun J ↦ by
    rw [Subgroup.map_comap_eq, hφ, inf_comm]
  rw [k, k, e]

/-- **Cusp counts along an injective map `φ : D' → D` onto `H`**: if `J ↦ φ⁻¹(J)` maps the cusp
groups `S` of `D` onto the cusp groups `S'` of `D'` and `J` is determined by `J ∩ H`, then
`D'` has as many cusps as `H`. -/
theorem cuspCount_eq_of_comap {S : Set (Subgroup D)} {S' : Set (Subgroup D')} (H : Subgroup D)
    (hφ : φ.range = H) (hS : ConjStable S) (h1 : ∀ J ∈ S, J.comap φ ∈ S')
    (h2 : ∀ J' ∈ S', ∃ J ∈ S, J.comap φ = J')
    (h3 : ∀ J₁ ∈ S, ∀ J₂ ∈ S, J₁ ⊓ H = J₂ ⊓ H → J₁ = J₂) :
    cuspCount S' ⊤ = cuspCount S H := by
  let F : CuspQuot S H → CuspQuot S' ⊤ :=
    Quotient.map' (fun J ↦ ⟨(J : Subgroup D).comap φ, h1 _ J.2⟩) (by
      rintro J₁ J₂ ⟨d, hd, e⟩
      rw [← hφ] at hd
      obtain ⟨d', rfl⟩ := hd
      refine ⟨d', Subgroup.mem_top d', ?_⟩
      change conjSub d' ((J₁ : Subgroup D).comap φ) = (J₂ : Subgroup D).comap φ
      rw [← comap_conjSub, e])
  have hsurj : Function.Surjective F := by
    intro q
    induction q using Quotient.inductionOn' with
    | h J' =>
      obtain ⟨J, hJ, e⟩ := h2 J'.1 J'.2
      exact ⟨Quotient.mk'' ⟨J, hJ⟩, congrArg Quotient.mk'' (Subtype.ext e)⟩
  have hinj : Function.Injective F := by
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn' with
    | h J₁ =>
      induction q₂ using Quotient.inductionOn' with
      | h J₂ =>
        intro he
        have he' : (Quotient.mk'' ⟨(J₁ : Subgroup D).comap φ, h1 _ J₁.2⟩ : CuspQuot S' ⊤) =
            Quotient.mk'' ⟨(J₂ : Subgroup D).comap φ, h1 _ J₂.2⟩ := he
        obtain ⟨d, -, e⟩ := Quotient.exact' he'
        apply Quotient.sound'
        refine ⟨φ d, by rw [← hφ]; exact ⟨d, rfl⟩, ?_⟩
        have e' : (conjSub (φ d) (J₁ : Subgroup D)).comap φ = (J₂ : Subgroup D).comap φ := by
          rw [comap_conjSub]
          exact e
        exact h3 _ (hS _ J₁.2 _) _ J₂.2 (inf_eq_of_comap_eq φ hφ e')
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

end CuspTransport

/-! ### The cyclotomic character along `Gal(Ω/K') ⊆ Gal(Ω/K)` -/

section Cyc

lemma cycChar_restrictScalars {K K' Ω : Type*} [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] [IsAlgClosed Ω] [CharZero Ω] (l k : ℕ)
    [NeZero l] (σ : Ω ≃ₐ[K'] Ω) :
    cycChar K Ω l k (σ.restrictScalars K) = cycChar K' Ω l k σ := by
  have e : MulSemiringAction.toRingAut (Ω ≃ₐ[K] Ω) Ω (σ.restrictScalars K) =
      MulSemiringAction.toRingAut (Ω ≃ₐ[K'] Ω) Ω σ := RingEquiv.ext fun _ ↦ rfl
  unfold cycChar
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e]

lemma map_conj_comm {G A : Type*} [Group G] [CommGroup A] (χ : G →* A) (c g : G) :
    χ (c * g * c⁻¹) = χ g := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end Cyc

/-! ### Cusp groups of `Π_U` -/

section Arith

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Two cuspidal inertia groups of `Π_U` with the same intersection with a finite index
subgroup agree** (they are commensurable, and `I = Comm(I) ∩ Δ_U`). -/
theorem eq_of_inf_eq_arithCusps (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {I₁ I₂ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (h₁ : I₁ ∈ arithCusps Ω C hc) (h₂ : I₂ ∈ arithCusps Ω C hc)
    (Q : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) [Q.FiniteIndex]
    (e : I₁ ⊓ Q = I₂ ⊓ Q) : I₁ = I₂ := by
  have c : ∀ I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      Subgroup.Commensurable I (I ⊓ Q) := fun I ↦ by
    haveI : Q.IsFiniteRelIndex I := Subgroup.isFiniteRelIndex_of_finiteIndex
    refine ⟨?_, ?_⟩
    · rw [Subgroup.relIndex_eq_one.2 inf_le_left]
      exact one_ne_zero
    · rw [Subgroup.inf_relIndex_left]
      exact Subgroup.relIndex_ne_zero
  have hcom : Subgroup.Commensurable I₁ I₂ := (c I₁).trans (by rw [e]; exact (c I₂).symm)
  calc I₁ = Subgroup.Commensurable.commensurator I₁ ⊓ (projGk Ω C hc).toMonoidHom.ker :=
        (commensurator_inf_of_mem_arithCusps Ω C hc h₁).symm
    _ = Subgroup.Commensurable.commensurator I₂ ⊓ (projGk Ω C hc).toMonoidHom.ker := by
        rw [Subgroup.Commensurable.eq hcom]
    _ = I₂ := commensurator_inf_of_mem_arithCusps Ω C hc h₂

/-- **A cusp group of `Δ_U` is determined by its intersection with an open `H ⊆ Δ_U`.** -/
theorem eq_of_inf_eq_deltaCusps (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (Q : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (hQ : IsOpen (Q : Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))))
    (H : OpenSubgroup (deltaU Ω C hc))
    (hkey : ∀ z : deltaU Ω C hc,
      (z : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈ Q ↔ z ∈ H)
    {J₁ J₂ : Subgroup (deltaU Ω C hc)} (h₁ : J₁ ∈ deltaCusps Ω C hc)
    (h₂ : J₂ ∈ deltaCusps Ω C hc)
    (e : J₁ ⊓ (H : Subgroup (deltaU Ω C hc)) = J₂ ⊓ (H : Subgroup (deltaU Ω C hc))) :
    J₁ = J₂ := by
  haveI := finiteIndex_of_isOpen hQ
  have key : ∀ J : Subgroup (deltaU Ω C hc), J.map (deltaU Ω C hc).subtype ⊓ Q =
      (J ⊓ (H : Subgroup (deltaU Ω C hc))).map (deltaU Ω C hc).subtype := by
    intro J
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxQ⟩
      exact ⟨y, ⟨hy, (hkey y).1 hxQ⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyH⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (hkey y).2 hyH⟩
  have e' : J₁.map (deltaU Ω C hc).subtype ⊓ Q = J₂.map (deltaU Ω C hc).subtype ⊓ Q := by
    rw [key, key, e]
  exact Subgroup.map_injective (Subgroup.subtype_injective _)
    (eq_of_inf_eq_arithCusps Ω C hc h₁ h₂ Q e')

/-- **(B2) for an injective `ι : Π_{U'} → Π_U` with `ι⁻¹(Δ_U) ⊆ Δ_{U'}`**: a cusp group `J` of
`Π_{U'}` mapping into a cusp group `I` of `Π_U` with finite index is `ι⁻¹(I)`. -/
theorem eq_comap_of_map_le (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {K' : Type u} [Field K'] [NumberField K'] [Algebra K' Ω] [Algebra.IsAlgebraic K' Ω]
    (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) →*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (hinj : Function.Injective ι) (hker : ∀ γ, ι γ ∈ deltaU Ω C hc → γ ∈ deltaU Ω C' hc')
    {J} (hJ : J ∈ arithCusps Ω C' hc') {I} (hI : I ∈ arithCusps Ω C hc) (hJI : J.map ι ≤ I)
    (hfin : (J.map ι).relIndex I ≠ 0) : J = I.comap ι := by
  have hle : J ≤ I.comap ι := Subgroup.map_le_iff_le_comap.1 hJI
  have hfin' : J.relIndex (I.comap ι) ≠ 0 := by
    have h1 : J.map ι ≤ ι.range ⊓ I := le_inf (Subgroup.map_le_range ι J) hJI
    have h2 := Subgroup.relIndex_mul_relIndex (J.map ι) (ι.range ⊓ I) I h1 inf_le_right
    have h3 : (J.map ι).relIndex (ι.range ⊓ I) ≠ 0 := left_ne_zero_of_mul (h2.symm ▸ hfin)
    have e1 := Subgroup.relIndex_map_map_of_injective J (I.comap ι) hinj
    have e2 : (I.comap ι).map ι = ι.range ⊓ I := Subgroup.map_comap_eq ι I
    exact e1 ▸ e2.symm ▸ h3
  have hcomm : Subgroup.Commensurable J (I.comap ι) :=
    ⟨hfin', (Subgroup.relIndex_eq_one.2 hle).symm ▸ one_ne_zero⟩
  refine le_antisymm hle ?_
  rw [← commensurator_inf_of_mem_arithCusps Ω C' hc' hJ, Subgroup.Commensurable.eq hcomm]
  exact le_inf (fun g hg ↦ mem_commensurator_of_mem hg)
    (fun g hg ↦ hker g (arithCusps_le Ω C hc hI (Subgroup.mem_comap.1 hg)))

/-- `G_{K'} → G_K` is the inclusion `Gal(Ω/K') ⊆ Gal(Ω/K)`. -/
lemma gkEquivGal_galoisMap {K' : Type u} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' Ω]
    [IsScalarTower K K' Ω] [Algebra.IsAlgebraic K' Ω]
    (s : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω)))) :
    gkEquivGal (K := K) Ω (galoisMap K K' Ω s) = (gkEquivGal (K := K') Ω s).restrictScalars K := by
  obtain ⟨σ, rfl⟩ := (mulEquivAutFiber K' Ω).surjective s
  have h1 := res_mulEquivAutFiber (K := K) (Ω := Ω) K' σ
  change (mulEquivAutFiber K Ω).symm (resGal K Ω K' (mulEquivAutFiber K' Ω σ)) =
    ((mulEquivAutFiber K' Ω).symm (mulEquivAutFiber K' Ω σ)).restrictScalars K
  rw [h1, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end Arith

/-! ### A cover realising `Q ⊆ Π_U` -/

section Cover

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  {V : Scheme.{u}} (f : V ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f] [ConnectedSpace V]
  (η : Spec (.of Ω) ⟶ V) (h : η ≫ f = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
  {K' : Type u} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra.IsAlgebraic K' Ω] (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (e : Spec Γ(C'.Xbar, C'.U) ≅ V)
  (he : e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `ι : Π_{U'} ≃ π₁ᵉᵗ(V) ⊆ Π_U`. -/
abbrev coverIncl : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) →*
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (coverPiIncl Ω C hc f η h).toMonoidHom.comp
    (coverPiEquiv Ω C hc f η h C' hc' e).toMulEquiv.toMonoidHom

/-- `ι` as a continuous homomorphism. -/
def coverInclC : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) →ₜ*
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  ⟨coverIncl Ω C hc f η h C' hc' e,
    (coverPiIncl Ω C hc f η h).continuous.comp (coverPiEquiv Ω C hc f η h C' hc' e).continuous⟩

lemma coverIncl_mem (γ : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) :
    coverIncl Ω C hc f η h C' hc' e γ ∈
      (coverSubgroup f η h : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :=
  (coverPiEquiv Ω C hc f η h C' hc' e γ).2

lemma exists_coverIncl_eq {y : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hy : y ∈ (coverSubgroup f η h :
      Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))) :
    ∃ γ, coverIncl Ω C hc f η h C' hc' e γ = y :=
  ⟨(coverPiEquiv Ω C hc f η h C' hc' e).symm ⟨y, hy⟩,
    congrArg (coverPiIncl Ω C hc f η h) ((coverPiEquiv Ω C hc f η h C' hc' e).apply_symm_apply _)⟩

lemma coverIncl_injective : Function.Injective (coverIncl Ω C hc f η h C' hc' e) := by
  intro a b hab
  apply (coverPiEquiv Ω C hc f η h C' hc' e).injective
  exact Subtype.ext hab

include he in
lemma projGk_coverIncl
    (γ : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) :
    projGk Ω C hc (coverIncl Ω C hc f η h C' hc' e γ) =
      coverConj Ω C hc f η h C' hc' e he * galoisMap K K' Ω (projGk Ω C' hc' γ) *
        (coverConj Ω C hc f η h C' hc' e he)⁻¹ :=
  toG_coverPiEquiv Ω C hc f η h C' hc' e he γ

include he in
lemma coverIncl_mem_deltaU_iff
    (γ : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) :
    coverIncl Ω C hc f η h C' hc' e γ ∈ deltaU Ω C hc ↔ γ ∈ deltaU Ω C' hc' := by
  change projGk Ω C hc (coverIncl Ω C hc f η h C' hc' e γ) = 1 ↔ projGk Ω C' hc' γ = 1
  rw [projGk_coverIncl Ω C hc f η h C' hc' e he]
  exact conj_eq_one_iff.trans (map_eq_one_iff _ (galoisMap_injective K K' Ω))

include he in
/-- **The cyclotomic characters agree along `ι`.** -/
lemma cyc3_coverIncl (γ : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))
    (k : ℕ) : cyc3 Ω C hc k (coverIncl Ω C hc f η h C' hc' e γ) = cyc3 Ω C' hc' k γ := by
  set χ := (cycChar K Ω 3 k).comp (gkEquivGal (K := K) Ω).toMulEquiv.toMonoidHom
  calc cyc3 Ω C hc k (coverIncl Ω C hc f η h C' hc' e γ) =
        χ (coverConj Ω C hc f η h C' hc' e he * galoisMap K K' Ω (projGk Ω C' hc' γ) *
          (coverConj Ω C hc f η h C' hc' e he)⁻¹) := by
        rw [← projGk_coverIncl Ω C hc f η h C' hc' e he]
        rfl
    _ = χ (galoisMap K K' Ω (projGk Ω C' hc' γ)) := map_conj_comm χ _ _
    _ = cycChar K Ω 3 k ((gkEquivGal (K := K') Ω (projGk Ω C' hc' γ)).restrictScalars K) :=
        congrArg (cycChar K Ω 3 k) (gkEquivGal_galoisMap Ω (projGk Ω C' hc' γ))
    _ = cyc3 Ω C' hc' k γ := cycChar_restrictScalars 3 k _

lemma isOpen_map_coverIncl
    (P' : Subgroup π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))
    (hP' : IsOpen (P' : Set π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))) :
    IsOpen ((P'.map (coverIncl Ω C hc f η h C' hc' e) :
      Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
        Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) := by
  have hR : Set.range (coverInclC Ω C hc f η h C' hc' e) =
      ((coverSubgroup f η h : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫
        baseChangeSpec K Ω Γ(C.Xbar, C.U))) : Set π₁ᵉᵗ(basePoint Ω C hc ≫
          baseChangeSpec K Ω Γ(C.Xbar, C.U))) := by
    ext y
    constructor
    · rintro ⟨γ, rfl⟩
      exact coverIncl_mem Ω C hc f η h C' hc' e γ
    · intro hy
      exact exists_coverIncl_eq Ω C hc f η h C' hc' e hy
  have hRo : IsOpen (Set.range (coverInclC Ω C hc f η h C' hc' e)) := by
    rw [hR]
    exact (coverSubgroup f η h).isOpen
  exact isOpen_map_of_isOpen_range (coverInclC Ω C hc f η h C' hc' e) hRo hP'

variable (H : OpenSubgroup (deltaU Ω C hc))
  (hkey : ∀ z : deltaU Ω C hc, (z : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
    (coverSubgroup f η h : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ↔
      z ∈ H)

/-- `ι : Δ_{U'} → H`. -/
def deltaHom : deltaU Ω C' hc' →ₜ* (H : Subgroup (deltaU Ω C hc)) where
  toFun y := ⟨⟨coverIncl Ω C hc f η h C' hc' e
      (y : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))),
    (coverIncl_mem_deltaU_iff Ω C hc f η h C' hc' e he y).2 y.2⟩,
    (hkey _).1 (coverIncl_mem Ω C hc f η h C' hc' e
      (y : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))))⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (coverIncl Ω C hc f η h C' hc' e)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (coverIncl Ω C hc f η h C' hc' e)
    (a : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) b))
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
    ((coverInclC Ω C hc f η h C' hc' e).continuous.comp continuous_subtype_val) _) _

lemma deltaHom_bijective : Function.Bijective (deltaHom Ω C hc f η h C' hc' e he H hkey) := by
  refine ⟨fun a b hab ↦ Subtype.ext (coverIncl_injective Ω C hc f η h C' hc' e ?_), fun z ↦ ?_⟩
  · have := congrArg (fun z : (H : Subgroup (deltaU Ω C hc)) ↦
      ((z : deltaU Ω C hc) : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))) hab
    exact this
  · have hz := (hkey (z : deltaU Ω C hc)).2 z.2
    obtain ⟨γ, hγ⟩ := exists_coverIncl_eq Ω C hc f η h C' hc' e hz
    have hγD : γ ∈ deltaU Ω C' hc' := by
      rw [← coverIncl_mem_deltaU_iff Ω C hc f η h C' hc' e he, hγ]
      exact (z : deltaU Ω C hc).2
    exact ⟨⟨γ, hγD⟩, Subtype.ext (Subtype.ext hγ)⟩

/-- **`ι : Δ_{U'} ≃ₜ* H`.** -/
def deltaEquiv : deltaU Ω C' hc' ≃ₜ* (H : Subgroup (deltaU Ω C hc)) :=
  continuousMulEquivOfBijective (deltaHom Ω C hc f η h C' hc' e he H hkey)
    (deltaHom_bijective Ω C hc f η h C' hc' e he H hkey)

include he hkey in
/-- **The character determinants agree along `ι`.** -/
lemma charDet_coverIncl (m : ℕ)
    (x' : π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))
    (hP : mapOpenSub (conjD (deltaU Ω C hc) (coverIncl Ω C hc f η h C' hc' e x')) H = H) :
    charDet (p := m) (conjD (deltaU Ω C hc) (coverIncl Ω C hc f η h C' hc' e x')) H hP =
      charDet (p := m) (conjD (deltaU Ω C' hc') x') ⊤ (mapOpenSub_top _) := by
  refine (charDet_charRestrict H (deltaEquiv Ω C hc f η h C' hc' e he H hkey) m _ hP _ _
    fun y ↦ ?_).symm
  apply Subtype.ext
  change coverIncl Ω C hc f η h C' hc' e (x' * (y : π₁ᵉᵗ(basePoint Ω C' hc' ≫
      baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) * x'⁻¹) =
    coverIncl Ω C hc f η h C' hc' e x' * coverIncl Ω C hc f η h C' hc' e y *
      (coverIncl Ω C hc f η h C' hc' e x')⁻¹
  rw [map_mul, map_mul, map_inv]

include hc' he hkey in
/-- **`χ₀(U') = [Δ_U : H] χ₀(U)`** (counting `ℤ/2`-characters of `Δ_{U'} ≅ H`). -/
lemma eulerU_cover : eulerU Ω C' = (H : Subgroup (deltaU Ω C hc)).index * eulerU Ω C := by
  obtain ⟨Φ, -⟩ := exists_equiv_deltaCusps_subset Ω C hc
  have hgr : 2 ≤ 2 * genusU Ω C + cuspsU Ω C := by
    have := isHyperbolic_genusU Ω C
    unfold Pi1.SurfaceGroup.IsHyperbolic at this
    omega
  have e1 : 2 ^ (eulerU Ω C' + 1) =
      2 ^ ((H : Subgroup (deltaU Ω C hc)).index * (2 * genusU Ω C + cuspsU Ω C - 2) + 1) :=
    ((card_charSpace_two_deltaU Ω C' hc').symm.trans
      (natCard_charSpace_top_eq H (deltaEquiv Ω C hc f η h C' hc' e he H hkey) 2)).trans
      (natCard_charSpace Φ (cuspsU_pos Ω C hc) hgr 2 H)
  have e2 := Nat.pow_right_injective (le_refl 2) e1
  change eulerU Ω C' = (H : Subgroup (deltaU Ω C hc)).index * (2 * genusU Ω C + cuspsU Ω C - 2)
  omega

/-- The map `Δ_{U'} → Δ_U` (onto `H`). -/
abbrev deltaIncl : deltaU Ω C' hc' →* deltaU Ω C hc :=
  (H : Subgroup (deltaU Ω C hc)).subtype.comp
    (deltaHom Ω C hc f η h C' hc' e he H hkey).toMonoidHom

include he hkey in
/-- **`Δ_{U'}` has as many cusps as `H`.** -/
lemma cuspCount_cover :
    cuspCount (deltaCusps Ω C' hc') ⊤ =
      cuspCount (deltaCusps Ω C hc) (H : Subgroup (deltaU Ω C hc)) := by
  set φ := deltaIncl Ω C hc f η h C' hc' e he H hkey
  have hφ : φ.range = (H : Subgroup (deltaU Ω C hc)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (deltaHom Ω C hc f η h C' hc' e he H hkey y).2
    · intro hz
      obtain ⟨y, hy⟩ := (deltaHom_bijective Ω C hc f η h C' hc' e he H hkey).2 ⟨z, hz⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  refine cuspCount_eq_of_comap φ _ hφ (conjStable_deltaCusps Ω C hc) ?_ ?_ ?_
  · intro J hJ
    have hJ' := comap_coverPiEquiv_mem_arithCusps Ω C hc C' hc' f η h e he
      (J := J.map (deltaU Ω C hc).subtype) hJ
    change (J.comap φ).map (deltaU Ω C' hc').subtype ∈ arithCusps Ω C' hc'
    suffices e0 : (J.comap φ).map (deltaU Ω C' hc').subtype = (J.map (deltaU Ω C hc).subtype).comap
        (coverIncl Ω C hc f η h C' hc' e) by
      rw [e0]
      exact hJ'
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      exact Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨φ y, hy, rfl⟩)
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hz)
      have h0 : coverIncl Ω C hc f η h C' hc' e z =
          (w : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) := hwz.symm
      have hzD : z ∈ deltaU Ω C' hc' := by
        rw [← coverIncl_mem_deltaU_iff Ω C hc f η h C' hc' e he, h0]
        exact w.2
      refine Subgroup.mem_map.2 ⟨⟨z, hzD⟩, ?_, rfl⟩
      have hw' : φ ⟨z, hzD⟩ = w := Subtype.ext h0
      change φ ⟨z, hzD⟩ ∈ J
      rw [hw']
      exact hw
  · intro J' hJ'
    haveI : IsFiniteEtale e.hom := {}
    haveI : IsFiniteEtale (e.hom ≫ f) :=
      MorphismProperty.comp_mem _ _ _ (inferInstanceAs (IsFiniteEtale e.hom)) ‹_›
    obtain ⟨I, hI, hJI, hfin⟩ := exists_arithCusps_map_le_of_conjInduced Ω C hc C' hc'
      (e.hom ≫ f) (coverIncl Ω C hc f η h C' hc' e)
      ((isConjInduced_coverPiEquiv Ω C hc C' hc' f η h e).congr_fun fun _ ↦ rfl)
      (J := J'.map (deltaU Ω C' hc').subtype) hJ'
    have hJeq := eq_comap_of_map_le Ω C hc C' hc' (coverIncl Ω C hc f η h C' hc' e)
      (coverIncl_injective Ω C hc f η h C' hc' e)
      (fun γ hγ ↦ (coverIncl_mem_deltaU_iff Ω C hc f η h C' hc' e he γ).1 hγ)
      (J := J'.map (deltaU Ω C' hc').subtype) hJ' hI hJI hfin
    refine ⟨I.subgroupOf (deltaU Ω C hc),
      (mem_arithCusps_iff_mem_deltaCusps Ω C hc (arithCusps_le Ω C hc hI)).1 hI, ?_⟩
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change coverIncl Ω C hc f η h C' hc' e (y : π₁ᵉᵗ(basePoint Ω C' hc' ≫
      baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) ∈ I ↔ _
    rw [← Subgroup.mem_comap, ← hJeq]
    exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)
  · intro J₁ h₁ J₂ h₂ e'
    exact eq_of_inf_eq_deltaCusps Ω C hc _ (coverSubgroup f η h).isOpen H hkey h₁ h₂ e'

include he hkey in
/-- **The cusp weight identity for `H` from the one for `Δ_{U'}`** (`U'` the cover with
`Δ_{U'} ≅ H`). -/
theorem exists_weight_of_cover
    (P' : Subgroup π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))
    (hP'o : IsOpen (P' : Set π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))))
    (hP' : ∀ x ∈ P', ∀ k : ℕ,
      charDet (p := 3 ^ k) (conjD (deltaU Ω C' hc') x) ⊤ (mapOpenSub_top _) ^ 2 =
        cyc3 Ω C' hc' k x ^ (eulerU Ω C' + cuspCount (deltaCusps Ω C' hc') ⊤)) :
    ∃ P : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      IsOpen (P : Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∧
      ∃ hP : ∀ x ∈ P, mapOpenSub (conjD (deltaU Ω C hc) x) H = H, ∀ x (hx : x ∈ P) (k : ℕ),
        charDet (p := 3 ^ k) (conjD (deltaU Ω C hc) x) H (hP x hx) ^ 2 =
          cyc3 Ω C hc k x ^ ((H : Subgroup (deltaU Ω C hc)).index * eulerU Ω C +
            cuspCount (deltaCusps Ω C hc) (H : Subgroup (deltaU Ω C hc))) := by
  have hmem : ∀ x ∈ P'.map (coverIncl Ω C hc f η h C' hc' e),
      x ∈ (coverSubgroup f η h :
        Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) := by
    rintro _ ⟨x', -, rfl⟩
    exact coverIncl_mem Ω C hc f η h C' hc' e x'
  refine ⟨P'.map (coverIncl Ω C hc f η h C' hc' e), isOpen_map_coverIncl Ω C hc f η h C' hc' e P'
    hP'o, fun x hx ↦ mapOpenSub_conjD_of_mem H _ hkey (hmem x hx), ?_⟩
  rintro _ ⟨x', hx', rfl⟩ k
  have := hP' x' hx' k
  rw [eulerU_cover Ω C hc f η h C' hc' e he H hkey, cuspCount_cover Ω C hc f η h C' hc' e he H hkey,
    ← cyc3_coverIncl Ω C hc f η h C' hc' e he x' k,
    ← charDet_coverIncl Ω C hc f η h C' hc' e he H hkey (3 ^ k) x'
      (mapOpenSub_conjD_of_mem H _ hkey (hmem _ ⟨x', hx', rfl⟩))] at this
  exact this

end Cover

/-! ### The reduction -/

section Main

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The cusp weight identity of `U` from the case `H = Δ` for all curves**: if every affine
hyperbolic curve `U'` with a cusp over a number field `K' ⊆ Ω` admits an open `P ⊆ Π_{U'}` on
which `det(x | Hom(Δ_{U'}, ℤ/3^k))² = χ_k(x)^{χ₀(U') + r(U')}` (`hTop`), then `U` satisfies
the cusp weight identity at `l = 3` for every open `H ⊆ Δ_U` (realise `H` as `Δ_{U'}` of a
finite étale cover `U' → U`). -/
theorem cuspWeightIdentity_of_top
    (hTop : ∀ (K' : Type u) [Field K'] [NumberField K'] [Algebra K' Ω]
      [Algebra.IsAlgebraic K' Ω] (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty),
      ∃ P : Subgroup π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)),
        IsOpen (P : Set π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) ∧
        ∀ x ∈ P, ∀ k : ℕ,
          charDet (p := 3 ^ k) (conjD (deltaU Ω C' hc') x) ⊤ (mapOpenSub_top _) ^ 2 =
            cyc3 Ω C' hc' k x ^ (eulerU Ω C' + cuspCount (deltaCusps Ω C' hc') ⊤))
    (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) 3 (eulerU Ω C) (cyc3 Ω C hc) := by
  intro H
  obtain ⟨Q, hQ⟩ := exists_openSubgroup_inf_eq (deltaU Ω C hc) H
  haveI := isIntegral_specSections C hc
  obtain ⟨V, f, hf, η, hη, hconn, hrange⟩ := exists_isFiniteEtale_range_eq_of_open
    (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) Q
  have hcs : (coverSubgroup f η hη :
      Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) = Q :=
    (range_fundamentalGroupMap_eq_coverSubgroup f η hη).symm.trans hrange
  have hkey : ∀ z : deltaU Ω C hc,
      (z : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
        (coverSubgroup f η hη :
          Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ↔ z ∈ H := by
    intro z
    rw [hcs]
    exact hQ z
  letI := coverAlgebra Ω C hc f η
  haveI := isScalarTower_coverAlgebra Ω C hc f η hη
  haveI := isAlgebraic_coverAlgebra Ω C hc f η hη
  obtain ⟨P', hP'o, hP'⟩ := hTop (coverField C hc f) (coverCurve C hc f) (coverCurve_cusp C hc f)
  exact exists_weight_of_cover Ω C hc f η hη (coverCurve C hc f) (coverCurve_cusp C hc f)
    (coverIso C hc f) (coverIso_spec C hc f) H hkey P' hP'o hP'

end Main

end CurvesJacobian.CuspChar
