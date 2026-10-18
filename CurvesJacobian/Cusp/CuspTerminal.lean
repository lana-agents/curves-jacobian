/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverGaloisData
import CurvesJacobian.Cusp.CuspInertiaFacts
import CurvesJacobian.Cusp.CoverCuspDegree
import CurvesJacobian.Cusp.CoverOpen
import CurvesJacobian.Cusp.DecompositionInertia
import CurvesJacobian.Picard.CurveGenus
import Oka.Analytification.RET.ES.NormalHartogs
import Pi1.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Cuspidal inertia groups are commensurably terminal (MR8.3, [AbsTopI] Lemma 4.1 (i))

[AbsTopI] Lemma 4.1 (i) (`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745): the
decomposition group of a cusp "is a torsion-free, commensurably terminal infinite subgroup of
`Δ`". Setting of `CurvesJacobian.Cusp.Inertia` (`k` algebraically closed of characteristic `0`,
Galois data `D`, `X` a curve over `k`, `U ⊆ X` open with finite complement and at least three
cusps, `W ⊇ k` a place of `Ω` not centred on `U`, `I = cuspInertia D X eL hH U W`).

Main results:

* `CurvesJacobian.Cusp.commensurator_cuspInertia`: **the commensurator of `I` in `π₁ᵉᵗ(U)` is
  `I`** (`Subgroup.Commensurable.commensurator`, as in `Belyi.Anabelian.ChainObj.IsCuspidal`);
  `mem_cuspInertia_of_relIndex_ne_zero`: already `[γIγ⁻¹ : I ∩ γIγ⁻¹] < ∞` forces `γ ∈ I`;
* `isClosed_cuspInertia`, `topologicalClosure_cuspInertia`,
  `commensurator_topologicalClosure_cuspInertia`: `I` is closed, so the same holds for `Ī = I`;
* `cuspInertia_eq_map_decompH`: `I` is the image of the decomposition group `D_W ∩ H`.

Auxiliary results of independent interest:

* `exists_isFiniteEtale_range_eq`: **Galois correspondence** — every open normal subgroup of
  `π₁ᵉᵗ(U, η)` is the image of `π₁ᵉᵗ(Y, ζ)` for a connected finite étale cover `Y ⟶ U` and every
  point `ζ` over `η` (Mathlib's `exists_lift_of_quotient_openSubgroup`, after a universe switch
  of the fibre functor);
* `isIntegral_of_connectedSpace`: a connected finite étale cover of a nonempty open of a curve
  is integral;
* `relIndex_cuspInertia_eq_zero_of_comapK_ne`: inertia groups of places over distinct cusps are
  not commensurable;
* `inter_nonempty_of_forall_isOpen_normal`, `isClosed_setOf_comap_eq`: profinite compactness and
  closedness of transporters of places.

## Proof (algebraic route)

Let `γ = ρ_U(σ)`, `σ ∈ H`, commensurate `I_W`; then `I_{σW} = γ I_W γ⁻¹`. For every open normal
`O ⊇ ker ρ_U` of `H`, the cover `Y ⟶ U` with image `ρ_U(O)` has compactification `N` with Galois
data `H' ⊆ O` (`CoverGaloisData`). If no element of `H'` maps `W` to `σW`, these places lie over
distinct cusps of `N`, and the images in `π₁ᵉᵗ(U)` of their inertia groups (finite index
subgroups of `I_W`, `I_{σW}`) would be commensurable, contradicting
`relIndex_cuspInertia_eq_zero_of_comapK_ne` for `N`. By compactness some `n ∈ ker ρ_U` maps `W`
to `σW`; then `σ⁻¹n` fixes `W`, so lies in the inertia group (`D_W = I_W`,
`mem_inertia_of_comap_eq_of_not_isCentredOn`), and `γ⁻¹ = ρ_U(σ⁻¹n) ∈ I_W`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

open scoped Pointwise

namespace CurvesJacobian.Cusp

/-! ### Topology -/

/-- A connected space in which every point has a preirreducible open neighbourhood is
irreducible. -/
theorem irreducibleSpace_of_isPreirreducible_nhds {T : Type*} [TopologicalSpace T]
    [ConnectedSpace T]
    (h : ∀ x : T, ∃ s : Set T, IsOpen s ∧ x ∈ s ∧ IsPreirreducible s) : IrreducibleSpace T := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨s₀, hs₀, hx₀, hirr₀⟩ := h x₀
  have hsub : ∀ x ∈ closure s₀, ∃ s : Set T, IsOpen s ∧ x ∈ s ∧ s ⊆ closure s₀ := by
    intro x hx
    obtain ⟨s, hs, hxs, hirr⟩ := h x
    refine ⟨s, hs, hxs, fun w hw ↦ ?_⟩
    rw [mem_closure_iff] at hx ⊢
    intro o ho hwo
    obtain ⟨z, -, hzo, hz₀⟩ := hirr o s₀ ho hs₀ ⟨w, hw, hwo⟩ (hx s hs hxs)
    exact ⟨z, hzo, hz₀⟩
  have hopen : IsOpen (closure s₀) := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨s, hs, hxs, hsc⟩ := hsub x hx
    exact ⟨s, hsc, hs, hxs⟩
  have huniv : closure s₀ = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_closure, hopen⟩ ⟨x₀, subset_closure hx₀⟩
  have hpre : IsPreirreducible (Set.univ : Set T) := huniv ▸ hirr₀.closure
  exact { isPreirreducible_univ := hpre, toNonempty := ⟨x₀⟩ }

/-! ### Profinite groups -/

/-- In a profinite group, a closed set meeting every open normal subgroup containing the closed
normal subgroup `N` meets `N`. -/
theorem inter_nonempty_of_forall_isOpen_normal {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) {A : Set G} (hA : IsClosed A)
    (h : ∀ O : Subgroup G, O.Normal → IsOpen (O : Set G) → N ≤ O → (A ∩ O).Nonempty) :
    (A ∩ N).Nonempty := by
  by_contra hAN
  have hC : IsClosed (A * (N : Set G)) := (hA.isCompact.mul hN.isCompact).isClosed
  have h1 : (1 : G) ∈ (A * (N : Set G))ᶜ := by
    rintro ⟨a, ha, n, hn, han⟩
    refine hAN ⟨a, ha, ?_⟩
    rw [eq_inv_of_mul_eq_one_left han]
    exact N.inv_mem hn
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hC.isOpen_compl h1
  haveI : M.toSubgroup.Normal := M.isNormal'
  obtain ⟨a, ha, haO⟩ := h (M.toSubgroup ⊔ N) inferInstance
    (Subgroup.isOpen_mono le_sup_left M.toOpenSubgroup.isOpen) le_sup_right
  rw [SetLike.mem_coe, ← SetLike.mem_coe, Subgroup.mul_normal] at haO
  obtain ⟨m, hm, n, hn, rfl⟩ := haO
  exact hM hm ⟨m * n, ha, n⁻¹, N.inv_mem hn, mul_inv_cancel_right m n⟩

/-! ### Closedness of transporter sets in Galois groups -/

section Transporter

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]

/-- `{ρ ∈ H | ρ a ∈ S}` is open in the Krull topology. -/
lemma isOpen_setOf_apply_mem (H : Subgroup (Ω ≃ₐ[K] Ω)) (a : Ω) (S : Set Ω) :
    IsOpen {ρ : H | (ρ : Ω ≃ₐ[K] Ω) a ∈ S} := by
  rw [isOpen_iff_forall_mem_open]
  intro ρ hρ
  refine ⟨(fun s : H ↦ ρ⁻¹ * s) ⁻¹'
    (Subtype.val ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) a : Set (Ω ≃ₐ[K] Ω))), ?_, ?_, ?_⟩
  · intro s hs
    have hs' : ((ρ : Ω ≃ₐ[K] Ω)⁻¹ * (s : Ω ≃ₐ[K] Ω)) a = a := hs
    have h2 : (s : Ω ≃ₐ[K] Ω) a = (ρ : Ω ≃ₐ[K] Ω) a := by
      have := congrArg (ρ : Ω ≃ₐ[K] Ω) hs'
      rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this
    change (s : Ω ≃ₐ[K] Ω) a ∈ S
    rw [h2]
    exact hρ
  · exact ((stabilizer_isOpen_of_isIntegral a).preimage continuous_subtype_val).preimage
      (continuous_const.mul continuous_id)
  · change ((ρ⁻¹ * ρ : H) : Ω ≃ₐ[K] Ω) a = a
    rw [inv_mul_cancel]
    rfl

/-- **The transporter `{ρ ∈ H | ρ⁻¹(W') = W}` of two valuation subrings is closed.** -/
lemma isClosed_setOf_comap_eq (H : Subgroup (Ω ≃ₐ[K] Ω)) (W W' : ValuationSubring Ω) :
    IsClosed {ρ : H | W'.comap ((ρ : Ω ≃ₐ[K] Ω) : Ω →+* Ω) = W} := by
  have e : {ρ : H | W'.comap ((ρ : Ω ≃ₐ[K] Ω) : Ω →+* Ω) = W} =
      ⋂ a : Ω, {ρ : H | ((ρ : Ω ≃ₐ[K] Ω) a ∈ W' ↔ a ∈ W)} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro h a
      rw [← h]
      rfl
    · intro h
      ext a
      exact h a
  rw [e]
  refine isClosed_iInter fun a ↦ ?_
  by_cases ha : a ∈ W
  · simp only [ha, iff_true]
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_apply_mem H a (W' : Set Ω)ᶜ
  · simp only [ha, iff_false]
    exact (isOpen_setOf_apply_mem H a (W' : Set Ω)).isClosed_compl

end Transporter

/-! ### Inertia elements fix the place -/

/-- An inertia element of `W` maps `W` onto itself. -/
lemma comap_eq_of_mem_inertia {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω]
    {W : ValuationSubring Ω} {ρ : Ω ≃ₐ[P] Ω} (hρ : ρ ∈ GaloisPi1.inertia W) :
    W.comap (ρ : Ω →+* Ω) = W := by
  have hW : ∀ a ∈ W, ρ a ∈ W := fun a ha ↦ by
    have h1 : ρ a - a ∈ W := (W.valuation_le_one_iff _).1 (hρ a ha).le
    simpa using add_mem h1 ha
  ext a
  rw [ValuationSubring.mem_comap]
  refine ⟨fun h ↦ ?_, fun h ↦ hW a h⟩
  by_contra ha
  have ha0 : a ≠ 0 := fun h0 ↦ ha (h0 ▸ W.zero_mem)
  have hinv : a⁻¹ ∈ W := (W.mem_or_inv_mem a).resolve_left ha
  have hlt : W.valuation a⁻¹ < 1 := by
    rw [valuation_lt_one_iff_mem]
    exact ⟨hinv, Or.inr (by rwa [inv_inv])⟩
  have h2 : W.valuation (ρ a⁻¹ - a⁻¹ + a⁻¹) < 1 :=
    Valuation.map_add_lt _ (hρ _ hinv) hlt
  rw [sub_add_cancel, map_inv₀] at h2
  have h3 : W.valuation (ρ a) ≤ 1 := (W.valuation_le_one_iff _).2 h
  have h4 : W.valuation (ρ a)⁻¹ * W.valuation (ρ a) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (by simpa using ha0), map_one]
  have h5 : W.valuation (ρ a)⁻¹ * W.valuation (ρ a) ≤ W.valuation (ρ a)⁻¹ * 1 := by
    gcongr
  rw [h4, mul_one] at h5
  exact absurd (h5.trans_lt h2) (lt_irrefl 1)

/-! ### Finite index of images -/

/-- The image of a finite index subgroup `A ⊓ B` of `A` has finite index in the image of `A`. -/
lemma relIndex_map_inf_ne_zero {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {A B : Subgroup G} (h : B.relIndex A ≠ 0) :
    ((A ⊓ B).map f).relIndex (A.map f) ≠ 0 := by
  rw [← Subgroup.relIndex_comap]
  refine mt (Subgroup.relIndex_eq_zero_of_le_left (Subgroup.le_comap_map f (A ⊓ B))) ?_
  rwa [Subgroup.inf_relIndex_left]

end CurvesJacobian.Cusp

namespace CurvesJacobian.Cusp

/-! ### Open normal subgroups of `π₁ᵉᵗ` and connected covers -/

section GaloisCorrespondence

open PreGaloisCategory

variable {U : Scheme.{u}} [ConnectedSpace U] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η' : Spec (.of Ω) ⟶ U)

/-- **Connected covers with prescribed image** (Galois correspondence for `π₁ᵉᵗ`, Stacks 0BN4):
for an open normal subgroup `O` of `π₁ᵉᵗ(U, η')` there is a connected finite étale `p : Y ⟶ U`
such that for every geometric point `ζ` of `Y` over `η'` the image of
`π₁ᵉᵗ(Y, ζ) → π₁ᵉᵗ(U, η')` is `O`. -/
theorem exists_isFiniteEtale_range_eq (O : OpenSubgroup π₁ᵉᵗ(η'))
    [(O : Subgroup π₁ᵉᵗ(η')).Normal] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ U) (_ : IsFiniteEtale p), ConnectedSpace Y ∧
      ∀ (ζ : Spec (.of Ω) ⟶ Y) (h : ζ ≫ p = η'),
        (fundamentalGroupMap p h).toMonoidHom.range = (O : Subgroup π₁ᵉᵗ(η')) := by
  -- move the fibre functor to the universe of `FiniteEtale U`
  let F' : FiniteEtale U ⥤ FintypeCat.{u + 1} := fiber η' ⋙ FintypeCat.uSwitch.{u, u + 1}
  letI : FiberFunctor F' := FiberFunctor.comp_right _
  let f : π₁ᵉᵗ(η') ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight (fiber η') FintypeCat.uSwitchEquivalence.{u, u + 1}.fullyFaithfulFunctor
  let O₁ : Subgroup (Aut F') := (O : Subgroup π₁ᵉᵗ(η')).map f.toMulEquiv.toMonoidHom
  have hO₁ : IsOpen (O₁ : Set (Aut F')) := by
    rw [Subgroup.coe_map]
    exact f.toHomeomorph.isOpenMap _ O.isOpen
  haveI : O₁.Normal := Subgroup.Normal.map inferInstance _ f.surjective
  obtain ⟨A, ⟨e⟩⟩ := exists_lift_of_quotient_openSubgroup (F := F') ⟨O₁, hO₁⟩
  let x : (fiber η').obj A :=
    FintypeCat.uSwitchEquiv.{u, u + 1} _ (e.inv.hom (QuotientGroup.mk 1))
  obtain ⟨B, i, y, -, hB, hi⟩ := fiber_in_connected_component (fiber η') A x
  have hinj : Function.Injective ((fiber η').map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 inferInstance
  have hpB : IsFiniteEtale B.hom := B.2
  refine ⟨B.left, B.hom, hpB, (isConnected_iff_connectedSpace B).1 hB, fun ζ h ↦ ?_⟩
  rw [@range_fundamentalGroupMap_of_isFiniteEtale' U B.left B.hom hpB Ω _ _ ζ η' h]
  ext γ
  rw [MulAction.mem_stabilizer_iff]
  let z : (fiber η').obj B := coverPt B.hom ζ h
  change γ • z = z ↔ _
  rw [← hinj.eq_iff]
  have hnat : (fiber η').map i (γ • z) = γ • (fiber η').map i z :=
    (NatTrans.naturality_apply γ.hom i z).symm
  rw [hnat]
  let e' : (fiber η').obj A ≃ F'.obj A :=
    (FintypeCat.uSwitchEquiv.{u, u + 1} ((fiber η').obj A)).symm
  have key : ∀ w : (fiber η').obj A, γ • w = w ↔ f γ • e' w = e' w := by
    intro w
    rw [← e'.symm.injective.eq_iff, Equiv.symm_apply_apply]
    change _ ↔ FintypeCat.uSwitchEquiv.{u, u + 1} _
      (FintypeCat.uSwitch.map (γ.hom.app A) ((FintypeCat.uSwitchEquiv.{u, u + 1} _).symm w)) = _
    rw [← FintypeCat.uSwitchEquiv_naturality, Equiv.apply_symm_apply]
    rfl
  rw [key]
  -- stabilisers in `Aut F' ⧸ O₁` are `O₁`
  have hinjE : Function.Injective e.hom.hom := fun a b hab ↦ by
    have h1 := FintypeCat.hom_inv_id_apply ((Action.forget _ _).mapIso e) a
    have h2 := FintypeCat.hom_inv_id_apply ((Action.forget _ _).mapIso e) b
    rw [← h1, ← h2]
    exact congrArg _ hab
  let w : F'.obj A := e' ((fiber η').map i z)
  have hcomm : e.hom.hom (f γ • w) = f γ • e.hom.hom w :=
    ConcreteCategory.congr_hom (e.hom.comm (f γ)) w
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.hom.hom w)
  change f γ • w = w ↔ _
  refine (hinjE.eq_iff (a := f γ • w) (b := w)).symm.trans ?_
  rw [hcomm, ← hg]
  change (f γ • (g : Aut F' ⧸ O₁) = (g : Aut F' ⧸ O₁)) ↔ _
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq,
    ← Subgroup.mem_map_iff_mem (f := f.toMulEquiv.toMonoidHom) f.injective
      (K := (O : Subgroup π₁ᵉᵗ(η')))]
  change _ ↔ f γ ∈ O₁
  constructor
  · intro h
    have := (inferInstance : O₁.Normal).conj_mem _ h g
    simpa [mul_assoc] using inv_mem this
  · intro h
    have := (inferInstance : O₁.Normal).conj_mem _ (inv_mem h) g⁻¹
    simpa [mul_assoc] using this

end GaloisCorrespondence

end CurvesJacobian.Cusp

namespace CurvesJacobian.Cusp

/-! ### Connected finite étale covers of opens of curves are integral -/

section Integral

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] {U : X.Opens} [Nonempty U] {Y : Scheme.{u}} (p : Y ⟶ U) [IsFiniteEtale p]

include k p in
/-- Every point of a finite étale cover of a nonempty open of a curve has an irreducible open
neighbourhood (an integral basic open of the normalisation, `exists_basicOpen_isDomain`). -/
lemma exists_isOpen_isPreirreducible (y : Y) :
    ∃ s : Set Y, IsOpen s ∧ y ∈ s ∧ IsPreirreducible s := by
  haveI := IsCurveOver.isIntegral k X
  haveI := isLocallyNoetherian_of_isCurveOver k X
  have hU : (U : Set X).Nonempty := ⟨_, (Classical.arbitrary U).2⟩
  haveI := isFinite_fromNormalization_of_isCurveOver (k := k) hU p
  haveI := isOpenImmersion_toNormalization k p
  have hxU : (p y).1 ∈ (U : Set X) := (p y).2
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hprod := isFiniteProductOfNormalDomains_preimage
    (isIntegrallyClosed_of_isCurveOver (k := k)) hU p hW ⟨_, hxW⟩
  let V : (p ≫ U.ι).normalization.Opens := (p ≫ U.ι).fromNormalization ⁻¹ᵁ W
  have hV : IsAffineOpen V := hW.preimage _
  haveI : IsAffine V := hV
  have hprod' : IsFiniteProductOfNormalDomains Γ(V, ⊤) :=
    hprod.of_ringEquiv V.topIso.commRingCatIsoToRingEquiv
  have hzV : (p ≫ U.ι).toNormalization y ∈ V := by
    change (p ≫ U.ι).fromNormalization ((p ≫ U.ι).toNormalization y) ∈ W
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact hxW
  obtain ⟨g, hzg, hdom, -⟩ := ComplexAnalytic.exists_basicOpen_isDomain hprod' ⟨_, hzV⟩
  let B : (V : Scheme).Opens := (V : Scheme).basicOpen g
  haveI : IsAffine B := (isAffineOpen_top (V : Scheme)).basicOpen g
  haveI : Nonempty B := ⟨⟨_, hzg⟩⟩
  haveI := hdom
  haveI : IsIntegral B := isIntegral_of_isAffine_of_isDomain B
  have hBirr : IsIrreducible (B : Set (V : Scheme)) := by
    have := (IrreducibleSpace.isIrreducible_univ (B : Scheme)).image Subtype.val
      continuous_subtype_val.continuousOn
    rw [Set.image_univ] at this
    convert this using 1
    ext x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  have hS : IsIrreducible (V.ι '' (B : Set (V : Scheme))) :=
    hBirr.image _ V.ι.continuous.continuousOn
  refine ⟨(p ≫ U.ι).toNormalization ⁻¹' (V.ι '' (B : Set (V : Scheme))), ?_, ?_, ?_⟩
  · exact (V.ι.isOpenEmbedding.isOpenMap _ B.2).preimage
      (p ≫ U.ι).toNormalization.continuous
  · exact ⟨⟨_, hzV⟩, hzg, rfl⟩
  · exact hS.isPreirreducible.preimage (p ≫ U.ι).toNormalization.isOpenEmbedding

include k p in
/-- **A connected finite étale cover of a nonempty open of a curve is integral.** -/
theorem isIntegral_of_connectedSpace [ConnectedSpace Y] : IsIntegral Y := by
  haveI := IsCurveOver.isIntegral k X
  haveI := isLocallyNoetherian_of_isCurveOver k X
  haveI : IsReduced Y := isReduced_of_etale p
  haveI : IrreducibleSpace Y :=
    irreducibleSpace_of_isPreirreducible_nhds (exists_isOpen_isPreirreducible (k := k) p)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end Integral

/-! ### Distinct cusps are not commensurable -/

section Commensurable

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
/-- **Cuspidal inertia groups of places over distinct cusps are not commensurable** (for `U`
with at least three cusps): `I_W ∩ I_{W'}` has infinite index in `I_{W'}`. -/
theorem relIndex_cuspInertia_eq_zero_of_comapK_ne {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W W' : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hWU : ¬ IsCentredOn D X eL U W) (hW'U : ¬ IsCentredOn D X eL U W')
    (hne : comapK D X eL hk W' ≠ comapK D X eL hk W) :
    (cuspInertia D X eL hH U W).relIndex (cuspInertia D X eL hH U W') = 0 := by
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hWU
  obtain ⟨y', hy'U, hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW' hW'U
  have hyy : y' ≠ y := fun h ↦ hne (by rw [← hy, ← hy', h])
  obtain ⟨V, hVeq⟩ := exists_opens_coe_eq_insert k X U hU y
  have hyV : y ∈ V := by
    rw [← SetLike.mem_coe, hVeq]
    exact Set.mem_insert _ _
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  have h : U ≤ V := fun x hx ↦ by
    rw [← SetLike.mem_coe, hVeq]
    exact Set.mem_insert_of_mem _ hx
  have hV : (V : Set X)ᶜ.Finite := by
    rw [hVeq]
    exact hU.subset (Set.compl_subset_compl.2 (Set.subset_insert _ _))
  have hcard : Nat.card ((V : Set X)ᶜ : Set X) + 1 = Nat.card ((U : Set X)ᶜ : Set X) := by
    rw [hVeq]
    exact card_compl_insert_add_one hU hyU
  have hWV : IsCentredOn D X eL V W := isCentredOn_of_stalkVS_eq D X eL hk V hkW hyV hy
  have hW'V : ¬ IsCentredOn D X eL V W' := fun hW'V ↦ by
    have hy'V := mem_of_isCentredOn D X eL hk V hV hW'V hy'
    rw [← SetLike.mem_coe, hVeq] at hy'V
    rcases hy'V with h' | h'
    · exact hyy h'
    · exact hy'U h'
  have hVne : (V : Set X)ᶜ.Nonempty := ⟨y', fun h' ↦ hW'V
    (isCentredOn_of_stalkVS_eq D X eL hk V hkW' h' hy')⟩
  have hne := cuspInertia_ne_bot D X eL hH hk hτ hV (by omega) hkW' hW'V
  have htf := cuspInertia_torsionFree D X eL hH V hV hVne W'
  exact relIndex_cuspInertia_eq_zero D X eL hH hk hτ hU hV h hWV hWU hne htf

end Commensurable

end CurvesJacobian.Cusp
namespace CurvesJacobian.Cusp

/-! ### The decomposition group of a cusp place -/

section Decomposition

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)

/-- **The decomposition group** `{ρ ∈ H | ρ(W) = W}` of a place `W`. -/
def decompH (W : ValuationSubring Ω) : Subgroup D.H where
  carrier := {ρ | W.comap ((ρ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω) = W}
  mul_mem' {a b} ha hb := by
    have ha' := SetLike.ext_iff.1 ha
    have hb' := SetLike.ext_iff.1 hb
    ext x
    change ((a : Ω ≃ₐ[K₀ k t] Ω) ((b : Ω ≃ₐ[K₀ k t] Ω) x)) ∈ W ↔ x ∈ W
    exact (ha' _).trans (hb' x)
  one_mem' := by
    ext x
    rfl
  inv_mem' {a} ha := by
    have ha' := SetLike.ext_iff.1 ha
    ext x
    change ((a : Ω ≃ₐ[K₀ k t] Ω)⁻¹ x) ∈ W ↔ x ∈ W
    rw [← ha' ((a : Ω ≃ₐ[K₀ k t] Ω)⁻¹ x)]
    change (a : Ω ≃ₐ[K₀ k t] Ω) ((a : Ω ≃ₐ[K₀ k t] Ω).symm x) ∈ W ↔ x ∈ W
    rw [AlgEquiv.apply_symm_apply]

lemma mem_decompH_iff (W : ValuationSubring Ω) (ρ : D.H) :
    ρ ∈ decompH D W ↔ W.comap ((ρ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω) = W :=
  Iff.rfl

variable [IsGalois (K₀ k t) Ω]

/-- The decomposition group of a place is closed. -/
lemma isClosed_decompH (W : ValuationSubring Ω) : IsClosed (decompH D W : Set D.H) :=
  isClosed_setOf_comap_eq D.H W W

end Decomposition

section Main

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

omit [X.Over (Spec (CommRingCat.of k))] [IsSepClosed Ω] [CharZero k] [IsCurveOver k X] in
/-- For a cusp place, the inertia elements in `H` form the decomposition group (`D_W = I_W`). -/
lemma mem_decompH_iff_mem_inertia (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hWU : ¬ IsCentredOn D X eL U W) (ρ : D.H) :
    ρ ∈ decompH D W ↔ (ρ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W :=
  ⟨fun h ↦ mem_inertia_of_comap_eq_of_not_isCentredOn D X eL U hkW hWU h,
    fun h ↦ comap_eq_of_mem_inertia h⟩

omit [X.Over (Spec (CommRingCat.of k))] [CharZero k] [IsCurveOver k X] in
/-- **The cuspidal inertia group is the image of the decomposition group.** -/
theorem cuspInertia_eq_map_decompH (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hWU : ¬ IsCentredOn D X eL U W) :
    cuspInertia D X eL hH U W = (decompH D W).map (D.chartHom hH (genericL D X eL U)) := by
  have e : (Subtype.val ⁻¹' GaloisPi1.inertia W : Set D.H) = (decompH D W : Set D.H) := by
    ext ρ
    exact (mem_decompH_iff_mem_inertia D X eL U hkW hWU ρ).symm
  rw [cuspInertia, e, ← MonoidHom.map_closure, Subgroup.closure_eq]

omit [X.Over (Spec (CommRingCat.of k))] [CharZero k] [IsCurveOver k X] in
/-- **Cuspidal inertia groups are closed.** -/
theorem isClosed_cuspInertia (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hWU : ¬ IsCentredOn D X eL U W) :
    IsClosed (cuspInertia D X eL hH U W : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := by
  haveI := GaloisPi1.compactSpace_of_isClosed D.H D.isClosed_H
  rw [cuspInertia_eq_map_decompH D X eL hH U hkW hWU, Subgroup.coe_map]
  exact ((isClosed_decompH D W).isCompact.image (D.continuous_chartHom hH _)).isClosed

omit [X.Over (Spec (CommRingCat.of k))] [CharZero k] [IsCurveOver k X] in
/-- The cuspidal inertia group equals its topological closure. -/
theorem topologicalClosure_cuspInertia (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hWU : ¬ IsCentredOn D X eL U W) :
    (cuspInertia D X eL hH U W).topologicalClosure = cuspInertia D X eL hH U W :=
  SetLike.coe_injective (Subgroup.topologicalClosure_coe.trans
    (isClosed_cuspInertia D X eL hH U hkW hWU).closure_eq)

end Main

end CurvesJacobian.Cusp
namespace CurvesJacobian.Cusp

open scoped Pointwise

/-! ### Commensurable terminality -/

section Terminal

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

attribute [local instance] normOver normNonempty

omit [IsAlgClosed k] in
include hk hτ in
/-- The image in `π₁ᵉᵗ(U)` of an open subgroup `O ⊇ ker` of `H` is open. -/
lemma isOpen_map_chartHom (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Finite)
    (O : Subgroup D.H) (hO : IsOpen (O : Set D.H))
    (hNO : (D.chartHom hH (genericL D X eL U)).ker ≤ O) :
    IsOpen ((O.map (D.chartHom hH (genericL D X eL U)) : Set π₁ᵉᵗ(specPoint D.L Ω ≫
      genericL D X eL U))) := by
  haveI := GaloisPi1.compactSpace_of_isClosed D.H D.isClosed_H
  have hsurj := (genericL_spec D X eL hk hH hτ U hU).2
  have e : ((O.map (D.chartHom hH (genericL D X eL U)) : Set π₁ᵉᵗ(specPoint D.L Ω ≫
      genericL D X eL U)))ᶜ = D.chartHom hH (genericL D X eL U) '' (O : Set D.H)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨σ, rfl⟩ := hsurj x
      exact ⟨σ, fun hσ ↦ hx ⟨σ, hσ, rfl⟩, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩ ⟨o, ho, hfo⟩
      apply hσ
      have : o⁻¹ * σ ∈ (D.chartHom hH (genericL D X eL U)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfo, inv_mul_cancel]
      simpa using O.mul_mem ho (hNO this)
  rw [← isClosed_compl_iff, e]
  exact (hO.isClosed_compl.isCompact.image (D.continuous_chartHom hH _)).isClosed

include hk hτ in
/-- **Key step: transporting a cusp place inside an open normal subgroup.** Let `W, W'` be places
over cusps of `U` (at least three cusps) whose cuspidal inertia groups satisfy
`[I_{W'} : I_W ∩ I_{W'}] < ∞`. Then for every open normal subgroup `O` of `H` containing the
kernel of `H ↠ π₁ᵉᵗ(U)` there is `ρ ∈ O` with `ρ⁻¹(W') = W`.

Proof: `O` corresponds to a connected finite étale cover `Y ⟶ U` (`exists_isFiniteEtale_range_eq`)
whose compactification `N` has Galois data `H' ⊆ O`. If no element of `H'` maps `W` to `W'`, then
`W, W'` lie over distinct cusps of `N` (Galois transitivity over `L'`), whose cuspidal inertia
groups are not commensurable (`relIndex_cuspInertia_eq_zero_of_comapK_ne`); but they are the
images in `π₁ᵉᵗ(U)` of finite index subgroups of `I_W, I_{W'}` (`map_cuspInertia_cover`). -/
theorem inter_nonempty_of_isOpen_normal {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W W' : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hWU : ¬ IsCentredOn D X eL U W) (hW'U : ¬ IsCentredOn D X eL U W')
    (hcomm : (cuspInertia D X eL hH U W).relIndex (cuspInertia D X eL hH U W') ≠ 0)
    (O : Subgroup D.H) [O.Normal] (hO : IsOpen (O : Set D.H))
    (hNO : (D.chartHom hH (genericL D X eL U)).ker ≤ O) :
    ({ρ : D.H | W'.comap ((ρ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω) = W} ∩ (O : Set D.H)).Nonempty := by
  haveI := isLocallyNoetherian_of_isCurveOver k X
  haveI := GaloisPi1.compactSpace_of_isClosed D.H D.isClosed_H
  have htop : U ≠ ⊤ := by
    rintro rfl
    simp at hU3
  obtain ⟨τ', hτ', hUeq⟩ := exists_chartOne_eq k U hU htop
  have hUaff : IsAffineOpen U := hUeq ▸ isAffineOpen_chartOne hτ'
  have hUne : (U : Set X).Nonempty := ⟨_, (Classical.arbitrary U).2⟩
  have hsurj := (genericL_spec D X eL hk hH hτ U hU).2
  haveI hNormal : (O.map (D.chartHom hH (genericL D X eL U))).Normal :=
    Subgroup.Normal.map inferInstance _ hsurj
  let O' : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) :=
    ⟨O.map (D.chartHom hH (genericL D X eL U)), isOpen_map_chartHom D X eL hH hk hτ U hU O hO hNO⟩
  haveI : (O' : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)).Normal := hNormal
  obtain ⟨Y, p, hp, hY, hrange⟩ :=
    exists_isFiniteEtale_range_eq (specPoint D.L Ω ≫ genericL D X eL U) O'
  haveI := hp
  haveI := hY
  haveI : IsIntegral Y := isIntegral_of_connectedSpace (k := k) p
  haveI : IsCurveOver k (p ≫ U.ι).normalization := normCurve p
  haveI : IsIntegral (p ≫ U.ι).normalization := IsCurveOver.isIntegral k _
  have hle := coverData_H_le_H D eL hk hτ (p ≫ U.ι).fromNormalization rfl (normGeneric k p)
  -- `H' ⊆ O`
  have hD'O : ∀ ρ : (coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl (normGeneric k p)).H,
      Subgroup.inclusion hle ρ ∈ O := by
    intro ρ
    have h1 := fundamentalGroupMap_genericY p D eL hk hτ hH ρ
    have h2 : D.chartHom hH (genericL D X eL U) (Subgroup.inclusion hle ρ) ∈
        (O' : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := by
      rw [← hrange _ (specPoint_genericY p D eL hk hτ), ← h1]
      exact ⟨_, rfl⟩
    obtain ⟨o, ho, hfo⟩ := h2
    have : o⁻¹ * Subgroup.inclusion hle ρ ∈ (D.chartHom hH (genericL D X eL U)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfo, inv_mul_cancel]
    simpa using O.mul_mem ho (hNO this)
  by_contra hempty
  -- `W` and `W'` restrict to different places of `L'`
  have hres : W.comap (algebraMap (coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl
      (normGeneric k p)).L Ω) ≠ W'.comap (algebraMap (coverData D eL hk hτ
        (p ≫ U.ι).fromNormalization rfl (normGeneric k p)).L Ω) := by
    intro heq
    haveI : IsGalois (coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl
        (normGeneric k p)).L Ω := IsGalois.tower_top_of_isGalois (K₀ k t) _ Ω
    obtain ⟨ρ, hρ⟩ := exists_algEquiv_comap_eq W W' heq
    have hρL : ρ.restrictScalars (K₀ k t) ∈
        (coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl (normGeneric k p)).HL := by
      have hcl := (coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl
        (normGeneric k p)).isClosed_HL
      have h := InfiniteGalois.fixingSubgroup_fixedField (⟨_, hcl⟩ : ClosedSubgroup _)
      change ρ.restrictScalars (K₀ k t) ∈ (⟨_, hcl⟩ : ClosedSubgroup _).toSubgroup
      rw [← h, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact ρ.commutes ⟨x, hx⟩
    apply hempty
    refine ⟨Subgroup.inclusion hle ⟨_, hρL⟩, ?_, hD'O _⟩
    change W'.comap (ρ : Ω →+* Ω) = W
    rw [hρ]
    exact GaloisPi1.comap_symm_comap W ρ
  let D' := coverData D eL hk hτ (p ≫ U.ι).fromNormalization rfl (normGeneric k p)
  let eL' := coverEL D eL hk hτ (p ≫ U.ι).fromNormalization rfl (normGeneric k p)
  let q := (p ≫ U.ι).fromNormalization
  have hkN : ∀ c : k, ((eL' (algebraMap k (p ≫ U.ι).normalization.functionField c) : D'.L) :
      Ω) = algebraMap k Ω c :=
    coverEL_algebraMap D eL hk hτ q rfl (normGeneric k p)
  have hτN := coverEL_τ D eL hk hτ q rfl (normGeneric k p)
  have hneN : comapK D' _ eL' hkN W' ≠ comapK D' _ eL' hkN W := fun h ↦
    hres (comap_algebraMap_eq_of_comapK_eq D' _ eL' hkN h).symm
  have hWN : ¬ IsCentredOn D' _ eL' (q ⁻¹ᵁ U) W :=
    (isCentredOn_normalization_iff p D eL hk hτ hUaff).not.2 hWU
  have hW'N : ¬ IsCentredOn D' _ eL' (q ⁻¹ᵁ U) W' :=
    (isCentredOn_normalization_iff p D eL hk hτ hUaff).not.2 hW'U
  have hfin : ((q ⁻¹ᵁ U : (p ≫ U.ι).normalization.Opens) :
      Set (p ≫ U.ι).normalization)ᶜ.Finite :=
    CurvesJacobian.finite_compl_of_nonempty k _ (q ⁻¹ᵁ U)
  have hcard : 2 < Nat.card (((q ⁻¹ᵁ U : (p ≫ U.ι).normalization.Opens) :
      Set (p ≫ U.ι).normalization)ᶜ :
      Set (p ≫ U.ι).normalization) := by
    haveI := hfin.to_subtype
    have hqs := surjective_fromNormalization (k := k) hUne p
    refine hU3.trans_le (Nat.card_le_card_of_surjective
      (fun x ↦ (⟨q x.1, x.2⟩ : ((U : Set X)ᶜ : Set X))) ?_)
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hqs x
    exact ⟨⟨y, hx⟩, rfl⟩
  have hrel := relIndex_cuspInertia_eq_zero_of_comapK_ne D' _ eL'
    (coverData_H_le D eL hk hτ q rfl (normGeneric k p)) hkN hτN hfin hcard hkW hkW' hWN hW'N
    hneN
  -- transport to `π₁ᵉᵗ(U)`
  haveI : IsFiniteEtale (q ∣_ U) := by
    rw [← normIso_inv_comp p]
    haveI : IsFiniteEtale (normIso p).inv := MorphismProperty.of_isIso @IsFiniteEtale _
    infer_instance
  have hinj := fundamentalGroupMap_injective_of_isFiniteEtale' (q ∣_ U)
    (specPoint D'.L Ω ≫ genericL D' _ eL' (q ⁻¹ᵁ U))
    (specPoint_coverGenericL D eL hk hτ q rfl (normGeneric k p) U)
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj,
    map_cuspInertia_cover D eL hk hτ q rfl (normGeneric k p) U hH W,
    map_cuspInertia_cover D eL hk hτ q rfl (normGeneric k p) U hH W'] at hrel
  -- the images are images of finite index subgroups of the decomposition groups
  let D'' : Subgroup D.H := D'.H.subgroupOf D.H
  have himg : ∀ V : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ V) →
      ¬ IsCentredOn D X eL U V →
      Subgroup.closure (D.chartHom hH (genericL D X eL U) ''
        {σ : D.H | (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia V ∧
          (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D'.H}) =
        (decompH D V ⊓ D'').map (D.chartHom hH (genericL D X eL U)) := by
    intro V hkV hVU
    have e : {σ : D.H | (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia V ∧
        (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D'.H} = ((decompH D V ⊓ D'' : Subgroup D.H) : Set D.H) := by
      ext σ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf, D'',
        Subgroup.mem_subgroupOf, mem_decompH_iff_mem_inertia D X eL U hkV hVU]
    rw [e, ← MonoidHom.map_closure, Subgroup.closure_eq]
  rw [himg W hkW hWU, himg W' hkW' hW'U] at hrel
  have hD''open : IsOpen (D'' : Set D.H) :=
    D'.isOpen_HL.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen D'' hD''open
  have hfinW : D''.relIndex (decompH D W) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (K := ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      (by rw [Subgroup.relIndex_top_left]; exact one_ne_zero)
  refine Subgroup.relIndex_ne_zero_trans
    (K := (decompH D W).map (D.chartHom hH (genericL D X eL U)))
    (relIndex_map_inf_ne_zero _ hfinW) ?_ hrel
  rw [← cuspInertia_eq_map_decompH D X eL hH U hkW hWU]
  refine fun h0 ↦ hcomm (Subgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rw [cuspInertia_eq_map_decompH D X eL hH U hkW' hW'U]
  exact Subgroup.map_mono inf_le_left

include hk hτ in
/-- **The transporter meets the kernel**: under the hypotheses of `inter_nonempty_of_isOpen_normal`
there is `n ∈ H` acting trivially on `π₁ᵉᵗ(U)` with `n⁻¹(W') = W` (compactness of `H`). -/
theorem exists_mem_ker_comap_eq {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W W' : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hWU : ¬ IsCentredOn D X eL U W) (hW'U : ¬ IsCentredOn D X eL U W')
    (hcomm : (cuspInertia D X eL hH U W).relIndex (cuspInertia D X eL hH U W') ≠ 0) :
    ∃ n : D.H, n ∈ (D.chartHom hH (genericL D X eL U)).ker ∧
      W'.comap ((n : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω) = W := by
  haveI := GaloisPi1.compactSpace_of_isClosed D.H D.isClosed_H
  have hNcl : IsClosed ((D.chartHom hH (genericL D X eL U)).ker : Set D.H) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (D.continuous_chartHom hH _)
  obtain ⟨n, hnA, hnN⟩ := inter_nonempty_of_forall_isOpen_normal _ hNcl
    (isClosed_setOf_comap_eq D.H W W') fun O hO hOo hNO ↦ by
      haveI := hO
      exact inter_nonempty_of_isOpen_normal D X eL hH hk hτ hU hU3 hkW hkW' hWU hW'U hcomm O hOo
        hNO
  exact ⟨n, hnN, hnA⟩

include hk hτ in
/-- **Cuspidal inertia groups are commensurably terminal** ([AbsTopI] Lemma 4.1 (i)): if
`γ ∈ π₁ᵉᵗ(U)` satisfies `[γ I γ⁻¹ : I ∩ γ I γ⁻¹] < ∞` for `I = I_W` (`W` a place over a cusp of
`U`, `U` with at least three cusps), then `γ ∈ I`. -/
theorem mem_cuspInertia_of_relIndex_ne_zero {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) {γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)}
    (hcomm : (cuspInertia D X eL hH U W).relIndex
      ((cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom) ≠ 0) :
    γ ∈ cuspInertia D X eL hH U W := by
  obtain ⟨σ, rfl⟩ := (genericL_spec D X eL hk hH hτ U hU).2 γ
  rw [← cuspInertia_comap] at hcomm
  have hkW' : ∀ c : k, algebraMap k Ω c ∈ W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω) :=
    fun c ↦ by
      change (σ : Ω ≃ₐ[K₀ k t] Ω).symm (algebraMap k Ω c) ∈ W
      rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes]
      rw [← IsScalarTower.algebraMap_apply k (K₀ k t) Ω]
      exact hkW c
  have hW'U := (isCentredOn_comap_iff D X eL U (hH σ.2) W).not.2 hWU
  obtain ⟨n, hn, hnW⟩ :=
    exists_mem_ker_comap_eq D X eL hH hk hτ hU hU3 hkW hkW' hWU hW'U hcomm
  have hρ : σ⁻¹ * n ∈ decompH D W := by
    rw [mem_decompH_iff]
    ext x
    have := SetLike.ext_iff.1 hnW x
    rw [← this]
    change (σ : Ω ≃ₐ[K₀ k t] Ω)⁻¹ ((n : Ω ≃ₐ[K₀ k t] Ω) x) ∈ W ↔
      (σ : Ω ≃ₐ[K₀ k t] Ω).symm ((n : Ω ≃ₐ[K₀ k t] Ω) x) ∈ W
    rw [AlgEquiv.aut_inv]
  have hmem : D.chartHom hH (genericL D X eL U) (σ⁻¹ * n) ∈ cuspInertia D X eL hH U W := by
    rw [cuspInertia_eq_map_decompH D X eL hH U hkW hWU]
    exact ⟨_, hρ, rfl⟩
  rw [map_mul, map_inv, (MonoidHom.mem_ker).1 hn, mul_one] at hmem
  exact inv_mem_iff.1 hmem

omit [IsAlgClosed k] [CharZero k] [IsCurveOver k X] in
lemma conjAct_smul_eq_map {G : Type*} [Group G] (γ : G) (I : Subgroup G) :
    ConjAct.toConjAct γ • I = I.map (MulAut.conj γ).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

include hk hτ in
/-- **The commensurator of a cuspidal inertia group is itself** ([AbsTopI] Lemma 4.1 (i),
`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745: cuspidal decomposition groups are
commensurably terminal), for `U` with at least three cusps. -/
theorem commensurator_cuspInertia {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    Subgroup.Commensurable.commensurator (cuspInertia D X eL hH U W) =
      cuspInertia D X eL hH U W := by
  ext γ
  rw [Subgroup.Commensurable.commensurator_mem_iff, conjAct_smul_eq_map]
  constructor
  · intro h
    exact mem_cuspInertia_of_relIndex_ne_zero D X eL hH hk hτ hU hU3 hkW hWU h.2
  · intro hγ
    have e : (cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom =
        cuspInertia D X eL hH U W := by
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mul_mem (mul_mem hγ hy) (inv_mem hγ)
      · intro hx
        refine ⟨γ⁻¹ * x * γ, mul_mem (mul_mem (inv_mem hγ) hx) hγ, by group⟩
    rw [e]

include hk hτ in
/-- The commensurator of the (closed) cuspidal inertia group, in topological-closure form. -/
theorem commensurator_topologicalClosure_cuspInertia {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    Subgroup.Commensurable.commensurator (cuspInertia D X eL hH U W).topologicalClosure =
      (cuspInertia D X eL hH U W).topologicalClosure := by
  rw [topologicalClosure_cuspInertia D X eL hH U hkW hWU]
  exact commensurator_cuspInertia D X eL hH hk hτ hU hU3 hkW hWU

end Terminal

end CurvesJacobian.Cusp
