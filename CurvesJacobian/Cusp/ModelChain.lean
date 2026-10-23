/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelDecusp
import CurvesJacobian.Cusp.TorsionFree

/-!
# Geometric models of all objects of a Belyi-type chain (MR8, round 26, step (1))

For the arithmetic cuspidal extension `Π_X ↠ G_K` of an affine hyperbolic curve over a number
field and a `Π`-chain `c` ([AbsTopI] Definition 4.2 (iii), `Topics in Absolute Anabelian Geometry
I.txt` l.2949–3027), every object of `c` has a geometric model (`CurvesJacobian.Cusp.GeomModel`)
provided `c` has no operation of type `⊚` and every object has a cuspidal decomposition group of
`Π_X` with infinite image (`ChainObj.HasInfCusp`; the hypothesis `hB` of
`GeomModel.exists_decusp`): `PiChain.nonempty_geomModel`. The base model is `X` itself
(`GeomModel.base`, transported along the identification `Π₀ ≅ Π` of condition (0Π)), and the
steps are `GeomModel.ofCover` (`⋏`), `GeomModel.ofQuot` (`⋎`) and `GeomModel.exists_decusp`
(`•`). The rel-isom-DGC over number fields (`hDGC`) is the only DGC input.

**Infinite cusp images in Belyi chains.** The source of an operation of type `•` has an infinite
cusp image (`ChainObj.hasInfCusp_of_isCuspidal`: the image is a nontrivial subgroup of the
torsion-free `J`), and operations `⋏`, `⋎` (open embeddings compatible with the rigidifying
homomorphisms) preserve the property in both directions (`ChainObj.hasInfCusp_iff_of_compat`).
Hence in a chain of type `⋏, ⋎, •^l, ⋏, •^r, ⋎` **all** objects have an infinite cusp image as
soon as the second to last object `Π_V` has one (`PiChain.IsBelyiType.hasInfCusp`), and
`PiChain.IsBelyiType.nonempty_geomModel` gives models of all objects under that single hypothesis
`hV`. Whether `hV` holds for *every* group-theoretic Belyi-type chain (the general converse of
[AbsTopII] Cor 3.7 (a)) is open here: a run of `•`'s might a priori end in the fundamental group of
a proper curve (see the MR8 plan, round 26). For chains transported from a geometric chain it holds
(see the Cor 3.8 existence step).

**Torsion-freeness along the final run** (step (2)). With a terminal isomorphism `Πₙ ≅ Π_X` (over
`G` up to conjugation), `Δ_n ≅ Δ_X` is torsion-free (free profinite); `⋎ : Π_V ↪ Πₙ` and every
`•` (kernel inside a torsion-free `J`) reflect torsion-freeness of `Δ` backwards
(`ChainObj.isTorsionFree_Delta_of_quot`, `ChainObj.isTorsionFree_Delta_of_decusp`), so every
object `Π_j`, `l + 3 ≤ j ≤ l + r + 3`, of the final run has torsion-free `Δ_j`
(`PiChain.IsBelyiType.isTorsionFree_Delta_run`), and every model of such an object can be enlarged
to a **full** model, `ι : Π_Y ≅ Π_j` (`GeomModel.exists_full`, option (Q) with `P' = Π_j`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {G H : Type*} [Group G] [Group H]

/-- Under an injective homomorphism, a subgroup is finite iff its image is (as commensurability
with `⊥`). -/
theorem map_commensurable_bot_iff (f : G →* H) (hf : Function.Injective f) {X : Subgroup G} :
    (X.map f).Commensurable ⊥ ↔ X.Commensurable ⊥ := by
  constructor
  · intro h
    have h' := h.comap' f
    rwa [Subgroup.comap_map_eq_self_of_injective hf, MonoidHom.comap_bot,
      (MonoidHom.ker_eq_bot_iff f).2 hf] at h'
  · intro h
    have h' := h.map' f
    rwa [Subgroup.map_bot] at h'

end CurvesJacobian.Cusp

namespace Belyi.Anabelian.ChainObj

open CurvesJacobian.Cusp

variable {E : CuspidalExt.{u}}

/-- **Some cuspidal decomposition group of `Π` has an infinite image in `A`** (the hypothesis `hB`
of `GeomModel.exists_decusp`). -/
def HasInfCusp (A : ChainObj E) : Prop :=
  ∃ I ∈ E.cusps, ¬ (A.image I).Commensurable ⊥

/-- **Open embeddings compatible with the rigidifying homomorphisms preserve infinite cusp
images** (`ρ_B(I) ∼ φ(ρ_A(I))`, `ChainObj.Compat.image_commensurable`). -/
theorem hasInfCusp_iff_of_compat {A B : ChainObj E} {φ : A.grp →ₜ* B.grp} (hC : Compat A B φ)
    (hinj : Function.Injective φ) : A.HasInfCusp ↔ B.HasInfCusp := by
  have key : ∀ I, (B.image I).Commensurable ⊥ ↔ (A.image I).Commensurable ⊥ := fun I ↦
    ⟨fun h ↦ (map_commensurable_bot_iff _ hinj).1 ((hC.image_commensurable I).symm.trans h),
      fun h ↦ (hC.image_commensurable I).trans ((map_commensurable_bot_iff _ hinj).2 h)⟩
  exact ⟨fun ⟨I, hI, h⟩ ↦ ⟨I, hI, fun h' ↦ h ((key I).1 h')⟩,
    fun ⟨I, hI, h⟩ ↦ ⟨I, hI, fun h' ↦ h ((key I).2 h')⟩⟩

/-- **The source of an operation of type `•` has an infinite cusp image**: the image `ρ_A(I)` of
the cusp defining `C` is nontrivial and lies in the torsion-free `J ⊇ C`. -/
theorem hasInfCusp_of_isCuspidal {A : ChainObj E} {C : Subgroup A.grp} (hC : A.IsCuspidal C)
    (htf : A.InTorsionFreeNormalOpen C) : A.HasInfCusp := by
  obtain ⟨I, hI, hne, rfl⟩ := hC
  obtain ⟨N, -, hCN, -, -, hNtf⟩ := htf
  refine ⟨I, hI, fun hfin ↦ hne ?_⟩
  haveI : Finite (A.image I) := (Subgroup.finite_of_commensurable_bot hfin).to_subtype
  refine eq_bot_iff.2 fun x hx ↦ Subgroup.mem_bot.2 ?_
  have hxN : x ∈ N := hCN ⟨le_commensurator_self' _ hx, A.image_le_Delta (E.cusps_le I hI) hx⟩
  refine hNtf x hxN ?_
  exact ((Subgroup.subtype_injective _).isOfFinOrder_iff (f := (A.image I).subtype)).2
    (isOfFinOrder_of_finite (⟨x, hx⟩ : A.image I))

end Belyi.Anabelian.ChainObj

namespace Belyi.Anabelian.ElemOp

open CurvesJacobian.Cusp ChainObj

variable {E : CuspidalExt.{u}} {A B : ChainObj E}

/-- **Infinite cusp images propagate backwards along operations other than `⊚`.** -/
theorem hasInfCusp_source (o : ElemOp A B) (ho : o.kind ≠ .deorb) (hB : B.HasInfCusp) :
    A.HasInfCusp := by
  match o, ho with
  | .cover _ inj _ compat, _ => exact (hasInfCusp_iff_of_compat compat inj).1 hB
  | .quot _ inj _ compat, _ => exact (hasInfCusp_iff_of_compat compat inj).2 hB
  | .decusp _ _ _ cusp tf _ _, _ => exact hasInfCusp_of_isCuspidal cusp tf
  | .deorb .., h => exact absurd rfl h

/-- **Infinite cusp images propagate forwards along `⋏` and `⋎`.** -/
theorem hasInfCusp_target (o : ElemOp A B) (ho : o.kind = .cover ∨ o.kind = .quot)
    (hA : A.HasInfCusp) : B.HasInfCusp := by
  match o, ho with
  | .cover _ inj _ compat, _ => exact (hasInfCusp_iff_of_compat compat inj).2 hA
  | .quot _ inj _ compat, _ => exact (hasInfCusp_iff_of_compat compat inj).1 hA
  | .decusp .., h => exact absurd h (by simp [kind])
  | .deorb .., h => exact absurd h (by simp [kind])

end Belyi.Anabelian.ElemOp

namespace Belyi.Anabelian.PiChain

open CurvesJacobian.Cusp ChainObj

variable {E : CuspidalExt.{u}} {c : PiChain E} {l r : ℕ}

/-- Transport of a property of chain objects along an equality of indices. -/
theorem objN_congr_iff (c : PiChain E) (P : ChainObj E → Prop) {a b : ℕ} (hab : a = b)
    (ha : a ≤ c.len) (hb : b ≤ c.len) : P (c.objN a ha) ↔ P (c.objN b hb) := by
  subst hab
  rfl

/-- **A Belyi-type chain has no operation of type `⊚`.** -/
theorem IsBelyiType.kind_ne_deorb (hc : c.IsBelyiType l r) (j : ℕ) (hj : j < c.len) :
    (c.opN j hj).kind ≠ .deorb := by
  obtain ⟨hlen, h0, h1, h2, h3, h4, h5⟩ := hc
  have hd : (OpKind.decusp) ≠ .deorb := by decide
  have hcv : (OpKind.cover) ≠ .deorb := by decide
  have hq : (OpKind.quot) ≠ .deorb := by decide
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact h0 ▸ hcv
    · exact h1 ▸ hq
  rcases Nat.lt_or_ge j (l + 2) with hjl | hjl
  · rw [c.kind_opN_congr (b := 2 + (j - 2)) (by omega) hj (by omega), h2 (j - 2) (by omega)]
    exact hd
  rcases Nat.lt_or_ge j (l + 3) with hjl' | hjl'
  · rw [c.kind_opN_congr (b := l + 2) (by omega) hj (by omega), h3]
    exact hcv
  rcases Nat.lt_or_ge j (l + r + 3) with hjr | hjr
  · rw [c.kind_opN_congr (b := l + 3 + (j - (l + 3))) (by omega) hj (by omega),
      h4 (j - (l + 3)) (by omega)]
    exact hd
  · rw [c.kind_opN_congr (b := l + r + 3) (by omega) hj (by omega), h5]
    exact hq

/-- **In a Belyi-type chain every object has an infinite cusp image as soon as `Π_V` (the second to
last object) has one.** -/
theorem IsBelyiType.hasInfCusp (hc : c.IsBelyiType l r)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp)
    (j : Fin (c.len + 1)) : (c.obj j).HasInfCusp := by
  have hlen := hc.len_eq
  have down : ∀ n k (hk : k ≤ c.len), k + n = l + r + 3 → (c.objN k hk).HasInfCusp := by
    intro n
    induction n with
    | zero =>
      intro k hk hkn
      exact (c.objN_congr_iff HasInfCusp (by omega) _ _).2 hV
    | succ n ih =>
      intro k hk hkn
      exact (c.opN k (by omega)).hasInfCusp_source (hc.kind_ne_deorb k (by omega))
        (ih (k + 1) (by omega) (by omega))
  rcases Nat.lt_or_ge j.1 (l + r + 4) with hj | hj
  · exact down (l + r + 3 - j.1) j.1 (by omega) (by omega)
  · have e : j = ⟨l + r + 3 + 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]
    refine (c.opN (l + r + 3) (by omega)).hasInfCusp_target (Or.inr hc.2.2.2.2.2.2)
      (down 0 (l + r + 3) (by omega) (by omega))

/-! ### Torsion-freeness of `Δ` along the final run -/

/-- **`⋎` reflects torsion-freeness of `Δ`**: `φ : A ↪ B` maps `Δ_A` into `Δ_B`. -/
theorem _root_.Belyi.Anabelian.ChainObj.isTorsionFree_Delta_of_quot {A B : ChainObj E}
    {φ : A.grp →ₜ* B.grp} (hinj : Function.Injective φ) (hC : Compat A B φ)
    (hB : IsTorsionFreeSubgroup B.Delta) : IsTorsionFreeSubgroup A.Delta := by
  intro a ha hfin
  have hΔ : φ a ∈ B.Delta := by
    change B.toG (φ a) = 1
    rw [ChainObj.toG_apply_of_compat hC]
    exact ha
  exact hinj ((hB _ hΔ ((φ : A.grp →* B.grp).isOfFinOrder hfin)).trans (map_one φ).symm)

/-- **`•` reflects torsion-freeness of `Δ`**: an element of finite order of `Δ_A` maps to `1` in the
torsion-free `Δ_B`, hence lies in `ker φ ⊆ J`, which is torsion-free. -/
theorem _root_.Belyi.Anabelian.ChainObj.isTorsionFree_Delta_of_decusp {A B : ChainObj E}
    (o : ElemOp A B) (ho : o.kind = .decusp) (hB : IsTorsionFreeSubgroup B.Delta) :
    IsTorsionFreeSubgroup A.Delta := by
  match o, ho with
  | .decusp φ _ C _ tf ker compat, _ =>
    obtain ⟨J, hJΔ, hCJ, hJn, hJo, hJtf⟩ := tf
    intro a ha hfin
    have hΔ : φ a ∈ B.Delta := by
      change B.toG (φ a) = 1
      rw [ChainObj.toG_apply_of_compat compat]
      exact ha
    have h1 : φ a = 1 := hB _ hΔ ((φ : A.grp →* B.grp).isOfFinOrder hfin)
    have hker : a ∈ (φ : A.grp →* B.grp).ker := h1
    rw [ker] at hker
    exact hJtf a (A.deltaNormalClosure_le hJΔ hJn hJo hCJ hker) hfin
  | .cover .., h => exact absurd h (by simp [ElemOp.kind])
  | .quot .., h => exact absurd h (by simp [ElemOp.kind])
  | .deorb .., h => exact absurd h (by simp [ElemOp.kind])

/-- **`⋎` reflects torsion-freeness of `Δ`** (as an elementary operation). -/
theorem _root_.Belyi.Anabelian.ChainObj.isTorsionFree_Delta_of_elemOp_quot {A B : ChainObj E}
    (o : ElemOp A B) (ho : o.kind = .quot) (hB : IsTorsionFreeSubgroup B.Delta) :
    IsTorsionFreeSubgroup A.Delta := by
  match o, ho with
  | .quot _ inj _ compat, _ => exact ChainObj.isTorsionFree_Delta_of_quot inj compat hB
  | .cover .., h => exact absurd h (by simp [ElemOp.kind])
  | .decusp .., h => exact absurd h (by simp [ElemOp.kind])
  | .deorb .., h => exact absurd h (by simp [ElemOp.kind])

end Belyi.Anabelian.PiChain

namespace CurvesJacobian.Cusp

open Belyi.Anabelian.ChainObj

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`Δ` of the last object of a chain with a terminal isomorphism to the trivial chain is
torsion-free** (`Δ_n ≅ Δ_X`, free profinite). -/
theorem _root_.Belyi.Anabelian.PiChain.TerminalIso.isTorsionFree_Delta
    {c : PiChain (arithmeticExt Ω CX hcX)} (t : c.TerminalIso (PiChain.trivial _)) :
    IsTorsionFreeSubgroup c.last.Delta := by
  obtain ⟨g, hg⟩ := t.over
  intro x hx hfin
  have hΔ : (arithmeticExt Ω CX hcX).pr (t.iso x) = 1 := by
    have := hg x
    change (arithmeticExt Ω CX hcX).pr (t.iso x) = g * c.last.toG x * g⁻¹ at this
    rw [this]
    have hx' : c.last.toG x = 1 := hx
    rw [hx', mul_one, mul_inv_cancel]
  have h1 := Delta_eq_one_of_isOfFinOrder Ω CX hcX (δ := ⟨t.iso x, hΔ⟩)
    (((Subgroup.subtype_injective _).isOfFinOrder_iff
      (f := ((projGk Ω CX hcX).toMonoidHom.ker).subtype)).1
      ((t.iso : c.last.grp →* (PiChain.trivial (arithmeticExt Ω CX hcX)).last.grp).isOfFinOrder
        hfin))
  exact t.iso.injective ((congrArg Subtype.val h1).trans (map_one t.iso).symm)

variable {c : PiChain (arithmeticExt Ω CX hcX)} {l r : ℕ}

/-- **Every object of the final run `Π_{l+3} ⇝ … ⇝ Π_{l+r+3} = Π_V` of a Belyi-type chain with a
terminal isomorphism has torsion-free `Δ`.** -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.isTorsionFree_Delta_run (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _)) (k : ℕ) (hk1 : l + 3 ≤ k) (hk2 : k ≤ l + r + 3) :
    IsTorsionFreeSubgroup (c.objN k (by have := hc.len_eq; omega)).Delta := by
  have hlen := hc.len_eq
  have hlast : IsTorsionFreeSubgroup (c.objN (l + r + 3 + 1) (by omega)).Delta :=
    (c.objN_congr_iff (fun A ↦ IsTorsionFreeSubgroup A.Delta) (by omega : c.len = _) le_rfl
      (by omega)).1 t.isTorsionFree_Delta
  have hV : IsTorsionFreeSubgroup (c.objN (l + r + 3) (by omega)).Delta :=
    isTorsionFree_Delta_of_elemOp_quot (c.opN (l + r + 3) (by omega)) hc.2.2.2.2.2.2 hlast
  have down : ∀ n k (hk : k ≤ c.len), l + 3 ≤ k → k + n = l + r + 3 →
      IsTorsionFreeSubgroup (c.objN k hk).Delta := by
    intro n
    induction n with
    | zero =>
      intro k hk _ hkn
      exact (c.objN_congr_iff (fun A ↦ IsTorsionFreeSubgroup A.Delta) (by omega) _ _).2 hV
    | succ n ih =>
      intro k hk hk3 hkn
      have hrun := hc.isDecuspRun r le_rfl
      have hkind : (c.opN k (by omega)).kind = .decusp := by
        rw [c.kind_opN_congr (b := l + 3 + (r - r) + (k - (l + 3))) (by omega) _ (by omega)]
        exact hrun (k - (l + 3)) (by omega)
      exact isTorsionFree_Delta_of_decusp (c.opN k (by omega)) hkind
        (ih (k + 1) (by omega) (by omega) (by omega))
  exact down (l + r + 3 - k) k _ hk1 (by omega)

namespace GeomModel

/-- **Full models** (option (Q) with `P' = A`): if `Δ_A` is torsion-free, every model of `A` can be
enlarged to a model with `ι : Π_Y ≅ A`. -/
theorem exists_full {A : ChainObj (arithmeticExt Ω CX hcX)} (D : GeomModel Ω CX hcX A)
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (htf : IsTorsionFreeSubgroup A.Delta) :
    ∃ D' : GeomModel Ω CX hcX A, Function.Surjective D'.ι := by
  obtain ⟨D', hD'⟩ := D.exists_enlarge hDGC ⊤ isOpen_univ
    (fun _ _ ↦ Subgroup.mem_set_normalizer_iff.2 fun _ ↦ by simp) (by rwa [top_inf_eq])
  refine ⟨D', fun a ↦ ?_⟩
  have ha : a ∈ Set.range D'.ι := by
    rw [hD']
    exact Subgroup.mem_top a
  exact ha

end GeomModel

/-- **Geometric models across an elementary operation other than `⊚`**, given an infinite cusp
image in the target (needed only for `•`). -/
theorem nonempty_geomModel_of_elemOp {A B : ChainObj (arithmeticExt Ω CX hcX)} (o : ElemOp A B)
    (D : GeomModel Ω CX hcX A)
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (ho : o.kind ≠ .deorb) (hB : B.HasInfCusp) : Nonempty (GeomModel Ω CX hcX B) := by
  match o, ho with
  | .cover φ inj op compat, _ => exact ⟨D.ofCover φ inj op compat⟩
  | .quot φ inj op compat, _ => exact ⟨D.ofQuot φ inj op compat⟩
  | .decusp φ surj _ cusp tf ker compat, _ =>
    exact D.exists_decusp hDGC φ surj cusp tf ker compat hB
  | .deorb .., h => exact absurd rfl h

/-- **Geometric models of all objects of a chain** without operations of type `⊚` whose objects
all have an infinite cusp image (assuming the rel-isom-DGC over number fields). -/
theorem _root_.Belyi.Anabelian.PiChain.nonempty_geomModel (c : PiChain (arithmeticExt Ω CX hcX))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hk : ∀ j, (c.op j).kind ≠ .deorb) (hinf : ∀ j, (c.obj j).HasInfCusp) (j : Fin (c.len + 1)) :
    Nonempty (GeomModel Ω CX hcX (c.obj j)) := by
  induction j using Fin.induction with
  | zero =>
    obtain ⟨e, he⟩ := c.obj_zero
    exact ⟨(GeomModel.base Ω CX hcX).ofCover (ContinuousMonoidHom.toContinuousMonoidHom e)
      e.injective (by
        convert isOpen_univ
        exact Set.eq_univ_of_forall fun x ↦ ⟨e.symm x, e.apply_symm_apply x⟩) he⟩
  | succ i ih =>
    obtain ⟨D⟩ := ih
    exact nonempty_geomModel_of_elemOp (c.op i) D hDGC (hk i) (hinf i.succ)

/-- **Geometric models of all objects of a Belyi-type chain** (MR8 round 26, step (1)), given that
`Π_V` (the second to last object) has an infinite cusp image. -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.nonempty_geomModel (hc : c.IsBelyiType l r)
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (j : Fin (c.len + 1)) :
    Nonempty (GeomModel Ω CX hcX (c.obj j)) :=
  c.nonempty_geomModel hDGC (fun j ↦ hc.kind_ne_deorb j.1 j.2) (hc.hasInfCusp hV) j

/-- **Full models of the objects of the final run** `Π_{l+3} ⇝ … ⇝ Π_V` of a Belyi-type chain with
a terminal isomorphism (MR8 round 26, step (2)). -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.exists_full_geomModel (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (k : ℕ)
    (hk1 : l + 3 ≤ k) (hk2 : k ≤ l + r + 3) :
    ∃ D : GeomModel Ω CX hcX (c.objN k (by have := hc.len_eq; omega)),
      Function.Surjective D.ι := by
  obtain ⟨D⟩ := hc.nonempty_geomModel hDGC hV ⟨k, by have := hc.len_eq; omega⟩
  exact D.exists_full hDGC (hc.isTorsionFree_Delta_run t k hk1 hk2)

end CurvesJacobian.Cusp
