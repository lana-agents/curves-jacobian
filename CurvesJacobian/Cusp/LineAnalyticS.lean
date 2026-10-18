/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineS
import CurvesJacobian.Cusp.PBranchLift

/-!
# `(ℙ¹ ∖ (S ∪ {∞}))^an = ℂ ∖ S` and loops near the cusps

For a field `k` with `k → ℂ` and a finite `S ⊆ k`, let `X = Spec (ℂ ⊗[k] k[t, 1/P_S(t)])`
(`CurvesJacobian.Cusp.lineXS`) and `S' ⊆ ℂ` the image of `S` (`CurvesJacobian.Cusp.imageS`).
The coordinate `t` is a homeomorphism `X^an ≃ₜ ℂ ∖ S'` (`CurvesJacobian.Cusp.lineHomeoS`).

**Loops near a cusp fix points of covers with branches there**
(`CurvesJacobian.Cusp.exists_monodromy_fixed_of_pBranch`): if a finite étale `Y' ⟶ X` has a
branch at the cusp `c` (`c = a ∈ k` or `c = ∞`, a `CurvesJacobian.Cusp.PBranch` with the
relation `t = a + s` resp. `t s = 1`), then every loop `g` of `ℂ ∖ S'` which is *near `c`*
(`CurvesJacobian.Cusp.IsNearLoop`: for every `r > 0`, `g` is conjugate to a loop in the punctured
disc of radius `r` around `c`, resp. in `{|z| > 1/r}`) acts on the fibre of `Y'^an → X^an` with a
fixed point. Being near a cusp is a purely topological notion, so it is easily transported along
self-homeomorphisms of `ℂ`.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology Metric
open Complex.PuncturedPlane
open scoped TensorProduct
open Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The line `ℙ¹ ∖ (S ∪ {∞})` over `ℂ` -/

section Line

variable {k : Type u} [Field k] [Algebra k (ULift.{u} ℂ)] (S : Finset k)

/-- The image `S' ⊆ ℂ` of `S ⊆ k` under `k → ℂ`. -/
def imageS : Finset ℂ := S.image fun a ↦ (algebraMap k (ULift.{u} ℂ) a).down

/-- `ℂ ⊗[k] k[t, 1/P_S(t)]`, the coordinate ring of `(ℙ¹ ∖ (S ∪ {∞}))_ℂ`. -/
abbrev lineCS : Type u := ULift.{u} ℂ ⊗[k] lineRingS S

/-- The coordinate `t` of `(ℙ¹ ∖ (S ∪ {∞}))_ℂ`. -/
abbrev lineTCS : lineCS S := 1 ⊗ₜ lineTS S

/-- `(ℙ¹ ∖ (S ∪ {∞}))_ℂ`, as a scheme locally of finite type over `ℂ`. -/
abbrev lineXS : SchemeLFTℂ.{u} := specLFT (lineCS S)

/-- The coordinate `t` on `(ℙ¹ ∖ (S ∪ {∞}))_ℂ^an`. -/
abbrev lineCoordS : C(analytification.obj (lineXS S), ℂ) := sCoord (lineTCS S)

lemma etale_mvAeval_lineTCS :
    (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ lineTCS S).toRingHom.Etale :=
  etale_mvAeval_baseChange (etale_mvAeval_lineTS S)

lemma isLocalHomeomorph_lineCoordS : IsLocalHomeomorph (lineCoordS S) :=
  isLocalHomeomorph_sCoord (etale_mvAeval_lineTCS S)

lemma isUnit_lineTCS_sub {a : k} (ha : a ∈ S) :
    IsUnit (lineTCS S - algebraMap (ULift.{u} ℂ) (lineCS S) (algebraMap k (ULift.{u} ℂ) a)) := by
  have hu : IsUnit (aeval (lineTCS S) (polyS S)) := by
    have h := (isUnit_aeval_lineTS S).map
      (Algebra.TensorProduct.includeRight (R := k) (A := ULift.{u} ℂ) (B := lineRingS S))
    rwa [← aeval_algHom_apply] at h
  rw [aeval_polyS] at hu
  have e : algebraMap k (lineCS S) a =
      algebraMap (ULift.{u} ℂ) (lineCS S) (algebraMap k (ULift.{u} ℂ) a) :=
    IsScalarTower.algebraMap_apply k (ULift.{u} ℂ) (lineCS S) a
  rw [← e]
  exact IsUnit.prod_iff.1 hu a ha

lemma lineCoordS_mem (v : analytification.obj (lineXS S)) :
    lineCoordS S v ∈ (Set.univ : Set ℂ) ∧ lineCoordS S v ∉ imageS S := by
  refine ⟨trivial, fun hmem ↦ ?_⟩
  obtain ⟨a, ha, he⟩ := Finset.mem_image.1 hmem
  have hu := (isUnit_lineTCS_sub S ha).map (evalAlgHom v)
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hu
  apply hu.ne_zero
  rw [sub_eq_zero]
  refine ULift.ext _ _ ?_
  rw [← sCoord_eq_evalAlgHom]
  exact he.symm

lemma lineCoordS_injective : Function.Injective (lineCoordS S) := by
  intro v w h
  apply evalAlgHom_injective
  refine Algebra.TensorProduct.ext (AlgHom.ext fun c ↦ ?_) ?_
  · change evalAlgHom v (algebraMap _ (lineCS S) c) = evalAlgHom w (algebraMap _ (lineCS S) c)
    rw [AlgHom.commutes, AlgHom.commutes]
  · apply lineRingS_algHom_ext
    change evalAlgHom v (lineTCS S) = evalAlgHom w (lineTCS S)
    exact ULift.ext _ _ (by rw [← sCoord_eq_evalAlgHom, ← sCoord_eq_evalAlgHom]; exact h)

lemma exists_lineCoordS_eq {c : ℂ} (hc : c ∉ imageS S) : ∃ v, lineCoordS S v = c := by
  have hu : IsUnit (aeval (⟨c⟩ : ULift.{u} ℂ) (polyS S)) := by
    rw [aeval_polyS]
    refine IsUnit.prod_iff.2 fun a ha ↦ isUnit_iff_ne_zero.2 fun h ↦ hc ?_
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    have := congrArg ULift.down h
    simp only [ULift.sub_down, ULift.zero_down] at this
    exact (sub_eq_zero.1 this).symm
  let φ : lineCS S →ₐ[ULift.{u} ℂ] ULift.{u} ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (lineLiftS (⟨c⟩ : ULift.{u} ℂ) hu)
      (fun _ _ ↦ Commute.all _ _)
  obtain ⟨v, hv⟩ := exists_evalAlgHom_eq φ
  refine ⟨v, ?_⟩
  rw [sCoord_eq_evalAlgHom, hv]
  simp [φ, Algebra.TensorProduct.lift_tmul]

/-- **`(ℙ¹ ∖ (S ∪ {∞}))_ℂ^an ≃ₜ ℂ ∖ S'`** through the coordinate `t`. -/
def lineHomeoS : analytification.obj (lineXS S) ≃ₜ Region Set.univ (imageS S) :=
  let hemb : IsOpenEmbedding (lineCoordS S) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (lineCoordS S).continuous
      (lineCoordS_injective S) (isLocalHomeomorph_lineCoordS S).isOpenMap
  have hrange : Set.range (lineCoordS S) =
      {z : ℂ | z ∈ (Set.univ : Set ℂ) ∧ z ∉ imageS S} := by
    ext z
    exact ⟨fun ⟨v, hv⟩ ↦ hv ▸ lineCoordS_mem S v, fun ⟨_, hz⟩ ↦ exists_lineCoordS_eq S hz⟩
  hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)

@[simp]
lemma coe_lineHomeoS (v : analytification.obj (lineXS S)) :
    (lineHomeoS S v : ℂ) = lineCoordS S v := rfl

/-- `t⁻¹ : ℂ ∖ S' → (ℙ¹ ∖ (S ∪ {∞}))_ℂ^an` as a continuous map. -/
abbrev lineInvS : C(Region Set.univ (imageS S), analytification.obj (lineXS S)) :=
  ⟨(lineHomeoS S).symm, (lineHomeoS S).symm.continuous⟩

lemma lineCoordS_eq_evalPoint (v : analytification.obj (lineXS S)) :
    lineCoordS S v =
      evalPoint (lineXS S) v ((Scheme.ΓSpecIso (.of (lineCS S))).inv (lineTCS S)) :=
  (evalPoint_sCoord _ v).symm

end Line

/-! ### Loops near a cusp -/

section Near

/-- The punctured neighbourhood of radius `r` of the point `c ∈ ℙ¹(ℂ)`: the punctured disc
`B(a, r) ∖ {a}` for `c = a ∈ ℂ`, `{z | 1/r < |z|}` for `c = ∞` (`none`). -/
def nearSet : Option ℂ → ℝ → Set ℂ
  | some a, r => ball a r \ {a}
  | none, r => {z | r⁻¹ < ‖z‖}

@[simp] lemma nearSet_some (a : ℂ) (r : ℝ) : nearSet (some a) r = ball a r \ {a} := rfl

@[simp] lemma nearSet_none (r : ℝ) : nearSet none r = {z | r⁻¹ < ‖z‖} := rfl

/-- **A loop near the point `c ∈ ℙ¹(ℂ)`** of `ℂ ∖ S'`: for every `r > 0`, `g` is conjugate to a
loop in the punctured neighbourhood of radius `r` of `c` (`CurvesJacobian.Cusp.nearSet`). -/
def IsNearLoop {S' : Finset ℂ} (c : Option ℂ) {x : Region Set.univ S'}
    (g : FundamentalGroup (Region Set.univ S') x) : Prop :=
  ∀ r > (0 : ℝ), ∃ (y : Region Set.univ S') (γ : Path y y)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
    g = δ ≫ ⟦γ⟧ ≫ Groupoid.inv δ ∧ ∀ θ, (γ θ : ℂ) ∈ nearSet c r

end Near

/-! ### Monodromy of loops near the cusps -/

section Monodromy

variable {k : Type u} [Field k] [Algebra k (ULift.{u} ℂ)] {S : Finset k}

/-- The covering map `Y'^an → (ℙ¹ ∖ (S ∪ {∞}))_ℂ^an`. -/
lemma isCoveringMap_lineS (Y' : AlgebraicGeometry.FiniteEtale (lineXS S).obj.left) :
    IsCoveringMap ((analytificationFiniteEtale (lineXS S)).obj Y').hom.toLRSHom.base :=
  AnalyticSpace.SeparatedFiniteEtaleOver.isCoveringMap _

variable {Y' : AlgebraicGeometry.FiniteEtale (lineXS S).obj.left}

/-- Transport of a closed lift along `(ℙ¹ ∖ (S ∪ {∞}))_ℂ^an ≃ₜ ℂ ∖ S'`. -/
lemma exists_fixed_of_loop_liftS {x y : Region Set.univ (imageS S)}
    (g : FundamentalGroup (Region Set.univ (imageS S)) x)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) (c : Path y y)
    (hg : g = δ ≫ ⟦c⟧ ≫ Groupoid.inv δ)
    (Λ : C(unitInterval, ((analytificationFiniteEtale (lineXS S)).obj Y').left))
    (hΛ : ∀ θ, lineCoordS S (((analytificationFiniteEtale (lineXS S)).obj Y').hom.toLRSHom.base
      (Λ θ)) = (c θ : ℂ)) (h01 : Λ 0 = Λ 1) :
    ∃ e, (isCoveringMap_lineS Y').monodromy
      (FundamentalGroup.map (lineInvS S) x g) e = e := by
  let F := FundamentalGroupoid.map (lineInvS S)
  have hFg : FundamentalGroup.map (lineInvS S) x g =
      F.map δ ≫ ⟦c.map (lineHomeoS S).symm.continuous⟧ ≫ Groupoid.inv (F.map δ) := by
    change F.map g = _
    subst hg
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
      ← Groupoid.inv_eq_inv]
    rfl
  rw [hFg]
  refine exists_monodromy_conj_fixed (isCoveringMap_lineS Y') (F.map δ)
    (c.map (lineHomeoS S).symm.continuous) Λ (fun θ ↦ ?_) h01
  change _ = (lineHomeoS S).symm (c θ)
  apply (lineHomeoS S).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (hΛ θ)

/-- **Loops near a cusp fix a point of every cover with a branch there.** If a finite étale
`Y' ⟶ (ℙ¹ ∖ (S ∪ {∞}))_ℂ` has a branch at the cusp `c : Option k` (relation `t = a + s` for
`c = a`, `t s = 1` for `c = ∞`), every loop `g` of `ℂ ∖ S'` near the image of `c` in `ℙ¹(ℂ)`
acts on the fibre of `Y'^an` with a fixed point. -/
theorem exists_monodromy_fixed_of_pBranch (c : Option k)
    (b : PBranch (ULift.{u} ℂ) (lineTCS S) Y'.hom ((cuspP c).map (algebraMap k (ULift.{u} ℂ)))
      ((cuspQ c).map (algebraMap k (ULift.{u} ℂ))))
    {x : Region Set.univ (imageS S)} {g : FundamentalGroup (Region Set.univ (imageS S)) x}
    (hg : IsNearLoop (c.map fun a ↦ (algebraMap k (ULift.{u} ℂ) a).down) g) :
    ∃ e, (isCoveringMap_lineS Y').monodromy (FundamentalGroup.map (lineInvS S) x g) e = e := by
  obtain ⟨r, hr, hlift⟩ := b.exists_closed_lift
  rw [map_cuspP, map_cuspQ] at hlift
  obtain ⟨y, γ, δ, hgδ, hγ⟩ := hg r hr
  have h01 : ((γ 0 : Region Set.univ (imageS S)) : ℂ) = (γ 1 : ℂ) := by
    rw [γ.source, γ.target]
  cases c with
  | some a =>
    set a' : ℂ := (algebraMap k (ULift.{u} ℂ) a).down
    let w : C(unitInterval, ℂ) := ⟨fun θ ↦ (γ θ : ℂ) - a',
      (continuous_subtype_val.comp γ.continuous).sub continuous_const⟩
    have hw01 : w 0 = w 1 := by
      change (γ 0 : ℂ) - a' = (γ 1 : ℂ) - a'
      rw [h01]
    have hw : ∀ θ, w θ ∈ ball (0 : ℂ) r ∧ w θ ≠ 0 := by
      intro θ
      have h := hγ θ
      simp only [Option.map_some, nearSet_some, Set.mem_sdiff, mem_ball,
        Set.mem_singleton_iff] at h
      refine ⟨?_, sub_ne_zero.2 h.2⟩
      rw [mem_ball, dist_zero_right]
      rw [dist_eq_norm] at h
      exact h.1
    obtain ⟨Λ, hΛ01, hΛ⟩ := hlift w hw01 hw
    refine exists_fixed_of_loop_liftS g δ γ hgδ Λ (fun θ ↦ ?_) hΛ01
    have h := hΛ θ
    simp only [Option.map_some, cuspQ_some, cuspP_some, map_one, mul_one, map_add, aeval_C,
      aeval_X, Algebra.algebraMap_self, RingHom.id_apply] at h
    have h' := congrArg ULift.down h
    rw [ULift.add_down] at h'
    rw [lineCoordS_eq_evalPoint]
    refine h'.trans ?_
    change a' + ((γ θ : ℂ) - a') = _
    ring
  | none =>
    have hne : ∀ θ, (γ θ : ℂ) ≠ 0 := fun θ h0 ↦ by
      have h := hγ θ
      simp only [Option.map_none, nearSet_none, Set.mem_setOf_eq, h0, norm_zero] at h
      exact absurd h (not_lt.2 (inv_pos.2 hr).le)
    let w : C(unitInterval, ℂ) := ⟨fun θ ↦ (γ θ : ℂ)⁻¹,
      (continuous_subtype_val.comp γ.continuous).inv₀ hne⟩
    have hw01 : w 0 = w 1 := by
      change (γ 0 : ℂ)⁻¹ = (γ 1 : ℂ)⁻¹
      rw [h01]
    have hw : ∀ θ, w θ ∈ ball (0 : ℂ) r ∧ w θ ≠ 0 := by
      intro θ
      have h := hγ θ
      simp only [Option.map_none, nearSet_none, Set.mem_setOf_eq] at h
      refine ⟨?_, inv_ne_zero (hne θ)⟩
      rw [mem_ball, dist_zero_right]
      change ‖(γ θ : ℂ)⁻¹‖ < r
      rw [norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.2 (hne θ)) hr).2 h
    obtain ⟨Λ, hΛ01, hΛ⟩ := hlift w hw01 hw
    refine exists_fixed_of_loop_liftS g δ γ hgδ Λ (fun θ ↦ ?_) hΛ01
    have h := hΛ θ
    simp only [Option.map_none, cuspQ_none, cuspP_none, aeval_X, map_one] at h
    have h' := congrArg ULift.down h
    rw [ULift.mul_down, ULift.one_down] at h'
    rw [lineCoordS_eq_evalPoint]
    change _ * (γ θ : ℂ)⁻¹ = 1 at h'
    exact (mul_inv_eq_one₀ (hne θ)).1 h'

end Monodromy

end CurvesJacobian.Cusp
