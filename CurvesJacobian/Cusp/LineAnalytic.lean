/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LoopLift
import CurvesJacobian.Cusp.BigLoops

/-!
# `(ℙ¹ ∖ {0, 1, ∞})^an = ℂ ∖ {0, 1}` and loops around the cusps

For a field `k` with `k → ℂ`, let `X = Spec (ℂ ⊗[k] k[t, 1/(t(t-1))])`
(`CurvesJacobian.Cusp.lineX`). The coordinate `t` is a homeomorphism `X^an ≃ₜ ℂ ∖ {0, 1}`
(`CurvesJacobian.Cusp.lineHomeo`): points of `X^an` are the `ℂ`-points of `X`
(`CurvesJacobian.Cusp.evalAlgHom`), determined by the value of `t`, which can be any `c ≠ 0, 1`,
and `t` is étale, hence a local homeomorphism.

**Loops around the cusps fix points of covers with branches**
(`CurvesJacobian.Cusp.exists_monodromy_fixed_of_cuspBranch`): if a finite étale `Y' ⟶ X` has a
branch at the cusp `j` (an unramified point over `0`, `1` or `∞`,
`CurvesJacobian.Cusp.CuspBranch`), then every loop around that cusp (`IsLoopAround g 0`,
`IsLoopAround g 1`, resp. a conjugate of a big circle around `1/2`) acts on the fibre of
`Y'^an → X^an` with a fixed point. The loop can be moved into the punctured disc where the branch
lifts it (`Complex.PuncturedPlane.circleArrow_eq_conj`,
`Complex.PuncturedPlane.ZeroOne.bigArrow_eq_conj`), and a closed lift of a loop is a fixed point
of its monodromy (`CurvesJacobian.Cusp.exists_monodromy_conj_fixed`).
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology Metric
open Complex.PuncturedPlane Complex.PuncturedPlane.ZeroOne
open scoped TensorProduct
open Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Points of `(Spec A)^an` -/

section Points

variable {A : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]

omit [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A] in
lemma ΓSpecIso_hom_inv_apply (a : A) :
    (Scheme.ΓSpecIso (.of A)).hom.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) = a := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- **Evaluation at a point of `(Spec A)^an`** as a `ℂ`-algebra map `A → ℂ`. -/
def evalAlgHom (v : analytification.obj (specLFT A)) : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ where
  toRingHom := ULift.ringEquiv.symm.toRingHom.comp
    ((evalPoint (specLFT A) v).comp (Scheme.ΓSpecIso (.of A)).inv.hom)
  commutes' c := by
    have h := evalPoint_eq_eval_coordFun (specCoord (0 : A)) (specCoord_comp_C 0) v
      (MvPolynomial.C c)
    simp only [MvPolynomial.map_C, MvPolynomial.eval_C] at h
    change ULift.ringEquiv.symm (evalPoint (specLFT A) v
      ((Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap (ULift.{u} ℂ) A c))) = c
    have e : specCoord (0 : A) (MvPolynomial.C c) =
        (Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap (ULift.{u} ℂ) A c) := by
      change (Scheme.ΓSpecIso (.of A)).inv.hom (MvPolynomial.aeval _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.aeval_C]
    rw [← e, h]
    rfl

lemma evalAlgHom_apply (v : analytification.obj (specLFT A)) (a : A) :
    (evalAlgHom v a).down = evalPoint (specLFT A) v ((Scheme.ΓSpecIso (.of A)).inv a) := rfl

lemma sCoord_eq_evalAlgHom (s : A) (v : analytification.obj (specLFT A)) :
    sCoord s v = (evalAlgHom v s).down := by
  rw [evalAlgHom_apply, evalPoint_sCoord]

omit [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A] in
/-- Two `K`-points with comparable kernels are equal. -/
lemma algHom_eq_of_ker_le {K : Type*} [Field K] [Algebra K A] {f g : A →ₐ[K] K}
    (h : RingHom.ker f ≤ RingHom.ker g) : f = g := by
  ext a
  have hmem : a - algebraMap K A (f a) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have := h hmem
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at this
  exact this.symm

lemma ker_evalAlgHom (v : analytification.obj (specLFT A)) :
    RingHom.ker (evalAlgHom v) =
      (idealOfPoint (specLFT A) v).comap (Scheme.ΓSpecIso (.of A)).inv.hom := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_comap, ← ker_evalPoint, RingHom.mem_ker]
  change ULift.ringEquiv.symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ ULift.ringEquiv.symm.injective]
  exact Iff.rfl

/-- **Points of `(Spec A)^an` are determined by their `ℂ`-points.** -/
lemma evalAlgHom_injective : Function.Injective (evalAlgHom (A := A)) := by
  intro v w h
  apply idealOfPoint_injective (V := specLFT A)
  have h' := congrArg RingHom.ker (congrArg AlgHom.toRingHom h)
  change RingHom.ker (evalAlgHom v) = RingHom.ker (evalAlgHom w) at h'
  rw [ker_evalAlgHom, ker_evalAlgHom] at h'
  exact Ideal.comap_injective_of_surjective _
    (by exact (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective) h'

/-- **Every `ℂ`-point of `A` is a point of `(Spec A)^an`.** -/
lemma exists_evalAlgHom_eq (φ : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ) :
    ∃ v, evalAlgHom v = φ := by
  let M : Ideal Γ((specLFT A).obj.left, ⊤) :=
    (RingHom.ker φ).comap (Scheme.ΓSpecIso (.of A)).hom.hom
  haveI : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun c ↦ ⟨algebraMap _ A c, φ.commutes c⟩)
  haveI : M.IsMaximal :=
    Ideal.comap_isMaximal_of_equiv (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  obtain ⟨v, hv⟩ := exists_idealOfPoint_eq (specLFT A) M
  refine ⟨v, (algHom_eq_of_ker_le ?_).symm⟩
  intro a ha
  rw [ker_evalAlgHom, hv, Ideal.mem_comap, Ideal.mem_comap]
  exact (congrArg φ (ΓSpecIso_hom_inv_apply a)).trans ha

end Points

/-! ### The line `ℙ¹ ∖ {0, 1, ∞}` over `ℂ` -/

section Line

variable (k : Type u) [Field k]

instance : Algebra.FiniteType k (lineRing k) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (X * (X - 1) : k[X])) _)

/-- `k[X₀] → k[t, 1/(t(t-1))]`, `X₀ ↦ t`, is étale (a localization). -/
lemma etale_mvAeval_lineT :
    (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ lineT k).toRingHom.Etale := by
  refine etale_mvAeval_of_etale_aeval ?_
  have e : (Polynomial.aeval (R := k) (lineT k)).toRingHom = algebraMap k[X] (lineRing k) :=
    Polynomial.ringHom_ext (fun c ↦ by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [IsScalarTower.algebraMap_apply k k[X] (lineRing k)]
      rfl)
      (by simp [lineT])
  rw [e]
  exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway (X * (X - 1) : k[X]))

variable [Algebra k (ULift.{u} ℂ)]

/-- `ℂ ⊗[k] k[t, 1/(t(t-1))]`, the coordinate ring of `(ℙ¹ ∖ {0, 1, ∞})_ℂ`. -/
abbrev lineC : Type u := ULift.{u} ℂ ⊗[k] lineRing k

/-- The coordinate `t` of `(ℙ¹ ∖ {0, 1, ∞})_ℂ`. -/
abbrev lineTC : lineC k := 1 ⊗ₜ lineT k

/-- `(ℙ¹ ∖ {0, 1, ∞})_ℂ`, as a scheme locally of finite type over `ℂ`. -/
abbrev lineX : SchemeLFTℂ.{u} := specLFT (lineC k)

/-- The coordinate `t` on `(ℙ¹ ∖ {0, 1, ∞})_ℂ^an`. -/
abbrev lineCoord : C(analytification.obj (lineX k), ℂ) := sCoord (lineTC k)

lemma etale_mvAeval_lineTC :
    (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ lineTC k).toRingHom.Etale :=
  etale_mvAeval_baseChange (etale_mvAeval_lineT k)

lemma isLocalHomeomorph_lineCoord : IsLocalHomeomorph (lineCoord k) :=
  isLocalHomeomorph_sCoord (etale_mvAeval_lineTC k)

lemma isUnit_lineTC : IsUnit (lineTC k * (lineTC k - 1)) := by
  have h : lineTC k * (lineTC k - 1) =
      Algebra.TensorProduct.includeRight (lineT k * (lineT k - 1)) := by
    rw [map_mul, map_sub, map_one]
    rfl
  rw [h]
  refine IsUnit.map _ ?_
  have := IsLocalization.Away.algebraMap_isUnit (S := lineRing k) (X * (X - 1) : k[X])
  simpa [lineT] using this

lemma lineCoord_mem (v : analytification.obj (lineX k)) :
    lineCoord k v ∈ (Set.univ : Set ℂ) ∧ lineCoord k v ∉ ({0, 1} : Finset ℂ) := by
  refine ⟨trivial, ?_⟩
  have hu := (isUnit_lineTC k).map (evalAlgHom v)
  rw [map_mul, map_sub, map_one] at hu
  have hne := hu.ne_zero
  rw [sCoord_eq_evalAlgHom]
  intro hmem
  rcases Finset.mem_insert.1 hmem with h0 | h1
  · apply hne
    rw [show evalAlgHom v (lineTC k) = 0 from ULift.ext _ _ h0, zero_mul]
  · apply hne
    rw [show evalAlgHom v (lineTC k) = 1 from ULift.ext _ _ (Finset.mem_singleton.1 h1),
      sub_self, mul_zero]

lemma lineCoord_injective : Function.Injective (lineCoord k) := by
  intro v w h
  apply evalAlgHom_injective
  refine Algebra.TensorProduct.ext (AlgHom.ext fun c ↦ ?_) ?_
  · change evalAlgHom v (algebraMap _ (lineC k) c) = evalAlgHom w (algebraMap _ (lineC k) c)
    rw [AlgHom.commutes, AlgHom.commutes]
  · apply lineRing_algHom_ext
    change evalAlgHom v (lineTC k) = evalAlgHom w (lineTC k)
    exact ULift.ext _ _ (by rw [← sCoord_eq_evalAlgHom, ← sCoord_eq_evalAlgHom]; exact h)

lemma exists_lineCoord_eq {c : ℂ} (h0 : c ≠ 0) (h1 : c ≠ 1) :
    ∃ v, lineCoord k v = c := by
  have hu : IsUnit ((⟨c⟩ : ULift.{u} ℂ) * (⟨c⟩ - 1)) := by
    refine isUnit_iff_ne_zero.2 fun h ↦ ?_
    have := congrArg ULift.down h
    simp only [ULift.mul_down, ULift.sub_down, ULift.one_down, ULift.zero_down] at this
    exact (mul_ne_zero h0 (sub_ne_zero.2 h1)) this
  let φ : lineC k →ₐ[ULift.{u} ℂ] ULift.{u} ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (lineLift (⟨c⟩ : ULift.{u} ℂ) hu)
      (fun _ _ ↦ Commute.all _ _)
  obtain ⟨v, hv⟩ := exists_evalAlgHom_eq φ
  refine ⟨v, ?_⟩
  rw [sCoord_eq_evalAlgHom, hv]
  simp [φ, Algebra.TensorProduct.lift_tmul]

/-- **`(ℙ¹ ∖ {0, 1, ∞})_ℂ^an ≃ₜ ℂ ∖ {0, 1}`** through the coordinate `t`. -/
def lineHomeo : analytification.obj (lineX k) ≃ₜ X01 :=
  let hemb : IsOpenEmbedding (lineCoord k) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (lineCoord k).continuous
      (lineCoord_injective k) (isLocalHomeomorph_lineCoord k).isOpenMap
  have hrange : Set.range (lineCoord k) =
      {z : ℂ | z ∈ (Set.univ : Set ℂ) ∧ z ∉ ({0, 1} : Finset ℂ)} := by
    ext z
    refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ lineCoord_mem k v, fun ⟨_, hz⟩ ↦ ?_⟩
    exact exists_lineCoord_eq k (fun h ↦ hz (by simp [h])) (fun h ↦ hz (by simp [h]))
  hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)

@[simp]
lemma coe_lineHomeo (v : analytification.obj (lineX k)) :
    (lineHomeo k v : ℂ) = lineCoord k v := rfl

end Line

/-! ### Monodromy of loops around the cusps -/

section Monodromy

/-- **A closed lift of a loop is a fixed point of the monodromy of its conjugates.** -/
lemma exists_monodromy_conj_fixed {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {x y : X}
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) (c : Path y y)
    (Λ : C(unitInterval, E)) (hΛ : ∀ θ, p (Λ θ) = c θ) (h01 : Λ 0 = Λ 1) :
    ∃ e : p ⁻¹' {x}, hp.monodromy (δ ≫ ⟦c⟧ ≫ Groupoid.inv δ) e = e := by
  let e₀ : p ⁻¹' {y} := ⟨Λ 0, by simp [hΛ]⟩
  let Γ : Path (Λ 0) (Λ 0) := { toContinuousMap := Λ, source' := rfl, target' := h01.symm }
  have hc : hp.monodromy (Path.Homotopic.Quotient.mk c) e₀ = e₀ := by
    refine hp.monodromy_eq_of_map_eq (ex := e₀) (ey := e₀) (Path.Homotopic.Quotient.mk Γ) ?_
    rw [← Path.Homotopic.Quotient.mk_map]
    change _ = Path.Homotopic.Quotient.cast (Path.Homotopic.Quotient.mk c) _ _
    rw [← Path.Homotopic.Quotient.mk_cast]
    congr 1
    ext θ
    exact hΛ θ
  refine ⟨hp.monodromy (Groupoid.inv δ) e₀, ?_⟩
  have hinv : hp.monodromy δ (hp.monodromy (Groupoid.inv δ) e₀) = e₀ := by
    rw [← hp.monodromy_trans_apply]
    change hp.monodromy (Groupoid.inv δ ≫ δ) e₀ = e₀
    rw [Groupoid.inv_comp]
    exact congrFun hp.monodromy_refl e₀
  change hp.monodromy (Path.Homotopic.Quotient.trans δ (Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.mk c) (Groupoid.inv δ))) _ = _
  rw [hp.monodromy_trans_apply, hp.monodromy_trans_apply, hinv, hc]

variable (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)]

/-- **A loop around the cusp `j`** of `ℂ ∖ {0, 1}`: a loop around `0`, around `1`, resp. a
conjugate of a big circle around `1/2` (a loop around `∞`). -/
def IsCuspLoop (j : Fin 3) {x : X01} (g : FundamentalGroup X01 x) : Prop :=
  ![IsLoopAround g 0, IsLoopAround g 1, ∃ (R : ℝ) (hR : 1 / 2 < R)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR)),
      g = δ ≫ bigArrow hR ≫ Groupoid.inv δ] j

/-- `t⁻¹ : ℂ ∖ {0, 1} → (ℙ¹ ∖ {0, 1, ∞})_ℂ^an` as a continuous map. -/
abbrev lineInv : C(X01, analytification.obj (lineX k)) :=
  ⟨(lineHomeo k).symm, (lineHomeo k).symm.continuous⟩

variable {k} {Y' : AlgebraicGeometry.FiniteEtale (lineX k).obj.left}

/-- The covering map `Y'^an → (ℙ¹ ∖ {0, 1, ∞})_ℂ^an`. -/
lemma isCoveringMap_line (Y' : AlgebraicGeometry.FiniteEtale (lineX k).obj.left) :
    IsCoveringMap ((analytificationFiniteEtale (lineX k)).obj Y').hom.toLRSHom.base :=
  AnalyticSpace.SeparatedFiniteEtaleOver.isCoveringMap _

/-- Transport of a closed lift along `(ℙ¹ ∖ {0, 1, ∞})_ℂ^an ≃ₜ ℂ ∖ {0, 1}`. -/
lemma exists_fixed_of_loop_lift {x y : X01} (g : FundamentalGroup X01 x)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) (c : Path y y)
    (hg : g = δ ≫ ⟦c⟧ ≫ Groupoid.inv δ)
    (Λ : C(unitInterval, ((analytificationFiniteEtale (lineX k)).obj Y').left))
    (hΛ : ∀ θ, lineCoord k (((analytificationFiniteEtale (lineX k)).obj Y').hom.toLRSHom.base
      (Λ θ)) = (c θ : ℂ)) (h01 : Λ 0 = Λ 1) :
    ∃ e, (isCoveringMap_line Y').monodromy
      (FundamentalGroup.map (lineInv k) x g) e = e := by
  let F := FundamentalGroupoid.map (lineInv k)
  have hFg : FundamentalGroup.map (lineInv k) x g =
      F.map δ ≫ ⟦c.map (lineHomeo k).symm.continuous⟧ ≫ Groupoid.inv (F.map δ) := by
    change F.map g = _
    subst hg
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
      ← Groupoid.inv_eq_inv]
    rfl
  rw [hFg]
  refine exists_monodromy_conj_fixed (isCoveringMap_line Y') (F.map δ)
    (c.map (lineHomeo k).symm.continuous) Λ (fun θ ↦ ?_) h01
  change _ = (lineHomeo k).symm (c θ)
  apply (lineHomeo k).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (hΛ θ)

lemma lineCoord_eq_evalPoint (v : analytification.obj (lineX k)) :
    lineCoord k v = evalPoint (lineX k) v ((Scheme.ΓSpecIso (.of (lineC k))).inv (lineTC k)) :=
  (evalPoint_sCoord _ v).symm

/-- **Loops around a cusp fix a point of every cover with a branch there.** If a finite étale
`Y' ⟶ (ℙ¹ ∖ {0, 1, ∞})_ℂ` has a branch at the cusp `j`, every loop `g` around that cusp acts
on the fibre of `Y'^an` with a fixed point. -/
theorem exists_monodromy_fixed_of_cuspBranch {j : Fin 3}
    (b : CuspBranch (ULift.{u} ℂ) (lineTC k) Y'.hom j) {x : X01} {g : FundamentalGroup X01 x}
    (hg : IsCuspLoop j g) :
    ∃ e, (isCoveringMap_line Y').monodromy (FundamentalGroup.map (lineInv k) x g) e = e := by
  obtain ⟨r, hr, hlift⟩ := b.exists_closed_lift
  -- the small circle around `0` in the local coordinate
  set r' := min (r / 2) (1 / 2) with hr'
  have hr'0 : 0 < r' := lt_min (by linarith) (by norm_num)
  have hr'r : r' < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr'1 : r' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let w : C(unitInterval, ℂ) := ⟨fun θ ↦ circleFun 0 r' θ,
    (continuous_circleFun 0 r').comp continuous_subtype_val⟩
  have hw01 : w 0 = w 1 := by
    change circleFun 0 r' (0 : unitInterval) = circleFun 0 r' (1 : unitInterval)
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, circleFun_zero, circleFun_one]
  have hw : ∀ θ, w θ ∈ ball (0 : ℂ) r ∧ w θ ≠ 0 := by
    intro θ
    have hn : ‖circleFun 0 r' θ - 0‖ = r' := norm_circleFun_sub 0 hr'0.le θ
    rw [sub_zero] at hn
    refine ⟨?_, fun h ↦ ?_⟩
    · rw [mem_ball, dist_zero_right]
      change ‖circleFun 0 r' θ‖ < r
      rw [hn]
      exact hr'r
    change circleFun 0 r' θ = 0 at h
    rw [h, norm_zero] at hn
    exact hr'0.ne hn
  have hadm : ∀ c : ℂ, c ∈ ({0, 1} : Finset ℂ) →
      Admissible Set.univ ({0, 1} : Finset ℂ) c r' := by
    intro c hc
    refine ⟨hr'0, Set.subset_univ _, fun s' hs' hs'c ↦ ?_⟩
    rw [mem_closedBall] at hs'c
    by_contra hne
    have h1 : dist s' c = 1 := by
      rcases Finset.mem_insert.1 hc with rfl | hc1 <;>
        rcases Finset.mem_insert.1 hs' with rfl | hs'1
      · exact absurd rfl hne
      · rw [Finset.mem_singleton.1 hs'1]; simp
      · rw [Finset.mem_singleton.1 hc1]; simp
      · exact absurd ((Finset.mem_singleton.1 hs'1).trans (Finset.mem_singleton.1 hc1).symm) hne
    linarith
  fin_cases j
  · -- the cusp `0`
    obtain ⟨r₀, h₀, δ, hδ⟩ : IsLoopAround g 0 := hg
    have h' := hadm 0 (by simp)
    obtain ⟨β, hβ⟩ := circleArrow_eq_conj h₀ h'
    obtain ⟨Λ, h01, hΛ⟩ := hlift w hw01 hw
    refine exists_fixed_of_loop_lift g (δ ≫ β) (circlePath h') ?_ Λ (fun θ ↦ ?_) h01
    · rw [hδ, hβ]
      simp [Category.assoc]
      rfl
    · rw [lineCoord_eq_evalPoint, coe_circlePath]
      exact hΛ θ
  · -- the cusp `1`
    obtain ⟨r₀, h₀, δ, hδ⟩ : IsLoopAround g 1 := hg
    have h' := hadm 1 (by simp)
    obtain ⟨β, hβ⟩ := circleArrow_eq_conj h₀ h'
    obtain ⟨Λ, h01, hΛ⟩ := hlift w hw01 hw
    refine exists_fixed_of_loop_lift g (δ ≫ β) (circlePath h') ?_ Λ (fun θ ↦ ?_) h01
    · rw [hδ, hβ]
      simp [Category.assoc]
      rfl
    · rw [lineCoord_eq_evalPoint, coe_circlePath]
      have h := hΛ θ
      change _ = 1 + circleFun 0 r' θ at h
      rw [h]
      simp [circleFun]
  · -- the cusp `∞`
    obtain ⟨R, hR, δ, hδ⟩ := hg
    set R' := max R (2 / r) + 1 with hR'def
    have hR' : 1 / 2 < R' := by
      have := le_max_left R (2 / r); rw [hR'def]; linarith
    have hR'r : 1 / R' < r := by
      have h2 : 2 / r < R' := by have := le_max_right R (2 / r); rw [hR'def]; linarith
      rw [div_lt_iff₀ (by linarith)]
      rw [div_lt_iff₀ hr] at h2
      linarith
    obtain ⟨β, hβ⟩ := bigArrow_eq_conj hR hR'
    have hB : ∀ θ : unitInterval, (bigPath R' θ : ℂ) - 1 / 2 ≠ 0 := fun θ h ↦ by
      have := norm_bigPath_sub (pos_of_half_lt hR').le θ
      rw [h, norm_zero] at this
      exact (pos_of_half_lt hR').ne this
    let w₂ : C(unitInterval, ℂ) := ⟨fun θ ↦ ((bigPath R' θ : ℂ) - 1 / 2)⁻¹,
      ((bigPath R').continuous.sub continuous_const).inv₀ hB⟩
    have hw01₂ : w₂ 0 = w₂ 1 := by
      change ((bigPath R' 0 : ℂ) - 1 / 2)⁻¹ = ((bigPath R' 1 : ℂ) - 1 / 2)⁻¹
      rw [(bigPath R').source, (bigPath R').target]
    have hw₂ : ∀ θ, w₂ θ ∈ ball (0 : ℂ) r ∧ w₂ θ ≠ 0 := by
      intro θ
      have hn := norm_bigPath_sub (pos_of_half_lt hR').le θ
      refine ⟨?_, inv_ne_zero (hB θ)⟩
      rw [mem_ball, dist_zero_right]
      change ‖((bigPath R' θ : ℂ) - 1 / 2)⁻¹‖ < r
      rw [norm_inv, hn, ← one_div]
      exact hR'r
    obtain ⟨Λ, h01, hΛ⟩ := hlift w₂ hw01₂ hw₂
    refine exists_fixed_of_loop_lift g (δ ≫ β) (bigLoop hR') ?_ Λ (fun θ ↦ ?_) h01
    · rw [hδ, hβ]
      simp [Category.assoc]
      rfl
    · rw [lineCoord_eq_evalPoint]
      have h := hΛ θ
      change 2 * _ * ((bigPath R' θ : ℂ) - 1 / 2)⁻¹ = ((bigPath R' θ : ℂ) - 1 / 2)⁻¹ + 2 at h
      change _ = (bigPath R' θ : ℂ)
      have hBθ := hB θ
      have h2 := congrArg (fun z ↦ z * ((bigPath R' θ : ℂ) - 1 / 2)) h
      simp only [add_mul, mul_assoc, inv_mul_cancel₀ hBθ, mul_one] at h2
      linear_combination h2 / 2

end Monodromy

end CurvesJacobian.Cusp
