/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FixedPointConj
import CurvesJacobian.Cusp.InertiaComm
import CurvesJacobian.Cusp.LineAnalytic
import Oka.Analytification.Pi1.General
import Oka.Topology.VanKampen.ZeroOneBasis
import Belyi.Converse.Pi1Invariance
import Belyi.Converse.Points
import Pi1.FundamentalGroup.FiberFunctorIso

/-!
# `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}`, compatibly with the inertia groups at the cusps

Let `k` be a countable algebraically closed field of characteristic `0` (e.g. `ℚ̄`), `Ω` a
separably closed Galois extension of `k(t)` and `η` the geometric generic point of
`U = ℙ¹ ∖ {0, 1, ∞} = Spec k[t, 1/(t(t-1))]` (`CurvesJacobian.Cusp.lineGen`).

**Main theorem** (`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertia`): there is an
isomorphism of topological groups `Θ : π₁ᵉᵗ(U, η) ≃ₜ* Π̂_{0,3}` (the profinite completion of
`⟨c₀, c₁, c₂ | c₀ c₁ c₂ = 1⟩ ≅ F₂`) such that for every place `W ⊇ k` of `Ω` over the cusp
`j ∈ {0, 1, ∞}` (`v_W(t) < 1`, `v_W(t - 1) < 1`, resp. `v_W(2/(2t - 1)) < 1`), the inertia group
of `W` in `π₁ᵉᵗ(U, η)` (`CurvesJacobian.Cusp.lineInertia`) is mapped onto a conjugate of the
cuspidal inertia group `Iⱼ = ⟨cⱼ⟩‾` (`Pi1.SurfaceGroup.inertia j`).

Under `Θ`, `c₀, c₁` are (the images of) loops `g₀, g₁` around `0, 1` forming a free basis of
`π₁(ℂ ∖ {0, 1})` with `g₀ g₁` a big circle, i.e. `c₂ = (g₀ g₁)⁻¹` a loop around `∞`
(oka's `Complex.exists_mulEquiv_freeGroup_zero_one`), transported along the homeomorphism
`U_ℂ^an ≃ₜ ℂ ∖ {0, 1}` (`CurvesJacobian.Cusp.lineHomeo`), the comparison theorem
`π₁ᵉᵗ(U_ℂ) ≅ π₁(U_ℂ^an)^` (oka's `ComplexAnalytic.etaleFundamentalGroupEquivCompletion`), the
invariance `π₁ᵉᵗ(U_ℂ) ≅ π₁ᵉᵗ(U)` (belyi's `FiniteEtale.fundamentalGroupBaseChangeEquiv`) and an
isomorphism of fibre functors (pi1's `nonempty_iso_of_fiberFunctor`).

## Proof

Let `A` be the inertia group of `W` and `B = Θ⁻¹(Iⱼ)`. If `A` fixes a point of the fibre of a
finite étale `Y ⟶ U`, then `Y` has an unramified point over the cusp
(`CurvesJacobian.Cusp.nonempty_cuspBranch_of_fixed`), which survives base change to `ℂ`
(`CurvesJacobian.Cusp.CuspBranch.baseChange`) and lifts small loops around the cusp to closed
loops (`CurvesJacobian.Cusp.exists_monodromy_fixed_of_cuspBranch`), so `cⱼ`, hence `B`, fixes a
point of the fibre. By the fixed-point criterion in Galois categories
(`CurvesJacobian.Cusp.exists_conj_mem_of_fixedPoints`) a conjugate of `B` lies in `A`. Finally
`A` is abelian (`CurvesJacobian.Cusp.lineInertia_comm`, tame inertia is cyclic) and `Iⱼ` is
commensurably terminal in `Π̂_{0,3}` (pi1's `Pi1.SurfaceGroup.commensurator_inertia`), so the
conjugate of `A` containing `Iⱼ` is `Iⱼ` (`CurvesJacobian.Cusp.eq_inertia_of_inertia_le`).
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology PreGaloisCategory
open ProfiniteGrp.ProfiniteCompletion Complex.PuncturedPlane Complex.PuncturedPlane.ZeroOne
open scoped TensorProduct
open AffOrbicurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Fixed points under transport of automorphisms of fibre functors -/

section Transport

universe w₁ w₂ w₃ w₄ w₅

variable {C : Type w₁} [Category.{w₂} C] {F G : C ⥤ FintypeCat.{w₃}}

lemma conjAut_hom_app_hom_app (e : F ≅ G) (σ : Aut F) {A : C} (x : F.obj A) :
    (e.conjAut σ).hom.app A (e.hom.app A x) = e.hom.app A (σ.hom.app A x) := by
  rw [Iso.conjAut_hom, Iso.conj_apply]
  simp

/-- A point fixed by `σ` gives a point fixed by `e.conjAut.symm σ`. -/
lemma exists_fixed_conjAut_symm (e : F ≅ G) (τ : Aut G) {A : C} (y : G.obj A)
    (hy : τ.hom.app A y = y) :
    (e.conjAut.symm τ).hom.app A (e.inv.app A y) = e.inv.app A y := by
  have hinj : ∀ a b, e.hom.app A a = e.hom.app A b → a = b := fun a b h ↦ by
    rw [← FintypeCat.hom_inv_id_apply (e.app A) a, ← FintypeCat.hom_inv_id_apply (e.app A) b]
    exact congrArg (e.inv.app A) h
  apply hinj
  rw [← conjAut_hom_app_hom_app, MulEquiv.apply_symm_apply]
  change τ.hom.app A ((e.app A).hom ((e.app A).inv y)) = (e.app A).hom ((e.app A).inv y)
  rw [FintypeCat.inv_hom_id_apply (e.app A) y]
  exact hy

variable {D : Type w₄} [Category.{w₅} D] {H : D ⥤ C} {G' : D ⥤ FintypeCat.{w₃}}

/-- A point fixed by `σ` gives a point fixed by `fiberAutMap e σ`. -/
lemma fiberAutMap_fixed (e : H ⋙ F ≅ G') (σ : Aut F) {A : D} (x : F.obj (H.obj A))
    (hx : σ.hom.app (H.obj A) x = x) :
    (fiberAutMap e σ).hom.app A (e.hom.app A x) = e.hom.app A x := by
  rw [fiberAutMap_hom_app_apply]
  change (e.app A).hom (σ.hom.app (H.obj A) ((e.app A).inv ((e.app A).hom x))) = _
  rw [FintypeCat.hom_inv_id_apply (e.app A) x, hx]
  rfl

end Transport

/-! ### `π₁` of `(ℙ¹ ∖ {0, 1, ∞})_ℂ^an` -/

section Homeo

variable (k : Type) [Field k] [Algebra k (ULift.{0} ℂ)]

/-- `t : (ℙ¹ ∖ {0, 1, ∞})_ℂ^an → ℂ ∖ {0, 1}` as a continuous map. -/
abbrev lineFwd : C(analytification.obj (lineX k), X01) := ⟨lineHomeo k, (lineHomeo k).continuous⟩

lemma lineFwd_lineInv (x : X01) : lineFwd k (lineInv k x) = x := (lineHomeo k).apply_symm_apply x

lemma mapOfEq_lineFwd_map_lineInv (x : X01) (p : FundamentalGroup X01 x) :
    FundamentalGroup.mapOfEq (lineFwd k) (lineFwd_lineInv k x)
      (FundamentalGroup.map (lineInv k) x p) = p := by
  revert p
  refine Path.Homotopic.Quotient.ind (fun q ↦ ?_)
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.cast
    (((Path.Homotopic.Quotient.mk q).map (lineInv k)).map (lineFwd k)) _ _ = _
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  exact Path.ext (funext fun θ ↦ (lineHomeo k).apply_symm_apply (q θ))

lemma map_lineInv_mapOfEq_lineFwd (x : X01)
    (p : FundamentalGroup (analytification.obj (lineX k)) (lineInv k x)) :
    FundamentalGroup.map (lineInv k) x
      (FundamentalGroup.mapOfEq (lineFwd k) (lineFwd_lineInv k x) p) = p := by
  revert p
  refine Path.Homotopic.Quotient.ind (fun q ↦ ?_)
  rw [FundamentalGroup.mapOfEq_apply]
  change (((Path.Homotopic.Quotient.mk q).map (lineFwd k)).cast _ _).map (lineInv k) = _
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    ← Path.Homotopic.Quotient.mk_map]
  congr 1
  exact Path.ext (funext fun θ ↦ (lineHomeo k).symm_apply_apply (q θ))

/-- **`π₁(ℂ ∖ {0, 1}, x) ≅ π₁((ℙ¹ ∖ {0, 1, ∞})_ℂ^an, t⁻¹(x))`.** -/
def fundamentalGroupLineEquiv (x : X01) :
    FundamentalGroup X01 x ≃* FundamentalGroup (analytification.obj (lineX k)) (lineInv k x) where
  toFun := FundamentalGroup.map (lineInv k) x
  invFun := FundamentalGroup.mapOfEq (lineFwd k) (lineFwd_lineInv k x)
  left_inv := mapOfEq_lineFwd_map_lineInv k x
  right_inv := map_lineInv_mapOfEq_lineFwd k x
  map_mul' := map_mul _

lemma fundamentalGroupLineEquiv_apply (x : X01) (g : FundamentalGroup X01 x) :
    fundamentalGroupLineEquiv k x g = FundamentalGroup.map (lineInv k) x g := rfl

end Homeo

/-! ### The free basis and the surface group -/

section Basis

/-- `{c₀, c₁}` (the free generators of `Π_{0,3}`) as `{0, 1} ⊆ ℂ`. -/
def surfaceGenZeroOne : Pi1.SurfaceGen 0 2 ≃ ({0, 1} : Finset ℂ) where
  toFun
    | .c j => if j = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
    | .a i => i.elim0
    | .b i => i.elim0
  invFun s := if (s : ℂ) = 0 then .c 0 else .c 1
  left_inv := by
    rintro (i | i | j)
    · exact i.elim0
    · exact i.elim0
    · fin_cases j <;> simp
  right_inv := by
    rintro ⟨s, hs⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · simp
    · obtain rfl := Finset.mem_singleton.1 hs
      simp

/-- In `Π_{0,3}`, `c₂ = (c₀ c₁)⁻¹`. -/
lemma cusp_two_eq : Pi1.SurfaceGroup.cusp (g := 0) (r := 3) 2 =
    (Pi1.SurfaceGroup.cusp 0 * Pi1.SurfaceGroup.cusp 1)⁻¹ := by
  have h := Pi1.SurfaceGroup.relation (g := 0) (r := 3)
  simp only [Pi1.SurfaceGen.commProd, Pi1.SurfaceGen.ordProd, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, one_mul] at h
  have h' : Pi1.SurfaceGroup.cusp (g := 0) (r := 3) 0 * (Pi1.SurfaceGroup.cusp 1 *
      Pi1.SurfaceGroup.cusp 2) = 1 := h
  rw [← mul_assoc] at h'
  exact eq_inv_of_mul_eq_one_right h'

end Basis

/-! ### The main theorem -/

section Main

instance (k : Type*) [Field k] : IsDomain (lineRing k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)))

/-- **The comparison isomorphism on points**: the image of a loop `γ` in the étale fundamental
group acts on the fibre of `A` by the monodromy of `γ` on `A^an`. -/
lemma etaleFundamentalGroupEquivCompletion_symm_etaFn_hom_app {X : SchemeLFTℂ.{u}}
    [ConnectedSpace X.obj.left] (x : analytification.obj X)
    (γ : FundamentalGroup (analytification.obj X) x) (A : FiniteEtale X.obj.left)
    (y : (FiniteEtale.fiber (geometricPoint X x)).obj A) :
    ((etaleFundamentalGroupEquivCompletion x).symm (etaFn _ γ)).hom.app A y =
      (fiberEquivOfIso (analytificationFiniteEtale X) (fiberGeometricPointIso x) A).symm
        ((AnalyticSpace.SeparatedFiniteEtaleOver.isCoveringMap
          ((analytificationFiniteEtale X).obj A)).monodromy γ
          (fiberEquivOfIso (analytificationFiniteEtale X) (fiberGeometricPointIso x) A y)) :=
  rfl

/-- A loop whose monodromy on `A^an` has a fixed point acts on the étale fibre with a fixed
point. -/
lemma exists_fixed_etaleFundamentalGroupEquivCompletion {X : SchemeLFTℂ.{u}}
    [ConnectedSpace X.obj.left] (x : analytification.obj X)
    (γ : FundamentalGroup (analytification.obj X) x) (A : FiniteEtale X.obj.left)
    (e : ((analytificationFiniteEtale X).obj A).hom.toLRSHom.base ⁻¹' {x})
    (he : (AnalyticSpace.SeparatedFiniteEtaleOver.isCoveringMap
      ((analytificationFiniteEtale X).obj A)).monodromy γ e = e) :
    ∃ y, ((etaleFundamentalGroupEquivCompletion x).symm (etaFn _ γ)).hom.app A y = y := by
  refine ⟨(fiberEquivOfIso (analytificationFiniteEtale X) (fiberGeometricPointIso x) A).symm e,
    ?_⟩
  rw [etaleFundamentalGroupEquivCompletion_symm_etaFn_hom_app, Equiv.apply_symm_apply]
  exact congrArg _ he

variable {k Ω : Type} [Field k] [IsAlgClosed k] [CharZero k] [Countable k] [Field Ω]
  [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω]

/-- **`π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}` with the inertia groups at the cusps going to conjugates of
the cuspidal inertia groups.** For `k` countable algebraically closed of characteristic `0` and
`η` the geometric generic point of `U = ℙ¹ ∖ {0, 1, ∞}` (`CurvesJacobian.Cusp.lineGen`), there is
`Θ : π₁ᵉᵗ(U, η) ≃ₜ* Π̂_{0,3}` such that for every place `W ⊇ k` of `Ω` over the cusp `j`
(`0`, `1`, `∞` for `j = 0, 1, 2`; `cuspCoord j t` is the local coordinate `t`, `t - 1`,
`2 / (2t - 1)`), some conjugate of the inertia group of `W` is mapped by `Θ` onto
`Iⱼ = ⟨cⱼ⟩‾`. Here `c₀ c₁ c₂ = 1`, and `c₀, c₁` are loops around `0, 1` forming a free basis of
`π₁(ℂ ∖ {0, 1})` (oka's `Complex.exists_mulEquiv_freeGroup_zero_one`). -/
theorem exists_continuousMulEquiv_lineInertia (ht : Transcendental k t) :
    ∃ Θ : π₁ᵉᵗ(lineGen ht) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 3,
      ∀ (j : Fin 3) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
        W.valuation (cuspCoord j t) < 1 →
          ∃ σ : π₁ᵉᵗ(lineGen ht),
            (lineInertia ht W).map ((Θ : π₁ᵉᵗ(lineGen ht) →* Pi1.ProfiniteSurfaceGroup 0 3).comp
              (MulAut.conj σ).toMonoidHom) = Pi1.SurfaceGroup.inertia j := by
  classical
  obtain ⟨φ⟩ := Belyi.Converse.nonempty_ringHom_complex_of_countable k
  letI : Algebra k (ULift.{0} ℂ) := (ULift.ringEquiv.symm.toRingHom.comp φ).toAlgebra
  -- the geometric basis of `π₁(ℂ ∖ {0, 1})`
  let xb : X01 := ⟨2, trivial, by norm_num⟩
  obtain ⟨ψ, hψ, δ, hδ⟩ := Complex.exists_mulEquiv_freeGroup_zero_one (R := 1) (by norm_num) xb
  let x := lineInv k xb
  let ι : Pi1.SurfaceGroup 0 3 ≃* FundamentalGroup (analytification.obj (lineX k)) x :=
    (Pi1.SurfaceGroup.freeEquiv (g := 0) (r := 2)).trans
      ((FreeGroup.freeGroupCongr surfaceGenZeroOne).trans
        (ψ.symm.trans (fundamentalGroupLineEquiv k xb)))
  let g₀ : FundamentalGroup X01 xb := ψ.symm (FreeGroup.of ⟨0, by simp⟩)
  let g₁ : FundamentalGroup X01 xb := ψ.symm (FreeGroup.of ⟨1, by simp⟩)
  have hι₀ : ι (Pi1.SurfaceGroup.cusp 0) = FundamentalGroup.map (lineInv k) xb g₀ := by
    have : Pi1.SurfaceGroup.cusp (g := 0) (r := 3) 0 =
        Pi1.SurfaceGroup.cusp (g := 0) (r := 2 + 1) (0 : Fin 2).castSucc := rfl
    simp only [ι, MulEquiv.trans_apply, this, Pi1.SurfaceGroup.freeEquiv_cusp_castSucc,
      FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
    rfl
  have hι₁ : ι (Pi1.SurfaceGroup.cusp 1) = FundamentalGroup.map (lineInv k) xb g₁ := by
    have : Pi1.SurfaceGroup.cusp (g := 0) (r := 3) 1 =
        Pi1.SurfaceGroup.cusp (g := 0) (r := 2 + 1) (1 : Fin 2).castSucc := rfl
    simp only [ι, MulEquiv.trans_apply, this, Pi1.SurfaceGroup.freeEquiv_cusp_castSucc,
      FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
    rfl
  have hι₂ : ι (Pi1.SurfaceGroup.cusp 2) = (FundamentalGroup.map (lineInv k) xb (g₀ * g₁))⁻¹ := by
    rw [cusp_two_eq, map_inv, map_mul, hι₀, hι₁, map_mul]
  have hloop : ∀ j : Fin 3, ∃ g : FundamentalGroup X01 xb, IsCuspLoop j g ∧
      (ι (Pi1.SurfaceGroup.cusp j) = FundamentalGroup.map (lineInv k) xb g ∨
        ι (Pi1.SurfaceGroup.cusp j) = (FundamentalGroup.map (lineInv k) xb g)⁻¹) := by
    intro j
    fin_cases j
    · exact ⟨g₀, hψ ⟨0, by simp⟩, Or.inl hι₀⟩
    · exact ⟨g₁, hψ ⟨1, by simp⟩, Or.inl hι₁⟩
    · refine ⟨g₀ * g₁, ⟨1, by norm_num, δ, ?_⟩, Or.inr hι₂⟩
      rw [← hδ, ← map_mul]
  -- the chain of isomorphisms
  haveI : ConnectedSpace (lineX k).obj.left :=
    inferInstanceAs (ConnectedSpace (Spec (.of (ULift.{0} ℂ ⊗[k] lineRing k))))
  let ξ := geometricPoint (lineX k) x
  let bc := FiniteEtale.baseChangeSpec k (ULift.{0} ℂ) (lineRing k)
  let Cmp := etaleFundamentalGroupEquivCompletion x
  let Inv := FiniteEtale.fundamentalGroupBaseChangeEquiv (k := k) (Ω := ULift.{0} ℂ)
    (R := lineRing k) ξ
  obtain ⟨α⟩ := nonempty_iso_of_fiberFunctor (FiniteEtale.fiber (lineGen ht))
    (FiniteEtale.fiber (ξ ≫ bc))
  let Bp := autContinuousMulEquivOfIso α
  let Θ : π₁ᵉᵗ(lineGen ht) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 3 :=
    Bp.trans (Inv.symm.trans (Cmp.trans (Pi1.Profinite.completionCongr ι).symm))
  refine ⟨Θ, fun j W hWk hWj ↦ ?_⟩
  set A := lineInertia ht W with hA
  have hAcl : IsClosed (A : Set π₁ᵉᵗ(lineGen ht)) := Subgroup.isClosed_topologicalClosure _
  obtain ⟨g, hgloop, hgι⟩ := hloop j
  let Φ : FundamentalGroup (analytification.obj (lineX k)) x →* π₁ᵉᵗ(lineGen ht) :=
    (α.conjAut.symm.toMonoidHom.comp (Inv.symm.symm.toMulEquiv.toMonoidHom.comp
      (Cmp.symm.toMulEquiv.toMonoidHom.comp
        (eta (GrpCat.of (FundamentalGroup (analytification.obj (lineX k)) x))).hom)))
  have hΘ : ∀ z : Pi1.SurfaceGroup 0 3, Θ.symm (etaFn _ z) = Φ (ι z) := by
    intro z
    change Bp.symm (Inv (Cmp.symm (Pi1.Profinite.completionCongr ι (etaFn _ z)))) = _
    rw [Pi1.Profinite.completionCongr_apply, Pi1.Profinite.completionMap_eta]
    rfl
  -- a fixed point of `A` gives a fixed point of `Θ⁻¹(cⱼ)`
  have key : ∀ (Y : FiniteEtale (Spec (.of (lineRing k))))
      (y : (FiniteEtale.fiber (lineGen ht)).obj Y), (∀ σ ∈ A, σ • y = y) →
        ∃ y' : (FiniteEtale.fiber (lineGen ht)).obj Y,
          Θ.symm (etaFn _ (Pi1.SurfaceGroup.cusp j)) • y' = y' := by
    intro Y y hy
    have hx : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, (lineGalois ht σ).hom.app Y y = y :=
      fun σ hσ ↦ hy _ (Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨σ, hσ, rfl⟩))
    obtain ⟨b⟩ := nonempty_cuspBranch_of_fixed ht j hWk hWj Y y hx
    let Yc := (FiniteEtale.pullback bc).obj Y
    obtain ⟨e, he⟩ := exists_monodromy_fixed_of_cuspBranch (Y' := Yc)
      (b.baseChange (ULift.{0} ℂ)) hgloop
    obtain ⟨y₁, hy₁⟩ := exists_fixed_etaleFundamentalGroupEquivCompletion x _ Yc e he
    have hy₂ := fiberAutMap_fixed (FiniteEtale.pullbackFiberIso bc rfl)
      (Cmp.symm (etaFn _ (FundamentalGroup.map (lineInv k) xb g))) y₁ hy₁
    have hy₃ := exists_fixed_conjAut_symm α _ _ hy₂
    refine ⟨α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁), ?_⟩
    have hΦ : Φ (FundamentalGroup.map (lineInv k) xb g) •
        α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁) =
        α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁) := hy₃
    refine (congrArg (· • _) (hΘ _)).trans ?_
    rcases hgι with h | h
    · exact (congrArg (fun z ↦ Φ z • _) h).trans hΦ
    · exact (congrArg (fun z ↦ Φ z • _) h).trans
        ((congrArg (· • _) (map_inv Φ _)).trans (inv_smul_eq_iff.2 hΦ.symm))
  have hfix : ∀ (Y : FiniteEtale (Spec (.of (lineRing k))))
      (y : (FiniteEtale.fiber (lineGen ht)).obj Y), (∀ σ ∈ A, σ • y = y) →
        ∃ y' : (FiniteEtale.fiber (lineGen ht)).obj Y,
          ∀ τ ∈ (Pi1.SurfaceGroup.inertia (g := 0) j).map
          (Θ.symm : Pi1.ProfiniteSurfaceGroup 0 3 →* π₁ᵉᵗ(lineGen ht)),
          τ • y' = y' := by
    intro Y y hy
    obtain ⟨y', hy'⟩ := key Y y hy
    refine ⟨y', ?_⟩
    have hS : Pi1.SurfaceGroup.inertia (g := 0) j ≤
        (MulAction.stabilizer π₁ᵉᵗ(lineGen ht) y').comap
          (Θ.symm : Pi1.ProfiniteSurfaceGroup 0 3 →* π₁ᵉᵗ(lineGen ht)) := by
      refine Subgroup.topologicalClosure_minimal _ ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hy'
      · exact (Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ y')).preimage
          Θ.symm.continuous
    rintro _ ⟨z, hz, rfl⟩
    exact hS hz
  obtain ⟨g', hg'⟩ := exists_conj_mem_of_fixedPoints (FiniteEtale.fiber (lineGen ht)) hAcl hfix
  refine ⟨g'⁻¹, eq_inertia_of_inertia_le (g := 0) (r := 1) j ?_ ?_⟩
  · intro z hz
    refine ⟨g' * Θ.symm z * g'⁻¹, hg' _ ⟨z, hz, rfl⟩, ?_⟩
    simp [mul_assoc]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, lineInertia_comm ht j hWk hWj a ha b hb]

end Main

end CurvesJacobian.Cusp
