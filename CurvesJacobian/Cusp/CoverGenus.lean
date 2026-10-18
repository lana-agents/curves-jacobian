/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverConstantField
import CurvesJacobian.Cusp.GenusLocAn
import CurvesJacobian.Scheme.TensorDomainConstantField
import CurvesJacobian.Scheme.ConstantField
import Mathlib.FieldTheory.LinearDisjoint

/-!
# The genus does not drop in a finite étale cover

Let `k` be a field of characteristic zero, `X̄` a curve over `k`, `U ⊆ X̄` a nonempty open,
`p : Y ⟶ U` finite étale with `Y` integral, `N` the normalisation of `X̄` in `Y` and
`k' = constField k N` its constant field, over which `N` is a curve
(`CurvesJacobian.Cusp.isCurveOver_constField`). We prove
`CurvesJacobian.Cusp.curveGenus_le_curveGenus_normalization`:
`g(X̄ / k) ≤ g(N / k')` for the genera `Belyi.Anabelian.curveGenus` (dimensions of the spaces of
regular differentials).

More generally (`CurvesJacobian.Cusp.curveGenus_le_of_genericPoint`), if `q : Y ⟶ X` maps the
generic point of the curve `Y / k'` to that of the curve `X / k`, compatibly with an algebraic
extension `k'/k`, then `g(X / k) ≤ g(Y / k')`.

## Proof

* `q` induces `φ₀ : K(X) → K(Y)` (`CurvesJacobian.Cusp.functionFieldMap`), compatible with the
  stalk maps; the composite `Φ : Ω[K(X)⁄k] → Ω[K(Y)⁄k] → Ω[K(Y)⁄k']` maps the differentials
  regular at `q y` into those regular at `y` (`CurvesJacobian.Cusp.kaehlerMap_mem_range`), hence
  global differentials to global differentials.
* `Ω[K(X)⁄k] = K(X) dt` for a transcendental `t`, and `Φ(dt) = d(φ₀ t) ≠ 0`: a `k'`-derivation
  of `K(Y)` killing `φ₀ t` kills `K(Y)`, which is separable algebraic over `k'(φ₀ t)`
  (`CurvesJacobian.Cusp.kaehler_D_ne_zero`).
* `K(X)` and `k'` are linearly disjoint over `k` (`k' ⊗_k K(X)` is a domain since `k` is
  algebraically closed in `K(X)`, hence a field since `k'/k` is algebraic), so a `k`-basis
  `f_i dt` of the global differentials of `X` maps to the `k'`-linearly independent family
  `φ₀(f_i) Φ(dt)` (`CurvesJacobian.Cusp.finrank_le_finrank_of_kaehlerMap`).
* The global differentials of a curve are finite-dimensional
  (`CurvesJacobian.Cusp.finiteDimensional_globalDifferentials`): every finite-dimensional
  subspace has dimension at most the Riemann–Roch genus (as in
  `CurvesJacobian.Cusp.locAn_curveGenus_le`).
-/

open CategoryTheory AlgebraicGeometry KaehlerDifferential Module
open scoped Belyi IntermediateField TensorProduct

universe u

namespace CurvesJacobian.Cusp

/-! ### Derivations of a field vanishing on a separating element -/

section Derivation

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [CharZero k]

/-- A `k`-derivation of `L` vanishing at `u` vanishes on `L` if `L / k⟮u⟯` is algebraic
(characteristic zero). -/
lemma derivation_eq_zero_of_isAlgebraic (δ : Derivation k L L) {u : L} (hu : δ u = 0)
    [Algebra.IsAlgebraic k⟮u⟯ L] (x : L) : δ x = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let C : IntermediateField k L :=
    { carrier := {y | δ y = 0}
      mul_mem' := fun {a b} (ha : δ a = 0) (hb : δ b = 0) ↦ by
        change δ (a * b) = 0
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      add_mem' := fun {a b} (ha : δ a = 0) (hb : δ b = 0) ↦ by
        change δ (a + b) = 0
        rw [map_add, ha, hb, add_zero]
      algebraMap_mem' := fun c ↦ δ.map_algebraMap c
      inv_mem' := fun a (ha : δ a = 0) ↦ by
        change δ a⁻¹ = 0
        rw [Derivation.leibniz_inv, ha, smul_zero] }
  have hF : k⟮u⟯ ≤ C := IntermediateField.adjoin_simple_le_iff.2 hu
  haveI : CharZero k⟮u⟯ := charZero_of_injective_algebraMap (algebraMap k k⟮u⟯).injective
  let δF : Derivation k⟮u⟯ L L := Derivation.mk'
    { toFun := δ
      map_add' := δ.map_add
      map_smul' := fun c y ↦ by
        have hc : δ (c : L) = 0 := hF c.2
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz,
          show δ (algebraMap k⟮u⟯ L c) = 0 from hc, smul_zero, add_zero]
        rfl }
    (fun a b ↦ δ.leibniz a b)
  have hint : IsIntegral k⟮u⟯ x := Algebra.IsIntegral.isIntegral x
  have hsep : (minpoly k⟮u⟯ x).Separable := (minpoly.irreducible hint).separable
  have h0 : δF (Polynomial.aeval x (minpoly k⟮u⟯ x)) =
      Polynomial.aeval x (Polynomial.derivative (minpoly k⟮u⟯ x)) • δF x := δF.map_aeval _ x
  rw [minpoly.aeval, map_zero] at h0
  exact (smul_eq_zero.mp h0.symm).resolve_left
    (hsep.aeval_derivative_ne_zero (minpoly.aeval k⟮u⟯ x))

/-- **`du ≠ 0`** in `Ω[L⁄k]` if `L / k⟮u⟯` is algebraic and `Ω[L⁄k] ≠ 0` (characteristic
zero). -/
theorem kaehler_D_ne_zero {u : L} [Algebra.IsAlgebraic k⟮u⟯ L] [Nontrivial Ω[L⁄k]] :
    D k L u ≠ 0 := by
  intro hu
  obtain ⟨v, hv⟩ := exists_ne (0 : Ω[L⁄k])
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual L Ω[L⁄k], f v ≠ 0 := by
    by_contra! h
    exact hv ((Module.forall_dual_apply_eq_zero_iff L v).1 h)
  have hδ : ∀ x : L, f.compDer (D k L) x = 0 :=
    derivation_eq_zero_of_isAlgebraic (u := u) (f.compDer (D k L)) (by simp [hu])
  have hf0 : f = 0 := Derivation.liftKaehlerDifferential_unique f 0 (by
    ext x
    simpa using hδ x)
  exact hf (by rw [hf0, LinearMap.zero_apply])

end Derivation

/-! ### The map of Kähler differentials -/

section Map

variable {k k' K L : Type*} [Field k] [Field k'] [Field K] [Field L]
  [Algebra k k'] [Algebra k K] [Algebra k L] [Algebra k' L] [Algebra K L]
  [IsScalarTower k k' L] [IsScalarTower k K L]

variable (k k' K L) in
/-- The composite `Ω[K⁄k] → Ω[L⁄k] → Ω[L⁄k']`. -/
noncomputable def kaehlerMap (ω : Ω[K⁄k]) : Ω[L⁄k'] :=
  KaehlerDifferential.map k k' L L (KaehlerDifferential.map k k K L ω)

lemma kaehlerMap_smul (a : K) (ω : Ω[K⁄k]) :
    kaehlerMap k k' K L (a • ω) = algebraMap K L a • kaehlerMap k k' K L ω := by
  rw [kaehlerMap, LinearMap.map_smul, ← algebraMap_smul L a, LinearMap.map_smul]
  rfl

lemma kaehlerMap_D (b : K) :
    kaehlerMap k k' K L (D k K b) = D k' L (algebraMap K L b) := by
  rw [kaehlerMap, map_D, map_D, Algebra.algebraMap_self_apply]

lemma kaehlerMap_zero : kaehlerMap k k' K L 0 = 0 := by
  rw [kaehlerMap, map_zero, map_zero]

lemma kaehlerMap_add (ω ω' : Ω[K⁄k]) :
    kaehlerMap k k' K L (ω + ω') = kaehlerMap k k' K L ω + kaehlerMap k k' K L ω' := by
  rw [kaehlerMap, map_add, map_add]
  rfl

/-- **Regular differentials go to regular differentials**: if the image of `A` in `L` lies in
the image of `B`, then `Φ` maps the image of `Ω[A⁄k]` into the image of `Ω[B⁄k']`. -/
lemma kaehlerMap_mem_range {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] [Algebra k' B] [Algebra B L] [IsScalarTower k' B L]
    (h : ∀ a : A, ∃ b : B, algebraMap K L (algebraMap A K a) = algebraMap B L b)
    {ω : Ω[K⁄k]} (hω : ∃ y, KaehlerDifferential.map k k A K y = ω) :
    ∃ z, KaehlerDifferential.map k' k' B L z = kaehlerMap k k' K L ω := by
  obtain ⟨y, rfl⟩ := hω
  obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective k A y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero, kaehlerMap_zero]⟩
  | tmul a b =>
    obtain ⟨a', ha⟩ := h a
    obtain ⟨b', hb⟩ := h b
    refine ⟨a' • D k' B b', ?_⟩
    have e1 : KaehlerDifferential.map k' k' B L (a' • D k' B b') =
        algebraMap B L a' • D k' L (algebraMap B L b') := by
      rw [LinearMap.map_smul, map_D, algebraMap_smul]
    have e2 : KaehlerDifferential.map k k A K ((D k A).tensorProductTo (a ⊗ₜ b)) =
        algebraMap A K a • D k K (algebraMap A K b) := by
      rw [Derivation.tensorProductTo_tmul, LinearMap.map_smul, map_D, algebraMap_smul]
    rw [e1, e2, kaehlerMap_smul, kaehlerMap_D, ha, hb]
  | add x y hx hy =>
    obtain ⟨z₁, h₁⟩ := hx
    obtain ⟨z₂, h₂⟩ := hy
    exact ⟨z₁ + z₂, by rw [map_add, map_add, map_add, h₁, h₂, kaehlerMap_add]⟩

/-- **The dimension count.** Let `k` (characteristic zero) be algebraically closed in `K`, let
`k'/k` be algebraic, `Ω[K⁄k]` of rank one and `Φ(dt) ≠ 0`. If `Φ` maps `G` into the
finite-dimensional `G'`, then `dim_k G ≤ dim_{k'} G'`. -/
theorem finrank_le_finrank_of_kaehlerMap [CharZero k] [Algebra.IsAlgebraic k k']
    (hK : ∀ x : K, IsAlgebraic k x → x ∈ (algebraMap k K).range)
    (hrank : Module.rank K Ω[K⁄k] = 1) {t : K} (ht : D k' L (algebraMap K L t) ≠ 0)
    (G : Submodule k Ω[K⁄k]) (G' : Submodule k' Ω[L⁄k']) [FiniteDimensional k' G']
    (hG : ∀ ω ∈ G, kaehlerMap k k' K L ω ∈ G') :
    finrank k G ≤ finrank k' G' := by
  classical
  by_cases hfin : FiniteDimensional k G
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _
  let b := Module.finBasis k G
  have hdt : D k K t ≠ 0 := fun h ↦ ht (by
    rw [← kaehlerMap_D (k := k) (k' := k') (K := K) (L := L), h, kaehlerMap_zero])
  have h1 : finrank K Ω[K⁄k] = 1 := Module.finrank_eq_of_rank_eq (by rw [hrank]; rfl)
  choose f hf using (finrank_eq_one_iff_of_nonzero' _ hdt).1 h1
  have hb : LinearIndependent k (fun i ↦ ((b i : G) : Ω[K⁄k])) :=
    b.linearIndependent.map' G.subtype G.ker_subtype
  have hfb : LinearIndependent k (fun i ↦ f (b i)) := by
    have e : (fun i ↦ ((b i : G) : Ω[K⁄k])) =
        ((LinearMap.toSpanSingleton K Ω[K⁄k] (D k K t)).restrictScalars k) ∘
          (fun i ↦ f (b i)) := by
      funext i
      simp [hf]
    rw [e] at hb
    exact hb.of_comp _
  -- linear disjointness of `K` and `k'`
  let φ : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  let A : IntermediateField k L := φ.fieldRange
  have hA : ∀ x : A, IsAlgebraic k x → x ∈ (algebraMap k A).range := by
    intro x hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 x.2
    have hy' : IsAlgebraic k (algebraMap K L y) := by
      have := hx.algHom A.val
      rw [IntermediateField.coe_val] at this
      rw [← hy] at this
      exact this
    obtain ⟨c, hc⟩ := hK y ((isAlgebraic_algebraMap_iff (R := k) (algebraMap K L).injective).1 hy')
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hy, ← hc]
    exact (φ.commutes c).symm
  haveI : IsDomain (k' ⊗[k] A) := isDomain_tensorProduct_of_isAlgClosedIn hA k'
  haveI : IsDomain (A ⊗[k] k') := (Algebra.TensorProduct.comm k A k').toMulEquiv.isDomain
  have hld : A.LinearDisjoint k' := IntermediateField.LinearDisjoint.of_isField
    (Algebra.TensorProduct.isField_of_isAlgebraic k A k' (Or.inr inferInstance))
  let a : Fin (finrank k G) → A := fun i ↦ ⟨φ (f (b i)), f (b i), rfl⟩
  have ha : LinearIndependent k a := by
    apply LinearIndependent.of_comp A.val.toLinearMap
    exact hfb.map' φ.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  have hw := hld.linearIndependent_left ha
  -- the image family in `G'`
  let v : Fin (finrank k G) → G' := fun i ↦ ⟨kaehlerMap k k' K L (b i), hG _ (b i).2⟩
  have hv : LinearIndependent k' v := by
    apply LinearIndependent.of_comp G'.subtype
    rw [linearIndependent_iff'] at hw ⊢
    intro s g hg i hi
    refine hw s g ?_ i hi
    have key : ∀ j, (G'.subtype ∘ v) j = (A.val ∘ a) j • D k' L (algebraMap K L t) :=
      fun j ↦ by
        change kaehlerMap k k' K L (b j : Ω[K⁄k]) = algebraMap K L (f (b j)) • _
        conv_lhs => rw [← hf (b j)]
        rw [kaehlerMap_smul, kaehlerMap_D]
    simp_rw [key, ← smul_assoc, ← Finset.sum_smul] at hg
    exact (smul_eq_zero.1 hg).resolve_right ht
  simpa using hv.fintype_card_le_finrank

end Map

/-! ### Function fields and global differentials of curves -/

section Curve

open WeilCurves.FunctionField Belyi

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsCurveOver k X]
  [IsIntegral X]

/-- `Ω[K(X)⁄k]` has rank one for a curve `X / k`. -/
theorem rank_kaehler_functionField :
    Module.rank X.functionField Ω[X.functionField⁄k] = 1 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U₀, -, V₀, hV₀, hx, e₀, h₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1)
      (f := X ↘ Spec (.of k)) x
  obtain rfl : U₀ = ⊤ := opens_eq_top_of_mem (e₀ hx)
  haveI : Nonempty V₀ := ⟨⟨x, hx⟩⟩
  have := (isStandardSmoothOfRelativeDimension_appLE_iff (X ↘ Spec (.of k)) (fun _ ↦ rfl) 1
    hV₀ e₀ (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 _ h₀)).1 h₀
  exact_mod_cast this

/-- **Every subspace of the regular differentials has dimension `≤ g`** (the Riemann–Roch genus),
as in `CurvesJacobian.Cusp.locAn_curveGenus_le`. -/
theorem finrank_le_curveGenus_of_le [CharZero k] (H : Submodule k Ω[X.functionField⁄k])
    (hH : H ≤ Anabelian.globalDifferentials k X) :
    (finrank k H : ℤ) ≤ CurvesJacobian.curveGenus k X := by
  set F := X.functionField
  choose π hπ using fun Q : Place k F ↦ Q.exists_ord_eq_one
  have hπQ : ∀ Q : Place k F, π Q ∈ Q.1 := fun Q ↦ Q.mem_of_ord_nonneg (by rw [hπ Q]; omega)
  choose π' hπ' using fun Q : Place k F ↦ exists_stalk_eq k X Q (hπQ Q)
  have hmax : ∀ Q : Place k F, IsLocalRing.maximalIdeal
      (X.presheaf.stalk (pointOfPlace k X Q)) = Ideal.span {π' Q} := fun Q ↦
    maximalIdeal_stalk_eq_span k X Q (by rw [hπ' Q, hπ Q])
  have hfin : ∀ Q : Place k F,
      letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
      Module.Finite (X.presheaf.stalk (pointOfPlace k X Q))
        Ω[X.presheaf.stalk (pointOfPlace k X Q)⁄k] := fun Q ↦ by
    letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
    haveI := essFiniteType_stalk k X (pointOfPlace k X Q)
    infer_instance
  refine finrank_le_genus π hπ (fun Q u hu ↦ ?_) (ell_zero_eq_one k X) H (fun ω hω Q ↦ ?_)
  · letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
    haveI := Anabelian.stalkAlgebra_isScalarTower k X (pointOfPlace k X Q)
    haveI := hfin Q
    obtain ⟨a, rfl⟩ := exists_stalk_eq k X Q hu
    obtain ⟨g, hg⟩ := exists_D_eq_smul_D (exists_aeval_stalk k X Q) (hmax Q) (F := F) a
    refine ⟨algebraMap _ F g, (stalkPlaceEquiv k X Q g).2, ?_⟩
    rw [hg, hπ' Q]
  · letI := Anabelian.stalkAlgebra k X (pointOfPlace k X Q)
    haveI := Anabelian.stalkAlgebra_isScalarTower k X (pointOfPlace k X Q)
    haveI := hfin Q
    have hω' : ω ∈ Anabelian.regularDifferentialsAt k X (pointOfPlace k X Q) :=
      (Submodule.mem_iInf _).mp (hH hω) _
    obtain ⟨g, hg⟩ := exists_eq_smul_D_of_mem_range (exists_aeval_stalk k X Q) (hmax Q)
      (F := F) hω'
    refine ⟨algebraMap _ F g, (stalkPlaceEquiv k X Q g).2, ?_⟩
    rw [hg, hπ' Q]

/-- **The space of regular differentials of a curve is finite-dimensional.** -/
theorem finiteDimensional_globalDifferentials [CharZero k] :
    FiniteDimensional k (Anabelian.globalDifferentials k X) := by
  by_contra hfin
  let G := Anabelian.globalDifferentials k X
  let n : ℕ := (CurvesJacobian.curveGenus k X).toNat + 1
  have hlt : (n : Cardinal) < Module.rank k G :=
    lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := n))
      (not_lt.1 fun h ↦ hfin (rank_lt_aleph0_iff.1 h))
  obtain ⟨s, hs, hli⟩ := Module.exists_set_linearIndependent_of_lt_rank hlt
  have hrk : finrank k (Submodule.span k s) = n :=
    Module.finrank_eq_of_rank_eq ((rank_span_set hli).trans hs)
  have hle := finrank_le_curveGenus_of_le k X ((Submodule.span k s).map G.subtype)
    (Submodule.map_subtype_le _ _)
  rw [Submodule.finrank_map_subtype_eq, hrk] at hle
  have := Int.self_le_toNat (CurvesJacobian.curveGenus k X)
  omega

end Curve

/-! ### The map of function fields -/

section FunctionField

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (q : Y ⟶ X)
  (hq : q (genericPoint Y) = genericPoint X)

/-- The map of function fields `K(X) → K(Y)` induced by a morphism mapping the generic point
to the generic point. -/
noncomputable def functionFieldMap : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes (show q (genericPoint Y) ⤳ genericPoint X by rw [hq]) ≫
    q.stalkMap (genericPoint Y)

/-- `functionFieldMap` is compatible with the stalk maps. -/
lemma functionFieldMap_algebraMap (y : Y) (a : X.presheaf.stalk (q y)) :
    functionFieldMap q hq (algebraMap _ X.functionField a) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (q.stalkMap y a) := by
  change ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫
      X.presheaf.stalkSpecializes (show q (genericPoint Y) ⤳ genericPoint X by rw [hq])) ≫
        q.stalkMap (genericPoint Y)) a =
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) (q.stalkMap y a)
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_apply q _ y (genericPoint_specializes y) a

/-- `functionFieldMap` on germs of global sections. -/
lemma functionFieldMap_germ_top (a : Γ(X, ⊤)) :
    functionFieldMap q hq (X.presheaf.germ ⊤ (genericPoint X) trivial a) =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial (q.appTop a) := by
  change q.stalkMap (genericPoint Y) (X.presheaf.stalkSpecializes _
    (X.presheaf.germ ⊤ (genericPoint X) trivial a)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  rfl

end FunctionField

/-! ### The genus inequality -/

section Genus

open WeilCurves.FunctionField Belyi

/-- **The genus does not drop under a morphism of curves preserving the generic point.** Let
`X / k` and `Y / k'` be curves, `k'/k` algebraic (characteristic zero), and `q : Y ⟶ X` a
morphism over `Spec k` mapping the generic point to the generic point. Then
`g(X / k) ≤ g(Y / k')`. -/
theorem curveGenus_le_of_genericPoint {k k' : Type u} [Field k] [Field k'] [CharZero k]
    [Algebra k k'] [Algebra.IsAlgebraic k k'] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k'))] [IsCurveOver k X] [IsCurveOver k' Y] [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ X) (hs : q ≫ (X ↘ Spec (.of k)) =
      (Y ↘ Spec (.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (hq : q (genericPoint Y) = genericPoint X) :
    Anabelian.curveGenus k X ≤ Anabelian.curveGenus k' Y := by
  haveI : CharZero k' := charZero_of_injective_algebraMap (algebraMap k k').injective
  letI : Algebra k Y.functionField :=
    ((algebraMap k' Y.functionField).comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra X.functionField Y.functionField := (functionFieldMap q hq).hom.toAlgebra
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (q ≫ (X ↘ Spec (.of k))).appTop =
      CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv ≫
        (Y ↘ Spec (.of k')).appTop := by
    rw [hs, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  haveI : IsScalarTower k X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      have hc : q.appTop ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) =
          (Y ↘ Spec (.of k')).appTop ((Scheme.ΓSpecIso (.of k')).inv (algebraMap k k' c)) := by
        have := congrArg (fun g ↦ g.hom c) key
        simp only [Scheme.Hom.comp_appTop] at this
        exact this
      change Y.presheaf.germ ⊤ (genericPoint Y) trivial ((Y ↘ Spec (.of k')).appTop
          ((Scheme.ΓSpecIso (.of k')).inv (algebraMap k k' c))) =
        functionFieldMap q hq (X.presheaf.germ ⊤ (genericPoint X) trivial
          ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
      rw [functionFieldMap_germ_top, hc]
  obtain ⟨t, ht⟩ := exists_transcendental (k := k) (K := X.functionField)
  have hu : Transcendental k' (algebraMap X.functionField Y.functionField t) := by
    intro halg
    have h2 : IsIntegral k (algebraMap X.functionField Y.functionField t) :=
      isIntegral_trans (A := k') _ halg.isIntegral
    exact ht ((isAlgebraic_algebraMap_iff (algebraMap X.functionField Y.functionField).injective).1
      h2.isAlgebraic)
  haveI := isAlgebraic_adjoin hu
  haveI : Nontrivial Ω[Y.functionField⁄k'] :=
    Module.nontrivial_of_finrank_eq_succ
      (Module.finrank_eq_of_rank_eq (by rw [rank_kaehler_functionField k' Y]; rfl) :
        finrank Y.functionField Ω[Y.functionField⁄k'] = 0 + 1)
  haveI := finiteDimensional_globalDifferentials k' Y
  have hD : D k' Y.functionField (algebraMap X.functionField Y.functionField t) ≠ 0 :=
    kaehler_D_ne_zero
  have hmap : ∀ ω ∈ Anabelian.globalDifferentials k X,
      kaehlerMap k k' X.functionField Y.functionField ω ∈
        Anabelian.globalDifferentials k' Y := ?_
  · exact finrank_le_finrank_of_kaehlerMap (k := k) (k' := k')
      (fun x hx ↦ curve_mem_range_algebraMap_of_isAlgebraic k X hx)
      (rank_kaehler_functionField k X) hD _ _ hmap
  intro ω hω
  rw [Anabelian.globalDifferentials, Submodule.mem_iInf] at hω ⊢
  intro y
  have hy := hω (q y)
  letI := Anabelian.stalkAlgebra k X (q y)
  haveI := Anabelian.stalkAlgebra_isScalarTower k X (q y)
  letI := Anabelian.stalkAlgebra k' Y y
  haveI := Anabelian.stalkAlgebra_isScalarTower k' Y y
  obtain ⟨z, hz⟩ := kaehlerMap_mem_range (k := k) (k' := k') (K := X.functionField)
    (L := Y.functionField) (A := X.presheaf.stalk (q y))
    (B := Y.presheaf.stalk y) (fun a ↦ ⟨q.stalkMap y a, functionFieldMap_algebraMap q hq y a⟩)
    (LinearMap.mem_range.1 hy)
  exact LinearMap.mem_range.2 ⟨z, hz⟩

end Genus

/-! ### The normalisation of a curve in a finite étale cover -/

section Normalization

variable {k : Type u} [Field k] [CharZero k] {Xb : Scheme.{u}} [Xb.Over (Spec (.of k))]
  [Belyi.IsCurveOver k Xb] {U : Xb.Opens} (hU : (U : Set Xb).Nonempty) {Y : Scheme.{u}}
  (p : Y ⟶ U) [IsFinite p] [Etale p]

include hU in
/-- The rings of sections of the normalisation over affine opens are integrally closed. -/
lemma isIntegrallyClosed_sections_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    ∀ (V : (p ≫ U.ι).normalization.Opens), IsAffineOpen V → ∀ [Nonempty V],
      IsIntegrallyClosed Γ((p ≫ U.ι).normalization, V) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := Belyi.IsCurveOver.isIntegral k Xb
  exact fun V hV _ ↦
    isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := k)) hU p hV

omit [CharZero k] in
include hU in
/-- `q : N ⟶ X̄` maps the generic point to the generic point. -/
lemma fromNormalization_genericPoint [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    haveI := Belyi.IsCurveOver.isIntegral k Xb
    (p ≫ U.ι).fromNormalization (genericPoint (p ≫ U.ι).normalization) = genericPoint Xb := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := Belyi.IsCurveOver.isIntegral k Xb
  haveI : Nonempty U := ⟨⟨_, hU.some_mem⟩⟩
  haveI := isOpenImmersion_toNormalization k p
  have h1 : (p ≫ U.ι).toNormalization (genericPoint Y) =
      genericPoint (p ≫ U.ι).normalization := genericPoint_eq_of_isOpenImmersion _
  have h2 : U.ι (genericPoint U) = genericPoint Xb := genericPoint_eq_of_isOpenImmersion _
  have h3 : p (genericPoint Y) = genericPoint U := by
    obtain ⟨y, hy, hpy⟩ := Flat.generalizingMap p (genericPoint_specializes (p (genericPoint Y)))
    rw [← hpy, (hy.antisymm (genericPoint_specializes y)).eq]
  rw [← h1, ← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization,
    Scheme.Hom.comp_apply, h3, h2]

include hU in
/-- **Step A: the genus does not drop in a finite étale cover.** For the normalisation `N` of
the curve `X̄ / k` in a finite étale cover `Y ⟶ U ⊆ X̄` (`Y` integral), a curve over its constant
field `k'` via `CurvesJacobian.Cusp.toSpecConstField`, `g(X̄ / k) ≤ g(N / k')`. -/
theorem curveGenus_le_curveGenus_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    letI := normalizationOver k p
    haveI := Belyi.IsCurveOver.isIntegral k Xb
    Belyi.Anabelian.curveGenus k Xb ≤
      @Belyi.Anabelian.curveGenus (constField k (p ≫ U.ι).normalization) _
        (p ≫ U.ι).normalization
        ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) hU p)⟩ _ := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  letI := normalizationOver k p
  haveI := Belyi.IsCurveOver.isIntegral k Xb
  have hN := isIntegrallyClosed_sections_normalization (k := k) hU p
  haveI : IsProper ((p ≫ U.ι).normalization ↘ Spec (.of k)) :=
    isProper_normalization (k := k) hU p
  haveI : SmoothOfRelativeDimension 1 ((p ≫ U.ι).normalization ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_normalization (k := k) hU p
  have hc := isCurveOver_constField k _ hN (ringKrullDim_stalk_normalization_le (k := k) hU p)
  letI : (p ≫ U.ι).normalization.Over (Spec (.of (constField k (p ≫ U.ι).normalization))) :=
    ⟨toSpecConstField k _ hN⟩
  exact curveGenus_le_of_genericPoint (k := k) (k' := constField k (p ≫ U.ι).normalization)
    (p ≫ U.ι).fromNormalization (toSpecConstField_comp k _ hN).symm
    (fromNormalization_genericPoint (k := k) hU p)

end Normalization

end CurvesJacobian.Cusp
