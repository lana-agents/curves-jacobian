/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernNatural

/-!
# Compatibility of `M_X/n ≅ μ_n` with the reductions `M_X/nm → M_X/n`

**The transition map.** For `G ≃ₜ* Π̂_{g,0}` we have `H²(G, Ẑ) ≅ Ẑ` and
`M_X = Hom(H²(G, Ẑ), Ẑ)` ([Mzk19] l.302–305). The reduction map `M_X/nm → M_X/n` is the one
that sends the reduction of `ψ ∈ M_X` modulo `nm` to its reduction modulo `n`. In terms of
`M_X/k = Hom(H²(G, ℤ/k), ℤ/k)` (`TopClass.MXmod`), the reduction of `ψ` modulo `k` is the
`φ_k` with `φ_k(red_k u) = red_k(ψ u)` for `u ∈ H²(G, Ẑ)`. Since
`red_n = red_{nm→n,*} ∘ red_{nm}` on `H²(G, Ẑ)`, the transition `T : M_X/nm → M_X/n` is
characterised by

  `T(φ)(red_{nm→n,*} v) = red_{nm→n}(φ(v))`  for all `v ∈ H²(G, ℤ/nm)`

(`IsMXTransition`), where `red_{nm→n} : ℤ/nm → ℤ/n` is the reduction (`redZ`) and
`red_{nm→n,*}` its effect on `H²` (`TopClass.h2Map`). `red_{nm→n,*}` is surjective (it is
`ℤ/nm ↠ ℤ/n` under the relator value), so this determines `T(φ)`. Such a `T` exists: under the
relator-value identifications `M_X/k ≅ ℤ/k`, `φ ↦ φ(u₀)` (`u₀` the class with relator
value `1`), it is the reduction `ℤ/nm → ℤ/n`. The definition (`mxTransition`) and all
statements do not depend on the orientation.

* `TopClass.redZ`, `TopClass.IsMXTransition`, **`TopClass.exists_unique_mxTransition`**,
  `TopClass.mxTransition`, `TopClass.mxTransition_spec`.
* **`TopClass.h2Map_mxTransition_taut`**: `T_*` sends the tautological class modulo `nm` to the
  tautological class modulo `n`.
* `TopClass.hom_ext_of_isTaut`: homomorphisms `M_X/n → A` are determined by their effect on the
  tautological class.
* **`ChernClass.natIso_transition`**: `(ζ ↦ ζ^m) ∘ natIso_{nm} = natIso_n ∘ T`, i.e. the natural
  isomorphisms `M_X/n ≅ μ_n` of [Mzk19] Prop. 1.2(ii) form a compatible system, and they induce
  `M_X ≅ Ẑ(1)` in the limit.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen

noncomputable section

namespace CurvesJacobian.TopClass

section Generic

variable (G : Type*) [Group G] [TopologicalSpace G] (n m : ℕ)

/-- The reduction `ℤ/nm → ℤ/n`. -/
def redZ : TrivZ G (n * m) →* TrivZ G n :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (dvd_mul_right n m) (ZMod n)).toAddMonoidHom

omit [Group G] [TopologicalSpace G] in
lemma redZ_one : redZ G n m (TrivZ.one G (n * m)) = TrivZ.one G n := by
  change Multiplicative.ofAdd (ZMod.castHom (dvd_mul_right n m) (ZMod n) 1) = _
  rw [map_one]
  rfl

/-- **`T : M_X/nm → M_X/n` is the reduction map**: `T(φ)(red_* v) = red(φ(v))` for all
`v ∈ H²(G, ℤ/nm)`. -/
def IsMXTransition (T : MXmod G (n * m) →* MXmod G n) : Prop :=
  ∀ (φ : MXmod G (n * m)) (v : H2lc G (TrivZ G (n * m))),
    evAt (h2Map (redZ G n m) (fun _ _ ↦ rfl) v) (T φ) = redZ G n m (evAt v φ)

variable {G n m}

lemma h2Map_congr {M M' : Type*} [CommGroup M] [CommGroup M'] [MulDistribMulAction G M]
    [MulDistribMulAction G M'] {ρ ρ' : M →* M'} (h : ρ = ρ')
    (hρ : ∀ (g : G) (x : M), ρ (g • x) = g • ρ x) (hρ' : ∀ (g : G) (x : M), ρ' (g • x) = g • ρ' x)
    (c : H2lc G M) : h2Map ρ hρ c = h2Map ρ' hρ' c := by
  subst h
  rfl

end Generic

section Orientation

variable {G : Type*} [Group G] [TopologicalSpace G] {g : ℕ}
  (hg : 0 < g) (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)

/-- Homomorphisms out of `H²(G, ℤ/k)` are determined by their value at `u₀ = eZ⁻¹(1)`. -/
lemma h2_hom_ext {k : ℕ} [NeZero k] {B : Type*} [CommGroup B]
    {f f' : H2lc G (TrivZ G k) →* B} (h : f ((eZ hg e).symm (TrivZ.one G k)) =
      f' ((eZ hg e).symm (TrivZ.one G k))) : f = f' := by
  have : f.comp (eZ hg e).symm.toMonoidHom = f'.comp (eZ hg e).symm.toMonoidHom :=
    monoidHom_ext_zmod (n := k) h
  refine MonoidHom.ext fun x ↦ ?_
  simpa using DFunLike.congr_fun this (eZ hg e x)

lemma evAt_phi0 {k : ℕ} [NeZero k] :
    evAt ((eZ hg e).symm (TrivZ.one G k)) (phi0 hg e) = TrivZ.one G k :=
  MulEquiv.apply_symm_apply (eZ hg e) _

/-- `M_X/k ≅ ℤ/k`, `φ ↦ φ(u₀)` (depends on the orientation). -/
def mxEquiv (k : ℕ) [NeZero k] : MXmod G k ≃* TrivZ G k :=
  MulEquiv.ofBijective (evAt ((eZ hg e).symm (TrivZ.one G k)))
    ⟨fun _ _ h ↦ mxmod_ext hg e h, fun x ↦ ⟨phi0 hg e ^ (Multiplicative.toAdd x).val, by
      rw [map_pow, evAt_phi0]
      exact (ofAdd_val_pow (Multiplicative.toAdd x)).symm⟩⟩

variable {n m : ℕ} [NeZero n] [NeZero m]

lemma h2Map_redZ_u0 :
    h2Map (redZ G n m) (fun _ _ ↦ rfl) ((eZ hg e).symm (TrivZ.one G (n * m))) =
      (eZ hg e).symm (TrivZ.one G n) := by
  apply (eZ hg e).injective
  rw [MulEquiv.apply_symm_apply, h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl),
    MulEquiv.apply_symm_apply, redZ_one]

include hg e in
lemma h2Map_redZ_surjective : Function.Surjective (h2Map (G := G) (redZ G n m) (fun _ _ ↦ rfl)) :=
  fun u ↦ by
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right n m) (ZMod n))
      (Multiplicative.toAdd (eZ hg e u))
    refine ⟨(eZ hg e).symm (Multiplicative.ofAdd y), (eZ hg e).injective ?_⟩
    rw [h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl), MulEquiv.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hy

lemma isMXTransition_mxEquiv :
    IsMXTransition G n m ((mxEquiv hg e n).symm.toMonoidHom.comp
      ((redZ G n m).comp (mxEquiv hg e (n * m)).toMonoidHom)) := by
  intro φ
  have h := h2_hom_ext hg e (k := n * m)
    (f := (MXmod.toHom G n ((mxEquiv hg e n).symm.toMonoidHom.comp
      ((redZ G n m).comp (mxEquiv hg e (n * m)).toMonoidHom) φ)).comp
        (h2Map (redZ G n m) (fun _ _ ↦ rfl)))
    (f' := (redZ G n m).comp (MXmod.toHom G (n * m) φ)) (by
      change evAt (h2Map (redZ G n m) (fun _ _ ↦ rfl) ((eZ hg e).symm (TrivZ.one G (n * m))))
        ((mxEquiv hg e n).symm _) = _
      rw [h2Map_redZ_u0]
      exact MulEquiv.apply_symm_apply (mxEquiv hg e n) _)
  exact fun v ↦ DFunLike.congr_fun h v

end Orientation

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] {g : ℕ} {n m : ℕ} [NeZero n] [NeZero m]

/-- **The reduction `M_X/nm → M_X/n` exists and is unique** (`G ≃ₜ* Π̂_{g,0}`, `g ≥ 1`). -/
theorem exists_unique_mxTransition (hg : 0 < g)
    (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) :
    ∃! T : MXmod G (n * m) →* MXmod G n, IsMXTransition G n m T := by
  obtain ⟨e⟩ := he
  refine ⟨_, isMXTransition_mxEquiv hg e, fun T hT ↦ MonoidHom.ext fun φ ↦ ?_⟩
  refine mxmod_ext hg e ?_
  rw [← h2Map_redZ_u0 hg e (m := m), hT, isMXTransition_mxEquiv hg e]

/-- **The reduction map `M_X/nm → M_X/n`** (`IsMXTransition`). -/
def mxTransition (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) :
    MXmod G (n * m) →* MXmod G n :=
  (exists_unique_mxTransition hg he).exists.choose

theorem mxTransition_spec (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) :
    IsMXTransition G n m (mxTransition hg he) :=
  (exists_unique_mxTransition hg he).exists.choose_spec

/-- The reduction map sends a tautological class to a tautological class. -/
theorem isTaut_h2Map_of_isMXTransition (hg : 0 < g)
    (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) {T : MXmod G (n * m) →* MXmod G n}
    (hT : IsMXTransition G n m T) {t : H2lc G (MXmod G (n * m))} (ht : IsTaut G (n * m) t) :
    IsTaut G n (h2Map T (fun _ _ ↦ rfl) t) := by
  obtain ⟨e⟩ := he
  intro u
  obtain ⟨v, rfl⟩ := h2Map_redZ_surjective hg e (m := m) u
  rw [h2Map_comp, h2Map_congr (ρ' := (redZ G n m).comp (evAt v))
    (MonoidHom.ext fun φ ↦ hT φ v) _ (fun _ _ ↦ rfl),
    ← h2Map_comp (evAt v) (fun _ _ ↦ rfl) (redZ G n m) (fun _ _ ↦ rfl), ht v]

/-- **The tautological classes are compatible**: the reduction `T : M_X/nm → M_X/n` sends the
tautological class of `H²(G, M_X/nm)` to that of `H²(G, M_X/n)`. -/
theorem h2Map_mxTransition_taut (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0))
    {t : H2lc G (MXmod G (n * m))} (ht : IsTaut G (n * m) t) {t' : H2lc G (MXmod G n)}
    (ht' : IsTaut G n t') : h2Map (mxTransition hg he) (fun _ _ ↦ rfl) t = t' :=
  (exists_unique_isTaut hg he).unique
    (isTaut_h2Map_of_isMXTransition hg he (mxTransition_spec hg he) ht) ht'

/-- **Homomorphisms `M_X/k → A` are determined by the image of the tautological class.** -/
theorem hom_ext_of_isTaut {k : ℕ} [NeZero k] (hg : 0 < g)
    (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) {A : Type*} [CommGroup A] [Finite A]
    [MulDistribMulAction G A] (htriv : ∀ (γ : G) (a : A), γ • a = a)
    {t : H2lc G (MXmod G k)} (ht : IsTaut G k t) {ψ ψ' : MXmod G k →* A}
    (hψ : ∀ (γ : G) (x : MXmod G k), ψ (γ • x) = γ • ψ x)
    (hψ' : ∀ (γ : G) (x : MXmod G k), ψ' (γ • x) = γ • ψ' x)
    (h : h2Map ψ hψ t = h2Map ψ' hψ' t) : ψ = ψ' := by
  obtain ⟨e⟩ := he
  haveI := finite_mxmod (n := k) hg e
  have h1 := congrArg (h2EquivAny hg e htriv) h
  rw [h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) htriv ψ t,
    h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) htriv ψ' t, eMX_isTaut hg e ht] at h1
  refine MonoidHom.ext fun φ ↦ ?_
  rw [eq_phi0_pow hg e φ, map_pow, map_pow, h1]

end Main

end CurvesJacobian.TopClass

namespace CurvesJacobian.ChernClass

universe u

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n m : ℕ} [NeZero n] [NeZero m]

attribute [local instance] instTrivMu

variable (hH n m) in
/-- The reduction `M_X/nm → M_X/n` for `Δ_X` (`TopClass.mxTransition`). -/
noncomputable def mxTransitionX (hgen : 0 < (curveGenus k X).toNat) :
    TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (n * m) →*
      TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n :=
  TopClass.mxTransition hgen (nonempty_orientation hH hk hτ)

include hk hτ in
/-- **The natural isomorphisms `M_X/n ≅ μ_n` are compatible in `n`**: for the reduction
`T : M_X/nm → M_X/n` and `ζ ↦ ζ^m : μ_{nm} → μ_n`, `(ζ ↦ ζ^m) ∘ natIso_{nm} = natIso_n ∘ T`
(both send the tautological class modulo `nm` to `c1One` modulo `n`: `c1One_of_mul`,
`TopClass.h2Map_mxTransition_taut`). -/
theorem natIso_transition (hgen : 0 < (curveGenus k X).toNat) :
    (Mu.transition (dvd_mul_right n m)).comp (natIso hH hk hτ (n * m) hgen).toMonoidHom =
      (natIso hH hk hτ n hgen).toMonoidHom.comp (mxTransitionX hH hk hτ n m hgen) := by
  refine TopClass.hom_ext_of_isTaut hgen (nonempty_orientation hH hk hτ) (fun _ _ ↦ rfl)
    (isTaut_tautX (hH := hH) hk hτ (n := n * m) hgen) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ?_
  have h2 : TopClass.h2Map (mxTransitionX hH hk hτ n m hgen) (fun _ _ ↦ rfl)
      (tautX hH hk hτ (n * m) hgen) = tautX hH hk hτ n hgen :=
    TopClass.h2Map_mxTransition_taut hgen _ (isTaut_tautX (hH := hH) hk hτ hgen)
      (isTaut_tautX (hH := hH) hk hτ hgen)
  rw [← TopClass.h2Map_comp _ (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl),
    ← TopClass.h2Map_comp _ (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl), natIso_spec,
    ← c1One_of_mul hk hτ (m := m) hgen, h2, natIso_spec]

end Curve

end CurvesJacobian.ChernClass
