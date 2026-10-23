/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NatIsoCompat

/-!
# `M_X ≅ Ẑ(1) ≅ I_x` at the `Ẑ(1)`-level ([AbsTopIII] Prop. 1.4(ii), [Mzk19] Prop. 1.2(ii))

[Mzk19] = *Absolute anabelian cuspidalizations of proper hyperbolic curves*
(`Absolute Anabelian Cuspidalizations.txt`), l.302–305: `M_X := Hom(H²(Δ_X, Ẑ), Ẑ)`;
Prop. 1.2(ii) (l.363–371): the unique `M_X ≅ Ẑ(1)` sending the tautological class to the first
Chern class of a degree-`1` line bundle. [AbsTopIII] Prop. 1.4(ii)
(`Topics in Absolute Anabelian Geometry III.txt` l.1771–1802): the extension
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` corresponds to the natural `M_X ≅ Ẑ(1) ≅ I_x`.

`Kummer/ChernNatural.lean` and `Kummer/NatIsoCompat.lean` prove this modulo every `n`, compatibly
in `n`. Here the levels are assembled into the inverse limit:

* `TopClass.redDvd`: `ℤ/N ↠ ℤ/n` for `n ∣ N`; `TopClass.IsMXCompat h φ ψ`: `ψ ∈ M_X/n` is the
  reduction of `φ ∈ M_X/N` (`ψ(red_* v) = red(φ v)`, orientation-free);
  `TopClass.eq_mxTransition_of_isMXCompat`: this is `mxTransition` when `N = n m`;
* **`TopClass.MXHat G K`** `= lim_n M_X/n` (compatible families over the Kummer indices of `K`),
  i.e. `Hom((H²(G, ℤ/n))_n, (ℤ/n)_n)`, the form of `M_X` used in iut `Reconstruction/Cusp`;
* `ChernClass.isMXCompat_iff_natIso`: `ψ` is the reduction of `φ` iff
  `natIso_N φ ↦ natIso_n ψ` under `μ_N → μ_n`;
* **`ChernClass.natIsoHat : M_X ≃* Ẑ(1)`** (`ZHatOne (F D) Ω`): [Mzk19] Prop. 1.2(ii) in the
  limit, levelwise `natIso` (`natIsoHat_apply`);
* **`ChernClass.syncEquiv : I_x ≃* M_X`**, the composite of `cuspInertiaZHatEquiv : I_x ≅ Ẑ(1)`
  (Prop. 1.4(i)) and `natIsoHat⁻¹`, with `natIso_syncEquiv`: its level-`n` component is `χ_n`
  under `natIso_n`; and **`ChernClass.IsCuspPushout.mk_eq_natIso_syncEquiv`**: every pushout of
  the cuspidally central extension along `I_x → M_X ↠ M_X/n ≅ μ_n` has class `natIso_*(taut)`
  (Prop. 1.4(ii), all levels at once).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen WeilCurves.FunctionField

noncomputable section

namespace CurvesJacobian.TopClass

section Hat

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- The reduction `ℤ/N → ℤ/n` for `n ∣ N`. -/
def redDvd {n N : ℕ} (h : n ∣ N) : TrivZ G N →* TrivZ G n :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod n)).toAddMonoidHom

omit [Group G] [TopologicalSpace G] in
lemma redDvd_mul (n m : ℕ) : redDvd G (dvd_mul_right n m) = redZ G n m := rfl

/-- **`ψ ∈ M_X/n` is the reduction of `φ ∈ M_X/N`** (`n ∣ N`): `ψ(red_* v) = red(φ(v))` for all
`v ∈ H²(G, ℤ/N)`. -/
def IsMXCompat {n N : ℕ} (h : n ∣ N) (φ : MXmod G N) (ψ : MXmod G n) : Prop :=
  ∀ v : H2lc G (TrivZ G N),
    evAt (h2Map (redDvd G h) (fun _ _ ↦ rfl) v) ψ = redDvd G h (evAt v φ)

variable (K : Type*) [Field K]

/-- **`M_X = lim_n M_X/n = Hom((H²(G, ℤ/n))_n, (ℤ/n)_n)`** ([Mzk19] l.302–305): the compatible
families of `φ_n ∈ M_X/n = Hom(H²(G, ℤ/n), ℤ/n)`, `n` running over the Kummer indices of `K`
(all `n ≥ 1` in characteristic `0`). -/
def MXHat : Subgroup (∀ i : KummerIndex K, MXmod G i.n) where
  carrier := {φ | ∀ i j (h : i ≤ j), IsMXCompat G h (φ j) (φ i)}
  mul_mem' {φ ψ} hφ hψ i j h v := by
    simp only [Pi.mul_apply, map_mul, hφ i j h v, hψ i j h v]
  one_mem' i j h v := by simp only [Pi.one_apply, map_one]
  inv_mem' {φ} hφ i j h v := by simp only [Pi.inv_apply, map_inv, hφ i j h v]

variable {G K}

/-- The projection `M_X → M_X/n`. -/
def MXHat.proj (i : KummerIndex K) : MXHat G K →* MXmod G i.n :=
  (Pi.evalMonoidHom _ i).comp (MXHat G K).subtype

@[simp] lemma MXHat.proj_apply (i : KummerIndex K) (φ : MXHat G K) :
    MXHat.proj i φ = (φ : ∀ i, MXmod G i.n) i := rfl

/-- `mxTransition` is the reduction in the sense of `IsMXCompat`. -/
lemma isMXCompat_mxTransition {g n m : ℕ} [NeZero n] [NeZero m] (hg : 0 < g)
    (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) (φ : MXmod G (n * m)) :
    IsMXCompat G (dvd_mul_right n m) φ (mxTransition hg he φ) :=
  mxTransition_spec hg he φ

/-- **The reduction of `φ` modulo `n` is unique**: it is `mxTransition φ`. -/
lemma eq_mxTransition_of_isMXCompat {g n m : ℕ} [NeZero n] [NeZero m] (hg : 0 < g)
    (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) {φ : MXmod G (n * m)} {ψ : MXmod G n}
    (hc : IsMXCompat G (dvd_mul_right n m) φ ψ) : ψ = mxTransition hg he φ := by
  obtain ⟨e⟩ := id he
  apply (MXmod.toHom G n).injective
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨v, rfl⟩ := h2Map_redZ_surjective hg e (m := m) u
  exact (hc v).trans (isMXCompat_mxTransition hg he φ v).symm

end Hat

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

attribute [local instance] instTrivMu

open TopClass

include hk hτ in
/-- **Reduction of `M_X` corresponds to `μ_N → μ_n` under the natural isomorphisms**: for
`n ∣ N`, `ψ ∈ M_X/n` is the reduction of `φ ∈ M_X/N` iff `natIso_N φ ↦ natIso_n ψ`
(`natIso_transition`). -/
theorem isMXCompat_iff_natIso (hgen : 0 < (curveGenus k X).toNat) {n N : ℕ} [NeZero n]
    [NeZero N] (h : n ∣ N) (φ : MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) N)
    (ψ : MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n) :
    IsMXCompat _ h φ ψ ↔
      Mu.transition h (natIso hH hk hτ N hgen φ) = natIso hH hk hτ n hgen ψ := by
  obtain ⟨m, rfl⟩ := h
  haveI : NeZero m := ⟨right_ne_zero_of_mul (NeZero.ne (n * m))⟩
  have hT := DFunLike.congr_fun (natIso_transition (hH := hH) hk hτ (n := n) (m := m) hgen) φ
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hT
  rw [hT]
  constructor
  · intro hc
    rw [eq_mxTransition_of_isMXCompat hgen (nonempty_orientation hH hk hτ) hc]
    rfl
  · intro he
    have := (natIso hH hk hτ n hgen).injective he
    rw [← this]
    exact isMXCompat_mxTransition hgen (nonempty_orientation hH hk hτ) φ

variable (hH) in
include hk hτ in
/-- **The natural isomorphism `M_X ≅ Ẑ(1)`** ([Mzk19] Prop. 1.2(ii)): the inverse limit of the
`natIso n : M_X/n ≃* μ_n` (`isMXCompat_iff_natIso`). -/
noncomputable def natIsoHat (hgen : 0 < (curveGenus k X).toNat) :
    MXHat π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (F D) ≃* ZHatOne (F D) Ω where
  toFun φ := ⟨fun i ↦ natIso hH hk hτ i.n hgen (φ.1 i), fun i j h ↦
    (isMXCompat_iff_natIso hk hτ hgen h _ _).1 (φ.2 i j h)⟩
  invFun z := ⟨fun i ↦ (natIso hH hk hτ i.n hgen).symm (z.1 i), fun i j h ↦
    (isMXCompat_iff_natIso hk hτ hgen h _ _).2 (by
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact z.2 i j h)⟩
  left_inv φ := Subtype.ext (funext fun i ↦ MulEquiv.symm_apply_apply _ _)
  right_inv z := Subtype.ext (funext fun i ↦ MulEquiv.apply_symm_apply _ _)
  map_mul' φ ψ := by
    apply Subtype.ext
    funext i
    exact map_mul (natIso hH hk hτ i.n hgen) (φ.1 i) (ψ.1 i)

@[simp] lemma natIsoHat_apply (hgen : 0 < (curveGenus k X).toNat)
    (φ : MXHat π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (F D)) (i : KummerIndex (F D)) :
    ZHatOne.proj i (natIsoHat hH hk hτ hgen φ) = natIso hH hk hτ i.n hgen (MXHat.proj i φ) :=
  rfl

variable {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X} {π : (F D)ˣ}

variable (hH U) in
/-- **The synchronization `I_x ≅ M_X`** ([AbsTopIII] Prop. 1.4(ii)): `I_x ≅ Ẑ(1)` by the tame
character (`cuspInertiaZHatEquiv`, Prop. 1.4(i)) followed by the inverse of the natural
`M_X ≅ Ẑ(1)` of [Mzk19] Prop. 1.2(ii) (`natIsoHat`). -/
noncomputable def syncEquiv (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    cuspInertia D X eL hH U W₀ ≃* MXHat π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (F D) :=
  (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U hπW hπ).toMulEquiv.trans
    (natIsoHat hH hk hτ hgen).symm

/-- The level-`n` component of `syncEquiv` is `χ_n : I_x ↠ μ_n` under `natIso_n`. -/
theorem natIso_syncEquiv (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (n : ℕ) [NeZero n] (σ : cuspInertia D X eL hH U W₀) :
    natIso hH hk hτ n hgen
        (MXHat.proj (kIdx D n) (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ σ)) =
      chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ σ := by
  simp only [syncEquiv, MulEquiv.trans_apply, MXHat.proj_apply]
  exact MulEquiv.apply_symm_apply (natIso hH hk hτ n hgen) _

include hk hτ in
/-- **[AbsTopIII] Prop. 1.4(ii), all levels** (T3 l.1771–1802): for a point `x` of `X` (genus
`≥ 1`), `U = X ∖ {x}`, and every `n`, every pushout `(Φ, Ψ)` of
`1 → I_x → Δ^{c-cn}_U → Δ_X → 1` along `I_x ≅ M_X ↠ M_X/n ≅ μ_n` (`syncEquiv`, then the
projection, then `natIso_n`) has class `natIso_*(taut)`: the extension corresponds to the
synchronization `I_x ≅ M_X` (`syncEquiv`). -/
theorem IsCuspPushout.mk_eq_natIso_syncEquiv (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (n : ℕ) [NeZero n]
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U (fun σ ↦ natIso hH hk hτ n hgen
      (MXHat.proj (kIdx D n) (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ σ))) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) =
      TopClass.h2Map (natIso hH hk hτ n hgen).toMonoidHom (fun _ _ ↦ rfl)
        (tautX hH hk hτ n hgen) := by
  have hχ : (fun σ ↦ natIso hH hk hτ n hgen
      (MXHat.proj (kIdx D n) (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ σ))) =
      chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ :=
    funext (natIso_syncEquiv hk hτ hgen hUx hW₀ hW₀U hπW hπ n)
  rw [hχ] at h
  exact IsCuspPushout.mk_eq_natIso hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ h

include hk hτ in
/-- **[AbsTopIII] Prop. 1.4(ii), tautological form**: every pushout of
`1 → I_x → Δ^{c-cn}_U → Δ_X → 1` along `I_x ≅ M_X ↠ M_X/n` (`syncEquiv` followed by the
projection) has the tautological class of `H²(Δ_X, M_X/n)` ([Mzk19] Prop. 1.2(i)): the
extension class corresponds to `syncEquiv` ("the `E₂`-differential of `1 ∈ Hom(I_x, I_x)` gives
`M_X ≅ I_x`", T3 l.1771–1795). -/
theorem IsCuspPushout.mk_eq_tautX (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (n : ℕ) [NeZero n]
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤)
      (MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U
      (fun σ ↦ MXHat.proj (kIdx D n) (syncEquiv hH hk hτ U hgen hUx hW₀ hW₀U hπW hπ σ)) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) = tautX hH hk hτ n hgen := by
  let ι := natIso hH hk hτ n hgen
  have h' := mk_eq_natIso_syncEquiv hk hτ hgen hUx hW₀ hW₀U hπW hπ n
    (hΦ.comp (⇑ι.toMonoidHom)) (h.map ι.toMonoidHom)
  apply (h2MapEquiv ι (fun _ _ ↦ rfl)).injective
  rw [h2MapEquiv_apply, h2MapEquiv_apply, ← h']
  rfl

end Curve

end CurvesJacobian.ChernClass
