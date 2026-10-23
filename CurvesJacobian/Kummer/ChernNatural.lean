/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernDivisor
import CurvesJacobian.Kummer.PicDivisible
import CurvesJacobian.Kummer.ChernCompat
import CurvesJacobian.Kummer.TopClass
import WeilCurves.Hurwitz.Belyi

/-!
# The natural identification `M_X/n ≅ μ_n` and [AbsTopIII] Prop. 1.4(ii) modulo `n`

[Mzk19] = *Absolute anabelian cuspidalizations of proper hyperbolic curves*, Prop. 1.2(ii)
(`Absolute Anabelian Cuspidalizations.txt` l.363–371): there is a unique isomorphism
`M_X ≅ Ẑ(1)` sending the tautological class of `H²(Δ_X, M_X)` to the first Chern class of a line
bundle of degree `1`. [AbsTopIII] Prop. 1.4(ii) (`Topics in Absolute Anabelian Geometry III.txt`
l.1771–1802): the class of the extension `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` corresponds to the
natural isomorphism `M_X ≅ Ẑ(1) ≅ I_x`. Here, modulo every `n`, in the Galois model of
`CuspChern` / `ChernDivisor` (`X` proper of genus `≥ 1` over `k = k̄` of characteristic `0`):

* `c1Div_single_eq`: `c₁(𝒪_X(P)) = c₁(𝒪_X(Q))` for all points (`Pic⁰` is divisible,
  `exists_nsmul_eq_of_deg_eq_zero`), and `c1Div_eq_deg_smul`: `c₁(E) = deg E • c₁(pt)`;
  `c1One`: **the first Chern class modulo `n` of a degree-`1` line bundle**;
* `IsCuspPushout.h2EquivAny_mk`: under the relator-value isomorphism `H²(Δ_X, μ_n) ≅ μ_n` of the
  orientation `Δ_X ≅ Π̂_{g,0}` of `CuspCentral.exists_cuspCentral_equiv`, a cusp pushout along
  `χ` goes to `χ(c)⁻¹`, `c` the cusp generator (the `key` step of `IsCuspPushout.mk_eq`);
  `chiN_mem_zpowers`: `χ_n(c)` generates `μ_n` (`c` topologically generates `I_x`, `χ_n` is
  continuous and onto); hence **`c1One_generates`**: `c1One n` generates `H²(Δ_X, μ_n)`;
* `natIso n : M_X/n ≃* μ_n` with `natIso_spec` / `natIso_unique`: **[Mzk19] Prop. 1.2(ii) modulo
  `n`** (`TopClass.exists_unique_mulEquiv` with `c = c1One n`);
* **`IsCuspPushout.mk_eq_natIso`** ([AbsTopIII] Prop. 1.4(ii) modulo `n`): every pushout of
  `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` along the natural `I_x ≅ Ẑ(1) ↠ μ_n` has class
  `natIso_*(taut)`;
* `c1One_of_mul`: compatibility of `c1One` with `μ_{nm} → μ_n`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen WeilCurves.FunctionField

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
  {n : ℕ} [NeZero n]

attribute [local instance] isFunctionField_F instTrivMu

/-! ### Points of `X` -/

omit [IsAlgClosed k] [IsSepClosed Ω] [NeZero n] in
include hk in
/-- **The data of a point** (in continuation-passing form): for every place `P` of `F` there are
a place `W₀` of `Ω` over `P`, the point `x` of `X` under it, `U = X ∖ {x}`, and a uniformiser
`π` in the sense of `CuspChern`. -/
theorem pointData (P : Place k (F D)) {R : Prop}
    (hR : ∀ (x : X) (U : X.Opens) [Nonempty U] (W₀ : ValuationSubring Ω) (π : (F D)ˣ),
      (U : Set X)ᶜ = {x} → IsCentredOn D X eL ⊤ W₀ → ¬ IsCentredOn D X eL U W₀ →
      (∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P.1) → W₀.valuation ((π : F D) : Ω) < 1 →
      (∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) → R) :
    R := by
  obtain ⟨W₀, hW₀P⟩ := exists_valuationSubring_liesOver D P
  have hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW₀P _).2 (P.algebraMap_mem c)
  haveI := isSeparated_of_over k X
  have hkO : ∀ c : k, algebraMap k X.functionField c ∈ comapK D X eL hk W₀ := fun c ↦ by
    change ((eL (algebraMap k X.functionField c) : D.L) : Ω) ∈ W₀
    rw [hk]
    exact hkW₀ c
  obtain ⟨y, hy⟩ : ∃ y : X, stalkVS k y = comapK D X eL hk W₀ := by
    refine ⟨(pointEquivValuationSubringOver k (valuationRing_stalk_of_isCurveOver k X)).symm
      ⟨_, hkO⟩, ?_⟩
    have := congrArg Subtype.val ((pointEquivValuationSubringOver k
      (valuationRing_stalk_of_isCurveOver k X)).apply_symm_apply ⟨_, hkO⟩)
    rw [pointEquivValuationSubringOver_apply] at this
    exact this
  have hyη : y ≠ genericPoint X := by
    intro hyη
    apply P.ne_top
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h1 : eL.symm ⟨_, mem_L_of_mem_F z⟩ ∈ comapK D X eL hk W₀ := by
      have htop : stalkVS k (genericPoint X) = ⊤ := stalkValuationSubring_genericPoint _
      rw [← hy, hyη, htop]
      trivial
    have h2 : ((z : F D) : Ω) ∈ W₀ := by
      change ((eL (eL.symm ⟨_, mem_L_of_mem_F z⟩) : D.L) : Ω) ∈ W₀ at h1
      simpa using h1
    exact (hW₀P z).1 h2
  let U : X.Opens := ⟨{y}ᶜ, (isClosed_closedPoint k X ⟨y, hyη⟩).isOpen_compl⟩
  have hUx : (U : Set X)ᶜ = {y} := compl_compl _
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ hyη h.symm⟩⟩
  have hUfin : (U : Set X)ᶜ.Finite := hUx ▸ Set.finite_singleton y
  have hW₀ : IsCentredOn D X eL ⊤ W₀ := isCentredOn_top_of hk hkW₀
  have hW₀U : ¬ IsCentredOn D X eL U W₀ := fun h ↦
    (mem_of_isCentredOn D X eL hk U hUfin h hy) rfl
  obtain ⟨π, -, hπW, hπ⟩ := exists_uniformiser hW₀P
  exact hR y U W₀ π hUx hW₀ hW₀U hW₀P hπW hπ

/-- The place of `F` under a place `W₀ ⊇ k` of `Ω` carrying a uniformiser. -/
def placeUnder (W₀ : ValuationSubring Ω) (hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀) (π : (F D)ˣ)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1) : Place k (F D) :=
  ⟨W₀.comap (algebraMap (F D) Ω), fun htop ↦ by
    have hinv : (((π⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W₀ := by
      have : ((π⁻¹ : (F D)ˣ) : F D) ∈ W₀.comap (algebraMap (F D) Ω) :=
        htop ▸ ValuationSubring.mem_top _
      exact this
    have h1 := (W₀.valuation_le_one_iff _).2 hinv
    rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv, map_inv₀] at h1
    have h0 : W₀.valuation ((π : F D) : Ω) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact fun h ↦ π.ne_zero (Subtype.ext h)
    exact absurd ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h1) (not_le.2 hπW), fun c ↦ by
    change algebraMap (F D) Ω (algebraMap k (F D) c) ∈ W₀
    rw [← IsScalarTower.algebraMap_apply k (F D) Ω]
    exact hkW₀ c⟩

/-! ### Point independence and the class of a degree-`1` line bundle -/

include hk hτ in
/-- **`c₁(𝒪_X(P)) = c₁(𝒪_X(Q))`**: `P - Q` has degree `0`, hence is `n` times a divisor modulo
principal divisors (`Pic⁰` is divisible), and both are killed by `c1Div`. -/
theorem c1Div_single_eq (hgen : 0 < (curveGenus k X).toNat) (P Q : Place k (F D)) :
    c1Div hH hk hτ n hgen (Finsupp.single P 1) = c1Div hH hk hτ n hgen (Finsupp.single Q 1) := by
  have hdeg : (QuotientAddGroup.mk (Finsupp.single P 1 - Finsupp.single Q 1) :
      Pic k (F D)) ∈ (Pic.deg k (F D)).ker := by
    rw [AddMonoidHom.mem_ker, Pic.deg_mk, Divisor.deg_sub, Divisor.deg_single,
      Divisor.deg_single, Place.deg_eq_one, Place.deg_eq_one, sub_self]
  obtain ⟨y, hy⟩ := exists_nsmul_eq_of_deg_eq_zero hH hk (NeZero.ne n) ⟨_, hdeg⟩
  obtain ⟨E', hE'⟩ := QuotientAddGroup.mk_surjective (y : Pic k (F D))
  have h1 : (QuotientAddGroup.mk (n • E') : Pic k (F D)) =
      QuotientAddGroup.mk (Finsupp.single P 1 - Finsupp.single Q 1) := by
    have := congrArg Subtype.val hy
    rw [AddSubgroup.coe_nsmul, ← hE'] at this
    rw [QuotientAddGroup.mk_nsmul]
    exact this
  have h2 : c1Div hH hk hτ n hgen (Finsupp.single P 1 - Finsupp.single Q 1) = 0 := by
    rw [← c1Pic_mk hk hτ hgen, ← h1, c1Pic_mk, c1Div_nsmul]
  rw [map_sub] at h2
  exact sub_eq_zero.1 h2

include hk hτ in
/-- **`c₁(𝒪_X(E)) = deg E • c₁(𝒪_X(P))`** for every divisor `E` and every point `P`. -/
theorem c1Div_eq_deg_smul (hgen : 0 < (curveGenus k X).toNat) (P : Place k (F D))
    (E : Divisor k (F D)) :
    c1Div hH hk hτ n hgen E = E.deg • c1Div hH hk hτ n hgen (Finsupp.single P 1) := by
  induction E using Finsupp.induction_linear with
  | zero => rw [map_zero, Divisor.deg_zero, zero_smul]
  | add E E' hE hE' => rw [map_add, hE, hE', Divisor.deg_add, add_smul]
  | single Q m =>
    rw [Divisor.deg_single, Place.deg_eq_one, Nat.cast_one, mul_one,
      ← c1Div_single_eq hk hτ hgen Q P, ← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]

variable (hH n) in
/-- **The first Chern class modulo `n` of a line bundle of degree `1`**: `c₁(𝒪_X(P)) mod n` for
any point `P` (independent of `P`, `c1One_eq`). -/
noncomputable def c1One (hgen : 0 < (curveGenus k X).toNat) :
    H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω) :=
  Additive.toMul (c1Div hH hk hτ n hgen
    (Finsupp.single (Classical.arbitrary (Place k (F D))) 1))

/-- `c1One` is `c₁(𝒪_X(P))` for every point `P`. -/
theorem c1One_eq (hgen : 0 < (curveGenus k X).toNat) (P : Place k (F D)) :
    c1One hH hk hτ n hgen = Additive.toMul (c1Div hH hk hτ n hgen (Finsupp.single P 1)) :=
  congrArg Additive.toMul (c1Div_single_eq hk hτ hgen _ P)

/-- `c1Div E = deg E • c1One`. -/
theorem c1Div_eq_deg_smul_c1One (hgen : 0 < (curveGenus k X).toNat) (E : Divisor k (F D)) :
    c1Div hH hk hτ n hgen E = E.deg • Additive.ofMul (c1One hH hk hτ n hgen) :=
  c1Div_eq_deg_smul hk hτ hgen _ E

variable {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X} {π : (F D)ˣ}

/-- `c1One` is the first Chern class modulo `n` of `𝒪_X(x)` (`chernClassX`) for every point. -/
theorem c1One_eq_chernClassX (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {P₀ : Place k (F D)} (hW₀P : ∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P₀.1) {f : Ω}
    (hf : IsChernRep D eL hH n U W₀ ((π : F D) : Ω) f) :
    c1One hH hk hτ n hgen = chernClassX hk hτ hf := by
  rw [c1One_eq hk hτ hgen P₀, c1Div_single_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hW₀P hf]
  rfl

/-! ### The class of a cusp pushout under the relator value -/

omit [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X] [NeZero n]
  [Nonempty (⊤ : X.Opens)] in
/-- The image of the cusp generator of `Π̂_{G,1}` lies in the cuspidal inertia group. -/
lemma cuspHat_mem {G : ℕ}
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0) :
    Θ.symm (CuspCentral.cuspHat G) ∈ cuspInertia D X eL hH U W₀ := by
  have : CuspCentral.cuspHat G ∈ inertia (g := G) (r := 1) 0 :=
    Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  rw [← hI] at this
  obtain ⟨y, hy, hyc⟩ := this
  rw [← hyc]
  have : Θ.symm (Θ.toMulEquiv.toMonoidHom y) = y := Θ.symm_apply_apply y
  rw [this]
  exact hy

omit [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X] [NeZero n] in
/-- **The relator value of a cusp pushout** (the `key` step of `IsCuspPushout.mk_eq`, for
coefficients in `Type`): under `H²(Δ_X, M) ≅ M` of the orientation `Θ₀`, every cusp pushout
along `χ` goes to `χ(c)⁻¹`, `c = Θ⁻¹(cuspHat)`. -/
theorem IsCuspPushout.h2Equiv_mk {M : Type} [CommGroup M] [Finite M]
    [MulDistribMulAction π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) M]
    (htriv : ∀ (γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤)) (m : M), γ • m = m)
    {G : ℕ} (hG : 0 < G)
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hfill : ∀ γ, Θ₀ (fundamentalGroupMap (X.homOfLE le_top)
      (specPoint_genericL_homOfLE D X eL le_top) γ) = CuspCentral.fillHat G (Θ γ))
    (hc : Θ.symm (CuspCentral.cuspHat G) ∈ cuspInertia D X eL hH U W₀)
    {χ : cuspInertia D X eL hH U W₀ → M}
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) M}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U χ Φ Ψ) :
    h2EquivOfContinuousMulEquiv hG Θ₀ htriv (QuotientGroup.mk (toCocyclesX htriv hΦ)) =
      (χ ⟨_, hc⟩)⁻¹ := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  let φ := Θ₀.symm.toMulEquiv.toMonoidHom
  let η := (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (SurfaceGroup (g + 1) 1))).hom
  let a₁ : Fin (g + 1) → ProfiniteSurfaceGroup (g + 1) 1 := fun i ↦ η (genA i)
  let b₁ : Fin (g + 1) → ProfiniteSurfaceGroup (g + 1) 1 := fun i ↦ η (genB i)
  have hcomm : commProd a₁ b₁ = (CuspCentral.cuspHat (g + 1))⁻¹ := by
    simp only [a₁, b₁]
    rw [← map_commProd, CuspCentral.commProd_genA_genB_one, map_inv]
    rfl
  have hfill' : ∀ γ, fillX D eL U γ = Θ₀.symm (CuspCentral.fillHat (g + 1) (Θ γ)) :=
    fun γ ↦ (ContinuousMulEquiv.eq_symm_apply Θ₀).2 (hfill γ)
  have hX : ∀ i, (Ψ (Θ.symm (a₁ i))).g = φ (genAhat i) := fun i ↦ by
    rw [h.1, hfill', ContinuousMulEquiv.apply_symm_apply]
    simp only [a₁, η, φ]
    erw [CuspCentral.fillHat_eta, CuspCentral.fillHom_genA]
    rfl
  have hY : ∀ i, (Ψ (Θ.symm (b₁ i))).g = φ (genBhat i) := fun i ↦ by
    rw [h.1, hfill', ContinuousMulEquiv.apply_symm_apply]
    simp only [b₁, η, φ]
    erw [CuspCentral.fillHat_eta, CuspCentral.fillHom_genB]
    rfl
  have hAB : commProd (fun i ↦ φ (genAhat (g := g + 1) i)) (fun i ↦ φ (genBhat i)) = 1 := by
    rw [← map_commProd, commProd_genAhat, map_one]
  have hrel := commProd_eq_incl_relVal hAB Φ _ _ hX hY
  have hL : commProd (fun i ↦ Ψ (Θ.symm (a₁ i))) (fun i ↦ Ψ (Θ.symm (b₁ i))) =
      Twist.incl (χ ⟨_, hc⟩)⁻¹ := by
    have := map_commProd (Ψ.comp Θ.symm.toMulEquiv.toMonoidHom) a₁ b₁
    change Ψ (Θ.symm (commProd a₁ b₁)) =
      commProd (fun i ↦ Ψ (Θ.symm (a₁ i))) (fun i ↦ Ψ (Θ.symm (b₁ i))) at this
    rw [← this, hcomm, map_inv, map_inv, map_inv]
    congr 1
    exact h.2 ⟨_, hc⟩
  rw [hL] at hrel
  have hrel' := (Twist.incl_injective hrel).symm
  rw [← relVal_comap φ commProd_genAhat Φ] at hrel'
  exact hrel'

omit [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- `IsCuspPushout.h2Equiv_mk` for `μ_n` (any universe), with `TopClass.h2EquivAny`. -/
theorem IsCuspPushout.h2EquivAny_mk {G : ℕ} (hG : 0 < G)
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hfill : ∀ γ, Θ₀ (fundamentalGroupMap (X.homOfLE le_top)
      (specPoint_genericL_homOfLE D X eL le_top) γ) = CuspCentral.fillHat G (Θ γ))
    (hc : Θ.symm (CuspCentral.cuspHat G) ∈ cuspInertia D X eL hH U W₀)
    {χ : cuspInertia D X eL hH U W₀ → Mu n Ω}
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U χ Φ Ψ) :
    TopClass.h2EquivAny hG Θ₀ (fun _ _ ↦ rfl)
      (QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ)) = (χ ⟨_, hc⟩)⁻¹ := by
  let e : Mu n Ω ≃* Shrink.{0} (Mu n Ω) := Shrink.mulEquiv.symm
  haveI : Finite (Shrink.{0} (Mu n Ω)) := Finite.of_equiv _ (equivShrink _)
  letI : MulDistribMulAction π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Shrink.{0} (Mu n Ω)) :=
    Pi1.SurfaceGroup.trivialAction _ _
  have he := IsCuspPushout.h2Equiv_mk (fun _ _ ↦ rfl) hG Θ Θ₀ hfill hc (hΦ.comp e)
    (h.map e.toMonoidHom)
  have key : h2EquivOfContinuousMulEquiv hG Θ₀ (fun _ _ ↦ rfl)
      (TopClass.h2MapEquiv e (fun _ _ ↦ rfl)
        (QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ))) = (e (χ ⟨_, hc⟩))⁻¹ := he
  change Shrink.mulEquiv (h2EquivOfContinuousMulEquiv hG Θ₀ (fun _ _ ↦ rfl)
    (TopClass.h2MapEquiv e (fun _ _ ↦ rfl) (QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ))))
    = _
  rw [key, map_inv]
  simp [e]

/-! ### `χ_n` of the cusp generator generates `μ_n` -/

include hk hτ in
/-- **`χ_n(c)` generates `μ_n`** for `c = Θ⁻¹(cuspHat)`: `c` topologically generates `I_x`
(`Θ(I_x) = ⟨cuspHat⟩‾`), and `χ_n : I_x → μ_n` is continuous (into a discrete group) and onto
(the tame character is onto at every level, `evalTriv_kummer_surjective`). -/
theorem chiN_mem_zpowers (hgen : 0 < (curveGenus k X).toNat) (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {G : ℕ} (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0)
    (ζ : Mu n Ω) :
    ζ ∈ Subgroup.zpowers
      (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ ⟨_, cuspHat_mem Θ hI⟩) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  set χ := chiNHom (hH := hH) hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  have hχc : Continuous χ :=
    (ZHatOne.continuous_proj _).comp (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U
      hπW hπ).continuous
  -- `χ_n` is onto
  have hsurj : ∀ ζ : Mu n Ω, ∃ i, χ i = ζ := fun ζ ↦ by
    obtain ⟨σ, hσ, hσζ⟩ := evalTriv_kummer_surjective (D := D) hW₀.1 π hπW hπ n ζ
    refine ⟨CuspCentral.inertiaToCusp D eL hH U W₀ ⟨σ, hσ⟩, ?_⟩
    change ZHatOne.proj (kIdx D n) (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U
      hπW hπ (CuspCentral.inertiaToCusp D eL hH U W₀ ⟨σ, hσ⟩)) = ζ
    rw [CuspCentral.cuspInertiaZHatEquiv_inertiaToCusp, proj_tameChar]
    exact hσζ
  -- `χ_n⁻¹⟨χ_n(c)⟩` is a closed subgroup containing `c`, hence all of `I_x`
  set i₀ : cuspInertia D X eL hH U W₀ := ⟨_, cuspHat_mem Θ hI⟩
  let K : Subgroup (cuspInertia D X eL hH U W₀) := (Subgroup.zpowers (χ i₀)).comap χ
  have hIc : IsCompact (cuspInertia D X eL hH U W₀ :
      Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := by
    rw [CuspCentral.cuspInertia_eq_map D eL hH U W₀, Subgroup.coe_map]
    exact (isClosed_inertiaH D W₀).isCompact.image (D.continuous_chartHom hH _)
  haveI : CompactSpace (cuspInertia D X eL hH U W₀) := isCompact_iff_compactSpace.1 hIc
  have hKc : IsCompact (K : Set (cuspInertia D X eL hH U W₀)) :=
    ((isClosed_discrete (Subgroup.zpowers (χ i₀) : Set (Mu n Ω))).preimage hχc).isCompact
  let T : Subgroup (ProfiniteSurfaceGroup G 1) :=
    (K.map (cuspInertia D X eL hH U W₀).subtype).map Θ.toMulEquiv.toMonoidHom
  have hTc : IsClosed (T : Set (ProfiniteSurfaceGroup G 1)) := by
    rw [Subgroup.coe_map, Subgroup.coe_map, Set.image_image]
    exact (hKc.image (Θ.continuous.comp continuous_subtype_val)).isClosed
  have hi₀K : i₀ ∈ K := Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)
  have hcT : CuspCentral.cuspHat G ∈ T :=
    ⟨(i₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)), ⟨i₀, hi₀K, rfl⟩,
      Θ.apply_symm_apply _⟩
  have hIT : inertia (g := G) (r := 1) 0 ≤ T :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hcT) hTc
  have hK : ∀ i, i ∈ K := fun i ↦ by
    have h1 : Θ.toMulEquiv.toMonoidHom (i : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) ∈ T :=
      hIT (by rw [← hI]; exact Subgroup.mem_map_of_mem _ i.2)
    obtain ⟨y, ⟨j, hj, rfl⟩, hy⟩ := h1
    have : j = i := Subtype.ext (Θ.injective hy)
    exact this ▸ hj
  obtain ⟨i, rfl⟩ := hsurj ζ
  exact hK i

include hk hτ in
/-- **The class of a cusp pushout along `χ_n` generates `H²(Δ_X, μ_n)`.** -/
theorem IsCuspPushout.mem_zpowers (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {G : ℕ} (hG : 0 < G)
    (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* ProfiniteSurfaceGroup G 1)
    (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* ProfiniteSurfaceGroup G 0)
    (hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0)
    (hfill : ∀ γ, Θ₀ (fundamentalGroupMap (X.homOfLE le_top)
      (specPoint_genericL_homOfLE D X eL le_top) γ) = CuspCentral.fillHat G (Θ γ))
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ) Φ Ψ)
    (c' : H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)) :
    c' ∈ Subgroup.zpowers (QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) :
      H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)) := by
  set E := TopClass.h2EquivAny (M := Mu n Ω) hG Θ₀ (fun _ _ ↦ rfl)
  have hE := h.h2EquivAny_mk hG Θ Θ₀ hfill (cuspHat_mem Θ hI) hΦ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1
    (chiN_mem_zpowers hk hτ hgen hUx hW₀ hW₀U hπW hπ Θ hI (E c'))
  refine Subgroup.mem_zpowers_iff.2 ⟨-m, E.injective ((map_zpow E _ (-m)).trans ?_)⟩
  rw [hE, inv_zpow', neg_neg, hm]

include hk hτ in
/-- **`c1One n` generates `H²(Δ_X, μ_n)`** (`X` of genus `≥ 1`): it is the class of a cusp pushout
along `χ_n` ([AbsTopIII] Prop. 1.4(ii) comparison, `cuspCentral_class_eq_chernClass`). -/
theorem c1One_generates (hgen : 0 < (curveGenus k X).toNat)
    (c' : H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)) :
    c' ∈ Subgroup.zpowers (c1One hH hk hτ n hgen) := by
  refine pointData hk (Classical.arbitrary (Place k (F D)))
    fun x U _ W₀ π hUx hW₀ hW₀U hW₀P hπW hπ ↦ ?_
  obtain ⟨f, hf⟩ := exists_isChernRep hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  obtain ⟨Θ, Θ₀, hI, hfill, -, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  obtain ⟨-, -, -, ⟨Φ, Ψ, hΦ, hΦΨ⟩, -⟩ :=
    cuspCentral_class_eq_chernClass hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  rw [c1One_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hW₀P hf,
    ← hΦΨ.mk_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ hf]
  exact hΦΨ.mem_zpowers hk hτ hgen hUx hW₀ hW₀U hπW hπ hgen Θ Θ₀ hI hfill hΦ c'

/-! ### [Mzk19] Prop. 1.2(ii) modulo `n` -/

variable (hH) in
include hk hτ hH in
/-- `Δ_X ≃ₜ* Π̂_{g,0}` (an orientation exists). -/
theorem nonempty_orientation :
    Nonempty (π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  refine pointData hk (Classical.arbitrary (Place k (F D)))
    fun x U _ W₀ π hUx hW₀ hW₀U _ _ _ ↦ ?_
  obtain ⟨-, Θ₀, -⟩ := CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  exact ⟨Θ₀⟩

omit [IsAlgClosed k] [IsGalois (K₀ k t) Ω] in
variable (Ω n) in
include k in
/-- `#μ_n(Ω) = n`. -/
lemma natCard_mu : Nat.card (Mu n Ω) = n := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  exact hμ.card_rootsOfUnity

variable (hH n) in
/-- **The tautological class** of `H²(Δ_X, M_X/n)` ([Mzk19] Prop. 1.2(i) modulo `n`). -/
noncomputable def tautX (hgen : 0 < (curveGenus k X).toNat) :
    H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤)
      (TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n) :=
  (TopClass.exists_unique_isTaut (n := n) hgen (nonempty_orientation hH hk hτ)).exists.choose

theorem isTaut_tautX (hgen : 0 < (curveGenus k X).toNat) :
    TopClass.IsTaut π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n (tautX hH hk hτ n hgen) :=
  (TopClass.exists_unique_isTaut (n := n) hgen (nonempty_orientation hH hk hτ)).exists.choose_spec

/-- [Mzk19] Prop. 1.2(ii) modulo `n` for `X`: existence and uniqueness. -/
theorem exists_unique_natIso (hgen : 0 < (curveGenus k X).toNat) :
    ∃! ι : TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n ≃* Mu n Ω,
      TopClass.h2Map ι.toMonoidHom (fun _ _ ↦ rfl) (tautX hH hk hτ n hgen) =
        c1One hH hk hτ n hgen :=
  TopClass.exists_unique_mulEquiv hgen (nonempty_orientation hH hk hτ) (fun _ _ ↦ rfl)
    (natCard_mu (k := k) (Ω := Ω) (n := n)) (c1One hH hk hτ n hgen) (c1One_generates hk hτ hgen)
    (isTaut_tautX hk hτ hgen)

variable (hH n) in
/-- **The natural isomorphism `M_X/n ≅ μ_n`** ([Mzk19] Prop. 1.2(ii) modulo `n`): the unique
isomorphism sending the tautological class to the first Chern class modulo `n` of a line bundle
of degree `1`. -/
noncomputable def natIso (hgen : 0 < (curveGenus k X).toNat) :
    TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n ≃* Mu n Ω :=
  (exists_unique_natIso (hH := hH) hk hτ hgen).exists.choose

theorem natIso_spec (hgen : 0 < (curveGenus k X).toNat) :
    TopClass.h2Map (natIso hH hk hτ n hgen).toMonoidHom (fun _ _ ↦ rfl) (tautX hH hk hτ n hgen) =
      c1One hH hk hτ n hgen :=
  (exists_unique_natIso (hH := hH) hk hτ hgen).exists.choose_spec

theorem natIso_unique (hgen : 0 < (curveGenus k X).toNat)
    (ι : TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n ≃* Mu n Ω)
    (hι : TopClass.h2Map ι.toMonoidHom (fun _ _ ↦ rfl) (tautX hH hk hτ n hgen) =
      c1One hH hk hτ n hgen) : ι = natIso hH hk hτ n hgen :=
  (exists_unique_natIso (hH := hH) hk hτ hgen).unique hι (natIso_spec hk hτ hgen)

/-! ### [AbsTopIII] Prop. 1.4(ii) modulo `n` -/

include hk hτ in
/-- **[AbsTopIII] Prop. 1.4(ii) modulo `n`** (T3 l.1771–1802): for a point `x` of `X` (genus
`≥ 1`), `U = X ∖ {x}`, a place `W₀` over `x` and a uniformiser `π`, every pushout `(Φ, Ψ)` of
`1 → I_x → Δ^{c-cn}_U → Δ_X → 1` along the natural `I_x ≅ Ẑ(1) ↠ μ_n` (`chiN`) has class
`natIso_*(taut)`: the extension corresponds to the natural isomorphism `M_X/n ≅ μ_n` of
[Mzk19] Prop. 1.2(ii). -/
theorem IsCuspPushout.mk_eq_natIso (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) =
      TopClass.h2Map (natIso hH hk hτ n hgen).toMonoidHom (fun _ _ ↦ rfl)
        (tautX hH hk hτ n hgen) := by
  obtain ⟨f, hf⟩ := exists_isChernRep hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  rw [natIso_spec, c1One_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ
    (P₀ := placeUnder W₀ hW₀.1 π hπW) (fun _ ↦ Iff.rfl) hf]
  exact h.mk_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ hf

/-! ### Compatibility in `n` -/

include hk hτ in
/-- **`c1One` is compatible with `μ_{nm} → μ_n`, `ζ ↦ ζ^m`** (`ChernCompat.chernClassX_of_mul`). -/
theorem c1One_of_mul {m : ℕ} [NeZero m] (hgen : 0 < (curveGenus k X).toNat) :
    c1One hH hk hτ n hgen = TopClass.h2Map (Mu.transition (dvd_mul_right n m)) (fun _ _ ↦ rfl)
      (c1One hH hk hτ (n * m) hgen) := by
  refine pointData hk (Classical.arbitrary (Place k (F D)))
    fun x U _ W₀ π hUx hW₀ hW₀U hW₀P hπW hπ ↦ ?_
  obtain ⟨f, hf⟩ := exists_isChernRep hk hτ (n := n * m) hgen hUx hW₀ hW₀U hπW hπ
  rw [c1One_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hW₀P hf.of_mul,
    c1One_eq_chernClassX hk hτ hgen hUx hW₀ hW₀U hπW hπ hW₀P hf]
  exact chernClassX_of_mul hk hτ hf

end Curve

end CurvesJacobian.ChernClass
