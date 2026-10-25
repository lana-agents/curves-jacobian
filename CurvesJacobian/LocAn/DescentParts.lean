/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.DescentBase
import CurvesJacobian.LocAn.UniqueProper
import CurvesJacobian.Cusp.ExtensionMap

/-!
# The three parts of the descent debt `DescentIso` ([LocAn] Cor. 15.5)

The debt `CurvesJacobian.LocAn.DescentIso` (`LocAn/DescentBase.lean`) descends an `L`-isomorphism
`U₁,L ≅ U₂,L` inducing the base change `φ_L` of `φ : Π_{U₁} ≃ Π_{U₂}` (over `G_K`) to a
`K`-isomorphism inducing `φ`. The proof of [LocAn] Cor. 15.5
(`The Local Pro-p Anabelian Geometry of Curves.txt`, l.4336–4370) has three steps:

* (i) **no moduli** (l.4350–4354): "since morphisms between hyperbolic curves … clearly have no
  moduli …, it follows that `φ_L` descends to a finite Galois extension `K'` of `K`";
* (ii) **Galois descent** (l.4354–4363): "if `σ ∈ Gal(K'/K)`, then conjugating `φ_{K'}` by `σ`
  gives a morphism `φ^σ_{K'}` whose induced morphism on geometric fundamental groups is the result
  of conjugating `θ^geom` by `σ`. … `θ^geom` is fixed (up to … an inner automorphism defined by an
  element of `Δ_Y`) by conjugation by `σ`. Thus, `φ_{K'}` and `φ^σ_{K'}` induce the same morphism
  on geometric fundamental groups, hence coincide … This shows that `φ_{K'}` descends to a
  morphism `φ_K`";
* (iii) **the covering step** (l.4363–4366): "Repeating this construction … for coverings of `X_K`
  and `Y_K` shows that the morphism induced by `φ_K` on fundamental groups coincides with `θ` (up
  to composition with an inner automorphism defined by an element of `Δ_Y`)".

This file states (i) and (ii) as plain propositions and **proves (iii)** at the `π₁ᵉᵗ` level: a
`K`-isomorphism `f` whose induced map agrees with `φ` on `Δ₁ = ker(Π_{U₁} → G_K)` (through a path
over the base) induces `φ` on all of `Π_{U₁}`. In place of the covering argument we use that both
`φ` and `γ_* ∘ π₁ᵉᵗ(f)` are homomorphisms of extensions `Δ_i ↪ Π_{U_i} ↠ G_K` agreeing on `Δ₁`,
and `Δ₂` is centre-free (`CurvesJacobian.Cusp.isExtLift_unique`).

## Main results

* `CurvesJacobian.LocAn.center_eq_bot_of_mulEquiv`: centre-freeness transported along a group
  isomorphism matching two subgroups;
* **`CurvesJacobian.LocAn.center_ker_toSpec_eq_bot`**: for a hyperbolic curve `C` with a cusp over a
  number field `K` and any geometric point `ξ` over an algebraic closure `Ω`,
  `Z(ker(π₁ᵉᵗ(U, ξ) → G_K)) = 1` (from `Δ ≅ Π̂_{g,r}` slim at MR8's base point,
  `CurvesJacobian.Cusp.isSlim_Delta`, transported along `U ≅ Spec Γ(U)` and a change of base
  point);
* `CurvesJacobian.LocAn.eq_of_isOver_of_eqOn_ker`: two maps of extensions over `Q` agreeing on
  `ker p₁` coincide when `Z(ker p₂) = 1` (from `CurvesJacobian.Cusp.isExtLift_unique`);
* `CurvesJacobian.LocAn.AgreesOnDelta ξ₁ ξ₂ f φ`: the induced map of `f` agrees with `φ` on `Δ₁`
  through a path over the base;
* **`CurvesJacobian.LocAn.inducedBy_of_agreesOnDelta`** (part (iii)): `AgreesOnDelta` and `φ` over
  `G_K` give `InducedBy ξ₁ ξ₂ f φ`, if `Z(Δ₂) = 1`;
* `CurvesJacobian.LocAn.DescentNoModuli` (debt (i)), `CurvesJacobian.LocAn.GaloisDescentGeom`
  (debt (ii)), `CurvesJacobian.LocAn.DescentGeom` ((i)+(ii)) and `descentGeom_of_parts`;
* **`CurvesJacobian.LocAn.descentIso_of_descentGeom`**: `DescentGeom → DescentIso` (centre-freeness
  discharged), and `descentIso_of_parts`.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian HypCurve CurvesJacobian.Cusp

noncomputable section

namespace CurvesJacobian.LocAn

/-! ### Centre-freeness of `Δ` at every geometric point -/

section Center

/-- **Centre-freeness along an isomorphism**: if `e : G ≃* H` matches `N ≤ G` with `M ≤ H` and `M`
is centre-free, so is `N`. -/
theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {N : Subgroup G} {M : Subgroup H} (hNM : ∀ g, g ∈ N ↔ e g ∈ M)
    (hM : Subgroup.center M = ⊥) : Subgroup.center N = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : (⟨e z, (hNM z).1 z.2⟩ : M) ∈ Subgroup.center M :=
    Subgroup.mem_center_iff.2 fun m ↦ by
      obtain ⟨g, hg⟩ := e.surjective m
      have hgN : g ∈ N := (hNM g).2 (hg ▸ m.2)
      have := Subgroup.mem_center_iff.1 hz ⟨g, hgN⟩
      apply Subtype.ext
      change (m : H) * e z = e z * m
      rw [← hg, ← map_mul, ← map_mul]
      exact congrArg (fun x : N ↦ e x) this
  rw [hM, Subgroup.mem_bot] at hz'
  exact Subtype.ext (e.injective ((congrArg Subtype.val hz').trans (map_one e).symm))

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- A change of base point `β` matches the kernels of `Π_U → G_k` at the two points. -/
lemma mem_ker_toSpec_iff_conjAut {C : HypCurve k} (pt pt' : GeomPt Ω C)
    (β : fiber pt.x ≅ fiber pt'.x) (σ : π₁ᵉᵗ(pt.x)) :
    σ ∈ (fundamentalGroupMap C.toSpec pt.over).toMonoidHom.ker ↔
      autContinuousMulEquivOfIso β σ ∈ (fundamentalGroupMap C.toSpec pt'.over).toMonoidHom.ker := by
  simp only [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom]
  have e := fundamentalGroupMap_autContinuousMulEquivOfIso C.toSpec pt.over pt'.over β σ
  refine ⟨fun h ↦ e.trans ((congrArg _ h).trans (map_one _)), fun h ↦ ?_⟩
  exact (map_eq_one_iff _ (autContinuousMulEquivOfIso _).injective).1 (e.symm.trans h)

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

omit [Algebra.IsAlgebraic K Ω] in
/-- At MR8's base point, `ker(Π_U → G_K)` (`projGk`) corresponds to the kernel at `arithGeomPt`. -/
lemma mem_ker_projGk_iff (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (σ) :
    σ ∈ (projGk Ω C hc).toMonoidHom.ker ↔ arithGeomEquiv Ω C hc σ ∈
      (fundamentalGroupMap C.toSpec (arithGeomPt Ω C hc).over).toMonoidHom.ker := by
  simp only [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom]
  exact (congrArg (· = 1) (fundamentalGroupMap_toSpec_arithGeomEquiv Ω C hc σ)).to_iff.symm

/-- **`Δ = ker(π₁ᵉᵗ(U, ξ) → G_K)` is centre-free** for a hyperbolic curve with a cusp over a number
field and every geometric point (`Δ ≅ Π̂_{g,r}` is slim, `CurvesJacobian.Cusp.isSlim_Delta`). -/
theorem center_ker_toSpec_eq_bot (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (pt : GeomPt Ω C) :
    Subgroup.center (fundamentalGroupMap C.toSpec pt.over).toMonoidHom.ker = ⊥ := by
  have h0 := (isSlim_Delta Ω C hc (isHyperbolic_baseChange Ω C)).center_eq_bot
  have h1 : Subgroup.center
      (fundamentalGroupMap C.toSpec (arithGeomPt Ω C hc).over).toMonoidHom.ker = ⊥ :=
    center_eq_bot_of_mulEquiv (arithGeomEquiv Ω C hc).symm.toMulEquiv
      (fun g ↦ by
        have := (mem_ker_projGk_iff C hc ((arithGeomEquiv Ω C hc).symm g)).symm
        rw [ContinuousMulEquiv.apply_symm_apply] at this
        exact this) h0
  obtain ⟨β⟩ : Nonempty (fiber pt.x ≅ fiber (arithGeomPt Ω C hc).x) :=
    nonempty_iso_of_fiberFunctor _ _
  exact center_eq_bot_of_mulEquiv (autContinuousMulEquivOfIso β).toMulEquiv
    (mem_ker_toSpec_iff_conjAut pt _ β) h1

end Center

/-- **Maps of extensions agreeing on the kernel coincide** if the target kernel is centre-free
(`CurvesJacobian.Cusp.isExtLift_unique`): `φ, Φ : E₁ → E₂` over `Q` with `φ` surjective and
`φ = Φ` on `ker p₁`. -/
theorem eq_of_isOver_of_eqOn_ker {E₁ E₂ Q : Type*} [Group E₁] [Group E₂] [Group Q]
    (p₁ : E₁ →* Q) (p₂ : E₂ →* Q) (hcen : Subgroup.center p₂.ker = ⊥) (φ Φ : E₁ →* E₂)
    (hsurj : Function.Surjective φ) (hφ : ∀ σ, p₂ (φ σ) = p₁ σ) (hΦ : ∀ σ, p₂ (Φ σ) = p₁ σ)
    (hΔ : ∀ σ, p₁ σ = 1 → φ σ = Φ σ) (σ : E₁) : φ σ = Φ σ := by
  let ψ : p₁.ker →* p₂.ker :=
    { toFun n := ⟨φ (n : E₁), by rw [MonoidHom.mem_ker, hφ]; exact n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp) }
  have hψ : Function.Surjective ψ := fun m ↦ by
    obtain ⟨x, hx⟩ := hsurj (m : E₂)
    have hxk : x ∈ p₁.ker := by
      rw [MonoidHom.mem_ker, ← hφ, hx]
      exact m.2
    exact ⟨⟨x, hxk⟩, Subtype.ext hx⟩
  exact isExtLift_unique (ψ := ψ) hcen hψ
    (isExtLift_of_hom φ (MonoidHom.ext hφ) (fun _ ↦ rfl) σ)
    (isExtLift_of_hom Φ (MonoidHom.ext hΦ) (fun n ↦ (hΔ n n.2).symm) σ)

/-! ### Part (iii): agreement on `Δ` gives agreement on `Π` -/

section Upgrade

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
  [IsGalois k Ω] {C₁ C₂ : HypCurve k}

/-- **`f` induces `φ` on the geometric fundamental groups** (up to `Δ₂`-conjugation): for a path
`γ : fiber (ξ₁ ≫ f) ≅ fiber ξ₂` over the base, `φ σ = γ_* (π₁ᵉᵗ(f) σ)` for every `σ` in
`Δ₁ = ker(π₁ᵉᵗ(U₁, ξ₁) → G_k)` ([LocAn] Cor. 15.5, proof, l.4344–4346: "`θ^geom` … the morphism
`Δ_X → Δ_Y` induced by `θ`"). -/
def AgreesOnDelta (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (f : KIso C₁ C₂)
    (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)) : Prop :=
  ∃ γ : fiber (ξ₁.x ≫ f.1.hom) ≅ fiber ξ₂.x, IsPathOverBase (comp_over_of_kHom ξ₁ f.2) ξ₂.over γ ∧
    ∀ σ, fundamentalGroupMap C₁.toSpec ξ₁.over σ = 1 →
      φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap f.1.hom rfl σ)

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- The map induced by `f` through a path over the base lies over `G_k`. -/
lemma toSpec_conjAut_fundamentalGroupMap (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (f : KIso C₁ C₂)
    (γ : fiber (ξ₁.x ≫ f.1.hom) ≅ fiber ξ₂.x)
    (hγ : IsPathOverBase (comp_over_of_kHom ξ₁ f.2) ξ₂.over γ) (σ : π₁ᵉᵗ(ξ₁.x)) :
    fundamentalGroupMap C₂.toSpec ξ₂.over
        (autContinuousMulEquivOfIso γ (fundamentalGroupMap f.1.hom rfl σ)) =
      fundamentalGroupMap C₁.toSpec ξ₁.over σ := by
  have h3 : ξ₁.x ≫ f.1.hom ≫ C₂.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [f.2]
    exact ξ₁.over
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp f.1.hom C₂.toSpec rfl
    (comp_over_of_kHom ξ₁ f.2) h3) σ
  rw [fundamentalGroupMap_congr f.2 h3 ξ₁.over] at c1
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso C₂.toSpec (comp_over_of_kHom ξ₁ f.2)
    ξ₂.over γ, (isPathOverBase_iff _ _ γ).1 hγ, c1]
  change (Iso.refl _).conjAut _ = _
  rw [Iso.conjAut_apply]
  simp

/-- An isomorphism over `G_k` maps `Π_{U₁} → G_k` to `Π_{U₂} → G_k`. -/
lemma toSpec_apply_of_isOverGk {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂}
    {φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)} (hφ : IsOverGk ξ₁ ξ₂ φ) (σ) :
    fundamentalGroupMap C₂.toSpec ξ₂.over (φ σ) = fundamentalGroupMap C₁.toSpec ξ₁.over σ := by
  have := DFunLike.congr_fun hφ σ
  simp only [toGaloisGroup, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, ContinuousMonoidHom.coe_toMonoidHom] at this
  exact (mulEquivAutFiber k Ω).symm.injective this

/-- **Part (iii) of [LocAn] Cor. 15.5** (l.4363–4366, "the morphism induced by `φ_K` on fundamental
groups coincides with `θ` (up to composition with an inner automorphism defined by an element of
`Δ_Y`)"): if `f` induces `φ` on `Δ₁` through a path over the base, `φ` lies over `G_k` and `Δ₂` is
centre-free, then `f` induces `φ` on all of `Π_{U₁}`. Both `φ` and `γ_* ∘ π₁ᵉᵗ(f)` are maps of
extensions over `G_k` that agree on `Δ₁`; such maps are unique since `Z(Δ₂) = 1`
(`CurvesJacobian.Cusp.isExtLift_unique`). -/
theorem inducedBy_of_agreesOnDelta {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} {f : KIso C₁ C₂}
    {φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)} (hφ : IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)))
    (H : AgreesOnDelta ξ₁ ξ₂ f φ)
    (hcen : Subgroup.center (fundamentalGroupMap C₂.toSpec ξ₂.over).toMonoidHom.ker = ⊥) :
    InducedBy ξ₁ ξ₂ f φ := by
  obtain ⟨γ, hγ, hΔ⟩ := H
  let p₁ := (fundamentalGroupMap C₁.toSpec ξ₁.over).toMonoidHom
  let p₂ := (fundamentalGroupMap C₂.toSpec ξ₂.over).toMonoidHom
  let φ₀ : π₁ᵉᵗ(ξ₁.x) →* π₁ᵉᵗ(ξ₂.x) := (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)).toMonoidHom
  let Φ : π₁ᵉᵗ(ξ₁.x) →* π₁ᵉᵗ(ξ₂.x) :=
    (autContinuousMulEquivOfIso γ).toMulEquiv.toMonoidHom.comp
      (fundamentalGroupMap f.1.hom rfl).toMonoidHom
  have hφ' : ∀ σ, p₂ (φ₀ σ) = p₁ σ := toSpec_apply_of_isOverGk hφ
  have hΦ' : ∀ σ, p₂ (Φ σ) = p₁ σ := toSpec_conjAut_fundamentalGroupMap ξ₁ ξ₂ f γ hγ
  have hΔ' : ∀ σ, p₁ σ = 1 → φ₀ σ = Φ σ := hΔ
  have key := eq_of_isOver_of_eqOn_ker p₁ p₂ hcen φ₀ Φ φ.surjective hφ' hΦ' hΔ'
  exact ⟨γ, hγ, key⟩

end Upgrade

/-! ### Parts (i) and (ii): the remaining debts -/

section Debt

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Agreement on `Δ` after base change**: an `L`-isomorphism `f' : U₁,L ≅ U₂,L` and a path `γ'`
over the base at the points `bcExtPt L Ω' ξᵢ` whose induced map on `Δ₁,L` agrees with `φ` after
the projections `Π_{Uᵢ,L} → Π_{Uᵢ}` (`bcExtPiU`): `pr₂(γ'_* π₁ᵉᵗ(f') σ) = φ (pr₁ σ)` for
`σ ∈ Δ₁,L = ker(π₁ᵉᵗ(U₁,L) → G_L)`. This is "`φ_L : X_L → Y_L` whose induced morphism on
geometric fundamental groups coincides with that defined by `θ`" ([LocAn] Cor. 15.5, proof,
l.4346–4348). -/
def AgreesOnDeltaBc {K : Type u} [Field K] [CharZero K] (L : Type u) [Field L] [Algebra K L]
    {Ω : Type u} (Ω' : Type u) [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra L Ω'] [Algebra Ω Ω']
    [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    {C₁ C₂ : HypCurve K} (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂)
    (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x)) : Prop :=
  ∃ f' : KIso (C₁.bcExt L) (C₂.bcExt L),
    ∃ γ' : fiber ((bcExtPt L Ω' gp₁).x ≫ f'.1.hom) ≅ fiber (bcExtPt L Ω' gp₂).x,
      IsPathOverBase (comp_over_of_kHom (bcExtPt L Ω' gp₁) f'.2) (bcExtPt L Ω' gp₂).over γ' ∧
      ∀ σ, fundamentalGroupMap (C₁.bcExt L).toSpec (bcExtPt L Ω' gp₁).over σ = 1 →
        bcExtPiU L C₂ gp₂ (autContinuousMulEquivOfIso γ' (fundamentalGroupMap f'.1.hom rfl σ)) =
          φ (bcExtPiU L C₁ gp₁ σ)

/-- **The hypothesis of `DescentIso` gives agreement on `Δ` over `L`**: if an `L`-isomorphism
induces `φ_L = bcExtPhi φ`, it agrees with `φ` on `Δ₁,L` (`bcExtPiU_bcExtPhi`). -/
theorem agreesOnDeltaBc_of_inducedBy {K : Type u} [Field K] [NumberField K] (L : Type u) [Field L]
    [Algebra K L] [CharZero L] {Ω Ω' : Type u} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra L Ω']
    [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'] [IsAlgClosed Ω]
    [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic L Ω']
    {C₁ C₂ : HypCurve K} (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) {gp₁ : GeomPt Ω C₁} {gp₂ : GeomPt Ω C₂}
    (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
    (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x)))
    (f : KIso (C₁.bcExt L) (C₂.bcExt L))
    (H : InducedBy (bcExtPt L Ω' gp₁) (bcExtPt L Ω' gp₂) f (bcExtPhi L hc₁ hc₂ φ hφ)) :
    AgreesOnDeltaBc L Ω' gp₁ gp₂ φ := by
  obtain ⟨γ, hγ, h⟩ := H
  refine ⟨f, γ, hγ, fun σ _ ↦ ?_⟩
  rw [show autContinuousMulEquivOfIso γ (fundamentalGroupMap f.1.hom rfl σ) =
    bcExtPhi L hc₁ hc₂ φ hφ σ from (h σ).symm]
  exact bcExtPiU_bcExtPhi L hc₁ hc₂ φ hφ σ

/-- **Debt (i), no moduli** ([LocAn] Cor. 15.5, proof, l.4350–4354: "since morphisms between
hyperbolic curves … clearly have no moduli (cf. the fact that the scheme `H_M` … was finite and
unramified over `M`), it follows that `φ_L` descends to a finite Galois extension `K'` of `K`"):
an `L`-isomorphism agreeing with `φ` on `Δ` (over `Ω' ⊇ Ω`) gives a `K'`-isomorphism agreeing with
`φ` on `Δ` (over `Ω`) for a finite Galois extension `K ⊆ K' ⊆ Ω`. The proof needs the finiteness
of `Isom(U₁,Ω, U₂,Ω)` (the isomorphism scheme is finite unramified over `K`), its invariance under
`Ω ⊆ Ω'`, and the invariance of `Δ` under `Ω ⊆ Ω'`. -/
def DescentNoModuli : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra K L]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Ω' : Type u) [Field Ω'] [Algebra L Ω'] [IsAlgClosure L Ω'] [Algebra Ω Ω'] [Algebra K Ω']
    [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'],
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω')
    ∀ (C₁ C₂ : HypCurve K) (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂)
      (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x)),
      AgreesOnDeltaBc L Ω' gp₁ gp₂ φ →
      ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ IsGalois K K' ∧
        AgreesOnDeltaBc K' Ω gp₁ gp₂ φ

/-- **Debt (ii), Galois descent** ([LocAn] Cor. 15.5, proof, l.4354–4363: "conjugating `φ_{K'}` by
`σ` gives a morphism `φ^σ_{K'}` whose induced morphism on geometric fundamental groups is the
result of conjugating `θ^geom` by `σ`. On the other hand, `θ^geom` arises from `θ` which lies over
`Γ_K`, so `θ^geom` is fixed (up to … an inner automorphism defined by an element of `Δ_Y`) by
conjugation by `σ`. Thus, `φ_{K'}` and `φ^σ_{K'}` induce the same morphism on geometric fundamental
groups, hence coincide …. This shows that `φ_{K'}` descends to a morphism `φ_K`"): for `φ` over
`G_K` and a `K'`-isomorphism agreeing with `φ` on `Δ` (`K'/K` finite Galois inside `Ω`), there is
a `K`-isomorphism agreeing with `φ` on `Δ`. The proof needs Galois descent of morphisms of
`K`-schemes along `K'/K` and the geometric uniqueness (an isomorphism of `U₁,Ω, U₂,Ω` is determined
by its action on `Δ` up to `Δ₂`-conjugation, the uniqueness preceding [LocAn] Cor. 15.3). -/
def GaloisDescentGeom : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω],
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    ∀ (C₁ C₂ : HypCurve K) (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂)
      (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x)),
      IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x)) →
      ∀ (K' : IntermediateField K Ω) [FiniteDimensional K K'] [IsGalois K K'],
      AgreesOnDeltaBc K' Ω gp₁ gp₂ φ → ∃ f : KIso C₁ C₂, AgreesOnDelta gp₁ gp₂ f φ

/-- **Parts (i) + (ii) of the descent**: the statement of `DescentIso` with the conclusion
weakened to agreement on the geometric fundamental groups `Δ₁` (`AgreesOnDelta`). -/
def DescentGeom : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra K L]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Ω' : Type u) [Field Ω'] [Algebra L Ω'] [IsAlgClosure L Ω'] [Algebra Ω Ω'] [Algebra K Ω']
    [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'],
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω')
    haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    ∀ (C₁ C₂ : HypCurve K) (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
      (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂)
      (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
      (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))),
      (∃ f : KIso (C₁.bcExt L) (C₂.bcExt L),
        InducedBy (bcExtPt L Ω' gp₁) (bcExtPt L Ω' gp₂) f (bcExtPhi L hc₁ hc₂ φ hφ)) →
      ∃ f : KIso C₁ C₂, AgreesOnDelta gp₁ gp₂ f φ

/-- **(i) + (ii) give `DescentGeom`.** -/
theorem descentGeom_of_parts (h₁ : DescentNoModuli.{u}) (h₂ : GaloisDescentGeom.{u}) :
    DescentGeom.{u} := by
  intro K _ _ L _ _ Ω _ _ _ Ω' _ _ _ _ _ _ _
  haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
  haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω')
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro C₁ C₂ hc₁ hc₂ gp₁ gp₂ φ hφ ⟨fL, HL⟩
  obtain ⟨K', hfin, hgal, hK'⟩ := h₁ K L Ω Ω' C₁ C₂ gp₁ gp₂ φ
    (agreesOnDeltaBc_of_inducedBy L hc₁ hc₂ φ hφ fL HL)
  exact h₂ K Ω C₁ C₂ gp₁ gp₂ φ hφ K' hK'

/-- **Part (iii) closes the descent**: `DescentGeom` gives the debt `DescentIso`; the
centre-freeness of `Δ₂` is `center_ker_toSpec_eq_bot`. -/
theorem descentIso_of_descentGeom (hG : DescentGeom.{u}) : DescentIso.{u} := by
  intro K _ _ L _ _ Ω _ _ _ Ω' _ _ _ _ _ _ _
  haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
  haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω')
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro C₁ C₂ hc₁ hc₂ gp₁ gp₂ φ hφ hL
  obtain ⟨f, hf⟩ := hG K L Ω Ω' C₁ C₂ hc₁ hc₂ gp₁ gp₂ φ hφ hL
  exact ⟨f, inducedBy_of_agreesOnDelta hφ hf (center_ker_toSpec_eq_bot C₂ hc₂ gp₂)⟩

/-- **The descent debt from its parts (i) and (ii)**. -/
theorem descentIso_of_parts (h₁ : DescentNoModuli.{u}) (h₂ : GaloisDescentGeom.{u}) :
    DescentIso.{u} :=
  descentIso_of_descentGeom (descentGeom_of_parts h₁ h₂)

end Debt

end CurvesJacobian.LocAn
