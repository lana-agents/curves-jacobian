/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCusps

/-!
# The kernel of the arithmetic Galois action: `Π_U ≅ Gal(M / K(X̄))`

For a hyperbolic curve `C = (X̄, U)` over a number field `K` with a cusp (`U` affine) and
`Ω = K̄`, `arithAction : Gal(K(X̄_Ω)^alg / K(X̄)) →* Π_U` (`NonRationalFill`) is the Galois action
at the generic point followed by a change of base point; it is surjective
(`arithAction_surjective`, `CoverCusps`). Here we identify `Π_U` with the Galois group of the
maximal extension `M` of `L₀ = K(X̄)` unramified over `U` (MR7 plan, "S2 route": the uniqueness
argument works with `M` and `Δ = Gal(M / K̄(X̄))`):

* `AlgebraicGeometry.FiniteEtale.galoisAction_eq_one_apply` (generic): if `g ∈ Gal(Ω / F)` acts
  trivially on `π₁ᵉᵗ(X, η)` through a field-valued point `Spec F ⟶ X`, then `g` fixes `φ(B)` for
  every point `φ : B → Ω` over `η` of a finite étale `Spec B ⟶ X`;
* `continuous_arithAction`, `arithKernel` (closed: `isClosed_arithKernel`, normal);
* `arithKernel_apply_eq_of_finiteEtale`: the kernel fixes the points over `arithPt` of all finite
  étale `Γ(U)`-algebras, in particular **`arithKernel_fixes_Omega`**: it fixes `Ω`;
* `arithMaxUnram = M`, the fixed field of `arithKernel`, with
  `fixingSubgroup_arithMaxUnram`, `IsGalois L₀ M`, `algebraMap_mem_arithMaxUnram` (`Ω ⊆ M`),
  `mem_arithMaxUnram_of_finiteEtale`, and **`arithGalEquiv : Gal(M / L₀) ≃ₜ* Π_U`** with
  `arithGalEquiv (g|_M) = arithAction g` (`arithGalEquiv_restrictNormalHom`).

## Proof

1. (`galoisAction_eq_one_apply`) `φ` is a point `x` of the fibre of the finite étale `X`-scheme
   `Spec B` at `η`, and `g` acts on it by precomposition with `Spec g`
   (`galoisAction_hom_app_left`). If the action is trivial, `Spec φ = Spec g ≫ Spec φ`, so
   `φ = g ∘ φ` (`Spec.map_injective`).
2. `arithAction` is `galoisAction` (continuous) followed by the homeomorphism
   `autContinuousMulEquivOfIso`; in particular its kernel is the kernel of `galoisAction`.
3. (`Ω` is fixed) For `c ∈ Ω`, `K⟮c⟯` is finite étale over `K` (characteristic zero), hence
   `B = Γ(U) ⊗_K K⟮c⟯` is finite étale over `Γ(U)`, and `a ⊗ y ↦ secEmb a · y` is a point of `B`
   over `arithPt`; apply 1 to `1 ⊗ c`.
4. (`M`) `arithKernel` is a closed normal subgroup, so by infinite Galois theory
   (`InfiniteGalois.fixingSubgroup_fixedField`, `normal_iff_isGalois`, `normalAutEquivQuotient`)
   `Gal(M / L₀) ≅ Gal(K(X̄_Ω)^alg / L₀) ⧸ arithKernel ≅ Π_U`. This is continuous since restriction
   to `M` is a quotient map (continuous surjection between compact Hausdorff groups), and a
   homeomorphism since `Gal(M / L₀)` is compact and `Π_U` is Hausdorff.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open scoped TensorProduct IntermediateField

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (F : Type u) [Field F]
  [Algebra F Ω] [IsGalois F Ω]

/-- **An element acting trivially through the Galois action fixes all field-valued points of
finite étale covers**: if `galoisAction F j h g = 1`, then `g` fixes the image of every ring map
`φ : B → Ω` lying over `η`, for `Spec B ⟶ X` finite étale. -/
lemma galoisAction_eq_one_apply (j : Spec (.of F) ⟶ X) {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) {g : Ω ≃ₐ[F] Ω}
    (hg : galoisAction F j h g = 1) {B : Type u} [CommRing B] (f : Spec (.of B) ⟶ X)
    [IsFiniteEtale f] (φ : B →+* Ω) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ f = η) (b : B) :
    g (φ b) = φ b := by
  let A : FiniteEtale X := FiniteEtale.mk f
  let x : (fiber η).obj A := (fiberObjEquivHom η A).symm (Over.homMk (Spec.map
    (CommRingCat.ofHom φ)) hφ)
  have key := galoisAction_hom_app_left F j h g A x
  have h1 : (1 : π₁ᵉᵗ(η)).hom.app A x = x := rfl
  rw [hg, h1, Equiv.apply_symm_apply] at key
  change Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom φ) at key
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at key
  have := congrArg (fun ψ ↦ ψ.hom b) (Spec.map_injective key)
  exact this.symm

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

open AlgebraicGeometry.FiniteEtale

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The arithmetic Galois action is continuous** (Krull topology on the source). -/
theorem continuous_arithAction : Continuous (arithAction Ω C hc) :=
  (autContinuousMulEquivOfIso (arithFiberIso Ω C hc)).continuous.comp
    (continuous_galoisAction _ _ _)

/-- **The kernel of the arithmetic Galois action** `Gal(K(X̄_Ω)^alg / K(X̄)) → Π_U`. -/
abbrev arithKernel :
    Subgroup (FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :=
  (arithAction Ω C hc).ker

theorem isClosed_arithKernel : IsClosed (arithKernel Ω C hc :
    Set (FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C))) :=
  isClosed_singleton.preimage (continuous_arithAction Ω C hc)

/-- An element of the kernel acts trivially through `galoisAction` at the generic point. -/
lemma galoisAction_eq_one_of_mem_arithKernel {g} (hg : g ∈ arithKernel Ω C hc) :
    galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc) (specMap_algebraMap_arithGenPt Ω C hc) g
      = 1 :=
  (autContinuousMulEquivOfIso (arithFiberIso Ω C hc)).injective
    ((MonoidHom.mem_ker.mp hg).trans (map_one _).symm)

/-- **The kernel fixes all points of finite étale covers of `U`**: if `Spec B ⟶ Spec Γ(U)` is
finite étale and `φ : B → K(X̄_Ω)^alg` lies over `arithPt`, then every `g ∈ arithKernel` fixes
`φ(B)`. -/
theorem arithKernel_apply_eq_of_finiteEtale {g} (hg : g ∈ arithKernel Ω C hc) {B : Type u}
    [CommRing B] (f : Spec (.of B) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f]
    (φ : B →+* FFClosure (geomCurve Ω C))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ f = arithPt Ω C hc) (b : B) :
    g (φ b) = φ b :=
  galoisAction_eq_one_apply _ _ _ (galoisAction_eq_one_of_mem_arithKernel Ω C hc hg) f φ
    (hφ.trans (specMap_algebraMap_arithGenPt Ω C hc)) b

/-- **The kernel fixes the constants** `Ω ⊆ K(X̄_Ω)^alg`. -/
theorem arithKernel_fixes_Omega {g} (hg : g ∈ arithKernel Ω C hc) (c : Ω) :
    g (algebraMap Ω (FFClosure (geomCurve Ω C)) c) = algebraMap Ω _ c := by
  have hU := isAffineOpen_U C hc
  let L := K⟮c⟯
  have hci : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hci
  haveI : Algebra.Etale K L :=
    ⟨.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let B := Γ(C.Xbar, C.U) ⊗[K] L
  haveI : Algebra.FiniteEtale Γ(C.Xbar, C.U) B := ⟨⟩
  haveI : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap Γ(C.Xbar, C.U) B))) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    infer_instance
  letI : Algebra K (FFClosure (geomCurve Ω C)) :=
    ((algebraMap Ω (FFClosure (geomCurve Ω C))).comp (algebraMap K Ω)).toAlgebra
  let s : Γ(C.Xbar, C.U) →ₐ[K] FFClosure (geomCurve Ω C) :=
    { secEmb Ω C hU with commutes' := secEmb_algebraMap Ω C hU }
  let t : L →ₐ[K] FFClosure (geomCurve Ω C) :=
    { (algebraMap Ω (FFClosure (geomCurve Ω C))).comp L.val.toRingHom with
      commutes' := fun _ ↦ rfl }
  let φ : B →+* FFClosure (geomCurve Ω C) := (Algebra.TensorProduct.productMap s t).toRingHom
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C.Xbar, C.U) B)) = arithPt Ω C hc := by
    rw [arithPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a ↦ ?_
    change Algebra.TensorProduct.productMap s t (a ⊗ₜ 1) = secEmb Ω C hU a
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  let x : L := ⟨c, IntermediateField.mem_adjoin_simple_self K c⟩
  have e : φ (1 ⊗ₜ x) = algebraMap Ω (FFClosure (geomCurve Ω C)) c := by
    change Algebra.TensorProduct.productMap s t (1 ⊗ₜ x) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl
  rw [← e]
  exact arithKernel_apply_eq_of_finiteEtale Ω C hc hg _ φ hφ _

/-! ### The maximal extension of `K(X̄)` unramified over `U` -/

/-- `arithKernel` as a closed subgroup. -/
def arithKernelClosed :
    ClosedSubgroup (FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :=
  ⟨arithKernel Ω C hc, isClosed_arithKernel Ω C hc⟩

instance normal_arithKernelClosed : (arithKernelClosed Ω C hc).Normal :=
  MonoidHom.normal_ker _

/-- **The maximal extension `M` of `K(X̄)` unramified over `U`** (inside `K(X̄_Ω)^alg`): the
fixed field of `arithKernel`. -/
def arithMaxUnram : IntermediateField (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) :=
  IntermediateField.fixedField (arithKernel Ω C hc)

theorem fixingSubgroup_arithMaxUnram :
    (arithMaxUnram Ω C hc).fixingSubgroup = arithKernel Ω C hc :=
  InfiniteGalois.fixingSubgroup_fixedField (arithKernelClosed Ω C hc)

theorem mem_arithMaxUnram_iff (z : FFClosure (geomCurve Ω C)) :
    z ∈ arithMaxUnram Ω C hc ↔ ∀ g ∈ arithKernel Ω C hc, g z = z :=
  ⟨fun hz g hg ↦ hz ⟨g, hg⟩, fun hz g ↦ hz g.1 g.2⟩

instance isGalois_arithMaxUnram : IsGalois (arithFF Ω C hc) (arithMaxUnram Ω C hc) :=
  (InfiniteGalois.normal_iff_isGalois _).mp
    (by rw [fixingSubgroup_arithMaxUnram]; infer_instance)

/-- **`Ω ⊆ M`.** -/
theorem algebraMap_mem_arithMaxUnram (c : Ω) :
    algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ arithMaxUnram Ω C hc :=
  (mem_arithMaxUnram_iff Ω C hc _).2 fun _ hg ↦ arithKernel_fixes_Omega Ω C hc hg c

/-- **Points of finite étale covers of `U` are defined over `M`.** -/
theorem mem_arithMaxUnram_of_finiteEtale {B : Type u} [CommRing B]
    (f : Spec (.of B) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f]
    (φ : B →+* FFClosure (geomCurve Ω C))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ f = arithPt Ω C hc) (b : B) :
    φ b ∈ arithMaxUnram Ω C hc :=
  (mem_arithMaxUnram_iff Ω C hc _).2 fun _ hg ↦
    arithKernel_apply_eq_of_finiteEtale Ω C hc hg f φ hφ b

/-- `Gal(M / K(X̄)) ≃* Π_U` as abstract groups. -/
def arithGalMulEquiv :
    (arithMaxUnram Ω C hc ≃ₐ[arithFF Ω C hc] arithMaxUnram Ω C hc) ≃*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (InfiniteGalois.normalAutEquivQuotient (arithKernelClosed Ω C hc)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (arithAction_surjective Ω C hc))

lemma arithGalMulEquiv_restrictNormalHom
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    arithGalMulEquiv Ω C hc (AlgEquiv.restrictNormalHom (K₁ := FFClosure (geomCurve Ω C))
        (arithMaxUnram Ω C hc) g) =
      arithAction Ω C hc g := by
  change QuotientGroup.quotientKerEquivOfSurjective _ (arithAction_surjective Ω C hc)
    ((InfiniteGalois.normalAutEquivQuotient (arithKernelClosed Ω C hc)).symm
      (InfiniteGalois.normalAutEquivQuotient (arithKernelClosed Ω C hc) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem continuous_arithGalMulEquiv : Continuous (arithGalMulEquiv Ω C hc) := by
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (AlgEquiv.restrictNormalHom_surjective (F := arithFF Ω C hc)
      (K₁ := arithMaxUnram Ω C hc) (FFClosure (geomCurve Ω C)))
    (InfiniteGalois.restrictNormalHom_continuous (arithMaxUnram Ω C hc))
  refine hq.continuous_iff.mpr ?_
  convert continuous_arithAction Ω C hc using 1
  exact funext (arithGalMulEquiv_restrictNormalHom Ω C hc)

/-- **`Gal(M / K(X̄)) ≅ Π_U`** as topological groups, where `M` is the maximal extension of
`K(X̄)` unramified over `U` (`arithMaxUnram`). -/
def arithGalEquiv :
    (arithMaxUnram Ω C hc ≃ₐ[arithFF Ω C hc] arithMaxUnram Ω C hc) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) where
  toMulEquiv := arithGalMulEquiv Ω C hc
  continuous_toFun := continuous_arithGalMulEquiv Ω C hc
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2 (f := (arithGalMulEquiv Ω C hc).toEquiv)
      (continuous_arithGalMulEquiv Ω C hc)).symm.continuous

@[simp]
lemma arithGalEquiv_apply (σ : arithMaxUnram Ω C hc ≃ₐ[arithFF Ω C hc] arithMaxUnram Ω C hc) :
    arithGalEquiv Ω C hc σ = arithGalMulEquiv Ω C hc σ := rfl

/-- **`Gal(M / K(X̄)) ≅ Π_U` is induced by the arithmetic Galois action.** -/
lemma arithGalEquiv_restrictNormalHom
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    arithGalEquiv Ω C hc (AlgEquiv.restrictNormalHom (K₁ := FFClosure (geomCurve Ω C))
        (arithMaxUnram Ω C hc) g) =
      arithAction Ω C hc g :=
  arithGalMulEquiv_restrictNormalHom Ω C hc g

end CurvesJacobian.Cusp
