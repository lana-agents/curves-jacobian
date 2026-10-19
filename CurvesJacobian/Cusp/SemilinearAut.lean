/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FieldTwistDGC
import CurvesJacobian.Scheme.ConstantField

/-!
# `K`-endomorphisms of `Γ(U)` are `M`-semilinear

Let `K → M` be an algebraic field extension and `C` a hyperbolic curve over `M`, with affine
open `U = C.U` of the geometrically integral curve `X̄ = C.Xbar`.

* `CurvesJacobian.Cusp.mem_range_algebraMap_sections_of_isAlgebraic`: `M` is algebraically
  closed in `Γ(X̄, U)`. A section algebraic over `M` has algebraic germ in the function field
  `K(X̄)`, which lies in `M` (`CurvesJacobian.mem_range_algebraMap_of_isAlgebraic`, geometric
  integrality), and the germ map `Γ(X̄, U) → K(X̄)` is injective.
* `CurvesJacobian.Cusp.exists_algEquiv_of_ringHom_sections`: a ring endomorphism `g` of
  `Γ(X̄, U)` fixing `K` maps `M` into `M` through a `K`-automorphism `β` of `M`: `g (m) = β m`.
  Indeed `g m` satisfies the minimal polynomial of `m` over `K`, so it is algebraic over `M`,
  hence in `M`; the induced `K`-algebra map `M → M` is bijective since `M / K` is algebraic.
* `CurvesJacobian.Cusp.exists_algEquiv_of_comp_sK`: the scheme form. An automorphism `G` of
  `Spec Γ(U)` over `Spec K` lies over `Spec β : Spec M ⟶ Spec M` for a `K`-automorphism `β`.
-/

open CategoryTheory AlgebraicGeometry Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Semilinear

variable {M : Type u} [Field M] (C : HypCurve M)

/-- `Γ(X̄, U)` is a domain. -/
lemma isDomain_sections_hypCurve : IsDomain Γ(C.Xbar, C.U) :=
  haveI := IsCurveOver.isIntegral M C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  inferInstance

/-- **`M` is algebraically closed in `Γ(X̄, U)`**: every section algebraic over `M` is a
constant. -/
theorem mem_range_algebraMap_sections_of_isAlgebraic {s : Γ(C.Xbar, C.U)}
    (hs : IsAlgebraic M s) : s ∈ (algebraMap M Γ(C.Xbar, C.U)).range := by
  haveI := IsCurveOver.isIntegral M C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  let γ : Γ(C.Xbar, C.U) →ₐ[M] C.Xbar.functionField :=
    { (C.Xbar.germToFunctionField C.U).hom with
      commutes' := fun c ↦ (algebraMap_functionField_eq_germ M C.Xbar C.U c).symm }
  have hγ : Function.Injective γ := C.Xbar.germToFunctionField_injective C.U
  obtain ⟨m, hm⟩ := mem_range_algebraMap_of_isAlgebraic M C.Xbar (hs.algHom γ)
  refine ⟨m, hγ ?_⟩
  rw [AlgHom.commutes]
  exact hm

variable {K : Type u} [Field K] [Algebra K M]

/-- The image of a constant under a ring endomorphism of `Γ(X̄, U)` fixing `K` is a constant,
provided `M / K` is algebraic. -/
lemma exists_eq_algebraMap_of_ringHom_sections [Algebra.IsAlgebraic K M]
    (g : Γ(C.Xbar, C.U) →+* Γ(C.Xbar, C.U))
    (hg : ∀ k : K, g (algebraMap M _ (algebraMap K M k)) = algebraMap M _ (algebraMap K M k))
    (m : M) : ∃ m' : M, g (algebraMap M _ m) = algebraMap M _ m' := by
  obtain ⟨p, hp0, hpm⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) m
  let ψ : K →+* Γ(C.Xbar, C.U) := (algebraMap M Γ(C.Xbar, C.U)).comp (algebraMap K M)
  have hψ : g.comp ψ = ψ := RingHom.ext hg
  have h0 : p.eval₂ ψ (algebraMap M Γ(C.Xbar, C.U) m) = 0 := by
    have h := Polynomial.hom_eval₂ p (algebraMap K M) (algebraMap M Γ(C.Xbar, C.U)) m
    rw [← Polynomial.aeval_def, hpm, map_zero] at h
    exact h.symm
  have halg : IsAlgebraic M (g (algebraMap M _ m)) := by
    refine ⟨p.map (algebraMap K M),
      (Polynomial.map_ne_zero_iff (algebraMap K M).injective).2 hp0, ?_⟩
    have h := Polynomial.hom_eval₂ p ψ g (algebraMap M Γ(C.Xbar, C.U) m)
    rw [h0, map_zero, hψ] at h
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact h.symm
  obtain ⟨m', hm'⟩ := mem_range_algebraMap_sections_of_isAlgebraic C halg
  exact ⟨m', hm'.symm⟩

/-- **A ring endomorphism of `Γ(X̄, U)` fixing `K` is `M`-semilinear**: it acts on the
constants `M` through a `K`-automorphism `β` of `M`. -/
theorem exists_algEquiv_of_ringHom_sections [Algebra.IsAlgebraic K M]
    (g : Γ(C.Xbar, C.U) →+* Γ(C.Xbar, C.U))
    (hg : ∀ k : K, g (algebraMap M _ (algebraMap K M k)) = algebraMap M _ (algebraMap K M k)) :
    ∃ β : M ≃ₐ[K] M, ∀ m : M, g (algebraMap M _ m) = algebraMap M _ (β m) := by
  haveI := isDomain_sections_hypCurve C
  choose b hb using exists_eq_algebraMap_of_ringHom_sections C g hg
  have hi : Function.Injective (algebraMap M Γ(C.Xbar, C.U)) :=
    (algebraMap M Γ(C.Xbar, C.U)).injective
  let βh : M →ₐ[K] M :=
    { toFun := b
      map_one' := hi (by rw [← hb, map_one, map_one])
      map_mul' := fun x y ↦ hi (by rw [← hb, map_mul, map_mul, map_mul, hb, hb])
      map_zero' := hi (by rw [← hb, map_zero, map_zero])
      map_add' := fun x y ↦ hi (by rw [← hb, map_add, map_add, map_add, hb, hb])
      commutes' := fun k ↦ hi (by rw [← hb, hg]) }
  exact ⟨AlgEquiv.ofBijective βh (Algebra.IsAlgebraic.algHom_bijective βh), hb⟩

/-- **Scheme form**: an automorphism `G` of `Spec Γ(U)` lying over `Spec K` lies over
`Spec β : Spec M ⟶ Spec M` for a `K`-automorphism `β` of `M`. -/
theorem exists_algEquiv_of_comp_sK [Algebra.IsAlgebraic K M]
    (G : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U))
    (hG : G.hom ≫ sKU C ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) =
      sKU C ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) :
    ∃ β : M ≃ₐ[K] M, G.hom ≫ sKU C = sKU C ≫ specRingEquiv₂ β.toRingEquiv := by
  let φ : Γ(C.Xbar, C.U) ⟶ Γ(C.Xbar, C.U) := Spec.preimage G.hom
  have h1 : G.hom = Spec.map φ := (Spec.map_preimage G.hom).symm
  rw [h1] at hG
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap K M) ≫
      CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U)) ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap K M) ≫
        CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) := by
    simpa only [Spec.map_comp, Category.assoc] using hG
  have h3 := Spec.map_injective h2
  have hg : ∀ k : K, φ.hom (algebraMap M _ (algebraMap K M k)) =
      algebraMap M _ (algebraMap K M k) := fun k ↦ congrArg (fun f ↦ f.hom k) h3
  obtain ⟨β, hβ⟩ := exists_algEquiv_of_ringHom_sections C φ.hom hg
  refine ⟨β, ?_⟩
  rw [h1]
  have h4 : CommRingCat.ofHom (β.toRingEquiv : M →+* M) ≫
      CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U)) =
      CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U)) ≫ φ :=
    CommRingCat.hom_ext (RingHom.ext fun m ↦ (hβ m).symm)
  change Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) ≫
      Spec.map (CommRingCat.ofHom (β.toRingEquiv : M →+* M))
  rw [← Spec.map_comp, ← Spec.map_comp, h4]

end Semilinear

end CurvesJacobian.Cusp
