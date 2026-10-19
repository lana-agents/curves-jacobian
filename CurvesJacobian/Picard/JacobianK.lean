/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianDescentField
import CurvesJacobian.Descent.GaloisInvariant

/-!
# The Jacobian `J_k` as a commutative group scheme over `k` (JAC R4′, R5′)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `Ω ⊇ k` an algebraic
closure, `L = jacFieldD C σ hσ Ω` and `J_k = jacK C σ hσ Ω` the Galois descent of `J_L`.

* **`CurvesJacobian.jacKRepresentableByInv`**: `Hom_k(T, J_k) ≃ Pic⁰_{C/k,σ}(T ×_k L)^{Gal(L/k)}`,
  naturally in `T`;
* instances **`GrpObj (jacK C σ hσ Ω)`**, **`IsCommMonObj (jacK C σ hσ Ω)`**: `J_k` is a commutative
  group scheme over `k`, with the group structure induced from `Pic⁰`;
* **`CurvesJacobian.jacKBaseChangeIso`**: `J_k ×_k L ≅ J_L` over `L` (R5′, first half);
* **`CurvesJacobian.jacKPointsEquiv`**: `Hom_k(Spec K, J_k) ≃ J(K) = Pic⁰_{C/k,σ}(K)` for every
  field `K ⊇ k` (R6), natural in `K` (`jacKPointsEquiv_symm_picRes`). For `K ⊇ L` this is the
  splitting `K ×_k L = ∐_{Gal(L/k)} Spec K` (`bijective_invNu`); in general one passes to a
  separable closure `K^s ⊇ L` and uses `J(K) ≅ J(K^s)^{Gal(K^s/K)}` (`exists_jacPoints_picRes_eq`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi GaloisDescent

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

/-- **`J_k` represents the Galois invariants of `Pic⁰`**:
`Hom_k(T, J_k) ≃ Pic⁰_{C/k,σ}(T ×_k L)^{Gal(L/k)}`. -/
def jacKRepresentableByInv :
    (invFunctor (L := jacFieldD C σ hσ Ω) (picZero C σ hσ (curveToP1 k C)) ⋙
      forget AddCommGrpCat).RepresentableBy (jacK C σ hσ Ω) :=
  descRepresentableByInv (picZero C σ hσ (curveToP1 k C)) (jacDRepresentableBy C σ hσ Ω)
    (jacD_hcov C σ hσ Ω)

/-- **The Jacobian `J_k` is a group scheme over `k`.** -/
instance : GrpObj (jacK C σ hσ Ω) :=
  inferInstanceAs (GrpObj (descScheme (twistGalAction (picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat) (jacDRepresentableBy C σ hσ Ω)) (jacD_hcov C σ hσ Ω)))

/-- **The Jacobian `J_k` is commutative.** -/
instance : IsCommMonObj (jacK C σ hσ Ω) :=
  inferInstanceAs (IsCommMonObj (descScheme (twistGalAction (picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat) (jacDRepresentableBy C σ hσ Ω)) (jacD_hcov C σ hσ Ω)))

/-- **`J_k ×_k L ≅ J_L`** (the counit of the Galois descent, R5′). -/
def jacKBaseChangeIso :
    pullback (jacK C σ hσ Ω).hom (sL k (jacFieldD C σ hσ Ω)) ≅ (jacD C σ hσ Ω).left :=
  haveI := isIso_descCounit (jacDAction C σ hσ Ω) (jacD_hcov C σ hσ Ω)
  asIso (descCounit (jacDAction C σ hσ Ω) (jacD_hcov C σ hσ Ω)).1

/-- `J_k ×_k L ≅ J_L` lies over `Spec L`. -/
lemma jacKBaseChangeIso_hom_comp :
    (jacKBaseChangeIso C σ hσ Ω).hom ≫ (jacD C σ hσ Ω).hom =
      pullback.snd (jacK C σ hσ Ω).hom (sL k (jacFieldD C σ hσ Ω)) :=
  (descCounit (jacDAction C σ hσ Ω) (jacD_hcov C σ hσ Ω)).2.1

section Points

/-- **The morphism to `J_k` of a class of `Pic⁰`**: `x ↦ (x|_{T_L} ∈ Pic⁰(T_L)^G)`. -/
def jacKOfClass {T : Over (Spec (CommRingCat.of k))}
    (x : (picZero C σ hσ (curveToP1 k C)).obj (op T)) : T ⟶ jacK C σ hσ Ω :=
  (jacKRepresentableByInv C σ hσ Ω).homEquiv.symm
    ((invNu (L := jacFieldD C σ hσ Ω) (picZero C σ hσ (curveToP1 k C))).app (op T) x)

/-- `jacKOfClass` is natural. -/
lemma jacKOfClass_naturality {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (x : (picZero C σ hσ (curveToP1 k C)).obj (op T)) :
    jacKOfClass C σ hσ Ω ((picZero C σ hσ (curveToP1 k C)).map f.op x) =
      f ≫ jacKOfClass C σ hσ Ω x := by
  apply (jacKRepresentableByInv C σ hσ Ω).homEquiv.injective
  rw [Functor.RepresentableBy.homEquiv_comp, jacKOfClass, jacKOfClass, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    ((invNu (L := jacFieldD C σ hσ Ω) (picZero C σ hσ (curveToP1 k C))).naturality f.op) x

/-- **`jacKOfClass` is bijective on `L`-schemes.** -/
theorem bijective_jacKOfClass_of_L {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of
    (jacFieldD C σ hσ Ω))) (t : T ⟶ Spec (CommRingCat.of k)) (hs : s ≫ sL k _ = t) :
    Function.Bijective (jacKOfClass C σ hσ Ω (T := Over.mk t)) := by
  subst hs
  exact (jacKRepresentableByInv C σ hσ Ω).homEquiv.symm.bijective.comp
    (bijective_invNu (picZero C σ hσ (curveToP1 k C)) (jacDRepresentableBy C σ hσ Ω) s)

variable (K : Type u) [Field K] [Algebra k K]

/-- **`J_k(K) = J(K)`** (R6): `jacKOfClass` is bijective on `K`-points for every field `K ⊇ k`. -/
theorem bijective_jacKOfClass_field :
    Function.Bijective (jacKOfClass C σ hσ Ω (T := Over.mk (specAlgebraMap (k₀ := k) K))) := by
  set L := jacFieldD C σ hσ Ω
  let Ω' := SeparableClosure K
  letI : Algebra k Ω' := ((algebraMap K Ω').comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Ω' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.IsSeparable k L := IsGalois.to_isSeparable
  let ε : L →ₐ[k] Ω' := IsSepClosed.lift
  let s : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom ε.toRingHom)
  have hs : s ≫ sL k L = specAlgebraMap (k₀ := k) Ω' := by
    rw [specAlgebraMap, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (ε.commutes r)
  let h := specMapAlg K Ω'
  have hh : h ≫ specAlgebraMap (k₀ := k) K = specAlgebraMap (k₀ := k) Ω' :=
    specMapAlg_comp_specAlgebraMap K Ω'
  have hΩ := bijective_jacKOfClass_of_L C σ hσ Ω s _ hs
  let hO : Over.mk (specAlgebraMap (k₀ := k) Ω') ⟶ Over.mk (specAlgebraMap (k₀ := k) K) :=
    Over.homMk h hh
  constructor
  · intro x x' hxx
    have e := (jacKOfClass_naturality C σ hσ Ω hO x).trans
      ((congrArg (hO ≫ ·) hxx).trans (jacKOfClass_naturality C σ hσ Ω hO x').symm)
    have e' := hΩ.1 e
    apply Subtype.ext
    exact picRes_injective C σ hσ K Ω' (congrArg Subtype.val e')
  · intro a
    obtain ⟨z, hz⟩ := hΩ.2 (hO ≫ a)
    have hinv : z.1 ∈ picInv C σ hσ K Ω' := fun τ ↦ by
      let hτ : Over.mk (specAlgebraMap (k₀ := k) Ω') ⟶ Over.mk (specAlgebraMap (k₀ := k) Ω') :=
        Over.homMk (specAut τ) (specAut_comp_specAlgebraMap τ)
      have e : jacKOfClass C σ hσ Ω ((picZero C σ hσ (curveToP1 k C)).map hτ.op z) =
          jacKOfClass C σ hσ Ω z := by
        rw [jacKOfClass_naturality, hz, ← Category.assoc]
        congr 1
        exact Over.OverMorphism.ext (specAut_comp_specMapAlg τ)
      exact congrArg Subtype.val (hΩ.1 e)
    obtain ⟨x, hx₀, hx⟩ := exists_jacPoints_picRes_eq C σ hσ K Ω' z.1 z.2 hinv
    refine ⟨⟨x, hx₀⟩, ?_⟩
    have e : hO ≫ jacKOfClass C σ hσ Ω ⟨x, hx₀⟩ = hO ≫ a := by
      rw [← jacKOfClass_naturality, ← hz]
      congr 1
      exact Subtype.ext hx
    apply Over.OverMorphism.ext
    exact eq_of_specMapAlg_comp_eq (K := K) (Ω := Ω') (congrArg CommaMorphism.left e)

/-- **The `K`-points of `J_k` are `J(K) = Pic⁰_{C/k,σ}(K)`** (R6). -/
def jacKPointsEquiv :
    (Over.mk (specAlgebraMap (k₀ := k) K) ⟶ jacK C σ hσ Ω) ≃ jacPoints C σ hσ K :=
  (Equiv.ofBijective (jacKOfClass C σ hσ Ω (T := Over.mk (specAlgebraMap (k₀ := k) K)))
    (bijective_jacKOfClass_field C σ hσ Ω K)).symm

lemma jacKPointsEquiv_symm_apply (x : jacPoints C σ hσ K) :
    (jacKPointsEquiv C σ hσ Ω K).symm x =
      jacKOfClass C σ hσ Ω (T := Over.mk (specAlgebraMap (k₀ := k) K)) x := rfl

/-- **Naturality of `J_k(K) = J(K)` in `K`**: restriction of points along `K ⊆ K'`. -/
lemma jacKPointsEquiv_symm_picRes (K' : Type u) [Field K'] [Algebra k K'] [Algebra K K']
    [IsScalarTower k K K'] (x : jacPoints C σ hσ K) :
    (jacKPointsEquiv C σ hσ Ω K').symm
      ⟨picRes C σ hσ K K' x, picRes_mem_jacPoints C σ hσ K K' x.2⟩ =
      Over.homMk (specMapAlg K K') (specMapAlg_comp_specAlgebraMap K K') ≫
        (jacKPointsEquiv C σ hσ Ω K).symm x := by
  rw [jacKPointsEquiv_symm_apply, jacKPointsEquiv_symm_apply, ← jacKOfClass_naturality]
  congr 1

end Points

end CurvesJacobian
