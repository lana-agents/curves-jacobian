/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianKProps
import CurvesJacobian.Kummer.JacobianBridge

/-!
# Kummer-faithful fields ([AbsTopIII] Definition 1.5) and the Jacobian (MR5 "J1")

Mochizuki, *Topics in Absolute Anabelian Geometry III* ([AbsTopIII]), Definition 1.5
(`T3` l.1807–1836): a field `k` of characteristic zero is **Kummer-faithful** (resp. **torally
Kummer-faithful**) if for every finite extension `k_H ⊆ k̄` of `k` and every semi-abelian variety
(resp. every torus) `A` over `k_H`, `⋂_{N ≥ 1} N · A(k_H) = {0}`.

We state this for group schemes over `Spec k_H`, i.e. group objects `A` in `Over (Spec k_H)`, with
`A(k_H) = Hom_{k_H}(Spec k_H, A)` carrying the group structure of `A` (Mathlib's `Hom.group`,
written multiplicatively). As in `ContinuousKummerTheory`'s `IsTorallyKummerFaithful` we quantify
over all finite extensions `k_H` of `k` in the universe of `k` instead of over the subfields of a
fixed `k̄` (every finite extension embeds into `k̄`).

* `CurvesJacobian.IsTorus T`: `T ×_{k_H} k̄ ≅ 𝔾_m^r` as group schemes over `k̄` for an algebraic
  closure `k̄` of `k_H`. Mathlib has no `𝔾_m`; we give the isomorphism on functors of points:
  a group isomorphism `Hom_{k_H}(S, T) = Hom_{k̄}(S, T_{k̄}) ≃ (Γ(S, 𝒪_S)ˣ)^r`, natural in the
  `k̄`-scheme `S` (by Yoneda this is an isomorphism `T_{k̄} ≅ 𝔾_m^r` of group schemes).
* `CurvesJacobian.SemiAbelianExtension A`: an exact sequence `0 → T → A → B → 0` of group schemes
  over `k_H` with `T` a torus and `B` an abelian variety (`IsAbelianVariety`): `i : T → A` and
  `p : A → B` are homomorphisms, `T` is the kernel of `p` (the square with the unit of `B` is a
  pullback) and `p` is faithfully flat of finite presentation (an fppf epimorphism).
* `CurvesJacobian.IsSemiAbelianVariety A`: `A` is commutative and an extension of an abelian
  variety by a torus (the standard definition of a semi-abelian variety).
* **`CurvesJacobian.IsKummerFaithful k`** and `CurvesJacobian.IsTorallyKummerFaithfulSch k`:
  [AbsTopIII] Definition 1.5, condition (a).
* `CurvesJacobian.IsAbelianVariety.isSemiAbelianVariety`: a commutative abelian variety is
  semi-abelian (`T = 0`, `p = id`).

## The Jacobian (MR5 "J1")

* `CurvesJacobian.jacKPointsMulEquiv`: the bijection `J_k(K) ≃ J(K) = Pic⁰_{C/k,σ}(K)` of
  `jacKPointsEquiv` is a group isomorphism (`J_k(K)` with the group structure of the group scheme
  `J_k`, `J(K)` written multiplicatively).
* `CurvesJacobian.jacPoints_eq_zero_of_isKummerFaithful`: if `k` is Kummer-faithful, then
  `⋂_{N ≥ 1} N · J(k) = 0` for the Jacobian of a curve with a rational point.
* **`CurvesJacobian.Kummer.isKummerFaithfulJac_of_isKummerFaithful`**: `IsKummerFaithfulJac` for the
  Galois model of a curve with a rational point over a Kummer-faithful field `k`, as used in the
  proof of [AbsTopIII] Prop. 1.6(iii) (l.2032–2039).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

noncomputable section

namespace CurvesJacobian

section Definitions

variable {K : Type u} [Field K]

/-- **Tori** over a field `K`: `T ×_K K̄ ≅ 𝔾_m^r` as group schemes over an algebraic closure `K̄`,
expressed on functors of points: a group isomorphism `Hom_K(S, T) ≃* (Γ(S, 𝒪_S)ˣ)^r`, natural in
the `K̄`-scheme `S` (`Hom_K(S, T) = Hom_{K̄}(S, T_{K̄})`). -/
def IsTorus (T : Over (Spec (CommRingCat.of K))) [GrpObj T] : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosed L) (_ : Algebra.IsAlgebraic K L)
    (r : ℕ) (e : ∀ S : Over (Spec (CommRingCat.of L)),
      ((Over.map (Belyi.specAlgebraMap (k₀ := K) L)).obj S ⟶ T) ≃* (Fin r → (Γ(S.left, ⊤))ˣ)),
    ∀ (S S' : Over (Spec (CommRingCat.of L))) (f : S' ⟶ S)
      (x : (Over.map (Belyi.specAlgebraMap (k₀ := K) L)).obj S ⟶ T),
      e S' ((Over.map (Belyi.specAlgebraMap (k₀ := K) L)).map f ≫ x) =
        fun i ↦ Units.map f.left.appTop.hom.toMonoidHom (e S x i)

/-- **An extension of an abelian variety by a torus**: an exact sequence `0 → T → A → B → 0` of
group schemes over `K`, `T` a torus, `B` an abelian variety. Exactness: `T` is the kernel of `p`
(`isPullback`: `T = A ×_B Spec K` along the unit of `B`) and `p` is faithfully flat and locally of
finite presentation (an epimorphism of fppf sheaves). -/
structure SemiAbelianExtension (A : Over (Spec (CommRingCat.of K))) [GrpObj A] where
  /-- The torus. -/
  T : Over (Spec (CommRingCat.of K))
  [grpT : GrpObj T]
  /-- The abelian variety. -/
  B : Over (Spec (CommRingCat.of K))
  [grpB : GrpObj B]
  /-- The inclusion of the torus. -/
  i : T ⟶ A
  /-- The projection to the abelian variety. -/
  p : A ⟶ B
  [isMonHom_i : IsMonHom i]
  [isMonHom_p : IsMonHom p]
  isTorus : IsTorus T
  isAbelianVariety : IsAbelianVariety B
  isPullback : IsPullback i (toUnit T) p η[B]
  flat : Flat p.left
  surjective : Surjective p.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation p.left

attribute [instance] SemiAbelianExtension.grpT SemiAbelianExtension.grpB
  SemiAbelianExtension.isMonHom_i SemiAbelianExtension.isMonHom_p

/-- **Semi-abelian varieties** over a field `K`: commutative group schemes over `K` which are
extensions of an abelian variety by a torus. -/
class IsSemiAbelianVariety (A : Over (Spec (CommRingCat.of K))) [GrpObj A] : Prop where
  isCommMonObj : IsCommMonObj A
  nonempty_extension : Nonempty (SemiAbelianExtension A)

/-- **Kummer-faithful fields** ([AbsTopIII] Definition 1.5, condition (a)): for every finite
extension `K` of `k` and every semi-abelian variety `A` over `K`, `⋂_{N ≥ 1} N · A(K) = {0}`
(with `A(K) = Hom_K(Spec K, A)`, written multiplicatively). The definition in [AbsTopIII] is for
fields of characteristic zero. -/
def IsKummerFaithful (k : Type u) [Field k] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsSemiAbelianVariety A →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, (∀ N : ℕ, 0 < N → ∃ y, y ^ N = x) → x = 1

/-- **Torally Kummer-faithful fields** ([AbsTopIII] Definition 1.5, condition (a), for tori), as a
statement about tori as group schemes. (`ContinuousKummerTheory` uses the equivalent
`𝔾_m`-form `KummerTheory.IsTorallyKummerFaithful`.) -/
def IsTorallyKummerFaithfulSch (k : Type u) [Field k] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsTorus A →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, (∀ N : ℕ, 0 < N → ∃ y, y ^ N = x) → x = 1

/-- The trivial group scheme `Spec K` is a torus (of dimension `0`). -/
theorem isTorus_tensorUnit : IsTorus (𝟙_ (Over (Spec (CommRingCat.of K)))) :=
  ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ ↦ MulEquiv.ofUnique, fun _ _ _ _ ↦ Subsingleton.elim _ _⟩

/-- **A commutative abelian variety is a semi-abelian variety** (`0 → 0 → A → A → 0`). -/
theorem IsAbelianVariety.isSemiAbelianVariety (A : Over (Spec (CommRingCat.of K))) [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianVariety A) : IsSemiAbelianVariety A where
  isCommMonObj := inferInstance
  nonempty_extension := ⟨{
    T := 𝟙_ _
    B := A
    i := η[A]
    p := 𝟙 A
    isTorus := isTorus_tensorUnit
    isAbelianVariety := hA
    isPullback := by
      rw [toUnit_unit]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    flat := by rw [Over.id_left]; infer_instance
    surjective := by rw [Over.id_left]; infer_instance
    locallyOfFinitePresentation := by rw [Over.id_left]; infer_instance }⟩

end Definitions

section Jacobian

open Belyi Cech GaloisDescent

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

/-- **The group structure of `J_k` on `Hom_k(T, J_k)` is that of `Pic⁰`**: the representing
bijection `Hom_k(T, J_k) ≃ Pic⁰_{C/k,σ}(T_L)^{Gal(L/k)}` is additive. -/
lemma jacKRepresentableByInv_homEquiv_mul {T : Over (Spec (CommRingCat.of k))}
    (f g : T ⟶ jacK C σ hσ Ω) :
    (jacKRepresentableByInv C σ hσ Ω).homEquiv (f * g) =
      (jacKRepresentableByInv C σ hσ Ω).homEquiv f +
        (jacKRepresentableByInv C σ hσ Ω).homEquiv g :=
  ((yonedaGrpObjIsoOfRepresentableBy (jacK C σ hσ Ω)
    ((invFunctor (L := jacFieldD C σ hσ Ω) (picZero C σ hσ (curveToP1 k C)) ⋙
      AddCommGrpCat.toCommGrp) ⋙ forget₂ CommGrpCat GrpCat)
    (descRepresentableByInvMul (picZero C σ hσ (curveToP1 k C)) (jacDRepresentableBy C σ hσ Ω)
      (jacD_hcov C σ hσ Ω))).hom.app (op T)).hom.map_mul f g

/-- `jacKOfClass` is additive. -/
lemma jacKOfClass_add {T : Over (Spec (CommRingCat.of k))}
    (x y : (picZero C σ hσ (curveToP1 k C)).obj (op T)) :
    jacKOfClass C σ hσ Ω (x + y) = jacKOfClass C σ hσ Ω x * jacKOfClass C σ hσ Ω y := by
  apply (jacKRepresentableByInv C σ hσ Ω).homEquiv.injective
  rw [jacKRepresentableByInv_homEquiv_mul, jacKOfClass, jacKOfClass, jacKOfClass,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact map_add _ x y

variable (K : Type u) [Field K] [Algebra k K]

/-- **`J_k(K) ≃ J(K)` as groups**: `jacKPointsEquiv` is an isomorphism from the group of
`K`-points of the group scheme `J_k` to `J(K) = Pic⁰_{C/k,σ}(K)` (written multiplicatively). -/
def jacKPointsMulEquiv :
    (Over.mk (Belyi.specAlgebraMap (k₀ := k) K) ⟶ jacK C σ hσ Ω) ≃*
      Multiplicative (jacPoints C σ hσ K) :=
  MulEquiv.symm
    { toEquiv := ((jacKPointsEquiv C σ hσ Ω K).trans Multiplicative.ofAdd).symm
      map_mul' x y := jacKOfClass_add C σ hσ Ω
        (T := Over.mk (Belyi.specAlgebraMap (k₀ := k) K)) x.toAdd y.toAdd }

lemma jacKPointsMulEquiv_symm_ofAdd (x : jacPoints C σ hσ K) :
    (jacKPointsMulEquiv C σ hσ Ω K).symm (Multiplicative.ofAdd x) =
      (jacKPointsEquiv C σ hσ Ω K).symm x := rfl

/-- `Spec k` as a `k`-scheme via `specAlgebraMap k` is the terminal object `𝟙_`. -/
def specAlgebraMapSelfIso :
    Over.mk (Belyi.specAlgebraMap (k₀ := k) k) ≅ 𝟙_ (Over (Spec (CommRingCat.of k))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Over.mk_hom, Belyi.specAlgebraMap]
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]
    rfl)

/-- **`⋂_{N ≥ 1} N · J(k) = 0` over a Kummer-faithful field** ([AbsTopIII] Definition 1.5 for
the abelian variety `A = J_k`, `k_H = k`), via `J_k(k) ≅ J(k)`. -/
theorem jacPoints_eq_zero_of_isKummerFaithful (hk : IsKummerFaithful k) :
    ∀ z ∈ jacPoints C σ hσ k,
      (∀ N : ℕ, 0 < N → ∃ y ∈ jacPoints C σ hσ k, N • y = z) → z = 0 := by
  intro z hz hdiv
  let φ := (jacKPointsMulEquiv C σ hσ (AlgebraicClosure k) k).symm
  let e := specAlgebraMapSelfIso (k := k)
  have hA : IsSemiAbelianVariety (jacK C σ hσ (AlgebraicClosure k)) :=
    IsAbelianVariety.isSemiAbelianVariety _ inferInstance
  have h1 := hk k (jacK C σ hσ (AlgebraicClosure k)) hA
      (e.inv ≫ φ (Multiplicative.ofAdd ⟨z, hz⟩)) fun N hN ↦ by
    obtain ⟨y, hy, hyz⟩ := hdiv N hN
    refine ⟨e.inv ≫ φ (Multiplicative.ofAdd ⟨y, hy⟩), ?_⟩
    rw [← MonObj.comp_pow, ← map_pow, ← ofAdd_nsmul]
    congr 3
    exact Subtype.ext hyz
  have h2 : φ (Multiplicative.ofAdd ⟨z, hz⟩) = 1 := by
    have := congrArg (e.hom ≫ ·) h1
    simpa only [Iso.hom_inv_id_assoc, MonObj.comp_one] using this
  have h3 : (Multiplicative.ofAdd (⟨z, hz⟩ : jacPoints C σ hσ k)) = 1 :=
    φ.injective (h2.trans (map_one φ).symm)
  exact congrArg Subtype.val (Multiplicative.ofAdd.injective h3 :
    (⟨z, hz⟩ : jacPoints C σ hσ k) = 0)

end Jacobian

namespace Kummer

open Belyi KummerTheory Curve AffOrbicurve CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **J1: Kummer-faithfulness of the Jacobian from [AbsTopIII] Definition 1.5.** For a curve `X`
with a rational point `σ` over a Kummer-faithful field `k` (of characteristic zero),
`⋂_{N ≥ 1} N · Pic(X_{k̄})^{G_k} = 0` in the Galois model (`IsKummerFaithfulJac`), as used in
the proof of [AbsTopIII] Prop. 1.6(iii) (l.2032–2039). -/
theorem isKummerFaithfulJac_of_isKummerFaithful (hk : IsKummerFaithful k)
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k))) :
    IsKummerFaithfulJac (curveGaloisData k hτ) :=
  isKummerFaithfulJac_curveGaloisData k hτ σ hσ
    (jacPoints_eq_zero_of_isKummerFaithful X σ hσ hk)

end Kummer

end CurvesJacobian
