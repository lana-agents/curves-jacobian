/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.TwistGalois

/-!
# Geometric models of chain objects and the semilinear action on them (MR8.5, option (A))

For the arithmetic cuspidal extension `E = Π_X ↠ G_K` of an affine hyperbolic curve `X` over a
number field `K` (`CurvesJacobian.Cusp.arithmeticExt`) and a chain object `A` of `E`
([AbsTopI] Def 4.2 (iii)), a **geometric model** (`CurvesJacobian.Cusp.GeomModel A`) is a
hyperbolic curve `Y` with a cusp over a number field `K ⊆ M ⊆ Ω` together with an open embedding
`ι : Π_Y ↪ A` with normal image, compatible with the projections to `G_K` up to conjugation
(`A.toG ∘ ι = conj(g₀) ∘ res ∘ pr_Y`, `res : G_M ↪ G_K`). In Mochizuki's proof of [AbsTopI]
Theorem 4.7 (i) the objects of `X̃/X`-chains are hyperbolic orbicurves; a geometric model replaces
the orbicurve `[Y/(A/ι(Π_Y))]` by the curve `Y` together with the action of `A/ι(Π_Y)` on it.

* `CurvesJacobian.Cusp.GeomModel.base`: `X` itself is a model of the trivial chain object.
* `CurvesJacobian.Cusp.GeomModel.conjPi`: for `g ∈ A`, conjugation by `g` on `ι(Π_Y)`, as a
  continuous automorphism of `Π_Y` (multiplicative in `g`, inner for `g ∈ ι(Π_Y)`:
  `conjPi_mul`, `conjPi_ι`); it lies over conjugation by a Galois element `τ_g` normalising
  `G_M` (`GeomModel.res_projGk_conjPi`), which therefore restricts to a `K`-automorphism `α_g` of
  `M` (`GeomModel.exists_resAut`).
* **`CurvesJacobian.Cusp.GeomModel.exists_semilinearAut`** (the action of `A/ι(Π_Y)` on `Y`,
  [AbsTopI] Thm 4.7 (i), proof, "by applying this rel-isom-DGC as was done in the proofs of
  [Mzk7] Thm 2.4; [Mzk9] Thm 2.3 (i)"): for each `g ∈ A` there are a `K`-automorphism `α_g` of
  `M` (the restriction of `τ_g`) and an automorphism `F_g` of the scheme `Spec Γ(U_Y)` lying over
  `Spec α_g` which induces `conjPi g` up to a change of base point; `F_g` is unique
  (`GeomModel.eq_of_semilinearAut`), and `α_g = id`, `F_g = id` for `g ∈ ι(Π_Y)`
  (`GeomModel.semilinearAut_ι`), so the action factors through `A / ι(Π_Y)`. This uses only
  `RelIsomDGC M` (through the twisted DGC,
  `CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_gal`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- `A ⟶ G_K` as a homomorphism into `π₁ᵉᵗ(Spec K)`. -/
def toGk (A : ChainObj (arithmeticExt Ω CX hcX)) : A.grp →* π₁ᵉᵗ(sK) :=
  (A.toG : A.grp →* (arithmeticExt Ω CX hcX).G)

variable (Ω CX hcX) in
/-- **A geometric model of a chain object** `A` of `Π_X ↠ G_K`: a hyperbolic curve `Y` with a cusp
over a number field `K ⊆ M ⊆ Ω` and an open embedding `ι : Π_Y ↪ A` with normal image, lying over
`res : G_M ↪ G_K` up to conjugation by some `g₀ ∈ G_K`. -/
structure GeomModel (A : ChainObj (arithmeticExt Ω CX hcX)) where
  /-- The field of definition `K ⊆ M ⊆ Ω` of the model. -/
  M : Type u
  [field : Field M]
  [numberField : NumberField M]
  [algK : Algebra K M]
  [algΩ : Algebra M Ω]
  [tower : IsScalarTower K M Ω]
  [finDim : FiniteDimensional K M]
  /-- The curve `Y` over `M`. -/
  Y : HypCurve M
  hY : (Y.U : Set Y.Xbar)ᶜ.Nonempty
  /-- The open embedding `Π_Y ↪ A` with normal image. -/
  ι : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) →ₜ* A.grp
  inj : Function.Injective ι
  isOpen_range : IsOpen (Set.range ι)
  normal : (ι : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) →* A.grp).range.Normal
  toG_eq : ∃ g₀ : π₁ᵉᵗ(sK), ∀ σ,
    toGk A (ι σ) = g₀ * resGal K Ω M (projGk Ω Y hY σ) * g₀⁻¹

namespace GeomModel

attribute [instance] field numberField algK algΩ tower finDim

variable {A : ChainObj (arithmeticExt Ω CX hcX)} (D : GeomModel Ω CX hcX A)

/-- `Π_Y`. -/
abbrev Pi := π₁ᵉᵗ(basePoint Ω D.Y D.hY ≫ baseChangeSpec D.M Ω Γ(D.Y.Xbar, D.Y.U))

instance : Algebra.IsAlgebraic D.M Ω := Algebra.IsAlgebraic.tower_top (K := K) D.M

/-- A choice of the conjugating element `g₀`. -/
def g₀ : π₁ᵉᵗ(sK) := D.toG_eq.choose

lemma toG_ι (σ : D.Pi) :
    toGk A (D.ι σ) = D.g₀ * resGal K Ω D.M (projGk Ω D.Y D.hY σ) * D.g₀⁻¹ :=
  D.toG_eq.choose_spec σ

lemma conj_mem_range (g : A.grp) (σ : D.Pi) :
    g * D.ι σ * g⁻¹ ∈ (D.ι : D.Pi →* A.grp).range :=
  D.normal.conj_mem _ ⟨σ, rfl⟩ g

/-- Conjugation by `g ∈ A` on `ι(Π_Y)`, pulled back to `Π_Y` (as a function). -/
def conjFun (g : A.grp) (σ : D.Pi) : D.Pi := (D.conj_mem_range g σ).choose

lemma ι_conjFun (g : A.grp) (σ : D.Pi) : D.ι (D.conjFun g σ) = g * D.ι σ * g⁻¹ :=
  (D.conj_mem_range g σ).choose_spec

lemma conjFun_inv_conjFun (g : A.grp) (σ : D.Pi) : D.conjFun g⁻¹ (D.conjFun g σ) = σ :=
  D.inj (by rw [ι_conjFun, ι_conjFun]; group)

/-- Conjugation by `g ∈ A` on `ι(Π_Y)` as a continuous automorphism of `Π_Y`. -/
def conjPi (g : A.grp) : D.Pi ≃ₜ* D.Pi where
  toFun := D.conjFun g
  invFun := D.conjFun g⁻¹
  left_inv := D.conjFun_inv_conjFun g
  right_inv σ := by simpa using D.conjFun_inv_conjFun g⁻¹ σ
  map_mul' a b := D.inj (by simp only [ι_conjFun, map_mul]; group)
  continuous_toFun := by
    have hemb : Topology.IsEmbedding D.ι :=
      (D.ι.continuous.isClosedEmbedding D.inj).isEmbedding
    refine hemb.continuous_iff.2 ?_
    have : (D.ι ∘ D.conjFun g) = fun σ ↦ g * D.ι σ * g⁻¹ := funext (D.ι_conjFun g)
    rw [this]
    fun_prop
  continuous_invFun := by
    have hemb : Topology.IsEmbedding D.ι :=
      (D.ι.continuous.isClosedEmbedding D.inj).isEmbedding
    refine hemb.continuous_iff.2 ?_
    have : (D.ι ∘ D.conjFun g⁻¹) = fun σ ↦ g⁻¹ * D.ι σ * g⁻¹⁻¹ := funext (D.ι_conjFun g⁻¹)
    rw [this]
    fun_prop

lemma ι_conjPi (g : A.grp) (σ : D.Pi) : D.ι (D.conjPi g σ) = g * D.ι σ * g⁻¹ :=
  D.ι_conjFun g σ

/-- On `ι(Π_Y)` itself, `conjPi` is inner. -/
lemma conjPi_ι (σ τ : D.Pi) : D.conjPi (D.ι σ) τ = σ * τ * σ⁻¹ :=
  D.inj (by rw [ι_conjPi, map_mul, map_mul, map_inv])

/-- `conjPi` is multiplicative in `g`. -/
lemma conjPi_mul (g h : A.grp) (σ : D.Pi) :
    D.conjPi (g * h) σ = D.conjPi g (D.conjPi h σ) :=
  D.inj (by rw [ι_conjPi, ι_conjPi, ι_conjPi]; group)

/-- The Galois element `τ_g` with `res ∘ pr_Y ∘ conjPi g = conj(τ_g⁻¹) ∘ res ∘ pr_Y`. -/
def tau (g : A.grp) : Ω ≃ₐ[K] Ω :=
  ((mulEquivAutFiber K Ω).symm (D.g₀⁻¹ * toGk A g * D.g₀))⁻¹

lemma mulEquivAutFiber_tau (g : A.grp) :
    mulEquivAutFiber K Ω (D.tau g) = (D.g₀⁻¹ * toGk A g * D.g₀)⁻¹ := by
  rw [tau, map_inv, MulEquiv.apply_symm_apply]

/-- **`conjPi g` lies over conjugation by `τ_g⁻¹`.** -/
lemma res_projGk_conjPi (g : A.grp) (σ : D.Pi) :
    resGal K Ω D.M (projGk Ω D.Y D.hY (D.conjPi g σ)) =
      (mulEquivAutFiber K Ω (D.tau g))⁻¹ * resGal K Ω D.M (projGk Ω D.Y D.hY σ) *
        mulEquivAutFiber K Ω (D.tau g) := by
  have h := D.toG_ι (D.conjPi g σ)
  rw [ι_conjPi, map_mul, map_mul, map_inv, toG_ι] at h
  rw [mulEquivAutFiber_tau, inv_inv]
  have h' : resGal K Ω D.M (projGk Ω D.Y D.hY (D.conjPi g σ)) =
      D.g₀⁻¹ * toGk A (D.ι (D.conjPi g σ)) * D.g₀ := by
    rw [toG_ι]
    group
  rw [h', ι_conjPi, map_mul, map_mul, map_inv, toG_ι]
  group

/-- `τ_g` normalises `G_M`, hence restricts to a `K`-automorphism of `M`. -/
lemma exists_resAut (g : A.grp) :
    ∃ α : D.M ≃ₐ[K] D.M, ∀ x, algebraMap D.M Ω (α x) = D.tau g (algebraMap D.M Ω x) := by
  refine exists_resAut_of_conj_mem_range D.M (D.tau g) fun γ hγ ↦ ?_
  obtain ⟨s, rfl⟩ := hγ
  obtain ⟨σ, rfl⟩ := projGk_surjective Ω D.Y D.hY s
  refine ⟨projGk Ω D.Y D.hY (D.conjPi g⁻¹ σ), ?_⟩
  change resGal K Ω D.M _ = _
  rw [res_projGk_conjPi, mulEquivAutFiber_tau, mulEquivAutFiber_tau, map_inv]
  change _ = _ * resGal K Ω D.M (projGk Ω D.Y D.hY σ) * _
  group

/-- **The semilinear action of `A` on the model** ([AbsTopI] Thm 4.7 (i), proof): for `g ∈ A`,
an automorphism `F_g` of `Spec Γ(U_Y)` lying over `Spec α_g` (`α_g` the restriction of `τ_g` to
`M`) that induces `conjPi g` up to a change of base point. -/
theorem exists_semilinearAut (hDGC : RelIsomDGC D.M) (g : A.grp) :
    ∃ (α : D.M ≃ₐ[K] D.M) (_ : ∀ x, algebraMap D.M Ω (α x) = D.tau g (algebraMap D.M Ω x))
      (F : Spec Γ(D.Y.Xbar, D.Y.U) ≅ Spec Γ(D.Y.Xbar, D.Y.U)),
      F.hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv α.toRingEquiv ∧
        IsConjInduced F.hom (D.conjPi g) := by
  obtain ⟨α, hα⟩ := D.exists_resAut g
  obtain ⟨F, hF, H⟩ := exists_isConjInduced_of_relIsomDGC_gal hDGC (D.conjPi g) hα
    (D.res_projGk_conjPi g)
  exact ⟨α, hα, F, hF, H⟩

/-- **Uniqueness of the semilinear automorphism** `F_g` (for a given restriction `α_g`). -/
theorem eq_of_semilinearAut (hDGC : RelIsomDGC D.M) (g : A.grp) {α : D.M ≃ₐ[K] D.M}
    (hα : ∀ x, algebraMap D.M Ω (α x) = D.tau g (algebraMap D.M Ω x))
    {F G : Spec Γ(D.Y.Xbar, D.Y.U) ≅ Spec Γ(D.Y.Xbar, D.Y.U)}
    (hF : F.hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv α.toRingEquiv)
    (hG : G.hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv α.toRingEquiv)
    (HF : IsConjInduced F.hom (D.conjPi g)) (HG : IsConjInduced G.hom (D.conjPi g)) : F = G :=
  eq_of_isConjInduced_of_relIsomDGC_gal hDGC (D.conjPi g) hα (D.res_projGk_conjPi g) hF hG HF HG

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma specRingEquiv_refl (L : Type u) [Field L] :
    specRingEquiv (RingEquiv.refl L) = 𝟙 (Spec (.of L)) := by
  change Spec.map (CommRingCat.ofHom (RingHom.id L)) = _
  exact Spec.map_id _

/-- `τ_g` fixes `M` for `g ∈ ι(Π_Y)`. -/
lemma tau_ι_apply (σ : D.Pi) (x : D.M) :
    D.tau (D.ι σ) (algebraMap D.M Ω x) = algebraMap D.M Ω x := by
  have hmem : mulEquivAutFiber K Ω (D.tau (D.ι σ)) ∈ (resGal K Ω D.M).toMonoidHom.range := by
    rw [mulEquivAutFiber_tau, toG_ι]
    refine ⟨(projGk Ω D.Y D.hY σ)⁻¹, ?_⟩
    change resGal K Ω D.M _ = _
    rw [map_inv]
    group
  have := (mem_range_resGal_iff D.M _).1 hmem x
  rwa [MulEquiv.symm_apply_apply] at this

/-- **The action is trivial on `ι(Π_Y)`**: for `g ∈ ι(Π_Y)` the restriction `α_g` is the identity
and the semilinear automorphism `F_g` is the identity, so the action factors through
`A / ι(Π_Y)`. -/
theorem semilinearAut_ι (hDGC : RelIsomDGC D.M) (σ : D.Pi) {α : D.M ≃ₐ[K] D.M}
    (hα : ∀ x, algebraMap D.M Ω (α x) = D.tau (D.ι σ) (algebraMap D.M Ω x))
    {F : Spec Γ(D.Y.Xbar, D.Y.U) ≅ Spec Γ(D.Y.Xbar, D.Y.U)}
    (hF : F.hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv α.toRingEquiv)
    (HF : IsConjInduced F.hom (D.conjPi (D.ι σ))) : α = AlgEquiv.refl ∧ F = Iso.refl _ := by
  have hα1 : α = AlgEquiv.refl := AlgEquiv.ext fun x ↦
    (algebraMap D.M Ω).injective ((hα x).trans (D.tau_ι_apply σ x))
  subst hα1
  refine ⟨rfl, D.eq_of_semilinearAut hDGC (D.ι σ) hα hF ?_ HF ?_⟩
  · change (Iso.refl _).hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv (RingEquiv.refl D.M)
    rw [specRingEquiv_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · refine (isConjInduced_iff _ (Category.comp_id _) _).2 ⟨σ, fun τ ↦ ?_⟩
    change _ = σ.conjAut (fundamentalGroupMap (𝟙 _) (Category.comp_id _) τ)
    rw [fundamentalGroupMap_id, Aut_conjAut_eq, conjPi_ι]
    rfl

/-- The restriction `α_g` is unique. -/
lemma resAut_unique (g : A.grp) {α β : D.M ≃ₐ[K] D.M}
    (hα : ∀ x, algebraMap D.M Ω (α x) = D.tau g (algebraMap D.M Ω x))
    (hβ : ∀ x, algebraMap D.M Ω (β x) = D.tau g (algebraMap D.M Ω x)) : α = β :=
  AlgEquiv.ext fun x ↦ (algebraMap D.M Ω).injective ((hα x).trans (hβ x).symm)

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `res : G_K → G_K` is the identity. -/
lemma resGal_self (s : π₁ᵉᵗ(sK)) : resGal K Ω K s = s := by
  have e : sKM K K = 𝟙 _ := by
    rw [sKM, Algebra.algebraMap_self]
    exact Spec.map_id _
  rw [resGal, fundamentalGroupMap_congr e (sM_sKM K) (Category.comp_id _), fundamentalGroupMap_id]
  rfl

variable (Ω CX hcX) in
/-- **The trivial chain object `Π_X` is modelled by `X` itself.** -/
def base : GeomModel Ω CX hcX (ChainObj.base (arithmeticExt Ω CX hcX)) where
  M := K
  Y := CX
  hY := hcX
  ι := ContinuousMonoidHom.id _
  inj := Function.injective_id
  isOpen_range := by
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩
  normal := ⟨fun n _ g ↦ ⟨(g * n * g⁻¹ : (ChainObj.base (arithmeticExt Ω CX hcX)).grp), rfl⟩⟩
  toG_eq := ⟨1, fun σ ↦ by
    rw [resGal_self]
    simp only [one_mul, inv_one, mul_one]
    rfl⟩

end GeomModel

end CurvesJacobian.Cusp
