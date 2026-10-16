/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Etale.Gm
import CurvesJacobian.Etale.KummerCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Etale

/-!
# The Kummer sequence on the small étale site

Let `X` be a scheme and `n ≥ 1` an integer invertible on `X`. On the small étale site of `X`:

* `CurvesJacobian.kummerMap X n : Gm X ⟶ Gm X` is `u ↦ uⁿ` (written `n • 𝟙` additively);
* `CurvesJacobian.isLocallySurjective_kummerMap`: it is locally surjective — every unit is
  étale-locally an `n`-th power, using the Kummer coverings `Spec A[T]/(Tⁿ - u) → Spec A`
  (`CurvesJacobian.etale_kummer`, `CurvesJacobian.faithfullyFlat_kummer`) on an affine open cover;
* `CurvesJacobian.epi_kummerMap`: hence it is an epimorphism of sheaves of abelian groups;
* `CurvesJacobian.mu X n := kernel (kummerMap X n)` and `CurvesJacobian.kummer_shortExact`: the
  **Kummer sequence** `0 → μₙ → 𝔾ₘ →(·)ⁿ 𝔾ₘ → 0` is a short exact sequence in
  `Sheaf X.smallEtaleTopology Ab` (Stacks, Lemma 03PK).
-/

open CategoryTheory Opposite Limits AlgebraicGeometry

namespace CurvesJacobian

universe u

variable (X : Scheme.{u})

/-- The `n`-th power map `𝔾ₘ → 𝔾ₘ` (multiplication by `n` in additive notation). -/
noncomputable def kummerMap (n : ℕ) : Gm X ⟶ Gm X := n • 𝟙 (Gm X)

lemma kummerMap_hom_app (n : ℕ) (U : X.Etaleᵒᵖ) (t : ToType ((Gm X).obj.obj U)) :
    (kummerMap X n).hom.app U t = n • t :=
  rfl

variable {X}

/-- The Kummer covering `Spec R[T]/(Tⁿ - u) → Spec R` is étale and surjective. -/
lemma etale_surjective_SpecMap_kummer (R : CommRingCat.{u}) {n : ℕ} (hn : 0 < n)
    (hnR : IsUnit (n : R)) (v : Rˣ) :
    Etale (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (kummerPoly n (v : R))))) ∧
      Function.Surjective
        (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (kummerPoly n (v : R))))) := by
  rw [← AdjoinRoot.algebraMap_eq]
  refine ⟨(HasRingHomProperty.Spec_iff (P := @Etale)).2
    ((RingHom.etale_algebraMap).2 (etale_kummer hn hnR v)), ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro x
    exact (IsEmpty.false (α := PrimeSpectrum R) x).elim
  · haveI : Module.FaithfullyFlat R (AdjoinRoot (kummerPoly n (v : R))) :=
      faithfullyFlat_kummer hn _
    exact ((flat_and_surjective_SpecMap_iff _).2
      ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)).2.surj

/-- **Every unit is étale-locally an `n`-th power** when `n` is invertible on `X`. -/
theorem isLocallySurjective_kummerMap {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.IsLocallySurjective (kummerMap X n) := by
  constructor
  intro U s
  let 𝒰 := U.left.affineOpenCover
  -- the unit `s` on the affine pieces
  let ui : ∀ i, (𝒰.X i)ˣ := fun i ↦ Units.map
    (((Scheme.ΓSpecIso (𝒰.X i)).hom.hom.comp (𝒰.f i).appTop.hom).toMonoidHom)
    (Additive.toMul s)
  have hnA : ∀ i, IsUnit ((n : 𝒰.X i)) := by
    intro i
    have h := hnX.map ((Scheme.ΓSpecIso (𝒰.X i)).hom.hom.comp
      ((𝒰.f i).appTop.hom.comp U.hom.appTop.hom))
    simpa using h
  let B : 𝒰.I₀ → CommRingCat.{u} := fun i ↦
    CommRingCat.of (AdjoinRoot (kummerPoly n ((ui i : 𝒰.X i))))
  let φ : ∀ i, 𝒰.X i ⟶ B i := fun i ↦ CommRingCat.ofHom (AdjoinRoot.of _)
  have hφ := fun i ↦ etale_surjective_SpecMap_kummer (𝒰.X i) hn (hnA i) (ui i)
  have hφs : ∀ i, Function.Surjective (Spec.map (φ i)) := fun i ↦ (hφ i).2
  have hZ : ∀ i, Etale (Spec.map (φ i) ≫ 𝒰.f i ≫ U.hom) := by
    intro i
    haveI : Etale (Spec.map (φ i)) := (hφ i).1
    haveI : Etale U.hom := U.prop
    infer_instance
  let Z : 𝒰.I₀ → X.Etale := fun i ↦
    @Scheme.Etale.mk X _ (Spec.map (φ i) ≫ 𝒰.f i ≫ U.hom) (hZ i)
  let g : ∀ i, Z i ⟶ U := fun i ↦
    MorphismProperty.Over.homMk (Spec.map (φ i) ≫ 𝒰.f i)
      (by simp only [Category.assoc]; rfl) trivial
  refine GrothendieckTopology.superset_covering _ ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff g).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    -- the `n`-th root of `s` on `Z i`
    have hroot : IsUnit (AdjoinRoot.root (kummerPoly n ((ui i : 𝒰.X i)))) := by
      have h := root_pow_kummer n ((ui i : 𝒰.X i))
      rw [← isUnit_pow_iff hn.ne', h]
      exact (ui i).isUnit.map _
    let r : (Γ(Spec (B i), ⊤))ˣ := Units.map (Scheme.ΓSpecIso (B i)).inv.hom.toMonoidHom hroot.unit
    refine ⟨Additive.ofMul r, ?_⟩
    rw [kummerMap_hom_app]
    apply Additive.toMul.injective
    apply Units.ext
    change ((r ^ n : (Γ(Spec (B i), ⊤))ˣ) : Γ(Spec (B i), ⊤)) =
      (Spec.map (φ i) ≫ 𝒰.f i).appTop ((Additive.toMul s : (Γ(U.left, ⊤))ˣ) : Γ(U.left, ⊤))
    rw [Units.val_pow_eq_pow_val]
    change ((Scheme.ΓSpecIso (B i)).inv (AdjoinRoot.root _)) ^ n = _
    rw [← map_pow, root_pow_kummer]
    set sv : Γ(U.left, ⊤) := ((Additive.toMul s : (Γ(U.left, ⊤))ˣ) : Γ(U.left, ⊤))
    have hnat := congrArg (fun h ↦ h.hom ((𝒰.f i).appTop sv)) (Scheme.ΓSpecIso_naturality (φ i))
    simp only [CommRingCat.comp_apply] at hnat
    have e1 : (AdjoinRoot.of (kummerPoly n ((ui i : 𝒰.X i)))) (ui i : 𝒰.X i) =
        (φ i).hom ((Scheme.ΓSpecIso (𝒰.X i)).hom ((𝒰.f i).appTop sv)) := rfl
    rw [AdjoinRoot.algebraMap_eq, e1, ← hnat, Iso.hom_inv_id_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨z, rfl⟩ := hφs (𝒰.idx x) y
    exact ⟨𝒰.idx x, z, hy⟩

/-- **The `n`-th power map on `𝔾ₘ` is an epimorphism** of étale sheaves when `n` is invertible. -/
theorem epi_kummerMap {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Epi (kummerMap X n) :=
  haveI := isLocallySurjective_kummerMap hn hnX
  Sheaf.epi_of_isLocallySurjective _

variable (X) in
/-- `μₙ`, the kernel of the `n`-th power map on `𝔾ₘ`. -/
noncomputable def mu (n : ℕ) : Sheaf X.smallEtaleTopology Ab.{u} := kernel (kummerMap X n)

variable (X) in
/-- The Kummer short complex `μₙ → 𝔾ₘ → 𝔾ₘ`. -/
noncomputable def kummerComplex (n : ℕ) : ShortComplex (Sheaf X.smallEtaleTopology Ab.{u}) :=
  ShortComplex.mk (kernel.ι (kummerMap X n)) (kummerMap X n) (kernel.condition _)

/-- **The Kummer sequence** `0 → μₙ → 𝔾ₘ → 𝔾ₘ → 0` is short exact on the small étale site
(Stacks, Lemma 03PK). -/
theorem kummer_shortExact {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    (kummerComplex X n).ShortExact := by
  haveI := epi_kummerMap hn hnX
  haveI : Mono (kummerComplex X n).f := inferInstanceAs (Mono (kernel.ι _))
  haveI : Epi (kummerComplex X n).g := inferInstanceAs (Epi (kummerMap X n))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance

end CurvesJacobian
