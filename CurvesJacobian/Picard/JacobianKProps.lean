/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianK
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# `J_k` is an abelian variety over `k` (JAC R5′, R7)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `Ω ⊇ k` an algebraic
closure, `L = jacFieldD C σ hσ Ω` and `J_k = jacK C σ hσ Ω`.

* **`CurvesJacobian.jacKBCRepresentableBy`**: for a field `M ⊇ k` into which `L` embeds over `k`,
  `J_k ×_k M` represents `Pic⁰_{C/k,σ}` on `(Sch/M)` (every `M`-scheme is an `L`-scheme, and
  `jacKOfClass` is bijective on `L`-schemes);
* **`CurvesJacobian.jacKBaseChangeIsoSepClosed`**: for `M` separably closed (and perfect),
  `J_k ×_k M ≅ Jacobian C_M` over `M` (R5′); in particular `J_k ×_k k̄ ≅ J_{k̄}`;
* instances (R7): `J_k` is smooth, proper, locally of finite presentation and geometrically
  irreducible (hence geometrically connected) over `k` — by fpqc descent along
  `Spec k̄ ⟶ Spec k` (`MorphismProperty.of_pullback_snd_of_descendsAlong`) from `J_{k̄}`, and,
  for geometric irreducibility, from `J_{K̄}` for every field `K ⊇ k`;
* **`IsAbelianVariety (jacK C σ hσ Ω)`**.
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

section BaseChange

variable (M : Type u) [Field M] [Algebra k M] (ε : jacFieldD C σ hσ Ω →ₐ[k] M)

lemma specMap_ε_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of M)) :
    (t ≫ Spec.map (CommRingCat.ofHom ε.toRingHom)) ≫ sL k (jacFieldD C σ hσ Ω) =
      t ≫ specAlgebraMap (k₀ := k) M := by
  rw [Category.assoc, ← Spec.map_comp, specAlgebraMap]
  congr 2
  ext r
  exact ε.commutes r

/-- `jacKOfClass` on `M`-schemes, as an equivalence. -/
def jacKOfClassEquivM (T : Over (Spec (CommRingCat.of M))) :
    (picZero C σ hσ (curveToP1 k C)).obj (op (Over.mk (T.hom ≫ specAlgebraMap (k₀ := k) M))) ≃
      (Over.mk (T.hom ≫ specAlgebraMap (k₀ := k) M) ⟶ jacK C σ hσ Ω) :=
  Equiv.ofBijective (jacKOfClass C σ hσ Ω (T := Over.mk (T.hom ≫ specAlgebraMap (k₀ := k) M)))
    (bijective_jacKOfClass_of_L C σ hσ Ω (T.hom ≫ Spec.map (CommRingCat.ofHom ε.toRingHom)) _
      (specMap_ε_comp C σ hσ Ω M ε T.hom))

/-- **`J_k ×_k M` represents `Pic⁰_{C/k,σ}` on `(Sch/M)`** if `L` embeds into `M` over `k`. -/
def jacKBCRepresentableBy :
    ((Over.map (specAlgebraMap (k₀ := k) M)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
      forget AddCommGrpCat).RepresentableBy
      ((Over.pullback (specAlgebraMap (k₀ := k) M)).obj (jacK C σ hσ Ω)) where
  homEquiv {T} := ((Over.mapPullbackAdj (specAlgebraMap (k₀ := k) M)).homEquiv T
    (jacK C σ hσ Ω)).symm.trans (jacKOfClassEquivM C σ hσ Ω M ε T).symm
  homEquiv_comp {T T'} f g := by
    rw [Equiv.trans_apply, Equiv.trans_apply, Adjunction.homEquiv_naturality_left_symm]
    refine (jacKOfClassEquivM C σ hσ Ω M ε T).symm_apply_eq.mpr ?_
    change _ = jacKOfClass C σ hσ Ω ((picZero C σ hσ (curveToP1 k C)).map
      ((Over.map (specAlgebraMap (k₀ := k) M)).map f).op _)
    rw [jacKOfClass_naturality]
    congr 1
    exact ((jacKOfClassEquivM C σ hσ Ω M ε T').apply_symm_apply _).symm

variable [PerfectField M] [IsSepClosed M]

/-- **`J_k ×_k M ≅ Jacobian C_M`** for `M` separably closed with `L ↪ M` (R5′). -/
def jacKBaseChangeIsoSepClosed :
    (Over.pullback (specAlgebraMap (k₀ := k) M)).obj (jacK C σ hσ Ω) ≅
      Jacobian (pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) M))
        (sigmaExt C σ hσ M) (sigmaExt_comp C σ hσ M) :=
  (jacKBCRepresentableBy C σ hσ Ω M ε).uniqueUpToIso (jacobianBCRepresentableBy C σ hσ M)

end BaseChange

/-- **`J_k ×_k k̄ ≅ J_{k̄}`** (R5′). -/
def jacKBaseChangeIsoOmega :
    (Over.pullback (specAlgebraMap (k₀ := k) Ω)).obj (jacK C σ hσ Ω) ≅ jacOmega C σ hσ Ω :=
  jacKBaseChangeIsoSepClosed C σ hσ Ω Ω (jacFieldD C σ hσ Ω).val

section Props

local instance : Subsingleton (Spec (CommRingCat.of Ω)) :=
  have : Subsingleton (PrimeSpectrum Ω) := inferInstance
  this

lemma pullback_snd_jacK_eq :
    pullback.snd (jacK C σ hσ Ω).hom (specAlgebraMap (k₀ := k) Ω) =
      (jacKBaseChangeIsoOmega C σ hσ Ω).hom.left ≫ (jacOmega C σ hσ Ω).hom :=
  (Over.w (jacKBaseChangeIsoOmega C σ hσ Ω).hom).symm

lemma isIso_jacKBaseChangeIsoOmega_left : IsIso (jacKBaseChangeIsoOmega C σ hσ Ω).hom.left :=
  inferInstanceAs (IsIso ((Over.forget _).map (jacKBaseChangeIsoOmega C σ hσ Ω).hom))

omit [PerfectField k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma fpqc_sΩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
    (specAlgebraMap (k₀ := k) Ω) :=
  ⟨⟨(inferInstance : Surjective (sL k Ω)), (inferInstance : Flat (sL k Ω))⟩,
    (inferInstance : QuasiCompact (sL k Ω))⟩

/-- **`J_k` is smooth over `k`** (fpqc descent from `J_{k̄}`). -/
instance : Smooth (jacK C σ hσ Ω).hom := by
  refine MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (fpqc_sΩ Ω) ?_
  rw [pullback_snd_jacK_eq]
  haveI := isIso_jacKBaseChangeIsoOmega_left C σ hσ Ω
  exact (MorphismProperty.cancel_left_of_respectsIso @Smooth
    (jacKBaseChangeIsoOmega C σ hσ Ω).hom.left (jacOmega C σ hσ Ω).hom).mpr inferInstance

/-- `J_k` is locally of finite presentation over `k`. -/
instance : LocallyOfFinitePresentation (jacK C σ hσ Ω).hom := inferInstance

/-- `J_k` is universally closed over `k`. -/
instance : UniversallyClosed (jacK C σ hσ Ω).hom := by
  refine MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (fpqc_sΩ Ω) ?_
  rw [pullback_snd_jacK_eq]
  haveI := isIso_jacKBaseChangeIsoOmega_left C σ hσ Ω
  exact (MorphismProperty.cancel_left_of_respectsIso @UniversallyClosed
    (jacKBaseChangeIsoOmega C σ hσ Ω).hom.left (jacOmega C σ hσ Ω).hom).mpr inferInstance

/-- **`J_k` is proper over `k`.** -/
instance : IsProper (jacK C σ hσ Ω).hom where
  toIsSeparated := isSeparated_of_grpObj_field _
  toUniversallyClosed := inferInstance
  toLocallyOfFiniteType := inferInstance

/-- **`J_k` is geometrically irreducible over `k`**: for a field `K ⊇ k`, `J_k ×_k K̄ ≅ J_{K̄}` is
irreducible and maps onto `J_k ×_k K`. -/
instance : GeometricallyIrreducible (jacK C σ hσ Ω).hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  let M := AlgebraicClosure K
  haveI : Algebra.IsAlgebraic k (jacFieldD C σ hσ Ω) := Algebra.IsAlgebraic.of_finite k _
  let ε : jacFieldD C σ hσ Ω →ₐ[k] M := IsAlgClosed.lift
  haveI : Subsingleton (Spec (CommRingCat.of M)) :=
    have : Subsingleton (PrimeSpectrum M) := inferInstance
    this
  haveI : Nonempty (Spec (CommRingCat.of M)) :=
    have : Nonempty (PrimeSpectrum M) := inferInstance
    this
  let e := jacKBaseChangeIsoSepClosed C σ hσ Ω M ε
  haveI : IrreducibleSpace (Jacobian (pullback (C ↘ Spec (CommRingCat.of k))
      (specAlgebraMap (k₀ := k) M)) (sigmaExt C σ hσ M) (sigmaExt_comp C σ hσ M)).left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (Jacobian (pullback
      (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) M)) (sigmaExt C σ hσ M)
        (sigmaExt_comp C σ hσ M)).hom
  haveI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have h1 : IrreducibleSpace ↥(pullback (jacK C σ hσ Ω).hom (specAlgebraMap (k₀ := k) M)) :=
    e.inv.left.homeomorph.irreducibleSpace_iff.mp inferInstance
  let h := specMapAlg K M
  have hh : h ≫ specAlgebraMap (k₀ := k) K = specAlgebraMap (k₀ := k) M :=
    specMapAlg_comp_specAlgebraMap K M
  let iso := pullbackLeftPullbackSndIso (jacK C σ hσ Ω).hom (specAlgebraMap (k₀ := k) K) h
  have h2 : IrreducibleSpace ↥(pullback (pullback.snd (jacK C σ hσ Ω).hom
      (specAlgebraMap (k₀ := k) K)) h) := by
    exact (iso ≪≫ pullback.congrHom rfl hh).hom.homeomorph.irreducibleSpace_iff.mpr h1
  haveI : Surjective h := ⟨fun x ↦
    ⟨Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of M))),
      Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩⟩
  have hs : Function.Surjective (pullback.fst (pullback.snd (jacK C σ hσ Ω).hom
      (specAlgebraMap (k₀ := k) K)) h) :=
    (MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance).surj
  exact hs.irreducibleSpace (Scheme.Hom.continuous _)

/-- `J_k` is geometrically connected over `k`. -/
instance : GeometricallyConnected (jacK C σ hσ Ω).hom := inferInstance

/-- **`J_k` is an abelian variety over `k`** (JAC R7). -/
instance : IsAbelianVariety (jacK C σ hσ Ω) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Props

end CurvesJacobian
