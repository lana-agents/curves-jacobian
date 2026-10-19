/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspDegreeEq
import CurvesJacobian.Cusp.HypBaseChange
import Belyi.Anabelian.BelyiInputNumberField

/-!
# Points become rational after a large enough base change

[AbsTopII] Example 3.6 (`Topics in Absolute Anabelian Geometry II.txt` l.4634–4635, l.4667–4668)
fills in only cusps which are rational over the field of definition: "By replacing `k′` by some
finite extension of `k′`, let us suppose further … that the cusps of `W` are all defined over
`k′`". This is forced by the definition of the operations of type `•` ([AbsTopI] Definition 4.2
(i) (c): "the complement of a single `k_{j+1}`-valued point"; on the group side the kernel is
normally generated *in `Δ_j`*, `Belyi.Anabelian.ChainObj.deltaNormalClosure`).

For a scheme `X` over a field `M`, a field extension `M'/M` with an `M'`-algebra `Ω`
algebraically closed, and a point `t` of `X_{M'} = Spec M' ×_M X` (`bcX`) with `κ(t)` algebraic
over `M'`: if every `M`-embedding `κ(x) → Ω` of the residue field of `x = bcπ t` takes values in
`M'`, then `t` is `M'`-rational, i.e. `κ(M') → κ(t)` is an isomorphism
(`CurvesJacobian.Cusp.isIso_residueFieldMap_bcX`).

Proof: an `M'`-embedding `τ : κ(t) → Ω` gives an `Ω`-point `g` of `X_{M'}` through `t`; its
image in `X` is given by an `M`-embedding `σ : κ(x) → Ω`, which factors through `M'`; this gives a
section `s : Spec M' ⟶ X_{M'}` of the structure map with `g = s ∘ (Spec Ω → Spec M')`, so `t` is
the image of `s` and the residue field map of the structure map at `t` has the left inverse
`κ(s)` (`CurvesJacobian.Cusp.isIso_residueFieldMap_of_comp_eq_id`).

`CurvesJacobian.Cusp.exists_finSub_resEmb`: for a finite set `S` of closed points of a scheme
locally of finite type over `M` and `Ω / M`, a finite subextension of `Ω / M` contains the images
of all `M`-embeddings `κ(x) → Ω`, `x ∈ S`; `ratFinSub` is a choice of one.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian IntermediateField

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- If `f ≫ g = 𝟙`, the residue field map of `g` at `f a` is an isomorphism. -/
lemma isIso_residueFieldMap_of_comp_eq_id {A B : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ A)
    (h : f ≫ g = 𝟙 A) (a : A) : IsIso (g.residueFieldMap (f a)) := by
  have hc : IsIso ((f ≫ g).residueFieldMap a) := by
    rw [h, Scheme.residueFieldMap_id]
    exact IsIso.id _
  have hbij : Function.Bijective ((f ≫ g).residueFieldMap a) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hc
  rw [Scheme.residueFieldMap_comp] at hbij
  have hinj : Function.Injective (f.residueFieldMap a) := (f.residueFieldMap a).hom.injective
  refine (ConcreteCategory.isIso_iff_bijective _).2
    ⟨(g.residueFieldMap (f a)).hom.injective, fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hbij.2 (f.residueFieldMap a y)
  exact ⟨z, hinj hz⟩

section Rational

variable (M M' Ω : Type u) [Field M] [Field M'] [Field Ω] [Algebra M M'] [Algebra M' Ω]
  [Algebra M Ω] [IsScalarTower M M' Ω] [IsAlgClosed Ω] {X : Scheme.{u}} [X.Over (Spec (.of M))]

/-- **Rationality after base change.** Let `t` be a point of `X_{M'} = Spec M' ×_M X` with
`κ(t)` algebraic over `M'` such that every `M`-embedding `σ : κ(x) → Ω` (`x` the image of `t` in
`X`) takes values in `M'`. Then `t` is `M'`-rational: the residue field map of
`X_{M'} ⟶ Spec M'` at `t` is an isomorphism. -/
theorem isIso_residueFieldMap_bcX (t : bcX M M' X)
    (halg : letI := Anabelian.residueFieldAlgebra M' (bcX M M' X) t
      Algebra.IsAlgebraic M' ((bcX M M' X).residueField t))
    (hK : ∀ (σ : ResEmb M Ω X (bcπ M M' X t)) a, σ a ∈ Set.range (algebraMap M' Ω)) :
    IsIso ((bcX M M' X ↘ Spec (.of M')).residueFieldMap t) := by
  letI := Anabelian.residueFieldAlgebra M' (bcX M M' X) t
  -- an `M'`-embedding `τ : κ(t) → Ω` and the `Ω`-point `g` through `t`
  let τ : (bcX M M' X).residueField t →ₐ[M'] Ω := IsAlgClosed.lift
  let g : Spec (.of Ω) ⟶ bcX M M' X :=
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (bcX M M' X).fromSpecResidueField t
  have hg1 : g ≫ (bcX M M' X ↘ Spec (.of M')) = specAlgebraMap M' Ω := by
    rw [Category.assoc, fromSpecResidueField_comp_structure M' t, ← Spec.map_comp,
      specAlgebraMap]
    congr 1
    ext a
    exact τ.commutes a
  have hgt : g (IsLocalRing.closedPoint Ω) = t := by
    change (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (bcX M M' X).fromSpecResidueField t)
      (IsLocalRing.closedPoint Ω) = t
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  -- the image of `g` in `X`
  have hx0 := (Scheme.SpecToEquivOfField Ω X).symm_apply_apply (g ≫ bcπ M M' X)
  generalize Scheme.SpecToEquivOfField Ω X (g ≫ bcπ M M' X) = p at hx0
  obtain ⟨c, ρ⟩ := p
  have hgc : Spec.map ρ ≫ X.fromSpecResidueField c = g ≫ bcπ M M' X := hx0
  have hc : c = bcπ M M' X t := by
    have := congrArg (fun φ : Spec (.of Ω) ⟶ X ↦ φ (IsLocalRing.closedPoint Ω)) hgc
    simp only [Scheme.Hom.comp_apply] at this
    rw [Scheme.fromSpecResidueField_apply, hgt] at this
    exact this
  subst hc
  letI := Anabelian.residueFieldAlgebra M X (bcπ M M' X t)
  have hρ : ρ.hom.comp (algebraMap M (X.residueField (bcπ M M' X t))) = algebraMap M Ω := by
    have h1 : (g ≫ bcπ M M' X) ≫ (X ↘ Spec (.of M)) = specAlgebraMap M Ω := by
      rw [Category.assoc, bcπ, ← pullback.condition, ← Category.assoc]
      change (g ≫ (bcX M M' X ↘ Spec (.of M'))) ≫ _ = _
      rw [hg1, specAlgebraMap_comp_specAlgebraMap]
    rw [← hgc, Category.assoc, fromSpecResidueField_comp_structure M, ← Spec.map_comp,
      specAlgebraMap] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  let σ : ResEmb M Ω X (bcπ M M' X t) := ⟨ρ.hom, fun r ↦ RingHom.congr_fun hρ r⟩
  -- `σ` takes values in `M'`
  have hσ : ∀ a, ρ.hom a ∈ (algebraMap M' Ω).range := fun a ↦ hK σ a
  let e : M' ≃+* (algebraMap M' Ω).range := RingEquiv.ofBijective (algebraMap M' Ω).rangeRestrict
    ⟨fun a b hab ↦ (algebraMap M' Ω).injective (congrArg Subtype.val hab),
      (algebraMap M' Ω).rangeRestrict_surjective⟩
  let σ' : X.residueField (bcπ M M' X t) →+* M' :=
    e.symm.toRingHom.comp (ρ.hom.codRestrict _ hσ)
  have hσ' : ∀ a, algebraMap M' Ω (σ' a) = ρ.hom a := fun a ↦
    congrArg Subtype.val (e.apply_symm_apply (ρ.hom.codRestrict _ hσ a))
  have hσ'M : σ'.comp (algebraMap M (X.residueField (bcπ M M' X t))) = algebraMap M M' := by
    ext r
    apply (algebraMap M' Ω).injective
    rw [RingHom.comp_apply, hσ', ← IsScalarTower.algebraMap_apply M M' Ω]
    exact RingHom.congr_fun hρ r
  -- the section `s : Spec M' ⟶ X_{M'}` through `t`
  let s : Spec (.of M') ⟶ bcX M M' X :=
    pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom σ') ≫ X.fromSpecResidueField _) (by
      rw [Category.id_comp, Category.assoc, fromSpecResidueField_comp_structure M,
        ← Spec.map_comp, specAlgebraMap]
      congr 1
      ext r
      exact (RingHom.congr_fun hσ'M r).symm)
  have hs : s ≫ (bcX M M' X ↘ Spec (.of M')) = 𝟙 _ := pullback.lift_fst _ _ _
  have hgs : specAlgebraMap M' Ω ≫ s = g := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      change specAlgebraMap M' Ω ≫ s ≫ (bcX M M' X ↘ Spec (.of M')) = _
      rw [hs, Category.comp_id]
      exact hg1.symm
    · rw [Category.assoc, pullback.lift_snd]
      change _ = g ≫ bcπ M M' X
      rw [← hgc, ← Category.assoc, specAlgebraMap, ← Spec.map_comp]
      congr 2
      ext a
      exact hσ' a
  have ht : s (specAlgebraMap M' Ω (IsLocalRing.closedPoint Ω)) = t := by
    rw [← Scheme.Hom.comp_apply, hgs]
    exact hgt
  rw [← ht]
  exact isIso_residueFieldMap_of_comp_eq_id s _ hs _

end Rational

section FinSub

variable (M Ω : Type u) [Field M] [Field Ω] [Algebra M Ω] {X : Scheme.{u}}
  [X.Over (Spec (.of M))]

/-- For a finite set `S` of closed points of a scheme locally of finite type over `M`, some finite
subextension of `Ω / M` contains the images of all `M`-embeddings `κ(x) → Ω`, `x ∈ S`. -/
theorem exists_finSub_resEmb [LocallyOfFiniteType (X ↘ Spec (.of M))] (S : Set X)
    (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed {x}) :
    ∃ K₀ : FinSub M Ω, ∀ x ∈ S, ∀ (σ : ResEmb M Ω X x) a, σ a ∈ K₀.1 := by
  classical
  haveI := hS.to_subtype
  haveI hfin : ∀ x : S, Finite (ResEmb M Ω X x.1) := fun x ↦ by
    letI := Anabelian.residueFieldAlgebra M X x.1
    haveI := finite_residueField M (hcl x.1 x.2)
    infer_instance
  let F : (Σ x : S, ResEmb M Ω X x.1) → IntermediateField M Ω := fun i ↦
    letI := Anabelian.residueFieldAlgebra M X i.1.1
    i.2.fieldRange
  haveI : ∀ i, FiniteDimensional M (F i) := fun i ↦ by
    letI := Anabelian.residueFieldAlgebra M X i.1.1
    haveI := finite_residueField M (hcl i.1.1 i.1.2)
    exact (AlgEquiv.ofInjectiveField i.2).toLinearEquiv.finiteDimensional
  refine ⟨⟨⨆ i, F i, inferInstance⟩, fun x hx σ a ↦ ?_⟩
  exact le_iSup F ⟨⟨x, hx⟩, σ⟩ ⟨a, rfl⟩

/-- A finite subextension of `Ω / M` containing the images of all `M`-embeddings `κ(x) → Ω` for
the closed points `x` of a finite set `S` (`exists_finSub_resEmb`; `⊥` if `S` is infinite). -/
def ratFinSub [LocallyOfFiniteType (X ↘ Spec (.of M))] (S : Set X) : FinSub M Ω :=
  haveI : Decidable ({x ∈ S | IsClosed {x}}).Finite := Classical.propDecidable _
  if h : ({x ∈ S | IsClosed {x}}).Finite then
    (exists_finSub_resEmb M Ω _ h fun _ hx ↦ hx.2).choose
  else Classical.arbitrary _

lemma mem_ratFinSub [LocallyOfFiniteType (X ↘ Spec (.of M))] {S : Set X} (hS : S.Finite)
    {x : X} (hx : x ∈ S) (hcl : IsClosed {x}) (σ : ResEmb M Ω X x) (a) :
    σ a ∈ (ratFinSub M Ω S).1 := by
  have h : ({x ∈ S | IsClosed {x}}).Finite := hS.subset fun _ hy ↦ hy.1
  rw [ratFinSub, dif_pos h]
  exact (exists_finSub_resEmb M Ω _ h fun _ hx ↦ hx.2).choose_spec x ⟨hx, hcl⟩ σ a

end FinSub

end CurvesJacobian.Cusp
