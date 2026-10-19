/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicFFieldExt
import Belyi.SpecFiniteTypeLimit

/-!
# Finitely many translates over `k̄`

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `π = curveToP1 k C`, and
`Ω ⊇ k` an algebraically closed field. The Jacobian `J_Ω` of `C_Ω` represents
`Pic⁰_{C/k,σ}` on `(Sch/Ω)` (`jacobianBCRepresentableBy`). For a class `c ∈ Pic_{C/k,σ}(Ω)` the
points of `J_Ω` whose translate by `c` lies in `F` form an open `U_c` (`F ⊆ Pic` is open), and by
`exists_picF_translate_ext` the `U_c` with `c ∈ ptSubgroup` cover `J_Ω`. As `J_Ω` is proper over
`Ω`, finitely many of them suffice (`exists_finset_translates`). This is the finiteness input of
the descent of the Jacobian to a finite extension of `k` (JAC R1).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Function

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi Scheme.OpenSubfunctor

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "sΩ" => specAlgebraMap (k₀ := k) Ω

section Cover

/-- The Jacobian `J_Ω` of `C_Ω`, representing `Pic⁰_{C/k,σ}` on `(Sch/Ω)`. -/
abbrev jacOmega : Over (Spec (CommRingCat.of Ω)) :=
  Jacobian (pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) Ω))
    (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)

/-- The universal point of `Pic⁰_{C/k,σ}` over `J_Ω`. -/
abbrev jacOmegaUniv : picZeroGrp (curveToP1 k C) σ hσ ((jacOmega C σ hσ Ω).hom ≫ sΩ) :=
  (jacobianBCRepresentableBy C σ hσ Ω).homEquiv (𝟙 _)

/-- The universal point, as an element of `Pic_{C/k,σ}(J_Ω)`. -/
abbrev jacOmegaUnivG : (G).obj (op (Over.mk ((jacOmega C σ hσ Ω).hom ≫ sΩ))) :=
  (jacOmegaUniv C σ hσ Ω).1

/-- The translate by `c ∈ Pic_{C/k,σ}(Ω)` of the universal point, as a point of `Pic_{C/k,σ}`
over `J_Ω`. -/
def univTranslate (c : (G).obj (op (Over.mk sΩ))) :
    (sigmaG G).obj (op (jacOmega C σ hσ Ω).left) :=
  ⟨(jacOmega C σ hσ Ω).hom ≫ sΩ,
    ((G).map (Over.homMk (jacOmega C σ hσ Ω).hom rfl :
      Over.mk ((jacOmega C σ hσ Ω).hom ≫ sΩ) ⟶ Over.mk sΩ).op).hom c +
      jacOmegaUnivG C σ hσ Ω⟩

lemma exists_opens_univTranslate (c : (G).obj (op (Over.mk sΩ))) :
    ∃ U : (jacOmega C σ hσ Ω).left.Opens, ∀ (T' : Scheme.{u}) (h : T' ⟶ (jacOmega C σ hσ Ω).left),
      picF σ hσ (curveToP1 k C) T' ((sigmaG G).map h.op (univTranslate C σ hσ Ω c)) ↔
        Set.range h ⊆ U :=
  exists_opens_of_isAffine
    (isLocalPredicate_picF σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ))
    (picF_open σ hσ (curveToP1 k C)) (univTranslate C σ hσ Ω c)

/-- The open `U_c ⊆ J_Ω` of points whose translate by `c` lies in `F`. -/
def translateOpens (c : (G).obj (op (Over.mk sΩ))) : (jacOmega C σ hσ Ω).left.Opens :=
  (exists_opens_univTranslate C σ hσ Ω c).choose

lemma translateOpens_spec (c : (G).obj (op (Over.mk sΩ))) (T' : Scheme.{u})
    (h : T' ⟶ (jacOmega C σ hσ Ω).left) :
    picF σ hσ (curveToP1 k C) T' ((sigmaG G).map h.op (univTranslate C σ hσ Ω c)) ↔
      Set.range h ⊆ translateOpens C σ hσ Ω c :=
  (exists_opens_univTranslate C σ hσ Ω c).choose_spec T' h

/-- The pullback of the translated universal point along `b : T ⟶ J_Ω`. -/
lemma map_univTranslate {T : Scheme.{u}} (b : T ⟶ (jacOmega C σ hσ Ω).left)
    (c : (G).obj (op (Over.mk sΩ))) :
    (sigmaG G).map b.op (univTranslate C σ hσ Ω c) =
      ⟨b ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ,
        ((G).map (Over.homMk (b ≫ (jacOmega C σ hσ Ω).hom) (Category.assoc _ _ _) :
          Over.mk (b ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ) ⟶ Over.mk sΩ).op).hom c +
        ((G).map (Over.homMk b rfl : Over.mk (b ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ) ⟶
          Over.mk ((jacOmega C σ hσ Ω).hom ≫ sΩ)).op).hom (jacOmegaUnivG C σ hσ Ω)⟩ := by
  rw [univTranslate, sigmaG_map_mk, map_add, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp]
  rfl

/-- **The `U_c`, `c ∈ ptSubgroup`, cover `J_Ω`** (by `exists_picF_translate_ext` at the
residue fields). -/
lemma exists_mem_translateOpens (t : (jacOmega C σ hσ Ω).left) :
    ∃ c ∈ ptSubgroup C σ hσ Ω, t ∈ translateOpens C σ hσ Ω c := by
  let K := (jacOmega C σ hσ Ω).left.residueField t
  let f := (jacOmega C σ hσ Ω).left.fromSpecResidueField t
  obtain ⟨c, hc, hF⟩ := exists_picF_translate_ext C (curveToP1 k C) σ hσ Ω K
    (Field.toIsField _) (f ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ) (f ≫ (jacOmega C σ hσ Ω).hom)
    (Category.assoc _ _ _)
    (((G).map (Over.homMk f rfl : Over.mk (f ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ) ⟶
      Over.mk ((jacOmega C σ hσ Ω).hom ≫ sΩ)).op).hom (jacOmegaUnivG C σ hσ Ω))
  refine ⟨c, hc, ?_⟩
  have h1 := (translateOpens_spec C σ hσ Ω c (Spec K) f).1 (by
    rw [map_univTranslate]
    exact hF)
  rw [Scheme.range_fromSpecResidueField] at h1
  exact h1 (Set.mem_singleton _)

instance : CompactSpace (jacOmega C σ hσ Ω).left :=
  QuasiCompact.compactSpace_of_compactSpace (jacOmega C σ hσ Ω).hom

/-- **Finitely many translates suffice**: there is a finite set `s ⊆ ptSubgroup` such that every
field valued point of `J_Ω` has a translate by some `c ∈ s` in `F`. -/
theorem exists_finset_translates :
    ∃ s : Finset (ptSubgroup C σ hσ Ω), ∀ (K : CommRingCat.{u}) (_ : IsField K)
      (b : Spec K ⟶ (jacOmega C σ hσ Ω).left), ∃ c ∈ s,
        picF σ hσ (curveToP1 k C) (Spec K) ((sigmaG G).map b.op
          (univTranslate C σ hσ Ω (c : (G).obj (op (Over.mk sΩ))))) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun c : ptSubgroup C σ hσ Ω ↦ (translateOpens C σ hσ Ω c : Set (jacOmega C σ hσ Ω).left))
    (fun c ↦ (translateOpens C σ hσ Ω c).isOpen) (fun t _ ↦ by
      obtain ⟨c, hc, ht⟩ := exists_mem_translateOpens C σ hσ Ω t
      exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, ht⟩)
  refine ⟨s, fun K hK b ↦ ?_⟩
  letI := hK.toField
  haveI : Subsingleton (Spec K) :=
    have : Subsingleton (PrimeSpectrum K) := inferInstance
    this
  obtain ⟨p⟩ : Nonempty (Spec K) := inferInstance
  obtain ⟨c, hcs, hc⟩ : ∃ c ∈ s, b p ∈ translateOpens C σ hσ Ω c := by
    have := hs (Set.mem_univ (b p))
    simpa using this
  refine ⟨c, hcs, (translateOpens_spec C σ hσ Ω c (Spec K) b).2 ?_⟩
  rintro _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

/-- `exists_finset_translates` in the form used for the descent: every degree `0` point over a
field `K ⊇ Ω` has a translate by some `c ∈ s` (pulled back to `K`) in `F`. -/
theorem exists_finset_translates' :
    ∃ s : Finset (ptSubgroup C σ hσ Ω), ∀ (K : CommRingCat.{u}) (_ : IsField K)
      (j : Spec K ⟶ SΩ) (z : (G).obj (op (Over.mk (j ≫ sΩ))))
      (_ : picDeg σ hσ (curveToP1 k C) 0 (Spec K) ⟨j ≫ sΩ, z⟩), ∃ c ∈ s,
        picF σ hσ (curveToP1 k C) (Spec K) ⟨j ≫ sΩ,
          ((G).map (Over.homMk j rfl : Over.mk (j ≫ sΩ) ⟶ Over.mk sΩ).op).hom
            (c : (G).obj (op (Over.mk sΩ))) + z⟩ := by
  obtain ⟨s, hs⟩ := exists_finset_translates C σ hσ Ω
  refine ⟨s, fun K hK j z hz ↦ ?_⟩
  let R := jacobianBCRepresentableBy C σ hσ Ω
  let b : Over.mk j ⟶ jacOmega C σ hσ Ω := R.homEquiv.symm ⟨z, hz⟩
  let bl : Spec K ⟶ (jacOmega C σ hσ Ω).left := b.left
  have hbw : bl ≫ (jacOmega C σ hσ Ω).hom = j := Over.w b
  have hbw2 : bl ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ = j ≫ sΩ := by
    rw [← Category.assoc, hbw]
  have hz' : z = ((G).map (Over.homMk bl hbw2 :
      Over.mk (j ≫ sΩ) ⟶ Over.mk ((jacOmega C σ hσ Ω).hom ≫ sΩ)).op).hom
        (jacOmegaUnivG C σ hσ Ω) := by
    have h1 : R.homEquiv b = ⟨z, hz⟩ := R.homEquiv.apply_symm_apply _
    have h2 := R.homEquiv_comp b (𝟙 _)
    rw [Category.comp_id, h1] at h2
    exact congrArg Subtype.val h2
  obtain ⟨c, hcs, hcF⟩ := hs K hK bl
  refine ⟨c, hcs, ?_⟩
  convert hcF using 1
  rw [map_univTranslate]
  refine (overSigma_mk_eq_iff (G ⋙ forget AddCommGrpCat) hbw2.symm _ _).mpr ?_
  change ((G).map _).hom (((G).map _).hom _ + z) = _
  rw [hz', map_add]
  congr 1
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 3
    exact congrArg Quiver.Hom.op (Over.OverMorphism.ext
      ((Category.id_comp _).trans hbw.symm))
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 3

end Cover

section Finite

variable [Algebra.IsAlgebraic k Ω]

/-- `Spec Ω ⟶ Spec L` for an intermediate field `k ⊆ L ⊆ Ω`. -/
abbrev specIncl (L : IntermediateField k Ω) :
    Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Ω))

omit [PerfectField k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma specIncl_comp (L : IntermediateField k Ω) :
    specIncl Ω L ≫ specAlgebraMap (k₀ := k) L = sΩ := by
  rw [specIncl, specAlgebraMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- `Spec L' ⟶ Spec L` for `L ≤ L'`. -/
abbrev specLE {L L' : IntermediateField k Ω} (h : L ≤ L') :
    Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

omit [PerfectField k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma specIncl_specLE {L L' : IntermediateField k Ω} (h : L ≤ L') :
    specIncl Ω L' ≫ specLE Ω h = specIncl Ω L := by
  rw [specIncl, specLE, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

omit [PerfectField k] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma specLE_comp {L L' : IntermediateField k Ω} (h : L ≤ L') :
    specLE Ω h ≫ specAlgebraMap (k₀ := k) L = specAlgebraMap (k₀ := k) L' := by
  rw [specLE, specAlgebraMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A class `c ∈ Pic_{C/k,σ}(Ω)` is **defined over** `L` if it is pulled back from
`Pic_{C/k,σ}(L)`. -/
def DefinedOver (c : (G).obj (op (Over.mk sΩ))) (L : IntermediateField k Ω) : Prop :=
  ∃ cL : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L))),
    c = ((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma DefinedOver.mono {c : (G).obj (op (Over.mk sΩ))} {L L' : IntermediateField k Ω}
    (hc : DefinedOver C σ hσ Ω c L) (h : L ≤ L') : DefinedOver C σ hσ Ω c L' := by
  obtain ⟨cL, rfl⟩ := hc
  refine ⟨((G).map (Over.homMk (specLE Ω h) (specLE_comp Ω h) :
    Over.mk (specAlgebraMap (k₀ := k) L') ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [show ((Over.homMk (specIncl Ω L') (specIncl_comp Ω L') :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L')) ≫ (Over.homMk (specLE Ω h)
      (specLE_comp Ω h) : Over.mk (specAlgebraMap (k₀ := k) L') ⟶
        Over.mk (specAlgebraMap (k₀ := k) L))) =
        Over.homMk (specIncl Ω L) (specIncl_comp Ω L) from
      Over.OverMorphism.ext (specIncl_specLE Ω h)]

omit [PerfectField k] [IsAlgClosed Ω] in
/-- **`Ω`-points of `C` are defined over finite subextensions**: `C` is locally of finite
presentation over `k` and `Spec Ω` is the limit of the `Spec R`, `R ⊆ Ω` finitely generated
(Stacks, Tag 01ZC; `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), and a finitely
generated subalgebra of the algebraic extension `Ω/k` generates a finite subextension. -/
theorem exists_finite_point (x : SΩ ⟶ C) (hx : x ≫ (C ↘ Sk) = sΩ) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L)
      (xL : Spec (CommRingCat.of L) ⟶ C) (_ : xL ≫ (C ↘ Sk) = specAlgebraMap (k₀ := k) L),
      specIncl Ω L ≫ xL = x := by
  let D := Belyi.SpecLimit.schemeDiagram k Ω
  let t : D ⟶ (Functor.const _).obj Sk :=
    { app R := Spec.map (CommRingCat.ofHom (algebraMap k R.unop.1))
      naturality R R' f := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1 }
  obtain ⟨i, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t
    (C ↘ Sk) (Belyi.SpecLimit.schemeCone k Ω) (Belyi.SpecLimit.isLimitSchemeCone k Ω) x (by
      ext R : 2
      change Spec.map _ ≫ Spec.map _ = x ≫ (C ↘ Sk)
      rw [hx, ← Spec.map_comp]
      congr 1)
  obtain ⟨s, hs, hsR⟩ := Subalgebra.fg_def.mp i.unop.2
  haveI : Finite s := hs
  let L := IntermediateField.adjoin k s
  have hL : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun y _ ↦ Algebra.IsIntegral.isIntegral y
  have hRL : i.unop.1 ≤ L.toSubalgebra := by
    rw [← hsR]
    exact IntermediateField.algebra_adjoin_le_adjoin k s
  let ρ : CommRingCat.of i.unop.1 ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (Subalgebra.inclusion hRL).toRingHom
  refine ⟨L, hL, Spec.map ρ ≫ g, ?_, ?_⟩
  · rw [Category.assoc]
    erw [hg2]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · rw [← hg1, ← Category.assoc, ← Spec.map_comp]
    rfl

omit [IsAlgClosed Ω] in
/-- **Every class of `ptSubgroup` is defined over a finite subextension of `Ω/k`.** -/
theorem exists_definedOver {c : (G).obj (op (Over.mk sΩ))} (hc : c ∈ ptSubgroup C σ hσ Ω) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L), DefinedOver C σ hσ Ω c L := by
  induction hc using AddSubgroup.closure_induction with
  | mem c hc =>
    rcases hc with ⟨c₀, rfl⟩ | ⟨x, hx, rfl⟩
    · refine ⟨⊥, inferInstance, restr G c₀ (specAlgebraMap (k₀ := k) (⊥ : IntermediateField k Ω)),
        ?_⟩
      change ((G).map _).hom c₀ = ((G).map _).hom (((G).map _).hom c₀)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rw [show ((Over.homMk (specIncl Ω ⊥) (specIncl_comp Ω ⊥) : Over.mk sΩ ⟶
          Over.mk (specAlgebraMap (k₀ := k) (⊥ : IntermediateField k Ω))) ≫
          toTop (specAlgebraMap (k₀ := k) (⊥ : IntermediateField k Ω))) = toTop sΩ from
        Over.OverMorphism.ext (specIncl_comp Ω ⊥)]
    · obtain ⟨L, hL, xL, hxL, rfl⟩ := exists_finite_point C Ω x hx
      exact ⟨L, hL, ptClass C σ hσ _ xL hxL,
        (map_ptClass C σ hσ _ xL hxL (specIncl Ω L) sΩ (specIncl_comp Ω L)).symm⟩
  | zero => exact ⟨⊥, inferInstance, 0, (map_zero _).symm⟩
  | add c c' _ _ h h' =>
    obtain ⟨L, hL, cL, rfl⟩ := h
    obtain ⟨L', hL', cL', rfl⟩ := h'
    obtain ⟨d, hd⟩ := DefinedOver.mono C σ hσ Ω ⟨cL, rfl⟩ (le_sup_left : L ≤ L ⊔ L')
    obtain ⟨d', hd'⟩ := DefinedOver.mono C σ hσ Ω ⟨cL', rfl⟩ (le_sup_right : L' ≤ L ⊔ L')
    exact ⟨L ⊔ L', IntermediateField.finiteDimensional_sup L L', d + d', by
      rw [map_add, ← hd, ← hd']⟩
  | neg c _ h =>
    obtain ⟨L, hL, cL, rfl⟩ := h
    exact ⟨L, hL, -cL, (map_neg _ _).symm⟩

end Finite

section Hfield

variable [Algebra.IsAlgebraic k Ω]

omit [C.Over Sk] [PerfectField k] in
lemma id_comp_eq {T : Scheme.{u}} {g₁ g₂ : T ⟶ Sk} (e : g₁ = g₂) : 𝟙 T ≫ g₂ = g₁ := by
  rw [Category.id_comp, e]

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma sigma_transport {T : Scheme.{u}} {g₁ g₂ : T ⟶ Sk} (e : g₁ = g₂)
    (y : (G).obj (op (Over.mk g₂))) :
    (⟨g₁, ((G).map (Over.homMk (𝟙 T) (id_comp_eq e) :
      Over.mk g₁ ⟶ Over.mk g₂).op).hom y⟩ : (sigmaG G).obj (op T)) = ⟨g₂, y⟩ := by
  subst e
  exact Sigma.ext rfl (heq_of_eq (map_homMk_id C σ hσ _ y))

/-- **The hypothesis `hfield` over a finite Galois extension** (JAC R1): there is a finite Galois
subextension `L` of `Ω/k` such that for every field `K` over `L`, every point of
`Pic_{C/k,σ}(K)` has a translate by a class pulled back from `Pic_{C/k,σ}(L)` lying in `F`. -/
theorem exists_finite_hfield :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      ∀ (K : CommRingCat.{u}) (_ : IsField K) (t : Spec K ⟶ Spec (CommRingCat.of L))
        (y : (G).obj (op (Over.mk (t ≫ specAlgebraMap (k₀ := k) L)))),
        ∃ c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L))),
          picF σ hσ (curveToP1 k C) (Spec K) ⟨t ≫ specAlgebraMap (k₀ := k) L,
            ((G).map (Over.homMk t rfl : Over.mk (t ≫ specAlgebraMap (k₀ := k) L) ⟶
              Over.mk (specAlgebraMap (k₀ := k) L)).op).hom c + y⟩ := by
  set π := curveToP1 k C
  obtain ⟨s, hs⟩ := exists_finset_translates' C σ hσ Ω
  obtain ⟨x₁, hx₁, hx₁W⟩ := exists_pt_chart_inf_ext C π Ω
  choose Lc hLc hdef using fun c : s ↦ exists_definedOver C σ hσ Ω c.1.2
  obtain ⟨L₁, hL₁, x₁L, hx₁L, hx₁e⟩ := exists_finite_point C Ω x₁ hx₁
  let L₀ : IntermediateField k Ω := (⨆ c : s, Lc c) ⊔ L₁
  haveI : FiniteDimensional k L₀ := by
    haveI : ∀ c : s, FiniteDimensional k (Lc c) := hLc
    haveI : FiniteDimensional k (⨆ c : s, Lc c : IntermediateField k Ω) :=
      IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_sup _ _
  haveI : Normal k Ω := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  haveI : IsGalois k Ω := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let L := IntermediateField.normalClosure k L₀ Ω
  have hL₀ : L₀ ≤ L := IntermediateField.le_normalClosure L₀
  haveI : FiniteDimensional k L := normalClosure.is_finiteDimensional k L₀ Ω
  haveI : IsGalois k L := IsGalois.normalClosure k L₀ Ω
  refine ⟨L, inferInstance, inferInstance, fun K hK t y ↦ ?_⟩
  let sL := specAlgebraMap (k₀ := k) L
  have hG := isSheaf_picSigmaSch_curve k C σ hσ
  -- the classes of `s` and the point `x₁` over `L`
  have hdefL : ∀ c : s, DefinedOver C σ hσ Ω c.1.1 L := fun c ↦
    (hdef c).mono C σ hσ Ω ((le_iSup Lc c).trans (le_sup_left.trans hL₀))
  have hL₁L : L₁ ≤ L := le_sup_right.trans hL₀
  let x₁' := specLE Ω hL₁L ≫ x₁L
  have hx₁' : x₁' ≫ (C ↘ Sk) = sL := by
    rw [Category.assoc, hx₁L, specLE_comp]
  have hx₁e' : specIncl Ω L ≫ x₁' = x₁ := by
    rw [← Category.assoc, specIncl_specLE, hx₁e]
  haveI : Subsingleton (Spec (CommRingCat.of L)) :=
    have : Subsingleton (PrimeSpectrum L) := inferInstance
    this
  have hx₁'W : ⊤ ≤ x₁' ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)) := by
    intro p _
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    rw [Subsingleton.elim p (specIncl Ω L q)]
    have := hx₁W (show q ∈ (⊤ : (Spec (CommRingCat.of Ω)).Opens) from trivial)
    rw [← hx₁e'] at this
    exact this
  let e₁ := ptClass C σ hσ sL x₁' hx₁'
  -- the field `Ω' = K̄` and the embedding `Ω → Ω'` over `L`
  letI : Field K := hK.toField
  let φ : CommRingCat.of L ⟶ K := Spec.preimage t
  have hφ : Spec.map φ = t := Spec.map_preimage t
  let Ω' := AlgebraicClosure K
  letI : Algebra L Ω' := ((algebraMap K Ω').comp φ.hom).toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := k) L
  haveI : Module.IsTorsionFree L Ω' := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  let ι : Ω →ₐ[L] Ω' := IsAlgClosed.lift
  let h : Spec (CommRingCat.of Ω') ⟶ Spec K := Spec.map (CommRingCat.ofHom (algebraMap K Ω'))
  let j : Spec (CommRingCat.of Ω') ⟶ SΩ := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hjt : j ≫ specIncl Ω L = h ≫ t := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact ι.commutes a
  have hg' : j ≫ sΩ = h ≫ t ≫ sL := by
    rw [← specIncl_comp Ω L, ← Category.assoc, hjt, Category.assoc]
  haveI : Subsingleton (Spec K) :=
    have : Subsingleton (PrimeSpectrum K) := inferInstance
    this
  -- the degree of `y`
  obtain ⟨d, hd⟩ : ∃ d : ℤ, picDeg σ hσ π d (Spec K) ⟨t ≫ sL, y⟩ := by
    obtain ⟨U, hU1, -, hU3⟩ := exists_degree_decomposition σ hσ π hG
      (⟨t ≫ sL, y⟩ : (sigmaG G).obj (op (Spec K)))
    obtain ⟨p⟩ : Nonempty (Spec K) := inferInstance
    have hp : p ∈ ⨆ d, U d := by rw [hU3]; trivial
    obtain ⟨d, hpd⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    refine ⟨d, ?_⟩
    have := (hU1 d (Spec K) (𝟙 _)).2 (by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim ((𝟙 (Spec K) : Spec K ⟶ Spec K) q) p]
      exact hpd)
    rwa [op_id, Functor.map_id_apply] at this
  -- the degree `0` point over `Ω'`, on the base `j ≫ sΩ`
  have hy' : h ≫ t ≫ sL = j ≫ sΩ := hg'.symm
  have hE' : (h ≫ t) ≫ sL = j ≫ sΩ := by rw [Category.assoc, hy']
  let y' : (G).obj (op (Over.mk (j ≫ sΩ))) :=
    ((G).map (Over.homMk h hy' : Over.mk (j ≫ sΩ) ⟶ Over.mk (t ≫ sL)).op).hom y
  let E : (G).obj (op (Over.mk (j ≫ sΩ))) :=
    ((G).map (Over.homMk (h ≫ t) hE' : Over.mk (j ≫ sΩ) ⟶ Over.mk sL).op).hom e₁
  let z₀ : (G).obj (op (Over.mk (j ≫ sΩ))) := y' + -(d • E)
  have key : ∀ {A B D : Over Sk} (f₁ : A ⟶ B) (f₂ : B ⟶ D) (f : A ⟶ D),
      f₁ ≫ f₂ = f → ∀ w : (G).obj (op D),
        ((G).map f₁.op).hom (((G).map f₂.op).hom w) = ((G).map f.op).hom w := by
    intro A B D f₁ f₂ f hf w
    subst hf
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hy'eq : (⟨j ≫ sΩ, y'⟩ : (sigmaG G).obj (op (Spec (CommRingCat.of Ω')))) =
      (sigmaG G).map h.op ⟨t ≫ sL, y⟩ := by
    refine (overSigma_mk_eq_iff (G ⋙ forget AddCommGrpCat) hg' _ _).mpr ?_
    exact key _ _ _ (Over.OverMorphism.ext (Category.id_comp _)) y
  have hz₀ : picDeg σ hσ π 0 (Spec (CommRingCat.of Ω')) ⟨j ≫ sΩ, z₀⟩ := by
    have hd' : picDeg σ hσ π d (Spec (CommRingCat.of Ω')) ⟨j ≫ sΩ, y'⟩ := by
      rw [hy'eq]
      intro T'' _ hF h''
      have := hd T'' hF (h'' ≫ h)
      rwa [← map_map_sigmaG] at this
    have hE := picDeg_one_ptClass C π σ hσ sL x₁' hx₁' hx₁'W (h ≫ t) (j ≫ sΩ) hE'
    have := picDeg_add π σ hσ _ y' _ hd' (picDeg_neg π σ hσ _ _
      (picDeg_zsmul C π σ hσ _ E hE d))
    exact picDeg_congr C π σ hσ rfl (by ring) this
  obtain ⟨⟨c, hcmem⟩, hcs, hcF⟩ := hs (CommRingCat.of Ω') (by exact Field.toIsField Ω') j z₀ hz₀
  obtain ⟨cL, hcL⟩ := hdefL ⟨⟨c, hcmem⟩, hcs⟩
  refine ⟨cL + -(d • e₁), picF_of_map C π σ hσ h _ ?_⟩
  convert hcF using 1
  rw [sigmaG_map_mk]
  refine (overSigma_mk_eq_iff (G ⋙ forget AddCommGrpCat) hy' _ _).mpr ?_
  have e0 : ∀ {A D : Over Sk} (f : A ⟶ D) (w : (G).obj (op D)),
      (ConcreteCategory.hom ((G ⋙ forget AddCommGrpCat).map f.op)) w = ((G).map f.op).hom w :=
    fun _ _ ↦ rfl
  rw [e0, key _ _ (Over.homMk h hy' : Over.mk (j ≫ sΩ) ⟶ Over.mk (t ≫ sL))
    (Over.OverMorphism.ext (Category.id_comp _)), map_add,
    key _ _ (Over.homMk (h ≫ t) hE' : Over.mk (j ≫ sΩ) ⟶ Over.mk sL)
      (Over.OverMorphism.ext rfl)]
  have hcL' : c = ((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL := hcL
  change _ = ((G).map _).hom c + z₀
  rw [hcL', key _ _ (Over.homMk (h ≫ t) hE' : Over.mk (j ≫ sΩ) ⟶ Over.mk sL)
    (Over.OverMorphism.ext hjt), map_add, map_neg, map_zsmul]
  dsimp only [z₀, y', E]
  abel

end Hfield

end CurvesJacobian
