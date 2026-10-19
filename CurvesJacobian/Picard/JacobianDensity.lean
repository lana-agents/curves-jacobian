/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianChart
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Galois-stable charts of `J_k̄` (JAC R2, density part)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `Ω ⊇ k` an algebraic
closure and `J_Ω` the Jacobian of `C_Ω`. Fix an `Ω`-point `a₀` of `W` (`chartPt`) and an affine
open `A ∋ a₀` of `W` (`chartOpenA`). This file shows:

* `CurvesJacobian.exists_definedOver_any`: every class `v ∈ Pic_{C/k,σ}(Ω)` is defined over a
  finite subextension of `Ω/k` (`v + c ∈ F` for some `c ∈ ptSubgroup`, and `Ω`-points of the
  locally finitely presented `W` are defined over finite subextensions);
* `CurvesJacobian.finite_conj`: such a class has finitely many `Aut(Ω/k)`-conjugates;
* **`CurvesJacobian.exists_finset_good`**: there are finitely many classes `c` of degree `g`
  such that every point of `J_Ω` lies in all the charts `V(τ^* c, A)`, `τ ∈ Aut(Ω/k)`, for one
  of them (closed points are `Ω`-points, `J_Ω` is irreducible and Jacobson, and `J_Ω` is
  quasi-compact).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Function

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi Scheme.OpenSubfunctor

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

section XiBase

lemma xiBase_eq : xiBase C σ hσ =
    (opensW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)).ι ≫
      hilbCurveHom k C (genusNat k C) := by
  change (opensW C σ hσ (curveToP1 k C) (isSheaf_picSigmaSch_curve k C σ hσ)).ι ≫
    (xiHilb C σ hσ).1 = _
  rw [xiHilb_fst]

instance : LocallyOfFinitePresentation (xiBase C σ hσ) := by
  rw [xiBase_eq]
  infer_instance

end XiBase

section Points

variable {E : Type u} [Field E] [Algebra k E] {X : Over (Spec (CommRingCat.of E))}
  (R : ((Over.map (specAlgebraMap (k₀ := k) E)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
    forget AddCommGrpCat).RepresentableBy X)

omit [PerfectField k] [IsCurveOver k C] in
lemma ptClassE_w {p : Spec (CommRingCat.of E) ⟶ X.left} (hp : p ≫ X.hom = 𝟙 _) :
    p ≫ X.hom ≫ specAlgebraMap (k₀ := k) E = specAlgebraMap (k₀ := k) E := by
  rw [← Category.assoc, hp, Category.id_comp]

/-- The class of an `E`-point `p` of `X`. -/
def ptClassE (p : Spec (CommRingCat.of E) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))) :=
  ((G).map (Over.homMk p (ptClassE_w hp) :
    Over.mk (specAlgebraMap (k₀ := k) E) ⟶
      Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R)

lemma picDeg_ptClassE (p : Spec (CommRingCat.of E) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    picDeg σ hσ (curveToP1 k C) 0 (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, ptClassE C σ hσ R p hp⟩ := by
  have h0 : picDeg σ hσ (curveToP1 k C) 0 _
      ⟨X.hom ≫ specAlgebraMap (k₀ := k) E, chartUniv C σ hσ R⟩ := (R.homEquiv (𝟙 X)).2
  have := picDeg_map_sigmaG C σ hσ p h0
  rwa [sigmaG_map_mk, sigma_mk_homMk C σ hσ (ptClassE_w hp) p rfl (ptClassE_w hp)] at this

lemma map_ptClassE_chartTranslate (p : Spec (CommRingCat.of E) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) :
    (sigmaG G).map p.op (chartTranslate C σ hσ R c) =
      ⟨specAlgebraMap (k₀ := k) E, c + ptClassE C σ hσ R p hp⟩ := by
  have e : p ≫ X.hom ≫ specAlgebraMap (k₀ := k) E = specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, hp, Category.id_comp]
  rw [map_chartTranslate]
  refine (sigma_mk_homMk_add C σ hσ (T := Spec (CommRingCat.of E)) e (p ≫ X.hom) p
    (Category.assoc _ _ _) (by rw [Category.assoc]; exact e) rfl e c
    (chartUniv C σ hσ R)).trans ?_
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine congrArg (· + ptClassE C σ hσ R p hp) ?_
  rw [mapG_congr_left C σ hσ (f₂ := 𝟙 _) hp, op_id, (G).map_id]
  rfl

/-- **`E`-points of the charts.** -/
lemma range_subset_chartA_iff_pt (p : Spec (CommRingCat.of E) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (c : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E)))) (A : (schW C σ hσ).Opens) :
    Set.range p ⊆ chartA C σ hσ R c A ↔
      InA C σ hσ A _ ⟨specAlgebraMap (k₀ := k) E, c + ptClassE C σ hσ R p hp⟩ := by
  rw [range_subset_chartA_iff, map_ptClassE_chartTranslate C σ hσ R p hp]
  exact Iff.rfl

/-- The `E`-point of `X` with a given class of degree `0`. -/
def ptOfClass (v : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (hv : picDeg σ hσ (curveToP1 k C) 0 (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, v⟩) :
    Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶ X :=
  R.homEquiv.symm (⟨((G).map (Over.homMk (𝟙 (Spec (CommRingCat.of E))) rfl :
      Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (specAlgebraMap (k₀ := k) E)).op).hom v,
    by
      have := picDeg_map_sigmaG C σ hσ (𝟙 (Spec (CommRingCat.of E))) hv
      rwa [sigmaG_map_mk] at this⟩ :
    picZeroGrp (curveToP1 k C) σ hσ (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E))

lemma ptOfClass_w (v : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (hv : picDeg σ hσ (curveToP1 k C) 0 (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, v⟩) :
    (ptOfClass C σ hσ R v hv).left ≫ X.hom = 𝟙 _ :=
  Over.w (ptOfClass C σ hσ R v hv)

lemma ptClassE_ptOfClass (v : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) E))))
    (hv : picDeg σ hσ (curveToP1 k C) 0 (Spec (CommRingCat.of E))
      ⟨specAlgebraMap (k₀ := k) E, v⟩) :
    ptClassE C σ hσ R (ptOfClass C σ hσ R v hv).left (ptOfClass_w C σ hσ R v hv) = v := by
  have w' : (ptOfClass C σ hσ R v hv).left ≫ X.hom ≫ specAlgebraMap (k₀ := k) E =
      𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E := by
    rw [← Category.assoc, ptOfClass_w]
    rfl
  have e : (Over.homMk (ptOfClass C σ hσ R v hv).left (ptOfClass_w C σ hσ R v hv) :
      Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶ X) = ptOfClass C σ hσ R v hv :=
    Over.OverMorphism.ext rfl
  have h1 : ((G).map (Over.homMk (ptOfClass C σ hσ R v hv).left w' :
      Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E) ⟶
        Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E)).op).hom (chartUniv C σ hσ R) =
      ((G).map (Over.homMk (𝟙 (Spec (CommRingCat.of E))) rfl :
        Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (specAlgebraMap (k₀ := k) E)).op).hom v := by
    rw [← homEquiv_homMk_val C σ hσ R _ (𝟙 _) (ptOfClass_w C σ hσ R v hv) w', e, ptOfClass,
      Equiv.apply_symm_apply]
  have h2 := congrArg ((G).map (Over.homMk (𝟙 (Spec (CommRingCat.of E)))
    ((Category.id_comp _).trans (Category.id_comp _)) :
    Over.mk (specAlgebraMap (k₀ := k) E) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E)).op).hom h1
  unfold ptClassE
  refine Eq.trans ?_ (h2.trans ?_)
  · exact (mapG_mapG_eq C σ hσ (Over.homMk (𝟙 (Spec (CommRingCat.of E)))
      ((Category.id_comp _).trans (Category.id_comp _)) :
        Over.mk (specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E))
      (Over.homMk (ptOfClass C σ hσ R v hv).left w' :
        Over.mk (𝟙 (Spec (CommRingCat.of E)) ≫ specAlgebraMap (k₀ := k) E) ⟶
          Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) E))
      (Over.homMk (ptOfClass C σ hσ R v hv).left (ptClassE_w (ptOfClass_w C σ hσ R v hv)))
      (Category.id_comp _) _).symm
  · exact (mapG_mapG_eq C σ hσ _ _ (𝟙 _) (Category.comp_id _) _).trans
      (by rw [op_id, (G).map_id]; rfl)

end Points

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "sΩ" => specAlgebraMap (k₀ := k) Ω

section Finite

variable [Algebra.IsAlgebraic k Ω]

omit [PerfectField k] [IsAlgClosed Ω] in
/-- `Ω`-points of a locally finitely presented `k`-scheme are defined over finite
subextensions of `Ω/k` (as `exists_finite_point`). -/
theorem exists_finite_point_of_lfp {Y : Scheme.{u}} (q : Y ⟶ Sk)
    [LocallyOfFinitePresentation q] (x : SΩ ⟶ Y) (hx : x ≫ q = sΩ) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L)
      (xL : Spec (CommRingCat.of L) ⟶ Y) (_ : xL ≫ q = specAlgebraMap (k₀ := k) L),
      specIncl Ω L ≫ xL = x := by
  let D := Belyi.SpecLimit.schemeDiagram k Ω
  let t : D ⟶ (Functor.const _).obj Sk :=
    { app R := Spec.map (CommRingCat.ofHom (algebraMap k R.unop.1))
      naturality R R' f := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1 }
  obtain ⟨i, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t
    q (Belyi.SpecLimit.schemeCone k Ω) (Belyi.SpecLimit.isLimitSchemeCone k Ω) x (by
      ext R : 2
      change Spec.map _ ≫ Spec.map _ = x ≫ q
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

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
lemma DefinedOver.sub {c c' : (G).obj (op (Over.mk sΩ))} {L L' : IntermediateField k Ω}
    (hc : DefinedOver C σ hσ Ω c L) (hc' : DefinedOver C σ hσ Ω c' L') :
    DefinedOver C σ hσ Ω (c - c') (L ⊔ L') := by
  obtain ⟨d, hd⟩ := hc.mono C σ hσ Ω (le_sup_left : L ≤ L ⊔ L')
  obtain ⟨d', hd'⟩ := hc'.mono C σ hσ Ω (le_sup_right : L' ≤ L ⊔ L')
  exact ⟨d - d', by rw [map_sub, ← hd, ← hd']⟩

/-- **Every class over `Ω` is defined over a finite subextension of `Ω/k`.** -/
theorem exists_definedOver_any (v : (G).obj (op (Over.mk sΩ))) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L), DefinedOver C σ hσ Ω v L := by
  obtain ⟨c, hc, hF⟩ := exists_picF_translate_ext C (curveToP1 k C) σ hσ Ω (CommRingCat.of Ω)
    (Field.toIsField Ω) sΩ (𝟙 _) (Category.id_comp _) v
  rw [map_homMk_id C σ hσ] at hF
  obtain ⟨a, ha⟩ := (picF_iff_exists_xiWk C σ hσ _).1 hF
  have hab : a ≫ xiBase C σ hσ = sΩ := congrArg Sigma.fst ha
  obtain ⟨L, hL, aL, haL, rfl⟩ := exists_finite_point_of_lfp Ω (xiBase C σ hσ) a hab
  obtain ⟨L', hL', hc'⟩ := exists_definedOver C σ hσ Ω hc
  have hdef : DefinedOver C σ hσ Ω (c + v) L := by
    refine ⟨((G).map (Over.homMk aL haL : Over.mk (specAlgebraMap (k₀ := k) L) ⟶
      Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2, ?_⟩
    have e1 : (sigmaG G).map aL.op (xiWk C σ hσ) = ⟨specAlgebraMap (k₀ := k) L,
        ((G).map (Over.homMk aL haL : Over.mk (specAlgebraMap (k₀ := k) L) ⟶
          Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2⟩ :=
      sigma_mk_homMk C σ hσ haL aL rfl haL _
    rw [← map_map_sigmaG, e1, sigmaG_map_mk,
      sigma_mk_homMk C σ hσ (specIncl_comp Ω L) _ rfl (specIncl_comp Ω L)] at ha
    exact (eq_of_heq (Sigma.mk.inj_iff.mp ha).2).symm
  have := hdef.sub C σ hσ Ω hc'
  rw [add_sub_cancel_left] at this
  exact ⟨L ⊔ L', IntermediateField.finiteDimensional_sup L L', this⟩

end Finite

section Conj

variable {Ω}

omit [PerfectField k] [IsAlgClosed Ω] in
lemma specAut_comp_sΩ (τ : Ω ≃ₐ[k] Ω) : specAut τ ≫ sΩ = sΩ :=
  specAut_comp_specMapAlg τ

/-- The conjugate `τ^* v` of a class over `Ω`, `τ ∈ Aut(Ω/k)`. -/
abbrev conjΩ (τ : Ω ≃ₐ[k] Ω) (v : (G).obj (op (Over.mk sΩ))) : (G).obj (op (Over.mk sΩ)) :=
  conjClass C σ hσ (specAut_comp_sΩ τ) v

/-- `Spec(e) : Spec L ⟶ Spec L` for an automorphism `e` of an intermediate field `L`. -/
abbrev specGalI {L : IntermediateField k Ω} (e : L ≃ₐ[k] L) :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (e : L →+* L))

omit [PerfectField k] [IsAlgClosed Ω] in
lemma specGalI_comp {L : IntermediateField k Ω} (e : L ≃ₐ[k] L) :
    specGalI e ≫ specAlgebraMap (k₀ := k) L = specAlgebraMap (k₀ := k) L := by
  rw [specGalI, specAlgebraMap, ← Spec.map_comp]
  congr 1
  ext r
  exact congrArg Subtype.val (e.commutes r)

omit [PerfectField k] [IsAlgClosed Ω] in
lemma specAut_specIncl (L : IntermediateField k Ω) [Normal k L] (τ : Ω ≃ₐ[k] Ω) :
    specAut τ ≫ specIncl Ω L = specIncl Ω L ≫ specGalI (τ.restrictNormal L) := by
  rw [specAut, specIncl, specGalI, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (AlgEquiv.restrictNormal_commutes τ L x).symm

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] in
lemma conjΩ_specIncl (L : IntermediateField k Ω) [Normal k L] (τ : Ω ≃ₐ[k] Ω)
    (cL : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L)))) :
    conjΩ C σ hσ τ (((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL) =
      ((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
        Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom
        (((G).map (Over.homMk (specGalI (τ.restrictNormal L)) (specGalI_comp _) :
          Over.mk (specAlgebraMap (k₀ := k) L) ⟶
            Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL) := by
  dsimp only [conjΩ, conjClass]
  refine (mapG_mapG_eq C σ hσ (Over.homMk (specAut τ) (specAut_comp_sΩ τ) :
    Over.mk sΩ ⟶ Over.mk sΩ) (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)) (Over.homMk (specAut τ ≫ specIncl Ω L)
    ((Category.assoc _ _ _).trans ((congrArg (specAut τ ≫ ·) (specIncl_comp Ω L)).trans
      (specAut_comp_sΩ τ)))) rfl _).trans ?_
  refine Eq.trans ?_ (mapG_mapG_eq C σ hσ (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L))
    (Over.homMk (specGalI (τ.restrictNormal L)) (specGalI_comp _) :
      Over.mk (specAlgebraMap (k₀ := k) L) ⟶ Over.mk (specAlgebraMap (k₀ := k) L))
    (Over.homMk (specIncl Ω L ≫
    specGalI (τ.restrictNormal L)) ((Category.assoc _ _ _).trans
      ((congrArg (specIncl Ω L ≫ ·) (specGalI_comp _)).trans (specIncl_comp Ω L)))) rfl _).symm
  exact mapG_congr_left C σ hσ (specAut_specIncl L τ) _

variable [Algebra.IsAlgebraic k Ω]

/-- **A class over `Ω` has finitely many `Aut(Ω/k)`-conjugates.** -/
theorem finite_conj (v : (G).obj (op (Over.mk sΩ))) :
    (Set.range fun τ : Ω ≃ₐ[k] Ω ↦ conjΩ C σ hσ τ v).Finite := by
  obtain ⟨L₀, hL₀, hv⟩ := exists_definedOver_any C σ hσ Ω v
  haveI : Normal k Ω := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  haveI : IsGalois k Ω := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let L := IntermediateField.normalClosure k L₀ Ω
  haveI : FiniteDimensional k L := normalClosure.is_finiteDimensional k L₀ Ω
  haveI : IsGalois k L := IsGalois.normalClosure k L₀ Ω
  obtain ⟨cL, rfl⟩ := hv.mono C σ hσ Ω (IntermediateField.le_normalClosure L₀)
  refine (Set.finite_range fun e : L ≃ₐ[k] L ↦
    ((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom
      (((G).map (Over.homMk (specGalI e) (specGalI_comp _) :
        Over.mk (specAlgebraMap (k₀ := k) L) ⟶
          Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL)).subset ?_
  rintro _ ⟨τ, rfl⟩
  exact ⟨τ.restrictNormal L, (conjΩ_specIncl C σ hσ L τ cL).symm⟩

end Conj

section Cover

local instance : Subsingleton SΩ :=
  have : Subsingleton (PrimeSpectrum Ω) := inferInstance
  this

local instance : Nonempty SΩ :=
  have : Nonempty (PrimeSpectrum Ω) := inferInstance
  this

instance : IrreducibleSpace (jacOmega C σ hσ Ω).left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (jacOmega C σ hσ Ω).hom

instance : JacobsonSpace (jacOmega C σ hσ Ω).left :=
  LocallyOfFiniteType.jacobsonSpace (jacOmega C σ hσ Ω).hom

lemma exists_chartPt : ∃ a : SΩ ⟶ schW C σ hσ, a ≫ xiBase C σ hσ = sΩ := by
  obtain ⟨c, -, hF⟩ := exists_picF_translate_ext C (curveToP1 k C) σ hσ Ω (CommRingCat.of Ω)
    (Field.toIsField Ω) sΩ (𝟙 _) (Category.id_comp _) 0
  obtain ⟨a, ha⟩ := (picF_iff_exists_xiWk C σ hσ _).1 hF
  exact ⟨a, congrArg Sigma.fst ha⟩

/-- A fixed `Ω`-point `a₀` of `W`. -/
def chartPt : SΩ ⟶ schW C σ hσ := (exists_chartPt C σ hσ Ω).choose

lemma chartPt_w : chartPt C σ hσ Ω ≫ xiBase C σ hσ = sΩ := (exists_chartPt C σ hσ Ω).choose_spec

lemma exists_chartOpenA : ∃ A : (schW C σ hσ).Opens, IsAffineOpen A ∧
    Set.range (chartPt C σ hσ Ω) ⊆ A := by
  obtain ⟨p⟩ : Nonempty SΩ := inferInstance
  obtain ⟨A, hA, hpA, -⟩ := exists_isAffineOpen_mem_and_subset (x := chartPt C σ hσ Ω p)
    (U := ⊤) trivial
  refine ⟨A, hA, ?_⟩
  rintro _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

/-- **The fixed affine open `A ∋ a₀` of `W`.** -/
def chartOpenA : (schW C σ hσ).Opens := (exists_chartOpenA C σ hσ Ω).choose

lemma isAffineOpen_chartOpenA : IsAffineOpen (chartOpenA C σ hσ Ω) :=
  (exists_chartOpenA C σ hσ Ω).choose_spec.1

/-- The class `ζ = ξ|_{a₀}` of degree `g`. -/
def zetaΩ : (G).obj (op (Over.mk sΩ)) :=
  ((G).map (Over.homMk (chartPt C σ hσ Ω) (chartPt_w C σ hσ Ω) :
    Over.mk sΩ ⟶ Over.mk (xiBase C σ hσ)).op).hom (xiWk C σ hσ).2

lemma map_chartPt_xiWk : (sigmaG G).map (chartPt C σ hσ Ω).op (xiWk C σ hσ) =
    ⟨sΩ, zetaΩ C σ hσ Ω⟩ :=
  sigma_mk_homMk C σ hσ (chartPt_w C σ hσ Ω) _ rfl _ _

lemma inA_zetaΩ : InA C σ hσ (chartOpenA C σ hσ Ω) SΩ ⟨sΩ, zetaΩ C σ hσ Ω⟩ :=
  ⟨chartPt C σ hσ Ω, (exists_chartOpenA C σ hσ Ω).choose_spec.2, map_chartPt_xiWk C σ hσ Ω⟩

lemma picDeg_zetaΩ : picDeg σ hσ (curveToP1 k C) (genusNat k C) SΩ ⟨sΩ, zetaΩ C σ hσ Ω⟩ := by
  have := picDeg_map_sigmaG C σ hσ (chartPt C σ hσ Ω) (picDeg_xiWk C σ hσ)
  rwa [map_chartPt_xiWk] at this

variable {Ω}

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] in
lemma conjΩ_add (τ : Ω ≃ₐ[k] Ω) (v w : (G).obj (op (Over.mk sΩ))) :
    conjΩ C σ hσ τ (v + w) = conjΩ C σ hσ τ v + conjΩ C σ hσ τ w :=
  map_add _ _ _

omit [PerfectField k] [IsCurveOver k C] [IsAlgClosed Ω] in
lemma conjΩ_conjΩ_symm (τ : Ω ≃ₐ[k] Ω) (w : (G).obj (op (Over.mk sΩ))) :
    conjΩ C σ hσ τ (conjΩ C σ hσ τ.symm w) = w := by
  dsimp only [conjΩ, conjClass]
  refine (mapG_mapG_eq C σ hσ (Over.homMk (specAut τ) (specAut_comp_sΩ τ) :
    Over.mk sΩ ⟶ Over.mk sΩ) (Over.homMk (specAut τ.symm) (specAut_comp_sΩ τ.symm) :
      Over.mk sΩ ⟶ Over.mk sΩ) (𝟙 _) ?_ _).trans (by rw [op_id, (G).map_id]; rfl)
  change specAut τ ≫ specAut τ.symm = 𝟙 _
  rw [specAut, specAut, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact τ.apply_symm_apply x

omit [IsAlgClosed Ω] in
lemma InA.conjΩ {A : (schW C σ hσ).Opens} {y : (G).obj (op (Over.mk sΩ))} (τ : Ω ≃ₐ[k] Ω)
    (h : InA C σ hσ A SΩ ⟨sΩ, y⟩) : InA C σ hσ A SΩ ⟨sΩ, conjΩ C σ hσ τ y⟩ := by
  have := h.map C σ hσ (specAut τ)
  rwa [sigmaG_map_mk, sigma_mk_homMk C σ hσ (specAut_comp_sΩ τ) _ rfl (specAut_comp_sΩ τ)] at this

omit [PerfectField k] [IsCurveOver k C] in
lemma nonempty_biInter_finset {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] {ι : Type*}
    (s : Finset ι) {U : ι → Set Y} (hU : ∀ i ∈ s, IsOpen (U i)) (hne : ∀ i ∈ s, (U i).Nonempty) :
    (⋂ i ∈ s, U i).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact nonempty_preirreducible_inter (hU a (Finset.mem_insert_self a s))
      (isOpen_biInter_finset fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
      (hne a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hne i (Finset.mem_insert_of_mem hi)))

variable (Ω) [Algebra.IsAlgebraic k Ω]

/-- **Closed points of `J_Ω` lie in all conjugates of one chart.** -/
theorem exists_good_closed (z : (jacOmega C σ hσ Ω).left) (hz : IsClosed {z}) :
    ∃ c : (G).obj (op (Over.mk sΩ)), picDeg σ hσ (curveToP1 k C) (genusNat k C) SΩ ⟨sΩ, c⟩ ∧
      ∀ τ : Ω ≃ₐ[k] Ω, z ∈ chartA C σ hσ (jacobianBCRepresentableBy C σ hσ Ω)
        (conjΩ C σ hσ τ c) (chartOpenA C σ hσ Ω) := by
  set R := jacobianBCRepresentableBy C σ hσ Ω
  set A := chartOpenA C σ hσ Ω
  have hp₀ := pointOfClosedPoint_comp (jacOmega C σ hσ Ω).hom z hz
  set p₀ := pointOfClosedPoint (jacOmega C σ hσ Ω).hom z hz
  set w := ptClassE C σ hσ R p₀ hp₀
  have hw : picDeg σ hσ (curveToP1 k C) 0 SΩ ⟨sΩ, w⟩ := picDeg_ptClassE C σ hσ R p₀ hp₀
  have hT := finite_conj C σ hσ w
  have hO : (⋂ v ∈ hT.toFinset, (chartA C σ hσ R (zetaΩ C σ hσ Ω + v) A :
      Set (jacOmega C σ hσ Ω).left)).Nonempty := by
    refine nonempty_biInter_finset _ (fun v _ ↦ (chartA C σ hσ R _ A).isOpen) fun v hv ↦ ?_
    obtain ⟨τ, rfl⟩ := (Set.Finite.mem_toFinset _).1 hv
    have hv0 : picDeg σ hσ (curveToP1 k C) 0 SΩ ⟨sΩ, -conjΩ C σ hσ τ w⟩ :=
      picDeg_congr C (curveToP1 k C) σ hσ rfl neg_zero (picDeg_neg (curveToP1 k C) σ hσ _ _
        (picDeg_conjClass C σ hσ (specAut_comp_sΩ τ) w hw))
    obtain ⟨q⟩ : Nonempty SΩ := inferInstance
    refine ⟨(ptOfClass C σ hσ R _ hv0).left q, ?_⟩
    refine (range_subset_chartA_iff_pt C σ hσ R _ (ptOfClass_w C σ hσ R _ hv0) _ A).2 ?_
      ⟨q, rfl⟩
    rw [ptClassE_ptOfClass, add_neg_cancel_right]
    exact inA_zetaΩ C σ hσ Ω
  obtain ⟨u, huO, hu⟩ := nonempty_inter_closedPoints hO
    (isOpen_biInter_finset fun v _ ↦ (chartA C σ hσ R _ A).isOpen).isLocallyClosed
  have hpu := pointOfClosedPoint_comp (jacOmega C σ hσ Ω).hom u hu
  set pu := pointOfClosedPoint (jacOmega C σ hσ Ω).hom u hu
  refine ⟨zetaΩ C σ hσ Ω + ptClassE C σ hσ R pu hpu, ?_, fun τ ↦ ?_⟩
  · exact picDeg_congr C (curveToP1 k C) σ hσ rfl (add_zero _) (picDeg_add (curveToP1 k C) σ hσ
      _ _ _ (picDeg_zetaΩ C σ hσ Ω) (picDeg_ptClassE C σ hσ R pu hpu))
  have hrange : ∀ {p : SΩ ⟶ (jacOmega C σ hσ Ω).left} {x : (jacOmega C σ hσ Ω).left}
      (_ : ∀ a, p a = x) {U : (jacOmega C σ hσ Ω).left.Opens}, x ∈ U ↔ Set.range p ⊆ U := by
    intro p x hpx U
    obtain ⟨q⟩ : Nonempty SΩ := inferInstance
    constructor
    · rintro hx _ ⟨a, rfl⟩
      rw [hpx]
      exact hx
    · intro h
      rw [← hpx q]
      exact h ⟨q, rfl⟩
  have key : InA C σ hσ A SΩ ⟨sΩ, (zetaΩ C σ hσ Ω + conjΩ C σ hσ τ.symm w) +
      ptClassE C σ hσ R pu hpu⟩ := by
    refine (range_subset_chartA_iff_pt C σ hσ R pu hpu _ A).1 ?_
    refine (hrange (pointOfClosedPoint_apply (jacOmega C σ hσ Ω).hom u hu)).1 ?_
    exact Set.mem_iInter₂.1 huO _ ((Set.Finite.mem_toFinset _).2 ⟨τ.symm, rfl⟩)
  have key2 := key.conjΩ C σ hσ τ
  rw [conjΩ_add, conjΩ_add, conjΩ_conjΩ_symm] at key2
  refine (hrange (pointOfClosedPoint_apply (jacOmega C σ hσ Ω).hom z hz)).2 ?_
  refine (range_subset_chartA_iff_pt C σ hσ R p₀ hp₀ _ A).2 ?_
  rw [conjΩ_add, add_right_comm]
  exact key2

/-- **Finitely many good classes**: there is a finite set `s` of classes of degree `g` over
`Ω` such that every point of `J_Ω` lies, for some `c ∈ s`, in all the charts `V(τ^* c, A)`. -/
theorem exists_finset_good : ∃ s : Finset ((G).obj (op (Over.mk sΩ))),
    (∀ c ∈ s, picDeg σ hσ (curveToP1 k C) (genusNat k C) SΩ ⟨sΩ, c⟩) ∧
      ∀ z : (jacOmega C σ hσ Ω).left, ∃ c ∈ s, ∀ τ : Ω ≃ₐ[k] Ω,
        z ∈ chartA C σ hσ (jacobianBCRepresentableBy C σ hσ Ω) (conjΩ C σ hσ τ c)
          (chartOpenA C σ hσ Ω) := by
  classical
  set R := jacobianBCRepresentableBy C σ hσ Ω
  set A := chartOpenA C σ hσ Ω
  let I := {c : (G).obj (op (Over.mk sΩ)) //
    picDeg σ hσ (curveToP1 k C) (genusNat k C) SΩ ⟨sΩ, c⟩}
  let U : I → Set (jacOmega C σ hσ Ω).left := fun c ↦
    ⋂ v ∈ (finite_conj C σ hσ c.1).toFinset, (chartA C σ hσ R v A : Set _)
  have hU : ∀ c, IsOpen (U c) := fun c ↦
    isOpen_biInter_finset fun v _ ↦ (chartA C σ hσ R v A).isOpen
  have hU' : ∀ c z, z ∈ U c → ∀ τ : Ω ≃ₐ[k] Ω, z ∈ chartA C σ hσ R (conjΩ C σ hσ τ c.1) A :=
    fun c z hz τ ↦ Set.mem_iInter₂.1 hz _ ((Set.Finite.mem_toFinset _).2 ⟨τ, rfl⟩)
  have hcov : ∀ z, ∃ c, z ∈ U c := by
    intro z
    obtain ⟨z₀, hz₀, hcl⟩ := isClosed_closure.exists_closed_singleton
      ⟨z, subset_closure (Set.mem_singleton z)⟩
    obtain ⟨c, hc, hτ⟩ := exists_good_closed C σ hσ Ω z₀ hcl
    refine ⟨⟨c, hc⟩, ?_⟩
    have hz₀U : z₀ ∈ U ⟨c, hc⟩ := Set.mem_iInter₂.2 fun v hv ↦ by
      obtain ⟨τ, rfl⟩ := (Set.Finite.mem_toFinset _).1 hv
      exact hτ τ
    obtain ⟨y, hyU, hy⟩ := mem_closure_iff.1 hz₀ _ (hU _) hz₀U
    rw [Set.mem_singleton_iff] at hy
    rwa [← hy]
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun z _ ↦ Set.mem_iUnion.2 (hcov z))
  refine ⟨s.image Subtype.val, ?_, fun z ↦ ?_⟩
  · intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hc
    exact c'.2
  · obtain ⟨c, hcs, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact ⟨c.1, Finset.mem_image_of_mem _ hcs, hU' c z hz⟩

end Cover

end CurvesJacobian
