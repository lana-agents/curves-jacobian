/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelAction
import CurvesJacobian.Cusp.InvariantLine
import CurvesJacobian.Scheme.CurveFunctionField

/-!
# The ring automorphisms underlying the semilinear action on a geometric model

For a geometric model `D` of a chain object (`CurvesJacobian.Cusp.GeomModel`) and the
rel-isom-DGC over its field of definition `M`, the semilinear action
`GeomModel.semilinearAction : N_A(ι(Π_Y)) →* Aut (Spec Γ(U_Y))` is induced by ring automorphisms
of `R = Γ(U_Y)` (`Spec` is fully faithful). Since `Spec` is contravariant we use `g ↦ (F_{g⁻¹})^*`:

* `CurvesJacobian.Cusp.GeomModel.autRing : N →* (R ≃ₐ[K] R)`, with
  `Spec.map (autRing g) = F_{g⁻¹}` (`GeomModel.specMap_autRing`), lying over `α_{g⁻¹} = α_g⁻¹` on
  `M` (`GeomModel.autRing_algebraMap_M`), trivial on `ι(Π_Y)` (`GeomModel.autRing_ι`). Here `R`
  is a `K`-algebra through `K → M → R` (`GeomModel.algebraSections`).
* `CurvesJacobian.Cusp.GeomModel.autGroup`: for a subgroup `P' ≤ N` in which `ι(Π_Y) ∩ P'` has
  finite index, the image of `P'` in `Aut_K(R)`, a finite group (`GeomModel.finite_autGroup`).
* Ring-theoretic properties of `R` over `K`: a domain (`GeomModel.isDomain_sections`), of finite
  type (`GeomModel.finiteType_sections_K`), of transcendence degree one
  (`GeomModel.trdeg_sections`).
* **`CurvesJacobian.Cusp.GeomModel.exists_invariant_line`**: there is `t ∈ R` fixed by the image
  of `P'`, transcendental over `K`, with `R` finite over `K[t]`
  (`CurvesJacobian.Cusp.exists_invariant_finite`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC D.M)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The `K`-algebra structure on `Γ(U_Y)` through `K → M → Γ(U_Y)`. -/
instance algebraSections : Algebra K Γ(D.Y.Xbar, D.Y.U) :=
  Algebra.compHom _ (algebraMap K D.M)

instance isScalarTower_sections : IsScalarTower K D.M Γ(D.Y.Xbar, D.Y.U) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-! ### The ring maps `F_g^*` -/

/-- The ring endomorphism `F_g^*` of `Γ(U_Y)` with `Spec (F_g^*) = F_g`. -/
def ringHomOf (g : D.Nrm) : Γ(D.Y.Xbar, D.Y.U) ⟶ Γ(D.Y.Xbar, D.Y.U) :=
  Spec.preimage (D.semilinearAutOf hDGC g).hom

lemma specMap_ringHomOf (g : D.Nrm) :
    Spec.map (D.ringHomOf hDGC g) = (D.semilinearAutOf hDGC g).hom :=
  Spec.map_preimage _

lemma ringHomOf_mul (g h : D.Nrm) :
    D.ringHomOf hDGC (g * h) = D.ringHomOf hDGC g ≫ D.ringHomOf hDGC h := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, specMap_ringHomOf, specMap_ringHomOf, specMap_ringHomOf,
    semilinearAutOf_mul, Iso.trans_hom]

lemma ringHomOf_of_mem_ker {g : D.Nrm} (hg : g ∈ (D.semilinearAction hDGC).ker) :
    D.ringHomOf hDGC g = 𝟙 _ := by
  refine Spec.map_injective ?_
  rw [specMap_ringHomOf, Spec.map_id, ← semilinearAction_apply, MonoidHom.mem_ker.1 hg]
  rfl

lemma ringHomOf_one : D.ringHomOf hDGC 1 = 𝟙 _ :=
  D.ringHomOf_of_mem_ker hDGC (one_mem _)

lemma ringHomOf_inv_mul_apply (g : D.Nrm) (x : Γ(D.Y.Xbar, D.Y.U)) :
    D.ringHomOf hDGC g (D.ringHomOf hDGC g⁻¹ x) = x := by
  change (D.ringHomOf hDGC g⁻¹ ≫ D.ringHomOf hDGC g) x = x
  rw [← ringHomOf_mul, inv_mul_cancel, ringHomOf_one]
  rfl

/-- `F_g^*` lies over `α_g` on `M`. -/
lemma ringHomOf_algebraMap (g : D.Nrm) (x : D.M) :
    D.ringHomOf hDGC g (algebraMap D.M Γ(D.Y.Xbar, D.Y.U) x) =
      algebraMap D.M Γ(D.Y.Xbar, D.Y.U) (D.resAut g x) := by
  have h := D.semilinearAutOf_sKU hDGC g
  rw [← specMap_ringHomOf] at h
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg (fun f ↦ f.hom x) (Spec.map_injective h)

/-! ### The action by `K`-algebra automorphisms -/

/-- The `K`-algebra automorphism `(F_{g⁻¹})^*` of `Γ(U_Y)`. -/
def autRingOf (g : D.Nrm) : Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U) where
  toFun := D.ringHomOf hDGC g⁻¹
  invFun := D.ringHomOf hDGC g
  left_inv := D.ringHomOf_inv_mul_apply hDGC g
  right_inv x := by
    simpa using D.ringHomOf_inv_mul_apply hDGC g⁻¹ x
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' c := by
    change D.ringHomOf hDGC g⁻¹ (algebraMap D.M Γ(D.Y.Xbar, D.Y.U) (algebraMap K D.M c)) =
      algebraMap D.M Γ(D.Y.Xbar, D.Y.U) (algebraMap K D.M c)
    rw [ringHomOf_algebraMap, AlgEquiv.commutes]

/-- **The ring automorphisms underlying the semilinear action**: `g ↦ (F_{g⁻¹})^*`, a
homomorphism `N_A(ι(Π_Y)) →* Aut_K(Γ(U_Y))`. -/
def autRing : D.Nrm →* (Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U)) where
  toFun := D.autRingOf hDGC
  map_one' := AlgEquiv.ext fun x ↦ by
    change D.ringHomOf hDGC 1⁻¹ x = x
    rw [inv_one, ringHomOf_one]
    rfl
  map_mul' g h := AlgEquiv.ext fun x ↦ by
    change D.ringHomOf hDGC (g * h)⁻¹ x = D.ringHomOf hDGC g⁻¹ (D.ringHomOf hDGC h⁻¹ x)
    rw [mul_inv_rev, ringHomOf_mul]
    rfl

lemma autRing_apply (g : D.Nrm) (x : Γ(D.Y.Xbar, D.Y.U)) :
    D.autRing hDGC g x = D.ringHomOf hDGC g⁻¹ x := rfl

/-- **`Spec (autRing g) = F_{g⁻¹}`**, the inverse of `F_g`. -/
theorem specMap_autRing (g : D.Nrm) :
    Spec.map (CommRingCat.ofHom (D.autRing hDGC g : Γ(D.Y.Xbar, D.Y.U) →+* Γ(D.Y.Xbar, D.Y.U))) =
      (D.semilinearAction hDGC g⁻¹).hom :=
  D.specMap_ringHomOf hDGC g⁻¹

/-- `Spec (autRing g) = F_g⁻¹`. -/
theorem specMap_autRing_eq_inv (g : D.Nrm) :
    Spec.map (CommRingCat.ofHom (D.autRing hDGC g : Γ(D.Y.Xbar, D.Y.U) →+* Γ(D.Y.Xbar, D.Y.U))) =
      (D.semilinearAction hDGC g).inv := by
  rw [specMap_autRing, map_inv, Aut.Aut_inv_def, Iso.symm_hom]

/-- **`autRing g` lies over `α_{g⁻¹} = α_g⁻¹`** on `M`. -/
theorem autRing_algebraMap_M (g : D.Nrm) (x : D.M) :
    D.autRing hDGC g (algebraMap D.M Γ(D.Y.Xbar, D.Y.U) x) =
      algebraMap D.M Γ(D.Y.Xbar, D.Y.U) (D.resAut g⁻¹ x) :=
  D.ringHomOf_algebraMap hDGC g⁻¹ x

/-- `α_{g⁻¹} = α_g⁻¹`. -/
lemma resAut_inv (g : D.Nrm) : D.resAut g⁻¹ = (D.resAut g).symm := by
  have h1 : D.resAut 1 = AlgEquiv.refl := AlgEquiv.ext fun y ↦
    (algebraMap D.M Ω).injective (by
      rw [resAut_spec]
      have : D.tau 1 = 1 := by
        apply (mulEquivAutFiber K Ω).injective
        rw [mulEquivAutFiber_tau, map_one]
        simp
      rw [this]
      rfl)
  refine AlgEquiv.ext fun y ↦ ?_
  have h := congrArg (fun α : D.M ≃ₐ[K] D.M ↦ α ((D.resAut g).symm y)) (D.resAut_mul g g⁻¹)
  simp only [mul_inv_cancel, h1, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- `autRing g` lies over `α_g⁻¹` on `M`. -/
theorem autRing_algebraMap_M' (g : D.Nrm) (x : D.M) :
    D.autRing hDGC g (algebraMap D.M Γ(D.Y.Xbar, D.Y.U) x) =
      algebraMap D.M Γ(D.Y.Xbar, D.Y.U) ((D.resAut g).symm x) := by
  rw [autRing_algebraMap_M, resAut_inv]

/-- The kernel of the semilinear action lies in the kernel of `autRing`. -/
theorem ker_semilinearAction_le : (D.semilinearAction hDGC).ker ≤ (D.autRing hDGC).ker :=
  fun g hg ↦ MonoidHom.mem_ker.2 (AlgEquiv.ext fun x ↦ by
    rw [autRing_apply, D.ringHomOf_of_mem_ker hDGC (inv_mem hg)]
    rfl)

/-- **`autRing` is trivial on `ι(Π_Y)`.** -/
theorem autRing_ι (σ : D.Pi) : D.autRing hDGC (D.ιN σ) = 1 :=
  MonoidHom.mem_ker.1 (D.ker_semilinearAction_le hDGC (D.range_ιNHom_le_ker hDGC ⟨σ, rfl⟩))

lemma range_ιNHom_le_ker_autRing : D.ιNHom.range ≤ (D.autRing hDGC).ker :=
  (D.range_ιNHom_le_ker hDGC).trans (D.ker_semilinearAction_le hDGC)

/-! ### The finite group of automorphisms induced by `P' ≤ N` -/

/-- The image of a subgroup `P' ≤ N` in `Aut_K(Γ(U_Y))`. -/
def autGroup (P' : Subgroup D.Nrm) : Subgroup (Γ(D.Y.Xbar, D.Y.U) ≃ₐ[K] Γ(D.Y.Xbar, D.Y.U)) :=
  ((D.autRing hDGC).comp P'.subtype).range

lemma mem_autGroup {P' : Subgroup D.Nrm} {g : D.Nrm} (hg : g ∈ P') :
    D.autRing hDGC g ∈ D.autGroup hDGC P' :=
  ⟨⟨g, hg⟩, rfl⟩

/-- **The image of `P'` is finite** if `ι(Π_Y) ∩ P'` has finite index in `P'` (the action of
`P'` factors through `P' / (ι(Π_Y) ∩ P')`). -/
theorem finite_autGroup {P' : Subgroup D.Nrm} (hP' : D.ιNHom.range.relIndex P' ≠ 0) :
    Finite (D.autGroup hDGC P') := by
  let ψ := (D.autRing hDGC).comp P'.subtype
  haveI : (D.ιNHom.range.subgroupOf P').FiniteIndex := ⟨hP'⟩
  have hle : D.ιNHom.range.subgroupOf P' ≤ ψ.ker := fun g hg ↦
    MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 (D.range_ιNHom_le_ker_autRing hDGC hg))
  haveI : ψ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv

/-! ### Ring-theoretic properties of `Γ(U_Y)` -/

instance isDomain_sections : IsDomain Γ(D.Y.Xbar, D.Y.U) := by
  haveI := isIntegral_specSections D.Y D.hY
  exact (affine_isIntegral_iff Γ(D.Y.Xbar, D.Y.U)).1 inferInstance

lemma finiteType_sections_M : Algebra.FiniteType D.M Γ(D.Y.Xbar, D.Y.U) :=
  finiteType_sections D.M (isAffineOpen_U D.Y D.hY)

instance finiteType_sections_K : Algebra.FiniteType K Γ(D.Y.Xbar, D.Y.U) :=
  haveI := D.finiteType_sections_M
  Algebra.FiniteType.trans (S := D.M) inferInstance inferInstance

/-- `Γ(U_Y)` has transcendence degree one over `M`. -/
theorem trdeg_sections_M : Algebra.trdeg D.M Γ(D.Y.Xbar, D.Y.U) = 1 := by
  haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
  haveI : Nonempty D.Y.U := D.Y.nonempty.to_subtype
  haveI : IsFractionRing Γ(D.Y.Xbar, D.Y.U) D.Y.Xbar.functionField :=
    functionField_isFractionRing_of_isAffineOpen D.Y.Xbar D.Y.U (isAffineOpen_U D.Y D.hY)
  haveI : IsScalarTower D.M Γ(D.Y.Xbar, D.Y.U) D.Y.Xbar.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of D.M)).inv ≫
        (D.Y.Xbar ↘ Spec (CommRingCat.of D.M)).appTop ≫
        D.Y.Xbar.presheaf.germ ⊤ (genericPoint D.Y.Xbar) trivial) c =
      D.Y.Xbar.germToFunctionField D.Y.U
        (((D.Y.Xbar ↘ Spec (CommRingCat.of D.M)).appLE ⊤ D.Y.U (by simp))
          ((Scheme.ΓSpecIso (CommRingCat.of D.M)).inv c))
    rw [Scheme.germToFunctionField, Scheme.Hom.appLE]
    simp only [CommRingCat.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  haveI : FaithfulSMul Γ(D.Y.Xbar, D.Y.U) D.Y.Xbar.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective Γ(D.Y.Xbar, D.Y.U) D.Y.Xbar.functionField)
  haveI : Algebra.IsAlgebraic Γ(D.Y.Xbar, D.Y.U) D.Y.Xbar.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(D.Y.Xbar, D.Y.U))
  have h := trdeg_add_eq (R := D.M) (S := Γ(D.Y.Xbar, D.Y.U)) (A := D.Y.Xbar.functionField)
  rw [trdeg_eq_zero (R := Γ(D.Y.Xbar, D.Y.U)), add_zero,
    WeilCurves.FunctionField.trdeg_eq_one] at h
  exact h

/-- **`Γ(U_Y)` has transcendence degree one over `K`.** -/
theorem trdeg_sections : Algebra.trdeg K Γ(D.Y.Xbar, D.Y.U) = 1 := by
  have h := trdeg_add_eq (R := K) (S := D.M) (A := Γ(D.Y.Xbar, D.Y.U))
  rw [trdeg_eq_zero (R := K) (A := D.M), zero_add, trdeg_sections_M] at h
  exact h.symm

/-- **An invariant line on the model**: for `P' ≤ N` with `ι(Π_Y) ∩ P'` of finite index in `P'`,
there is `t ∈ Γ(U_Y)` fixed by the image of `P'`, transcendental over `K`, with `Γ(U_Y)` finite
over `K[t]`. -/
theorem exists_invariant_line {P' : Subgroup D.Nrm} (hP' : D.ιNHom.range.relIndex P' ≠ 0) :
    ∃ t : Γ(D.Y.Xbar, D.Y.U), (∀ g ∈ D.autGroup hDGC P', g t = t) ∧ Transcendental K t ∧
      (lineHom K t).Finite := by
  haveI := D.finite_autGroup hDGC hP'
  obtain ⟨t, ht, htr, hfin⟩ := exists_invariant_finite (D.autGroup hDGC P').subtype
    D.trdeg_sections
  exact ⟨t, fun g hg ↦ ht ⟨g, hg⟩, htr, hfin⟩

/-- The invariant line, stated for the elements of `P'`. -/
theorem exists_invariant_line' {P' : Subgroup D.Nrm} (hP' : D.ιNHom.range.relIndex P' ≠ 0) :
    ∃ t : Γ(D.Y.Xbar, D.Y.U), (∀ g ∈ P', D.autRing hDGC g t = t) ∧ Transcendental K t ∧
      (lineHom K t).Finite := by
  obtain ⟨t, ht, htr, hfin⟩ := D.exists_invariant_line hDGC hP'
  exact ⟨t, fun g hg ↦ ht _ (D.mem_autGroup hDGC hg), htr, hfin⟩

end CurvesJacobian.Cusp.GeomModel
