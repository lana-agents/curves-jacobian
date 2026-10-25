/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DupFillMatch
import CurvesJacobian.Cusp.CoverCuspClasses
import CurvesJacobian.Cusp.WeierAutVE
import CurvesJacobian.Cusp.FillCuspClasses
import CurvesJacobian.Cusp.Cor38Exists

/-!
# [AbsTopII] Corollary 3.4 for `X = E ∖ {O}` and `U_X = E ∖ E[2]`

`Topics in Absolute Anabelian Geometry II.txt` l.4540–4596. For elliptic curves `E_i` over number
fields `K_i` with `K_i`-rational `2`-torsion and an isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of
cuspidal extensions:

* `cor34_dup₃` (existence): `Φ` lifts along the fillings `Π_{E_i∖E_i[2]} ↠ Π_{E_i∖O}`
  (`cor38Fill`) to `φ_U : Π_{E₁∖E₁[2]} ≅ Π_{E₂∖E₂[2]}`; input: the existence half of the
  rel-isom-DGC, applied once to an automorphism of `Π_{E₂∖O}` over `G_{K₂}`;
* `cor34_dup_unique₃` (uniqueness up to conjugation by the kernel of the filling).

Route (β) of the MR8 plan: `Φ` preserves the `[2]`-subgroup `Π_U` (`map_dupPiU`, step G2), so it
restricts to `φ : Π_{V₁} ≅ Π_{V₂}` along the `[2]`-covers `c_i` (`dupC₃`). The kernel of the
filling is the closed normal closure of the cusps `c⁻¹(g I g⁻¹)`, `g ∉ g₀ Π_U`
(`exists_ker_dupFill_eq₃`: `FillCuspClasses`, `CoverCuspClasses`, `DupDecomp`), so a twist of `φ`
by an element of `Π_{X₂}` matches the kernels and induces `Ψ : Π_{X₁} ≅ Π_{X₂}` with
`fill₂ ∘ φ' = Ψ ∘ fill₁` (`exists_dupFill_match₃`, step G3). Then `Φ ∘ Ψ⁻¹`, corrected by an inner
automorphism, lies over `G_{K₂}`, so it is induced by a `K₂`-automorphism of `E₂ ∖ {O}` (DGC),
which preserves `E₂ ∖ E₂[2]` and lifts along the filling (`exists_isoVE_piV_of_isoXE`, step G4).
-/

open scoped Pointwise
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section OneCurve

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K)
  [E.IsElliptic] (hne : ((VE E : (curveE E).Opens) : Set (curveE E)).Nonempty)
  (α₀ : fiber (basePoint Ω (hypCurveX E) (compl_XE_nonempty E)) ≅
    fiber (fillPoint Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
      (compl_nonempty_of_le (VE_le_XE E) (compl_XE_nonempty E)) (VE_le_XE E)))

/-- The `[2]`-cover map `Π_{E∖E[2]} ↪ Π_{E∖O}`, with source the group of the open
`E ∖ E[2] ⊆ E ∖ {O}` (definitionally `hypCurveV E`). -/
abbrev dupC₃ : (arithmeticExt Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
      (compl_nonempty_of_le (VE_le_XE E) (compl_XE_nonempty E))).Pi →ₜ*
    (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E) (coverXMorK E)

/-- The filling `Π_{E∖E[2]} ↠ Π_{E∖O}`. -/
abbrev dupFill₃ : (arithmeticExt Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
      (compl_nonempty_of_le (VE_le_XE E) (compl_XE_nonempty E))).Pi →*
    (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  cor38Fill Ω (hypCurveX E) (compl_XE_nonempty E) (VE E) (VE_le_XE E) hne α₀

/-- The cuspidal inertia groups of `Π_{E∖E[2]}`. -/
abbrev cuspsV₃ : Set (Subgroup (arithmeticExt Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
    (compl_nonempty_of_le (VE_le_XE E) (compl_XE_nonempty E))).Pi) :=
  arithCusps Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
    (compl_nonempty_of_le (VE_le_XE E) (compl_XE_nonempty E))

lemma range_dupC₃ : (dupC₃ Ω E hne).toMonoidHom.range = dupPiU Ω E := rfl

lemma dupC₃_injective : Function.Injective (dupC₃ Ω E hne) :=
  coverPiHom_injective Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
    (coverXMorK E)

set_option maxHeartbeats 2000000 in
-- unifying `hypCurveV E` with `subCurve …` inside the cover/fill homomorphisms is slow
/-- **Step G3 for one curve**: given the fill-side facts (killed cusps generate the kernel; the
surviving cusps form one class; some cusp survives), `ker(fill)` is the closed normal closure of
the cusps `J_g = c⁻¹(g I g⁻¹)`, `g ∉ g₀ · Π_U`. -/
theorem exists_ker_dupFill_eq_of₃ (hE : E.Ψ₂Sq.Splits)
    {I : Subgroup (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi}
    (hI : I ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E))
    (hA1 : (dupFill₃ Ω E hne α₀).ker = (Subgroup.normalClosure (⋃ (J) (_ : J ∈
      cuspsV₃ Ω E hne ∧ J ≤ (dupFill₃ Ω E hne α₀).ker),
        (J : Set _))).topologicalClosure)
    (hA2 : ∀ J ∈ cuspsV₃ Ω E hne,
      ∀ J' ∈ cuspsV₃ Ω E hne,
      ¬ J ≤ (dupFill₃ Ω E hne α₀).ker → ¬ J' ≤ (dupFill₃ Ω E hne α₀).ker →
        ∃ v, J' = J.map (MulAut.conj v).toMonoidHom)
    (hA3 : ∃ J ∈ cuspsV₃ Ω E hne, ¬ J ≤ (dupFill₃ Ω E hne α₀).ker) :
    ∃ g₀, (dupFill₃ Ω E hne α₀).ker = (Subgroup.normalClosure
      (dupCuspSet (dupC₃ Ω E hne).toMonoidHom I g₀)).topologicalClosure := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_of_splits E hE
  haveI : (dupC₃ Ω E hne).toMonoidHom.range.Normal := dupPiU_normal Ω E he
  have hcomm := commensurator_le_dupPiU₂ Ω E hE hI
  have hIle : I ≤ (dupC₃ Ω E hne).toMonoidHom.range := fun x hx ↦
    hcomm (mem_commensurator_of_mem hx)
  have hnorm : ∀ x, I.map (MulAut.conj x).toMonoidHom = I →
      x ∈ (dupC₃ Ω E hne).toMonoidHom.range := fun x hx ↦ by
    refine hcomm ?_
    rw [Subgroup.Commensurable.commensurator_mem_iff]
    have hs : ConjAct.toConjAct x • I = I := by
      ext y
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul,
        inv_inv]
      conv_rhs => rw [← hx]
      rw [mem_map_conj_iff₃]
    rw [hs]
  exact exists_eq_closure_dupCuspSet (dupC₃ Ω E hne).toMonoidHom I hIle hnorm
    (cuspsV₃ Ω E hne)
    (fun J hJ ↦ (exists_dup_conj_eq_comap₂ Ω E hI hJ).imp fun _ h ↦ h.2)
    (fun g ↦ comap_dup_mem_arithCusps₂ Ω E hI g) _ hA1 hA2 hA3

/-- **Step G3 for one curve**: `ker(Π_{E∖E[2]} ↠ Π_{E∖O})` is the closed normal closure of the
cusps `J_g = c⁻¹(g I g⁻¹)` with `g ∉ g₀ · Π_U`, for every cusp `I` of `Π_{E∖O}`. -/
theorem exists_ker_dupFill_eq₃ (hE : E.Ψ₂Sq.Splits)
    {I : Subgroup (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi}
    (hI : I ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E)) :
    ∃ g₀, (dupFill₃ Ω E hne α₀).ker = (Subgroup.normalClosure
      (dupCuspSet (dupC₃ Ω E hne).toMonoidHom I g₀)).topologicalClosure :=
  exists_ker_dupFill_eq_of₃ Ω E hne α₀ hE hI
    (ker_cor38Fill_eq_closure_killedCusps_VE₂ Ω E (compl_XE_nonempty E) hne α₀)
    (fun _ hJ _ hJ' hk hk' ↦
      exists_conj_eq_of_not_le_ker_cor38Fill_VE₂ Ω E (compl_XE_nonempty E) hne α₀ hJ hJ' hk hk')
    (exists_mem_arithCusps_not_le_ker_cor38Fill_VE₂ Ω E (compl_XE_nonempty E) hne α₀)

end OneCurve

section TwoCurves

/-- Removing the conjugation at the end of `cor34_dup₃`. -/
lemma conj_fill_aux₃ {V X : Type*} [Group V] [Group X] (fill : V →* X) (z w' : V) (s s' y : X)
    (hw' : fill w' = s' * s) (hz : fill z = s' * (s * y * s⁻¹) * s'⁻¹) :
    fill (w'⁻¹ * z * w'⁻¹⁻¹) = y := by
  rw [map_mul, map_mul, map_inv, inv_inv, hw', hz]
  group

variable {K₁ : Type u} [Field K₁] [NumberField K₁] (Ω₁ : Type u) [Field Ω₁] [Algebra K₁ Ω₁]
  [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁] [CharZero Ω₁] (E₁ : WeierstrassCurve K₁)
  [E₁.IsElliptic]
  {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] (E₂ : WeierstrassCurve K₂)
  [E₂.IsElliptic]
  (hne₁ : ((VE E₁ : (curveE E₁).Opens) : Set (curveE E₁)).Nonempty)
  (hne₂ : ((VE E₂ : (curveE E₂).Opens) : Set (curveE E₂)).Nonempty)
  (α₁ : fiber (basePoint Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)) ≅
    fiber (fillPoint Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
      (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁)) (VE_le_XE E₁)))
  (α₂ : fiber (basePoint Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)) ≅
    fiber (fillPoint Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
      (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂)) (VE_le_XE E₂)))
  (Φ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Iso
    (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)))

/-- **Step G3 (matching the kept cusp)**, from the one-curve descriptions of the kernels of the
fillings: there are `g ∈ Π_{X₂}`, `φ' : Π_{V₁} ≅ Π_{V₂}` over `conj(g) ∘ Φ` along the
`[2]`-covers, and `Ψ : Π_{X₁} ≅ Π_{X₂}` with `fill₂ ∘ φ' = Ψ ∘ fill₁`. -/
theorem exists_dupFill_match_of₃ (hE₁ : E₁.Ψ₂Sq.Splits) (hE₂ : E₂.Ψ₂Sq.Splits)
    (hK₁ : ∀ I ∈ arithCusps Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁), ∃ g₀,
      (dupFill₃ Ω₁ E₁ hne₁ α₁).ker = (Subgroup.normalClosure
        (dupCuspSet (dupC₃ Ω₁ E₁ hne₁).toMonoidHom I g₀)).topologicalClosure)
    (hK₂ : ∀ I ∈ arithCusps Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂), ∃ g₀,
      (dupFill₃ Ω₂ E₂ hne₂ α₂).ker = (Subgroup.normalClosure
        (dupCuspSet (dupC₃ Ω₂ E₂ hne₂).toMonoidHom I g₀)).topologicalClosure) :
    ∃ (g : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi)
      (φ' : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
          (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
          (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi)
      (Ψ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi),
      (∀ v, dupC₃ Ω₂ E₂ hne₂ (φ' v) = g * Φ.pi (dupC₃ Ω₁ E₁ hne₁ v) * g⁻¹) ∧
        ∀ v, dupFill₃ Ω₂ E₂ hne₂ α₂ (φ' v) = Ψ (dupFill₃ Ω₁ E₁ hne₁ α₁ v) := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_of_splits E₂ hE₂
  haveI : (dupC₃ Ω₂ E₂ hne₂).toMonoidHom.range.Normal := dupPiU_normal Ω₂ E₂ he
  obtain ⟨I₁, hI₁⟩ := exists_mem_cusps₂ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)
  obtain ⟨I₂, hI₂⟩ := exists_mem_cusps₂ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)
  have hΦI := (Φ.cusps_map I₁).1 hI₁
  obtain ⟨h, hh⟩ : ∃ h : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi,
      I₁.map Φ.pi.toMulEquiv.toMonoidHom = I₂.map (MulAut.conj h).toMonoidHom :=
    (exists_conj_eq_of_mem_arithCusps₂ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)
      (subsingleton_compl_geomOpen_XE₂ Ω₂ E₂) hI₂ hΦI).imp fun _ h ↦ h.2
  have hI : ∀ x, x ∈ I₁ ↔ h⁻¹ * Φ.pi.toMulEquiv x * h ∈ I₂ := fun x ↦ by
    rw [← mem_map_conj_iff₃, ← hh, Subgroup.mem_map_equiv]
    change x ∈ I₁ ↔ Φ.pi.symm (Φ.pi x) ∈ I₁
    rw [ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨g₁, hg₁⟩ := hK₁ I₁ hI₁
  obtain ⟨g₂, hg₂⟩ := hK₂ I₂ hI₂
  obtain ⟨φ, hφ⟩ := exists_lift_of_map_range (dupC₃ Ω₁ E₁ hne₁) (dupC₃ Ω₂ E₂ hne₂)
    (dupC₃_injective Ω₁ E₁ hne₁) (dupC₃_injective Ω₂ E₂ hne₂) Φ.pi
    (map_dupPiU Ω₁ E₁ Ω₂ E₂ Φ hE₁ hE₂)
  obtain ⟨g, φ', hφ', hmap⟩ := exists_twist_map_closure_dupCuspSet (dupC₃ Ω₁ E₁ hne₁)
    (dupC₃ Ω₂ E₂ hne₂) (dupC₃_injective Ω₂ E₂ hne₂) Φ.pi.toMulEquiv φ hφ hI g₁ g₂
  rw [← hg₁, ← hg₂] at hmap
  let f₁ : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
      (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁))).Pi →ₜ*
      (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi :=
    ⟨dupFill₃ Ω₁ E₁ hne₁ α₁, continuous_cor38Fill₂ Ω₁ _ _ _ _ hne₁ α₁⟩
  let f₂ : (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
      (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi →ₜ*
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi :=
    ⟨dupFill₃ Ω₂ E₂ hne₂ α₂, continuous_cor38Fill₂ Ω₂ _ _ _ _ hne₂ α₂⟩
  obtain ⟨Ψ, hΨ⟩ := exists_quotient_iso f₁ f₂ (cor38Fill_surjective₂ Ω₁ _ _ _ _ hne₁ α₁)
    (cor38Fill_surjective₂ Ω₂ _ _ _ _ hne₂ α₂) φ' hmap
  exact ⟨g, φ', Ψ, hφ', hΨ⟩

/-- **Step G3**: unconditional form of `exists_dupFill_match_of₃`. -/
theorem exists_dupFill_match₃ (hE₁ : E₁.Ψ₂Sq.Splits) (hE₂ : E₂.Ψ₂Sq.Splits) :
    ∃ (g : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi)
      (φ' : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
          (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
          (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi)
      (Ψ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi),
      (∀ v, dupC₃ Ω₂ E₂ hne₂ (φ' v) = g * Φ.pi (dupC₃ Ω₁ E₁ hne₁ v) * g⁻¹) ∧
        ∀ v, dupFill₃ Ω₂ E₂ hne₂ α₂ (φ' v) = Ψ (dupFill₃ Ω₁ E₁ hne₁ α₁ v) :=
  exists_dupFill_match_of₃ Ω₁ E₁ Ω₂ E₂ hne₁ hne₂ α₁ α₂ Φ hE₁ hE₂
    (fun _ hI ↦ exists_ker_dupFill_eq₃ Ω₁ E₁ hne₁ α₁ hE₁ hI)
    (fun _ hI ↦ exists_ker_dupFill_eq₃ Ω₂ E₂ hne₂ α₂ hE₂ hI)

/-- `Φ.g` as a map of absolute Galois groups. -/
abbrev gΦ₃ (y : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₁ Ω₁)))) :
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₂ Ω₂))) :=
  Φ.g y

/-- **[AbsTopII] Corollary 3.4 for `X = E ∖ {O}`, `U_X = E ∖ E[2]` (existence)**
(`Topics in Absolute Anabelian Geometry II.txt` l.4540–4596): for elliptic curves `E_i` over
number fields with rational `2`-torsion, every isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal
extensions lifts along the fillings `Π_{E_i∖E_i[2]} ↠ Π_{E_i∖O}` to an isomorphism
`φ_U : Π_{E₁∖E₁[2]} ≅ Π_{E₂∖E₂[2]}`. Input: the existence half of the rel-isom-DGC (`hDGC`), used
once on `E₂ ∖ {O}`; uniqueness up to the kernel is `cor38_unique`. -/
theorem cor34_dup₃ (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hE₁ : E₁.Ψ₂Sq.Splits) (hE₂ : E₂.Ψ₂Sq.Splits) :
    ∃ φU : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
          (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
          (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi,
      ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂
          (φU e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁) (VE_le_XE E₁) hne₁ α₁
          e) := by
  obtain ⟨g, φ', Ψ, hc, hf⟩ := exists_dupFill_match₃ Ω₁ E₁ Ω₂ E₂ hne₁ hne₂ α₁ α₂ Φ hE₁ hE₂
  obtain ⟨t₁, ht₁⟩ := exists_pr_cor38Fill₃ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁)
    (VE_le_XE E₁) hne₁ α₁
  obtain ⟨t₂, ht₂⟩ := exists_pr_cor38Fill₃ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂)
    (VE_le_XE E₂) hne₂ α₂
  have ha₁ := pr_coverPiHom_self₃ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (hypCurveV E₁)
    (hcV_dup E₁) (coverXMorK E₁) (coverXMorK_over₂ E₁)
  have ha₂ := pr_coverPiHom_self₃ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (hypCurveV E₂)
    (hcV_dup E₂) (coverXMorK E₂) (coverXMorK_over₂ E₂)
  set a₁ := coverG Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (hypCurveV E₁) (hcV_dup E₁)
    (coverXMorK E₁) (coverXMorK_over₂ E₁)
  set a₂ := coverG Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (hypCurveV E₂) (hcV_dup E₂)
    (coverXMorK E₂) (coverXMorK_over₂ E₂)
  -- `Ψ` lies over `conj(T) ∘ Φ.g`
  have hT : ∀ x, projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Ψ x) =
      (t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
        gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹)) *
        (gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) x)) *
        (t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
        gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹))⁻¹ := by
    intro x
    obtain ⟨v, rfl⟩ := cor38Fill_surjective₂ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁)
      (VE_le_XE E₁) hne₁ α₁ x
    have e1 := ht₂ (φ' v)
    have e2 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (dupC₃ Ω₂ E₂ hne₂ (φ' v)) =
        a₂ * projGk Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
          (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂)) (φ' v) * a₂⁻¹ :=
      ha₂ (φ' v)
    have e3 := congrArg (projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)) (hc v)
    have e4 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Φ.pi (dupC₃ Ω₁ E₁ hne₁ v)) =
        gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ
          (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (dupC₃ Ω₁ E₁ hne₁ v)) :=
      Φ.pr_comm _
    have e5 : projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (dupC₃ Ω₁ E₁ hne₁ v) =
        a₁ * projGk Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
          (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁)) v * a₁⁻¹ :=
      ha₁ v
    have e6 := ht₁ v
    rw [← hf v]
    change projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)
      (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂
        (φ' v)) = _
    rw [e1]
    have e2' : projGk Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
        (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂)) (φ' v) =
        a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (dupC₃ Ω₂ E₂ hne₂ (φ' v)) * a₂ := by
      rw [e2]
      group
    rw [e2', e3, map_mul, map_mul, map_inv, e4,
      e5, e6]
    simp only [map_mul, map_inv]
    group
  obtain ⟨s, hs⟩ : ∃ s : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi,
      projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) s =
        t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
          gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹) :=
    projGk_surjective Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) _
  let θ : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi :=
    (Ψ.symm.trans Φ.pi).trans (conjCME₃ s)
  have hθ : ∀ y, projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (θ y) =
      projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) y := fun y ↦ by
    have h1 := hT (Ψ.symm y)
    rw [ContinuousMulEquiv.apply_symm_apply] at h1
    have h2 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Φ.pi (Ψ.symm y)) =
        gΦ₃ Ω₁ E₁ Ω₂ E₂ Φ (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (Ψ.symm y)) :=
      Φ.pr_comm _
    change projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (s * Φ.pi (Ψ.symm y) * s⁻¹) = _
    rw [map_mul, map_mul, map_inv, h2, hs, h1]
  obtain ⟨F, hFK, hFθ⟩ := exists_isConjInduced_of_relIsomDGC Ω₂ (C₁ := hypCurveX E₂)
    (C₂ := hypCurveX E₂) (hc₁ := compl_XE_nonempty E₂) (hc₂ := compl_XE_nonempty E₂)
    (hDGC K₂) θ hθ
  obtain ⟨-, -, -, θV₀, -, hs''⟩ := exists_isoVE_piV_of_isoXE Ω₂ E₂ (compl_XE_nonempty E₂)
    hne₂ α₂ F hFK θ hFθ
  obtain ⟨θV, s', hs'⟩ : ∃ (θV : (arithmeticExt Ω₂
        (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
        (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
        (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi)
      (s' : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi), ∀ σ,
      cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂ (θV σ) =
        s' * θ (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂
          α₂ σ) * s'⁻¹ := ⟨θV₀, hs''⟩
  obtain ⟨w', hw'⟩ := cor38Fill_surjective₂ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂)
    (VE_le_XE E₂) hne₂ α₂ (s' * s)
  have hθΨ : ∀ x, θ (Ψ x) = s * Φ.pi x * s⁻¹ := fun x ↦ by
    change s * Φ.pi (Ψ.symm (Ψ x)) * s⁻¹ = _
    rw [ContinuousMulEquiv.symm_apply_apply]
  refine ⟨(φ'.trans θV).trans (conjCME₃ w'⁻¹), fun e ↦ ?_⟩
  have hfe : cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂
      (φ' e) = Ψ (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁) (VE_le_XE E₁)
        hne₁ α₁ e) := hf e
  have hz := (hs' (φ' e)).trans (by rw [hfe, hθΨ])
  exact conj_fill_aux₃ _ _ _ _ _ _ hw' hz

/-- **[AbsTopII] Corollary 3.4 for `E ∖ E[2] ⊆ E ∖ {O}`, uniqueness**: two lifts of `Φ` differ by
conjugation with an element of the kernel of the filling (`cor38_unique`). -/
theorem cor34_dup_unique₃ (hDGC : RelIsomDGC.Exists K₂)
    (φ₁ φ₂ : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VE E₁) (VE_le_XE E₁) hne₁)
          (compl_nonempty_of_le (VE_le_XE E₁) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VE E₂) (VE_le_XE E₂) hne₂)
          (compl_nonempty_of_le (VE_le_XE E₂) (compl_XE_nonempty E₂))).Pi)
    (h₁ : ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂
          (φ₁ e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁) (VE_le_XE E₁) hne₁ α₁
          e))
    (h₂ : ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂
          (φ₂ e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VE E₁) (VE_le_XE E₁) hne₁ α₁
          e)) :
    ∃ n ∈ (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂
      α₂).ker, ∀ e, φ₂ e = n * φ₁ e * n⁻¹ :=
  cor38_unique Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VE E₂) (VE_le_XE E₂) hne₂ α₂ hDGC φ₁ φ₂
    fun e ↦ (h₂ e).trans (h₁ e).symm

end TwoCurves

end CurvesJacobian.Cusp
