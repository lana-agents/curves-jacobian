/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DupFillMatch
import CurvesJacobian.Cusp.MulNDecomp
import CurvesJacobian.Cusp.Cor34Elliptic
import CurvesJacobian.Cusp.WeierAutVNE
import CurvesJacobian.Cusp.CoverCuspClasses
import CurvesJacobian.Cusp.WeierAutVE
import CurvesJacobian.Cusp.FillCuspClasses
import CurvesJacobian.Cusp.Cor38Exists

/-!
# [AbsTopII] Corollary 3.4 for `X = E ∖ {O}` and `U_X = E ∖ E[N]`

`Topics in Absolute Anabelian Geometry II.txt` l.4540–4596. For elliptic curves `E_i` over number
fields `K_i` with `#E_i(K_i)[N] = N²` (`TorsionCardN`) and an isomorphism
`Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal extensions:

* `cor34_mulN` (existence): `Φ` lifts along the fillings `Π_{E_i∖E_i[N]} ↠ Π_{E_i∖O}`
  (`cor38Fill`) to `φ_U : Π_{E₁∖E₁[N]} ≅ Π_{E₂∖E₂[N]}`; input: the existence half of the
  rel-isom-DGC, applied once to an automorphism of `Π_{E₂∖O}` over `G_{K₂}`;
* `cor34_mulN_unique` (uniqueness up to conjugation by the kernel of the filling).

The proof is that of `Cor34Elliptic` (`N = 2`) with the `[N]`-subgroup: `map_mulNPiU`
(`MulNDecomp`, step G2) restricts `Φ` along the `[N]`-covers (`mulNC₃`); the kernel of the
filling is the closed normal closure of the cusps `c⁻¹(g I g⁻¹)`, `g ∉ g₀ Π_U`
(`exists_ker_mulNFill_eq`, step G3); the induced automorphism of `Π_{E₂∖O}` is corrected by the
DGC and `exists_isoVNE_piV_of_isoXE` (`WeierAutVNE`, step G4).
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
  [E.IsElliptic] (N : ℕ) [NeZero N]
  (hne : ((VNE E N : (curveE E).Opens) : Set (curveE E)).Nonempty)
  (α₀ : fiber (basePoint Ω (hypCurveX E) (compl_XE_nonempty E)) ≅
    fiber (fillPoint Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
      (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E)) (VNE_le_XE E N)))

/-- The `[N]`-cover map `Π_{E∖E[N]} ↪ Π_{E∖O}`, with source the group of the open
`E ∖ E[N] ⊆ E ∖ {O}` (definitionally `hypCurveVN E N`). -/
abbrev mulNC₃ : (arithmeticExt Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
      (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))).Pi →ₜ*
    (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N) (compl_VNE_nonempty E N)
    (mulByNXMor E N)

/-- The filling `Π_{E∖E[N]} ↠ Π_{E∖O}`. -/
abbrev mulNFill₃ : (arithmeticExt Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
      (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))).Pi →*
    (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi :=
  cor38Fill Ω (hypCurveX E) (compl_XE_nonempty E) (VNE E N) (VNE_le_XE E N) hne α₀

/-- The cuspidal inertia groups of `Π_{E∖E[N]}`. -/
abbrev cuspsVN₃ : Set (Subgroup (arithmeticExt Ω
    (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
    (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))).Pi) :=
  arithCusps Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
    (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))

lemma range_mulNC₃ : (mulNC₃ Ω E N hne).toMonoidHom.range = mulNPiU Ω E N := rfl

lemma mulNC₃_injective : Function.Injective (mulNC₃ Ω E N hne) :=
  coverPiHom_injective Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
    (compl_VNE_nonempty E N) (mulByNXMor E N)

/-- **Step G3 for one curve**: given the fill-side facts (killed cusps generate the kernel; the
surviving cusps form one class; some cusp survives), `ker(fill)` is the closed normal closure of
the cusps `J_g = c⁻¹(g I g⁻¹)`, `g ∉ g₀ · Π_U`. -/
theorem exists_ker_mulNFill_eq_of (hcard : TorsionCardN E N)
    {I : Subgroup (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi}
    (hI : I ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E))
    (hA1 : (mulNFill₃ Ω E N hne α₀).ker = (Subgroup.normalClosure (⋃ (J) (_ : J ∈
      cuspsVN₃ Ω E N hne ∧ J ≤ (mulNFill₃ Ω E N hne α₀).ker),
        (J : Set _))).topologicalClosure)
    (hA2 : ∀ J ∈ cuspsVN₃ Ω E N hne,
      ∀ J' ∈ cuspsVN₃ Ω E N hne,
      ¬ J ≤ (mulNFill₃ Ω E N hne α₀).ker → ¬ J' ≤ (mulNFill₃ Ω E N hne α₀).ker →
        ∃ v, J' = J.map (MulAut.conj v).toMonoidHom)
    (hA3 : ∃ J ∈ cuspsVN₃ Ω E N hne, ¬ J ≤ (mulNFill₃ Ω E N hne α₀).ker) :
    ∃ g₀, (mulNFill₃ Ω E N hne α₀).ker = (Subgroup.normalClosure
      (dupCuspSet (mulNC₃ Ω E N hne).toMonoidHom I g₀)).topologicalClosure := by
  haveI : (mulNC₃ Ω E N hne).toMonoidHom.range.Normal := mulNPiU_normal Ω hcard
  have hcomm := commensurator_le_mulNPiU Ω hcard hI
  have hIle : I ≤ (mulNC₃ Ω E N hne).toMonoidHom.range := fun x hx ↦
    hcomm (mem_commensurator_of_mem hx)
  have hnorm : ∀ x, I.map (MulAut.conj x).toMonoidHom = I →
      x ∈ (mulNC₃ Ω E N hne).toMonoidHom.range := fun x hx ↦ by
    refine hcomm ?_
    rw [Subgroup.Commensurable.commensurator_mem_iff]
    have hs : ConjAct.toConjAct x • I = I := by
      ext y
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul,
        inv_inv]
      conv_rhs => rw [← hx]
      rw [mem_map_conj_iff₃]
    rw [hs]
  exact exists_eq_closure_dupCuspSet (mulNC₃ Ω E N hne).toMonoidHom I hIle hnorm
    (cuspsVN₃ Ω E N hne)
    (fun J hJ ↦ (exists_conj_eq_comap₂ Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveVN E N)
      (compl_VNE_nonempty E N) (mulByNXMor E N) (mulByNXMor_spec E N)
      (subsingleton_compl_geomOpen_XE₂ Ω E) hI hJ).imp fun _ h ↦ h.2)
    (fun g ↦ comap_map_conj_mem_arithCusps₂ Ω (hypCurveX E) (compl_XE_nonempty E)
      (hypCurveVN E N) (compl_VNE_nonempty E N) (mulByNXMor E N) (mulByNXMor_spec E N) hI g)
    _ hA1 hA2 hA3

/-- **Step G3 for one curve**: `ker(Π_{E∖E[N]} ↠ Π_{E∖O})` is the closed normal closure of the
cusps `J_g = c⁻¹(g I g⁻¹)` with `g ∉ g₀ · Π_U`, for every cusp `I` of `Π_{E∖O}`. -/
instance isFiniteEtale_mulByNCover₃ :
    IsFiniteEtale (X := Spec Γ((hypCurveVN E N).Xbar, (hypCurveVN E N).U))
      (Y := Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U)) (mulByNXMor E N) :=
  isFiniteEtale_mulByNXMor E N

theorem exists_ker_mulNFill_eq (hcard : TorsionCardN E N)
    {I : Subgroup (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).Pi}
    (hI : I ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E)) :
    ∃ g₀, (mulNFill₃ Ω E N hne α₀).ker = (Subgroup.normalClosure
      (dupCuspSet (mulNC₃ Ω E N hne).toMonoidHom I g₀)).topologicalClosure :=
  exists_ker_mulNFill_eq_of Ω E N hne α₀ hcard hI
    (by
      rw [ker_cor38Fill₂]
      exact ker_fillMap_eq_closure_killedCusps₂ Ω (subCurve (hypCurveX E) (VNE E N)
        (VNE_le_XE E N) hne) (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))
        (U' := (hypCurveX E).U) (VNE_le_XE E N) (compl_XE_nonempty E))
    (fun _ hJ _ hJ' hk hk' ↦ by
      rw [ker_cor38Fill₂] at hk hk'
      exact exists_conj_eq_of_not_le_ker_fillMap₂ Ω (subCurve (hypCurveX E) (VNE E N)
        (VNE_le_XE E N) hne) (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))
        (U' := (hypCurveX E).U) (VNE_le_XE E N) (compl_XE_nonempty E)
        (subsingleton_compl_baseChangeOpen_XE₂ Ω E) hJ hJ' hk hk')
    (by
      rw [ker_cor38Fill₂]
      exact exists_mem_arithCusps_not_le_ker_fillMap₂ Ω (subCurve (hypCurveX E) (VNE E N)
        (VNE_le_XE E N) hne) (compl_nonempty_of_le (VNE_le_XE E N) (compl_XE_nonempty E))
        (U' := (hypCurveX E).U) (VNE_le_XE E N) (compl_XE_nonempty E) (hypCurveX E).hyperbolic)

end OneCurve

section TwoCurves

/-- Removing the conjugation at the end of `cor34_dup₃`. -/
lemma conj_fill_auxN {V X : Type*} [Group V] [Group X] (fill : V →* X) (z w' : V) (s s' y : X)
    (hw' : fill w' = s' * s) (hz : fill z = s' * (s * y * s⁻¹) * s'⁻¹) :
    fill (w'⁻¹ * z * w'⁻¹⁻¹) = y := by
  rw [map_mul, map_mul, map_inv, inv_inv, hw', hz]
  group

variable {K₁ : Type u} [Field K₁] [NumberField K₁] (Ω₁ : Type u) [Field Ω₁] [Algebra K₁ Ω₁]
  [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁] [CharZero Ω₁] (E₁ : WeierstrassCurve K₁)
  [E₁.IsElliptic]
  {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] (E₂ : WeierstrassCurve K₂)
  [E₂.IsElliptic] (N : ℕ) [NeZero N]
  (hne₁ : ((VNE E₁ N : (curveE E₁).Opens) : Set (curveE E₁)).Nonempty)
  (hne₂ : ((VNE E₂ N : (curveE E₂).Opens) : Set (curveE E₂)).Nonempty)
  (α₁ : fiber (basePoint Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)) ≅
    fiber (fillPoint Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
      (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁)) (VNE_le_XE E₁ N)))
  (α₂ : fiber (basePoint Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)) ≅
    fiber (fillPoint Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
      (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂)) (VNE_le_XE E₂ N)))
  (Φ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Iso
    (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)))

/-- **Step G3 (matching the kept cusp)**, from the one-curve descriptions of the kernels of the
fillings: there are `g ∈ Π_{X₂}`, `φ' : Π_{V₁} ≅ Π_{V₂}` over `conj(g) ∘ Φ` along the
`[N]`-covers, and `Ψ : Π_{X₁} ≅ Π_{X₂}` with `fill₂ ∘ φ' = Ψ ∘ fill₁`. -/
theorem exists_mulNFill_match_of (hE₁ : TorsionCardN E₁ N) (hE₂ : TorsionCardN E₂ N)
    (hK₁ : ∀ I ∈ arithCusps Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁), ∃ g₀,
      (mulNFill₃ Ω₁ E₁ N hne₁ α₁).ker = (Subgroup.normalClosure
        (dupCuspSet (mulNC₃ Ω₁ E₁ N hne₁).toMonoidHom I g₀)).topologicalClosure)
    (hK₂ : ∀ I ∈ arithCusps Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂), ∃ g₀,
      (mulNFill₃ Ω₂ E₂ N hne₂ α₂).ker = (Subgroup.normalClosure
        (dupCuspSet (mulNC₃ Ω₂ E₂ N hne₂).toMonoidHom I g₀)).topologicalClosure) :
    ∃ (g : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi)
      (φ' : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
          (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
          (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi)
      (Ψ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi),
      (∀ v, mulNC₃ Ω₂ E₂ N hne₂ (φ' v) = g * Φ.pi (mulNC₃ Ω₁ E₁ N hne₁ v) * g⁻¹) ∧
        ∀ v, mulNFill₃ Ω₂ E₂ N hne₂ α₂ (φ' v) = Ψ (mulNFill₃ Ω₁ E₁ N hne₁ α₁ v) := by
  haveI : (mulNC₃ Ω₂ E₂ N hne₂).toMonoidHom.range.Normal := mulNPiU_normal Ω₂ hE₂
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
  obtain ⟨φ, hφ⟩ := exists_lift_of_map_range (mulNC₃ Ω₁ E₁ N hne₁) (mulNC₃ Ω₂ E₂ N hne₂)
    (mulNC₃_injective Ω₁ E₁ N hne₁) (mulNC₃_injective Ω₂ E₂ N hne₂) Φ.pi
    (map_mulNPiU Ω₁ Ω₂ Φ hE₁ hE₂)
  obtain ⟨g, φ', hφ', hmap⟩ := exists_twist_map_closure_dupCuspSet (mulNC₃ Ω₁ E₁ N hne₁)
    (mulNC₃ Ω₂ E₂ N hne₂) (mulNC₃_injective Ω₂ E₂ N hne₂) Φ.pi.toMulEquiv φ hφ hI g₁ g₂
  rw [← hg₁, ← hg₂] at hmap
  let f₁ : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
      (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁))).Pi →ₜ*
      (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi :=
    ⟨mulNFill₃ Ω₁ E₁ N hne₁ α₁, continuous_cor38Fill₂ Ω₁ _ _ _ _ hne₁ α₁⟩
  let f₂ : (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
      (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi →ₜ*
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi :=
    ⟨mulNFill₃ Ω₂ E₂ N hne₂ α₂, continuous_cor38Fill₂ Ω₂ _ _ _ _ hne₂ α₂⟩
  obtain ⟨Ψ, hΨ⟩ := exists_quotient_iso f₁ f₂ (cor38Fill_surjective₂ Ω₁ _ _ _ _ hne₁ α₁)
    (cor38Fill_surjective₂ Ω₂ _ _ _ _ hne₂ α₂) φ' hmap
  exact ⟨g, φ', Ψ, hφ', hΨ⟩

/-- **Step G3**: unconditional form of `exists_mulNFill_match_of`. -/
theorem exists_mulNFill_match (hE₁ : TorsionCardN E₁ N) (hE₂ : TorsionCardN E₂ N) :
    ∃ (g : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi)
      (φ' : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
          (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
          (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi)
      (Ψ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi),
      (∀ v, mulNC₃ Ω₂ E₂ N hne₂ (φ' v) = g * Φ.pi (mulNC₃ Ω₁ E₁ N hne₁ v) * g⁻¹) ∧
        ∀ v, mulNFill₃ Ω₂ E₂ N hne₂ α₂ (φ' v) = Ψ (mulNFill₃ Ω₁ E₁ N hne₁ α₁ v) :=
  exists_mulNFill_match_of Ω₁ E₁ Ω₂ E₂ N hne₁ hne₂ α₁ α₂ Φ hE₁ hE₂
    (fun _ hI ↦ exists_ker_mulNFill_eq Ω₁ E₁ N hne₁ α₁ hE₁ hI)
    (fun _ hI ↦ exists_ker_mulNFill_eq Ω₂ E₂ N hne₂ α₂ hE₂ hI)

/-- `Φ.g` as a map of absolute Galois groups. -/
abbrev gΦN (y : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₁ Ω₁)))) :
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₂ Ω₂))) :=
  Φ.g y

/-- **[AbsTopII] Corollary 3.4 for `X = E ∖ {O}`, `U_X = E ∖ E[N]` (existence)**
(`Topics in Absolute Anabelian Geometry II.txt` l.4540–4596): for elliptic curves `E_i` over
number fields with `#E_i(K_i)[N] = N²`, every isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal
extensions lifts along the fillings `Π_{E_i∖E_i[N]} ↠ Π_{E_i∖O}` to an isomorphism
`φ_U : Π_{E₁∖E₁[N]} ≅ Π_{E₂∖E₂[N]}`. Input: the existence half of the rel-isom-DGC (`hDGC`), used
once on `E₂ ∖ {O}`; uniqueness up to the kernel is `cor34_mulN_unique`. -/
theorem cor34_mulN (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hE₁ : TorsionCardN E₁ N) (hE₂ : TorsionCardN E₂ N) :
    ∃ φU : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
          (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
          (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi,
      ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂ α₂
          (φU e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁ α₁
          e) := by
  obtain ⟨g, φ', Ψ, hc, hf⟩ := exists_mulNFill_match Ω₁ E₁ Ω₂ E₂ N hne₁ hne₂ α₁ α₂ Φ hE₁ hE₂
  obtain ⟨t₁, ht₁⟩ := exists_pr_cor38Fill₃ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N)
    (VNE_le_XE E₁ N) hne₁ α₁
  obtain ⟨t₂, ht₂⟩ := exists_pr_cor38Fill₃ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N)
    (VNE_le_XE E₂ N) hne₂ α₂
  have ha₁ := pr_coverPiHom_self₃ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (hypCurveVN E₁ N)
    (compl_VNE_nonempty E₁ N) (mulByNXMor E₁ N) (mulByNXMor_spec E₁ N)
  have ha₂ := pr_coverPiHom_self₃ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (hypCurveVN E₂ N)
    (compl_VNE_nonempty E₂ N) (mulByNXMor E₂ N) (mulByNXMor_spec E₂ N)
  set a₁ := coverG Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (hypCurveVN E₁ N)
    (compl_VNE_nonempty E₁ N) (mulByNXMor E₁ N) (mulByNXMor_spec E₁ N)
  set a₂ := coverG Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (hypCurveVN E₂ N)
    (compl_VNE_nonempty E₂ N) (mulByNXMor E₂ N) (mulByNXMor_spec E₂ N)
  -- `Ψ` lies over `conj(T) ∘ Φ.g`
  have hT : ∀ x, projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Ψ x) =
      (t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
        gΦN Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹)) *
        (gΦN Ω₁ E₁ Ω₂ E₂ Φ (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) x)) *
        (t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
        gΦN Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹))⁻¹ := by
    intro x
    obtain ⟨v, rfl⟩ := cor38Fill_surjective₂ Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N)
      (VNE_le_XE E₁ N) hne₁ α₁ x
    have e1 := ht₂ (φ' v)
    have e2 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (mulNC₃ Ω₂ E₂ N hne₂ (φ' v)) =
        a₂ * projGk Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
          (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂)) (φ' v) * a₂⁻¹ :=
      ha₂ (φ' v)
    have e3 := congrArg (projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)) (hc v)
    have e4 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Φ.pi (mulNC₃ Ω₁ E₁ N hne₁ v)) =
        gΦN Ω₁ E₁ Ω₂ E₂ Φ
          (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (mulNC₃ Ω₁ E₁ N hne₁ v)) :=
      Φ.pr_comm _
    have e5 : projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (mulNC₃ Ω₁ E₁ N hne₁ v) =
        a₁ * projGk Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
          (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁)) v * a₁⁻¹ :=
      ha₁ v
    have e6 := ht₁ v
    rw [← hf v]
    change projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)
      (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂ α₂
        (φ' v)) = _
    rw [e1]
    have e2' : projGk Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
        (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂)) (φ' v) =
        a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (mulNC₃ Ω₂ E₂ N hne₂ (φ' v)) *
          a₂ := by
      rw [e2]
      group
    rw [e2', e3, map_mul, map_mul, map_inv, e4,
      e5, e6]
    simp only [map_mul, map_inv]
    group
  obtain ⟨s, hs⟩ : ∃ s : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi,
      projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) s =
        t₂ * a₂⁻¹ * projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) g *
          gΦN Ω₁ E₁ Ω₂ E₂ Φ (a₁ * t₁⁻¹) :=
    projGk_surjective Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) _
  let θ : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi :=
    (Ψ.symm.trans Φ.pi).trans (conjCME₃ s)
  have hθ : ∀ y, projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (θ y) =
      projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) y := fun y ↦ by
    have h1 := hT (Ψ.symm y)
    rw [ContinuousMulEquiv.apply_symm_apply] at h1
    have h2 : projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (Φ.pi (Ψ.symm y)) =
        gΦN Ω₁ E₁ Ω₂ E₂ Φ (projGk Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (Ψ.symm y)) :=
      Φ.pr_comm _
    change projGk Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (s * Φ.pi (Ψ.symm y) * s⁻¹) = _
    rw [map_mul, map_mul, map_inv, h2, hs, h1]
  obtain ⟨F, hFK, hFθ⟩ := exists_isConjInduced_of_relIsomDGC Ω₂ (C₁ := hypCurveX E₂)
    (C₂ := hypCurveX E₂) (hc₁ := compl_XE_nonempty E₂) (hc₂ := compl_XE_nonempty E₂)
    (hDGC K₂) θ hθ
  obtain ⟨-, -, -, θV₀, -, hs''⟩ := exists_isoVNE_piV_of_isoXE Ω₂ E₂ N (compl_XE_nonempty E₂)
    hne₂ α₂ F hFK θ hFθ
  obtain ⟨θV, s', hs'⟩ : ∃ (θV : (arithmeticExt Ω₂
        (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
        (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
        (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi)
      (s' : (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).Pi), ∀ σ,
      cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂ α₂
          (θV σ) =
        s' * θ (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂
          α₂ σ) * s'⁻¹ := ⟨θV₀, hs''⟩
  obtain ⟨w', hw'⟩ := cor38Fill_surjective₂ Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N)
    (VNE_le_XE E₂ N) hne₂ α₂ (s' * s)
  have hθΨ : ∀ x, θ (Ψ x) = s * Φ.pi x * s⁻¹ := fun x ↦ by
    change s * Φ.pi (Ψ.symm (Ψ x)) * s⁻¹ = _
    rw [ContinuousMulEquiv.symm_apply_apply]
  refine ⟨(φ'.trans θV).trans (conjCME₃ w'⁻¹), fun e ↦ ?_⟩
  have hfe : cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂ α₂
      (φ' e) = Ψ (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N) (VNE_le_XE E₁ N)
        hne₁ α₁ e) := hf e
  have hz := (hs' (φ' e)).trans (by rw [hfe, hθΨ])
  exact conj_fill_auxN _ _ _ _ _ _ hw' hz

omit [NeZero N] in
/-- **[AbsTopII] Corollary 3.4 for `E ∖ E[N] ⊆ E ∖ {O}`, uniqueness**: two lifts of `Φ` differ by
conjugation with an element of the kernel of the filling (`cor38_unique`). -/
theorem cor34_mulN_unique (hDGC : RelIsomDGC.Exists K₂)
    (φ₁ φ₂ : (arithmeticExt Ω₁ (subCurve (hypCurveX E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁)
          (compl_nonempty_of_le (VNE_le_XE E₁ N) (compl_XE_nonempty E₁))).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve (hypCurveX E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂)
          (compl_nonempty_of_le (VNE_le_XE E₂ N) (compl_XE_nonempty E₂))).Pi)
    (h₁ : ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N)
          hne₂ α₂ (φ₁ e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁ α₁
          e))
    (h₂ : ∀ e, cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N)
          hne₂ α₂ (φ₂ e) =
        Φ.pi (cor38Fill Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁) (VNE E₁ N) (VNE_le_XE E₁ N) hne₁ α₁
          e)) :
    ∃ n ∈ (cor38Fill Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂
      α₂).ker, ∀ e, φ₂ e = n * φ₁ e * n⁻¹ :=
  cor38_unique Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂) (VNE E₂ N) (VNE_le_XE E₂ N) hne₂ α₂ hDGC
    φ₁ φ₂
    fun e ↦ (h₂ e).trans (h₁ e).symm

end TwoCurves

end CurvesJacobian.Cusp
