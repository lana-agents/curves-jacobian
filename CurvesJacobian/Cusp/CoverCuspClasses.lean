/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DupDecomp
import CurvesJacobian.Cusp.CoverCuspComap

/-!
# Cusps of a cover are the pull-backs of the conjugates of one cusp ([AbsTopII] Cor 3.4, step G3)

For affine hyperbolic curves `C` over `K` and `C'` over `K' ⊇ K` (with cusps) and a finite étale
`F : Spec Γ(U') ⟶ Spec Γ(U)` over `Spec K' ⟶ Spec K`, with `c = coverPiHom F : Π_{U'} ↪ Π_U`:

* **`exists_conj_eq_of_mem_arithCusps₂`** (B0): if `U_Ω` has (at most) one cusp, any two
  cuspidal inertia groups of `Π_U` are conjugate by an element of `Δ_U`
  (`exists_comap_eq_of_isCuspPlace₂` moves the place, `arithInertia_comap` conjugates);
* **`comap_map_conj_mem_arithCusps₂`** (B1): `c⁻¹(g I g⁻¹)` is a cuspidal inertia group of
  `Π_{U'}` for every cuspidal inertia group `I` of `Π_U` and every `g`;
* **`exists_eq_comap_of_mem_arithCusps₂`** (B2): every cuspidal inertia group `J` of `Π_{U'}` is
  `c⁻¹(I)` for a cuspidal inertia group `I` of `Π_U`: `c(J) ⊆ I` with finite index
  (`exists_arithCusps_map_coverPiHom`), so `J ⊆ c⁻¹(I) ⊆ Comm(J) ∩ Δ_{U'} = J`;
* **`exists_conj_eq_comap₂`**: combined, if `U_Ω` has one cusp and `I₀` is a cuspidal inertia
  group of `Π_U`, every cuspidal inertia group of `Π_{U'}` is `c⁻¹(g I₀ g⁻¹)`;
* (B3) the instance for `[2] : E ∖ E[2] → E ∖ {O}` (`dupPiU_eq_range₂`,
  `comap_dup_mem_arithCusps₂`, `exists_dup_conj_eq_comap₂`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section OneCusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **(B0) One geometric cusp ⇒ all cuspidal inertia groups of `Π_U` are conjugate**, by an
element of `Δ_U`. -/
theorem exists_conj_eq_of_mem_arithCusps₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {I I' : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hI : I ∈ arithCusps Ω C hc) (hI' : I' ∈ arithCusps Ω C hc) :
    ∃ g : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      projGk Ω C hc g = 1 ∧ I' = I.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω C hc).1 hI
  obtain ⟨W', hW', rfl⟩ := (mem_arithCusps_iff Ω C hc).1 hI'
  obtain ⟨n, hpr, hn⟩ := exists_comap_eq_of_isCuspPlace₂ Ω C hc h1 hW hW'
  refine ⟨arithAction Ω C hc n, hpr, ?_⟩
  rw [hn]
  exact arithInertia_comap Ω C hc W n

end OneCusp

section Cover

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {K' : Type u} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra.IsAlgebraic K' Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale F]
  (hF : F ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')))

attribute [local instance] isAlgClosure_of_isAlgebraic

include hF in
/-- **(B1)** The preimage in `Π_{U'}` of a conjugate of a cuspidal inertia group of `Π_U` is a
cuspidal inertia group. -/
theorem comap_map_conj_mem_arithCusps₂
    {I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hI : I ∈ arithCusps Ω C hc) (g : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    (I.map (MulAut.conj g).toMonoidHom).comap (coverPiHom Ω C hc C' hc' F).toMonoidHom ∈
      arithCusps Ω C' hc' :=
  comap_coverPiHom_mem_arithCusps Ω C hc C' hc' F hF (map_conj_mem_arithCusps Ω C hc hI g)

include hF in
/-- **(B2) Every cuspidal inertia group of `Π_{U'}` is the preimage of a cuspidal inertia group
of `Π_U`.** -/
theorem exists_eq_comap_of_mem_arithCusps₂
    {J : Subgroup π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))}
    (hJ : J ∈ arithCusps Ω C' hc') :
    ∃ I ∈ arithCusps Ω C hc, J = I.comap (coverPiHom Ω C hc C' hc' F).toMonoidHom := by
  obtain ⟨I, hI, hJI, hfin⟩ := exists_arithCusps_map_coverPiHom Ω C hc C' hc' F hJ
  refine ⟨I, hI, ?_⟩
  set f := (coverPiHom Ω C hc C' hc' F).toMonoidHom
  have hinj : Function.Injective f := coverPiHom_injective Ω C hc C' hc' F
  have hle : J ≤ I.comap f := Subgroup.map_le_iff_le_comap.1 hJI
  have hfin' : J.relIndex (I.comap f) ≠ 0 := by
    have h1 : J.map f ≤ f.range ⊓ I := le_inf (Subgroup.map_le_range f J) hJI
    have h2 := Subgroup.relIndex_mul_relIndex (J.map f) (f.range ⊓ I) I h1 inf_le_right
    have h3 : (J.map f).relIndex (f.range ⊓ I) ≠ 0 := left_ne_zero_of_mul (h2.symm ▸ hfin)
    have e1 := Subgroup.relIndex_map_map_of_injective J (I.comap f) hinj
    have e2 : (I.comap f).map f = f.range ⊓ I := Subgroup.map_comap_eq f I
    exact e1 ▸ e2.symm ▸ h3
  have hcomm : Subgroup.Commensurable J (I.comap f) :=
    ⟨hfin', (Subgroup.relIndex_eq_one.2 hle).symm ▸ one_ne_zero⟩
  refine le_antisymm hle ?_
  rw [← commensurator_inf_of_mem_arithCusps Ω C' hc' hJ, Subgroup.Commensurable.eq hcomm]
  exact le_inf (fun g hg ↦ mem_commensurator_of_mem hg)
    ((Subgroup.comap_mono (arithCusps_le Ω C hc hI)).trans
      (comap_coverPiHom_ker_projGk_le Ω C hc C' hc' F hF))

include hF in
/-- **(B0) + (B2)**: if `U_Ω` has one cusp and `I₀` is a cuspidal inertia group of `Π_U`, every
cuspidal inertia group of `Π_{U'}` is the preimage of a `Δ_U`-conjugate of `I₀`. -/
theorem exists_conj_eq_comap₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {I₀ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hI₀ : I₀ ∈ arithCusps Ω C hc)
    {J : Subgroup π₁ᵉᵗ(basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))}
    (hJ : J ∈ arithCusps Ω C' hc') :
    ∃ g : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)), projGk Ω C hc g = 1 ∧
      J = (I₀.map (MulAut.conj g).toMonoidHom).comap
        (coverPiHom Ω C hc C' hc' F).toMonoidHom := by
  obtain ⟨I, hI, rfl⟩ := exists_eq_comap_of_mem_arithCusps₂ Ω C hc C' hc' F hF hJ
  obtain ⟨g, hg, hgI⟩ := exists_conj_eq_of_mem_arithCusps₂ Ω C hc h1 hI₀ hI
  exact ⟨g, hg, by rw [← hgI]⟩

end Cover

/-! ### (B3) The `[2]`-cover `E ∖ E[2] → E ∖ {O}` -/

section Dup

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K) [E.IsElliptic]

attribute [local instance] isAlgClosure_of_isAlgebraic

instance isFiniteEtale_dupCover₂ :
    IsFiniteEtale (X := Spec Γ((hypCurveV E).Xbar, (hypCurveV E).U))
      (Y := Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U)) (coverXMorK E) :=
  isFiniteEtale_coverXMorK E

/-- `[2] : E ∖ E[2] → E ∖ {O}` lies over `Spec K`. -/
lemma coverXMorK_over₂ : coverXMorK E ≫
    Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ((hypCurveV E).Xbar, (hypCurveV E).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
  change coverXMorK E ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) = _
  simp only [coverXMorK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun c ↦ coverXHom_algebraMap E c

/-- `Π_U = im(c : Π_{E∖E[2]} → Π_{E∖O})`. -/
lemma dupPiU_eq_range₂ : dupPiU Ω E =
    (coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
      (coverXMorK E)).toMonoidHom.range :=
  rfl

/-- **(B1) for `[2]`**: preimages of conjugates of cuspidal inertia groups of `Π_{E∖O}` are
cuspidal inertia groups of `Π_{E∖E[2]}`. -/
theorem comap_dup_mem_arithCusps₂
    {I : Subgroup π₁ᵉᵗ(basePoint Ω (hypCurveX E) (compl_XE_nonempty E) ≫
      baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U))}
    (hI : I ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E))
    (g : π₁ᵉᵗ(basePoint Ω (hypCurveX E) (compl_XE_nonempty E) ≫
      baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U))) :
    (I.map (MulAut.conj g).toMonoidHom).comap
        (coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
          (coverXMorK E)).toMonoidHom ∈ arithCusps Ω (hypCurveV E) (hcV_dup E) :=
  comap_map_conj_mem_arithCusps₂ Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
    (coverXMorK E) (coverXMorK_over₂ E) hI g

/-- **(B2) + (B0) for `[2]`**: every cuspidal inertia group of `Π_{E∖E[2]}` is the preimage of a
`Δ`-conjugate of a fixed cuspidal inertia group `I₀` of `Π_{E∖O}`. -/
theorem exists_dup_conj_eq_comap₂
    {I₀ : Subgroup π₁ᵉᵗ(basePoint Ω (hypCurveX E) (compl_XE_nonempty E) ≫
      baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U))}
    (hI₀ : I₀ ∈ arithCusps Ω (hypCurveX E) (compl_XE_nonempty E))
    {J : Subgroup π₁ᵉᵗ(basePoint Ω (hypCurveV E) (hcV_dup E) ≫
      baseChangeSpec K Ω Γ((hypCurveV E).Xbar, (hypCurveV E).U))}
    (hJ : J ∈ arithCusps Ω (hypCurveV E) (hcV_dup E)) :
    ∃ g : π₁ᵉᵗ(basePoint Ω (hypCurveX E) (compl_XE_nonempty E) ≫
        baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)),
      projGk Ω (hypCurveX E) (compl_XE_nonempty E) g = 1 ∧
        J = (I₀.map (MulAut.conj g).toMonoidHom).comap
          (coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
            (coverXMorK E)).toMonoidHom :=
  exists_conj_eq_comap₂ Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
    (coverXMorK E) (coverXMorK_over₂ E) (subsingleton_compl_geomOpen_XE₂ Ω E) hI₀ hJ

end Dup

end CurvesJacobian.Cusp
