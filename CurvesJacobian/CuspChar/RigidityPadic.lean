/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspRigidityFill
import CurvesJacobian.CuspChar.ArithTop
import CurvesJacobian.CuspChar.FinalPadic

/-!
# [GalSect] Thm. 4.3 over `p`-adic fields: the arithmetic layer

[GalSect] = *Galois sections in absolute anabelian geometry* (`Galois Sections.txt`), Thm. 4.3
(l.841–882) is stated for an isomorphism `α : Π_{X_K} ≅ Π_{Y_L}` of arithmetic fundamental groups
of hyperbolic curves over `p`-adic fields. `Kummer/CuspRigidity*.lean` proves it for the geometric
data (`α_U : Δ_U ≃ₜ* Δ_V` in Galois models, `α_U(I_x) = I_y`, compatibility with filling in the
other cusps). This file supplies the arithmetic layer, for affine hyperbolic curves `U`, `U'` over
finite extensions `K/ℚ_p`, `K'/ℚ_{p'}` (cj's arithmetic model `π₁ᵉᵗ(U)` of `Cusp/ArithmeticSlim`):

* **[AbsAnab] Lemma 1.3.8** (`Absolute Anabelian Geometry.txt` l.977–985: `α` is compatible with
  the quotients `Π ↠ G_K`) enters as the named hypothesis `ArithQuotientPreservedPadic` (debt,
  `MR13-plan.md`): its proof ("formally from Lemmas 1.1.4, 1.1.5") needs, besides local class
  field theory, Lemma 1.1.5 on Tate modules of semi-abelian varieties over `p`-adic fields
  (Faltings–Chai degenerations, Riemann hypothesis over finite fields);
* `gkEquivOfDelta`, `projGk_gkEquivOfDelta`: the induced `G_K ≃ₜ* G_{K'}`, so that
  `mem_arithCusps_iff_map_mem_of_lemma138`: every isomorphism `Π_U ≃ₜ* Π_{U'}` preserves the
  cuspidal inertia groups (via [AbsTopI] Lemma 4.5 (v), `mem_arithCusps_iff_map_mem_padic`);
* **the bridge** `geomEquivOfDelta`: `Δ_U ≃ₜ* Δ_{U'}` transported along `deltaGeomEquiv` to the
  Galois models `π₁ᵉᵗ(U_Ω) ≃ₜ* π₁ᵉᵗ(U'_{Ω'})`, with `mem_geomCusps_iff_map_padic` (cusps go to
  cusps) and `exists_map_cuspInertia_padic` (`α_U(I_x) = I_y` for some cusp `y`);
* **filling compatibility** `map_ker_fillOpen_of_cusps` (Galois models, generic) and
  `map_ker_fillOpen_padic`: `α_U(ker(Δ_U ↠ Δ_{X∖x})) = ker(Δ_V ↠ Δ_{Y∖y})`, from cusp preservation
  and "conjugate cuspidal inertia groups lie over the same point"
  (`CuspChar.mem_iff_of_cuspInertia_conj_hyp`, valid for every hyperbolic `U`; no lower bound on
  the number of cusps, unlike `Cusp.relIndex_cuspInertia_eq_zero_of_comapK_ne`);
* **`rigidity_cuspInertia_padic`**: [GalSect] Thm. 4.3 for `Φ : Π_U ≃ₜ* Π_{U'}`
  (compactifications of
  genus `≥ 1`), modulo the two debts `ArithQuotientPreservedPadic` ([AbsAnab] Lemma 1.3.8) and
  `DegOneChernPreserved` ([AbsAnab] Lemma 2.5(ii)) for the filled isomorphism `fillEquivPadic`;
  the cyclotome isomorphism `β` is an input, as in [GalSect]'s statement.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen WeilCurves.FunctionField Belyi.Anabelian

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspRigidity

open ChernClass

universe u v

/-! ### Filling compatibility from cusp preservation (Galois models) -/

section Conj

variable {A B : Type*} [Group A] [Group B]

lemma map_map_conj (α : A ≃* B) (g : A) (I : Subgroup A) :
    (I.map (MulAut.conj g).toMonoidHom).map α.toMonoidHom =
      (I.map α.toMonoidHom).map (MulAut.conj (α g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

/-- If `α(I) = J^γ` and `α(I₀) = J`, then `I = I₀^{α⁻¹ γ}`. -/
lemma eq_map_conj_of_map (α : A ≃* B) {I I₀ : Subgroup A} {J : Subgroup B} (γ : B)
    (hI : I.map α.toMonoidHom = J.map (MulAut.conj γ).toMonoidHom)
    (hI₀ : I₀.map α.toMonoidHom = J) :
    I = I₀.map (MulAut.conj (α.symm γ)).toMonoidHom := by
  apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
  rw [map_map_conj, hI₀, MulEquiv.apply_symm_apply, hI]

end Conj

section CentredOn

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {D : GaloisData k t}
  {X : Scheme.{u}} [IsIntegral X] {eL : X.functionField ≃+* D.L}

/-- A place centred on `U` is centred on every larger open `U'`. -/
lemma isCentredOn_mono {U U' : X.Opens} [Nonempty U] [Nonempty U'] (hUU' : U ≤ U')
    {W : ValuationSubring Ω} (h : IsCentredOn D X eL U W) : IsCentredOn D X eL U' W := by
  refine ⟨h.1, fun a ↦ ?_⟩
  rw [← CurvesJacobian.germToFunctionField_res (homOfLE hUU') a]
  exact h.2 _

end CentredOn

section KerFill

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero Ω] {t : Ω} [IsGalois (K₀ k t) Ω]
  {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U U' : X.Opens} [Nonempty U] [Nonempty U'] {W₀ : ValuationSubring Ω}
  {k' Ω' : Type v} [Field k'] [IsAlgClosed k'] [CharZero k']
  [Field Ω'] [Algebra k' Ω'] [IsAlgClosed Ω'] [CharZero Ω'] {t' : Ω'} [IsGalois (K₀ k' t') Ω']
  {D' : GaloisData k' t'}
  {Y : Scheme.{v}} [Y.Over (Spec (.of k'))] [IsCurveOver k' Y] [IsIntegral Y]
  {eL' : Y.functionField ≃+* D'.L} {hH' : D'.H ≤ D'.HL}
  (hk' : ∀ c : k', ((eL' (algebraMap k' Y.functionField c) : D'.L) : Ω') = algebraMap k' Ω' c)
  {τ' : Y.functionField} (hτ' : ((eL' τ' : D'.L) : Ω') = t')
  {V V' : Y.Opens} [Nonempty V] [Nonempty V'] {W₁ : ValuationSubring Ω'}

/-- Being centred on `U` only depends on the place of `F` below. -/
lemma isCentredOn_congr (hH : D.H ≤ D.HL) (U : X.Opens) [Nonempty U]
    {W W' : ValuationSubring Ω} (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hF : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W') :
    IsCentredOn D X eL U W → IsCentredOn D X eL U W' := fun h ↦
  ⟨hkW', fun a ↦ (hF (CuspChar.secF D X eL hH U a)).1 (h.2 a)⟩

include hk hτ hk' in
/-- **A cusp other than `x` goes to a cusp other than `y`.** Let `U ⊆ U'` with `U'` missing only
the point under `W₀`, `V ⊆ V'` with `V'` missing at most one point (the one under `W₁`), and
`α_U : Δ_U ≃ₜ* Δ_V` mapping cuspidal inertia groups to cuspidal inertia groups with
`α_U(I_{W₀}) = I_{W₁}`. Then for a cusp `W` of `U` centred on `U'`, `α_U(I_W) = I_{W'}` for a cusp
`W'` of `V` centred on `V'`. (Conjugate cuspidal inertia groups lie over the same point,
`CuspChar.mem_iff_of_cuspInertia_conj_hyp`; this needs only `U` hyperbolic.) -/
theorem exists_map_cuspInertia_isCentredOn (hU : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    (hUU' : U ≤ U') (hV' : ((⊤ : Set Y) \ V').Subsingleton)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hcusp : ∀ I ∈ cusps D X eL hH U, I.map αU.toMulEquiv.toMonoidHom ∈ cusps D' Y eL' hH' V)
    (hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀) (hW₀U' : ¬ IsCentredOn D X eL U' W₀)
    (hkW₁ : ∀ c : k', algebraMap k' Ω' c ∈ W₁) (hW₁V' : ¬ IsCentredOn D' Y eL' V' W₁)
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁)
    {W : ValuationSubring Ω} (hWU' : IsCentredOn D X eL U' W) (hWU : ¬ IsCentredOn D X eL U W) :
    ∃ W' : ValuationSubring Ω', IsCentredOn D' Y eL' V' W' ∧ ¬ IsCentredOn D' Y eL' V W' ∧
      (cuspInertia D X eL hH U W).map αU.toMulEquiv.toMonoidHom =
        cuspInertia D' Y eL' hH' V W' := by
  obtain ⟨W', hkW', hW'V, hW'⟩ := hcusp _ ⟨W, hWU'.1, hWU, rfl⟩
  refine ⟨W', ?_, hW'V, hW'⟩
  by_contra hW'V'
  have hcomap := comap_algebraMap_eq_of_isCentredOn D' Y eL' hk' (U := V') (V := ⊤)
    (by simp) hV' (ChernClass.isCentredOn_top_of hk' hkW₁) hW₁V'
    (ChernClass.isCentredOn_top_of hk' hkW') hW'V'
  obtain ⟨γ, hγ⟩ := exists_cuspInertia_eq_conj D' Y eL' hH' V W₁ W' hcomap
  have hconj := eq_map_conj_of_map αU.toMulEquiv γ (hW'.trans hγ) hI
  have hW₀U : ¬ IsCentredOn D X eL U W₀ := fun h ↦ hW₀U' (isCentredOn_mono hUU' h)
  have hF := CuspChar.mem_iff_of_cuspInertia_conj_hyp D X eL hk hH hτ hU hhyp hkW₀ hWU'.1 hW₀U
    hWU ⟨_, hconj⟩
  exact hW₀U' (isCentredOn_congr hH U' hkW₀ (fun x ↦ (hF x).symm) hWU')

include hk hτ hk' hτ' in
/-- One inclusion of `map_ker_fillOpen_of_cusps`. -/
theorem map_ker_fillOpen_le (hU : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    (hUU' : U ≤ U') (hU' : (U' : Set X)ᶜ.Finite) (hV : (V : Set Y)ᶜ.Finite) (hVV' : V ≤ V')
    (hV' : (V' : Set Y)ᶜ.Finite) (hV'1 : ((⊤ : Set Y) \ V').Subsingleton)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hcusp : ∀ I ∈ cusps D X eL hH U, I.map αU.toMulEquiv.toMonoidHom ∈ cusps D' Y eL' hH' V)
    (hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀) (hW₀U' : ¬ IsCentredOn D X eL U' W₀)
    (hkW₁ : ∀ c : k', algebraMap k' Ω' c ∈ W₁) (hW₁V' : ¬ IsCentredOn D' Y eL' V' W₁)
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁) :
    (fillOpen D eL hUU').ker.map αU.toMulEquiv.toMonoidHom ≤ (fillOpen D' eL' hVV').ker := by
  rw [Subgroup.map_le_iff_le_comap]
  have hkerU := ker_fundamentalGroupMap_homOfLE_eq_cuspInertia D X eL hH hk hτ hU hU' hUU'
  have hkerV := ker_fundamentalGroupMap_homOfLE_eq_cuspInertia D' Y eL' hH' hk' hτ' hV hV' hVV'
  change (fundamentalGroupMap (X.homOfLE hUU')
    (specPoint_genericL_homOfLE D X eL hUU')).toMonoidHom.ker ≤ _
  rw [hkerU]
  have hcl : IsClosed (((fillOpen D' eL' hVV').ker.comap αU.toMulEquiv.toMonoidHom : Subgroup _) :
      Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :=
    (isClosed_singleton.preimage (continuous_fillOpen hVV')).preimage αU.continuous
  haveI : ((fillOpen D' eL' hVV').ker.comap αU.toMulEquiv.toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
  intro s hs
  obtain ⟨W, ⟨hWU', hWU⟩, hsW⟩ := Set.mem_iUnion₂.1 hs
  obtain ⟨W', hW'V', hW'V, hW'⟩ := exists_map_cuspInertia_isCentredOn hk hτ hk' hU hhyp hUU' hV'1
    αU hcusp hkW₀ hW₀U' hkW₁ hW₁V' hI hWU' hWU
  have hmem : αU s ∈ cuspInertia D' Y eL' hH' V W' := by
    rw [← hW']
    exact Subgroup.mem_map_of_mem _ hsW
  change αU s ∈ (fundamentalGroupMap (Y.homOfLE hVV')
    (specPoint_genericL_homOfLE D' Y eL' hVV')).toMonoidHom.ker
  rw [hkerV]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_normalClosure (Set.mem_iUnion₂.2 ⟨W', ⟨hW'V', hW'V⟩, hmem⟩))

include hk hτ hk' hτ' in
/-- **Filling compatibility from cusp preservation** (the hypothesis `hker` of
`rigidity_cuspInertia_fill`). For `U ⊆ U' = X ∖ {x}`, `V ⊆ V' = Y ∖ {y}` with `U`, `V`
hyperbolic, and `α_U : Δ_U ≃ₜ* Δ_V` mapping the cuspidal inertia groups of `Δ_U` exactly onto
those of `Δ_V` with `α_U(I_x) = I_y`: `α_U(ker(Δ_U ↠ Δ_{U'})) = ker(Δ_V ↠ Δ_{V'})` (both kernels
are the closed normal subgroups generated by the inertia groups of the cusps other than `x`,
resp. `y`, `ker_fundamentalGroupMap_homOfLE_eq_cuspInertia`). Unlike
`Cusp.relIndex_cuspInertia_eq_zero_of_comapK_ne`, no lower bound on the number of cusps is
needed. -/
theorem map_ker_fillOpen_of_cusps (hU : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    (hUU' : U ≤ U') (hU' : (U' : Set X)ᶜ.Finite) (hU'1 : ((⊤ : Set X) \ U').Subsingleton)
    (hV : (V : Set Y)ᶜ.Finite)
    (hhyp' : 2 < 2 * (curveGenus k' Y).toNat + Nat.card ((V : Set Y)ᶜ : Set Y))
    (hVV' : V ≤ V') (hV' : (V' : Set Y)ᶜ.Finite) (hV'1 : ((⊤ : Set Y) \ V').Subsingleton)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hcusp : ∀ I, I ∈ cusps D X eL hH U ↔ I.map αU.toMulEquiv.toMonoidHom ∈ cusps D' Y eL' hH' V)
    (hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀) (hW₀U' : ¬ IsCentredOn D X eL U' W₀)
    (hkW₁ : ∀ c : k', algebraMap k' Ω' c ∈ W₁) (hW₁V' : ¬ IsCentredOn D' Y eL' V' W₁)
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁) :
    (fillOpen D eL hUU').ker.map αU.toMulEquiv.toMonoidHom = (fillOpen D' eL' hVV').ker := by
  have hback : ∀ J : Subgroup π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V),
      (J.map αU.symm.toMulEquiv.toMonoidHom).map αU.toMulEquiv.toMonoidHom = J := by
    intro J
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    exact MonoidHom.ext fun y ↦ αU.apply_symm_apply y
  have hfwd : ∀ J : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U),
      (J.map αU.toMulEquiv.toMonoidHom).map αU.symm.toMulEquiv.toMonoidHom = J := by
    intro J
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    exact MonoidHom.ext fun y ↦ αU.symm_apply_apply y
  refine le_antisymm (map_ker_fillOpen_le hk hτ hk' hτ' hU hhyp hUU' hU' hV hVV' hV' hV'1 αU
    (fun I hI ↦ (hcusp I).1 hI) hkW₀ hW₀U' hkW₁ hW₁V' hI) ?_
  have h := map_ker_fillOpen_le hk' hτ' hk hτ hV hhyp' hVV' hV' hU hUU' hU' hU'1 αU.symm
    (fun J hJ ↦ (hcusp _).2 (by rw [hback]; exact hJ)) hkW₁ hW₁V' hkW₀ hW₀U'
    (by rw [← hI, hfwd])
  calc (fillOpen D' eL' hVV').ker
      = ((fillOpen D' eL' hVV').ker.map αU.symm.toMulEquiv.toMonoidHom).map
          αU.toMulEquiv.toMonoidHom := (hback _).symm
    _ ≤ _ := Subgroup.map_mono h

end KerFill

/-! ### The arithmetic layer over `p`-adic fields -/

section Arith

open CuspChar

variable {K : Type u} [Field K] [CharZero K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K' : Type u} [Field K'] [CharZero K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
  {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The isomorphism `G_K ≃ₜ* G_{K'}` induced by `Φ : Π_U ≃ₜ* Π_{U'}` with `Φ(Δ_U) = Δ_{U'}`.** -/
noncomputable def gkEquivOfDelta
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc') :
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))) :=
  inducedContEquiv Φ (p := (projGk Ω C hc).toMonoidHom) (q := (projGk Ω' C' hc').toMonoidHom)
    (projGk Ω C hc).continuous (projGk Ω' C' hc').continuous (projGk_surjective Ω C hc)
    (projGk_surjective Ω' C' hc') hD

/-- `Φ` lies over `gkEquivOfDelta Φ hD`. -/
lemma projGk_gkEquivOfDelta
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc')
    (x : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    projGk Ω' C' hc' (Φ x) = gkEquivOfDelta Φ hD (projGk Ω C hc x) :=
  (inducedContEquiv_apply Φ (p := (projGk Ω C hc).toMonoidHom)
    (q := (projGk Ω' C' hc').toMonoidHom) (projGk Ω C hc).continuous
    (projGk Ω' C' hc').continuous (projGk_surjective Ω C hc) (projGk_surjective Ω' C' hc') hD
    x).symm

/-- **The bridge from the arithmetic model to the Galois model**: `Φ : Π_U ≃ₜ* Π_{U'}` with
`Φ(Δ_U) = Δ_{U'}` restricted to `Δ_U ≃ₜ* Δ_{U'}` and transported along `deltaGeomEquiv` to the
geometric Galois models `π₁ᵉᵗ(U_Ω) ≃ₜ* π₁ᵉᵗ(U'_{Ω'})` used in `Kummer/CuspRigidity*.lean`. -/
noncomputable def geomEquivOfDelta
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc') :
    π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)) ≃ₜ*
    π₁ᵉᵗ(specPoint (geomData Ω' C').L (FFClosure (geomCurve Ω' C')) ≫
      genericL (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω' C'))
        (geomOpen Ω' C')) :=
  (deltaGeomEquiv Ω C hc).symm.trans ((resD Φ hD).trans (deltaGeomEquiv Ω' C' hc'))

lemma map_trans_eq {A B E : Type*} [Group A] [Group B] [Group E] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace E] (e : A ≃ₜ* B) (f : B ≃ₜ* E) (I : Subgroup A) :
    I.map (e.trans f).toMulEquiv.toMonoidHom =
      (I.map e.toMulEquiv.toMonoidHom).map f.toMulEquiv.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

lemma map_symm_map_eq {A B : Type*} [Group A] [Group B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ* B) (I : Subgroup B) :
    (I.map e.symm.toMulEquiv.toMonoidHom).map e.toMulEquiv.toMonoidHom = I := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id I
  exact MonoidHom.ext fun y ↦ e.apply_symm_apply y

lemma map_subtype_map_resD
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc')
    (J : Subgroup (deltaU Ω C hc)) :
    (J.map (deltaU Ω C hc).subtype).map Φ.toMulEquiv.toMonoidHom =
      (J.map (resD Φ hD).toMulEquiv.toMonoidHom).map (deltaU Ω' C' hc').subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

variable (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  (p' : ℕ) [Fact p'.Prime] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']

include p p' in
/-- **Cusp preservation in the Galois models** ([AbsTopI] Lemma 4.5 (v),
`mem_arithCusps_iff_map_mem_padic`, transported along `deltaGeomEquiv`): for `p`-adic `K`, `K'`
and `Φ : Π_U ≃ₜ* Π_{U'}` with `Φ(Δ_U) = Δ_{U'}`, the induced `π₁ᵉᵗ(U_Ω) ≃ₜ* π₁ᵉᵗ(U'_{Ω'})`
maps the cuspidal inertia groups exactly onto the cuspidal inertia groups. -/
theorem mem_geomCusps_iff_map_padic
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc')
    (I : Subgroup π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C))) :
    I ∈ geomCusps Ω C ↔ I.map (geomEquivOfDelta Φ hD).toMulEquiv.toMonoidHom ∈ geomCusps Ω' C' := by
  set J := I.map (deltaGeomEquiv Ω C hc).symm.toMulEquiv.toMonoidHom
  have hJ : J.map (deltaGeomEquiv Ω C hc).toMulEquiv.toMonoidHom = I := map_symm_map_eq _ I
  have hJ' : (J.map (resD Φ hD).toMulEquiv.toMonoidHom).map
      (deltaGeomEquiv Ω' C' hc').toMulEquiv.toMonoidHom =
        I.map (geomEquivOfDelta Φ hD).toMulEquiv.toMonoidHom := by
    rw [geomEquivOfDelta, map_trans_eq, map_trans_eq]
  rw [← hJ, ← mem_deltaCusps_iff_map Ω C hc J, hJ, ← hJ', ← mem_deltaCusps_iff_map Ω' C' hc']
  change J.map (deltaU Ω C hc).subtype ∈ arithCusps Ω C hc ↔
    (J.map (resD Φ hD).toMulEquiv.toMonoidHom).map (deltaU Ω' C' hc').subtype ∈
      arithCusps Ω' C' hc'
  rw [← map_subtype_map_resD Φ hD J]
  exact mem_arithCusps_iff_map_mem_padic p p' Φ (gkEquivOfDelta Φ hD)
    (projGk_gkEquivOfDelta Φ hD) _

end Arith

/-! ### [AbsAnab] Lemma 1.3.8 (debt) and the assembly -/

section Padic

open CuspChar

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharZero K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (p' : ℕ) [Fact p'.Prime] (K' : Type u) [Field K'] [CharZero K'] [Algebra ℚ_[p'] K']
  [FiniteDimensional ℚ_[p'] K'] (Ω' : Type u) [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω']

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsAnab] Lemma 1.3.8 (Group-theoreticity of arithmetic quotients) — a named hypothesis
(debt, `MR13-plan.md`).** For affine hyperbolic curves `U`, `U'` over finite extensions `K/ℚ_p`,
`K'/ℚ_{p'}`, every isomorphism `Φ : Π_U ≃ₜ* Π_{U'}` of arithmetic fundamental groups maps
`Δ_U = ker(Π_U ↠ G_K)` onto `Δ_{U'}`. (`Absolute Anabelian Geometry.txt` l.977–985: Lemma 1.3.8,
"follows formally from Lemmas 1.1.4, 1.1.5"; Lemma 1.1.4(ii), l.258–313, characterises `Δ` by
the dimensions `dim_{ℚ_p}(Π'^{ab} ⊗ ℚ_p) - dim_{ℚ_l}(Π'^{ab} ⊗ ℚ_l) = [K' : ℚ_p]` of open
subgroups — local class field theory — given the hypothesis `(∗)` on the Galois coinvariants of
`Δ'^{ab}`, which is Lemma 1.1.5, l.314–354: Tate modules of semi-abelian varieties over `p`-adic
fields, via Faltings–Chai degenerations [FC] Ch. III Cor. 7.3 and the Riemann hypothesis for
abelian varieties over finite fields.) -/
def ArithQuotientPreservedPadic (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharZero K]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (p' : ℕ) [Fact p'.Prime] (K' : Type u)
      [Field K'] [CharZero K'] [Algebra ℚ_[p'] K']
    [FiniteDimensional ℚ_[p'] K'] (Ω' : Type u) [Field Ω'] [Algebra K' Ω'] [IsAlgClosed Ω']
    [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] : Prop :=
  ∀ (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (C' : HypCurve K')
    (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U))),
    (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc'

variable {p K Ω p' K' Ω'} {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}

include p p' in
/-- **Every isomorphism of arithmetic fundamental groups over `p`-adic fields is an isomorphism of
cuspidal extensions**, given [AbsAnab] Lemma 1.3.8 (`ArithQuotientPreservedPadic`, debt): the
quotient isomorphism `G_K ≃ₜ* G_{K'}` is `gkEquivOfDelta`, and cusps are preserved by
`arithmeticExtIso_padic` ([AbsTopI] Lemma 4.5 (v)). -/
theorem mem_arithCusps_iff_map_mem_of_lemma138
    (hΔ : ArithQuotientPreservedPadic p K Ω p' K' Ω')
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    I ∈ arithCusps Ω C hc ↔ I.map Φ.toMulEquiv.toMonoidHom ∈ arithCusps Ω' C' hc' :=
  mem_arithCusps_iff_map_mem_padic p p' Φ (gkEquivOfDelta Φ (hΔ C hc C' hc' Φ))
    (projGk_gkEquivOfDelta Φ (hΔ C hc C' hc' Φ)) I

include p p' in
/-- **A cusp `x` of `U_Ω` goes to a cusp `y` of `U'_{Ω'}`**: `α_U(I_x) = I_y` for the induced
`α_U : π₁ᵉᵗ(U_Ω) ≃ₜ* π₁ᵉᵗ(U'_{Ω'})` (the hypothesis "`α` induces `I_x ≅ I_y`" of [GalSect]
Thm. 4.3, `Galois Sections.txt` l.841–848). -/
theorem exists_map_cuspInertia_padic (hΔ : ArithQuotientPreservedPadic p K Ω p' K' Ω')
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    {W₀ : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkW₀ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W₀)
    (hW₀U : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W₀) :
    ∃ W₁ : ValuationSubring (FFClosure (geomCurve Ω' C')),
      (∀ c : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C')) c ∈ W₁) ∧
      ¬ IsCentredOn (geomData Ω' C') (geomCurve Ω' C')
        (curveEquivL Ω' (transcendental_geomCoord Ω' C')) (geomOpen Ω' C') W₁ ∧
      (cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (curveGaloisData_H_le Ω _) (geomOpen Ω C) W₀).map
          (geomEquivOfDelta Φ (hΔ C hc C' hc' Φ)).toMulEquiv.toMonoidHom =
        cuspInertia (geomData Ω' C') (geomCurve Ω' C')
          (curveEquivL Ω' (transcendental_geomCoord Ω' C')) (curveGaloisData_H_le Ω' _)
          (geomOpen Ω' C') W₁ := by
  obtain ⟨W₁, hkW₁, hW₁, h⟩ := (mem_geomCusps_iff_map_padic p p' Φ (hΔ C hc C' hc' Φ) _).1
    ⟨W₀, hkW₀, hW₀U, rfl⟩
  exact ⟨W₁, hkW₁, hW₁, h⟩

end Padic

/-! ### Assembly: [GalSect] Thm. 4.3 for isomorphisms of arithmetic fundamental groups -/

section Assembly

open CuspChar

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharZero K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (p' : ℕ) [Fact p'.Prime] {K' : Type u} [Field K'] [CharZero K'] [Algebra ℚ_[p'] K']
  [FiniteDimensional ℚ_[p'] K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω']
  {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
  {U' : (geomCurve Ω C).Opens} [Nonempty U'] {x : geomCurve Ω C}
  {W₀ : ValuationSubring (FFClosure (geomCurve Ω C))}
  {V' : (geomCurve Ω' C').Opens} [Nonempty V'] {y : geomCurve Ω' C'}
  {W₁ : ValuationSubring (FFClosure (geomCurve Ω' C'))}

attribute [local instance] isAlgClosure_of_isAlgebraic

lemma sdiff_subsingleton_of_compl_eq {Z : Scheme.{u}} {U' : Z.Opens} {x : Z}
    (h : (U' : Set Z)ᶜ = {x}) : ((⊤ : Set Z) \ U').Subsingleton := by
  rw [Set.top_eq_univ, ← Set.compl_eq_univ_sdiff, h]
  exact Set.subsingleton_singleton

include p p' in
/-- **Filling compatibility for isomorphisms of arithmetic fundamental groups** (the hypothesis
`hker` of `rigidity_cuspInertia_fill`, derived, cf. [GalSect] l.864–868 "By 'filling in' …"):
for the induced `α_U = geomEquivOfDelta Φ hD`, `U' = X̄ ∖ {x}`, `V' = Ȳ ∖ {y}` and
`α_U(I_x) = I_y`, `α_U` maps `ker(Δ_U ↠ Δ_{U'})` onto `ker(Δ_V ↠ Δ_{V'})`. -/
theorem map_ker_fillOpen_padic
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc')
    (hUU' : geomOpen Ω C ≤ U') (hU'x : (U' : Set (geomCurve Ω C))ᶜ = {x})
    (hkW₀ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W₀)
    (hW₀U' : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω
      C)) U' W₀)
    (hVV' : geomOpen Ω' C' ≤ V') (hV'y : (V' : Set (geomCurve Ω' C'))ᶜ = {y})
    (hkW₁ : ∀ c : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C')) c ∈ W₁)
    (hW₁V' : ¬ IsCentredOn (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω'
      (transcendental_geomCoord Ω' C')) V' W₁)
    (hI : (cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω _) (geomOpen Ω C) W₀).map
        (geomEquivOfDelta Φ hD).toMulEquiv.toMonoidHom =
      cuspInertia (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω'
        C')) (curveGaloisData_H_le Ω' _) (geomOpen Ω' C') W₁) :
    (fillOpen (geomData Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C)) hUU').ker.map
        (geomEquivOfDelta Φ hD).toMulEquiv.toMonoidHom =
      (fillOpen (geomData Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω' C')) hVV').ker :=
  map_ker_fillOpen_of_cusps (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _)
    (curveEquivL_algebraMap Ω' _) (curveEquivL_τ Ω' _) (compl_finite_baseChangeOpen K Ω C.nonempty)
    (isHyperbolic_genusU Ω C) hUU' (hU'x ▸ Set.finite_singleton x)
    (sdiff_subsingleton_of_compl_eq hU'x) (compl_finite_baseChangeOpen K' Ω' C'.nonempty)
    (isHyperbolic_genusU Ω' C') hVV' (hV'y ▸ Set.finite_singleton y)
    (sdiff_subsingleton_of_compl_eq hV'y) (geomEquivOfDelta Φ hD)
    (mem_geomCusps_iff_map_padic p p' Φ hD) hkW₀ hW₀U' hkW₁ hW₁V' hI

include p p' in
/-- **The filled isomorphism `Δ_X ≃ₜ* Δ_Y`** (`X = X̄_Ω`, `Y = Ȳ_{Ω'}` the proper curves) induced by
an isomorphism `Φ` of arithmetic fundamental groups with `Φ(Δ_U) = Δ_{U'}` and `α_U(I_x) = I_y`:
first fill in the cusps other than `x`, `y` (`fillOpenEquiv`, compatibility
`map_ker_fillOpen_padic`), then `x`, `y` (`fillEquiv`). -/
noncomputable def fillEquivPadic
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hD : (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc')
    (hUU' : geomOpen Ω C ≤ U') (hU'x : (U' : Set (geomCurve Ω C))ᶜ = {x})
    (hW₀ : IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      ⊤ W₀) (hW₀U' : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω
      (transcendental_geomCoord Ω C)) U' W₀)
    (hVV' : geomOpen Ω' C' ≤ V') (hV'y : (V' : Set (geomCurve Ω' C'))ᶜ = {y})
    (hW₁ : IsCentredOn (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord
      Ω' C')) ⊤ W₁) (hW₁V' : ¬ IsCentredOn (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω'
      (transcendental_geomCoord Ω' C')) V' W₁)
    (hI : (cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω _) (geomOpen Ω C) W₀).map
        (geomEquivOfDelta Φ hD).toMulEquiv.toMonoidHom =
      cuspInertia (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω'
        C')) (curveGaloisData_H_le Ω' _) (geomOpen Ω' C') W₁) :
    π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genericL (geomData Ω C) (geomCurve
      Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C)) ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint (geomData Ω' C').L (FFClosure (geomCurve Ω' C')) ≫ genericL (geomData Ω' C')
        (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω' C')) ⊤) :=
  fillEquiv (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (curveEquivL_algebraMap Ω' _)
    (curveEquivL_τ Ω' _) hU'x hW₀ hW₀U' hV'y hW₁ hW₁V'
    (fillOpenEquiv (curveGaloisData_H_le Ω _) (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _)
      (curveGaloisData_H_le Ω' _) (curveEquivL_algebraMap Ω' _) (curveEquivL_τ Ω' _) hUU'
      (hU'x ▸ Set.finite_singleton x) hVV' (hV'y ▸ Set.finite_singleton y)
      (geomEquivOfDelta Φ hD)
      (map_ker_fillOpen_padic p p' Φ hD hUU' hU'x hW₀.1 hW₀U' hVV' hV'y hW₁.1 hW₁V' hI))
    (map_cuspInertia_fillOpenEquiv (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _)
      (curveEquivL_algebraMap Ω' _) (curveEquivL_τ Ω' _) hUU' _ hVV' _ (geomEquivOfDelta Φ hD)
      (map_ker_fillOpen_padic p p' Φ hD hUU' hU'x hW₀.1 hW₀U' hVV' hV'y hW₁.1 hW₁V' hI) hI)

include p p' in
/-- **[GalSect] Thm. 4.3 (Rigidity of cuspidal geometric decomposition groups) for isomorphisms of
arithmetic fundamental groups over `p`-adic fields** (`Galois Sections.txt` l.841–882). Let
`U`, `U'` be affine hyperbolic curves over finite extensions `K/ℚ_p`, `K'/ℚ_{p'}` whose smooth
compactifications have genus `≥ 1`, and `Φ : Π_U ≃ₜ* Π_{U'}` any isomorphism. Given
* [AbsAnab] Lemma 1.3.8 (`ArithQuotientPreservedPadic`, debt) — so `Φ(Δ_U) = Δ_{U'}`, and `Φ`
  induces `α_U : π₁ᵉᵗ(U_Ω) ≃ₜ* π₁ᵉᵗ(U'_{Ω'})` (`geomEquivOfDelta`);
* cusps `x`, `y` with `α_U(I_x) = I_y` (such `y` exists for every `x`:
  `exists_map_cuspInertia_padic`);
* `β : Ẑ(1) ≃* Ẑ(1)` with levels `β_n` (the cyclotome isomorphism; [GalSect] takes it as induced
  by `α`), and [AbsAnab] Lemma 2.5(ii) for the filled isomorphism (`DegOneChernPreserved` of
  `fillEquivPadic`, debt),

the natural isomorphisms `I_x ≅ Ẑ(1)`, `I_y ≅ Ẑ(1)` (roots of local coordinates, here composed
with filling in the other cusps, which is injective on `I_x`) are compatible with `α_U` and `β`.
The filling compatibility is derived from cusp preservation ([AbsTopI] Lemma 4.5 (v),
`mem_geomCusps_iff_map_padic`; `map_ker_fillOpen_padic`). -/
theorem rigidity_cuspInertia_padic (hΔ : ArithQuotientPreservedPadic p K Ω p' K' Ω')
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (hgen : 0 < (curveGenus Ω (geomCurve Ω C)).toNat)
    (hUU' : geomOpen Ω C ≤ U') (hU'x : (U' : Set (geomCurve Ω C))ᶜ = {x})
    (hW₀ : IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      ⊤ W₀) (hW₀U' : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω
      (transcendental_geomCoord Ω C)) U' W₀)
    {π : (F (geomData Ω C))ˣ}
    (hπW : W₀.valuation ((π : F (geomData Ω C)) : FFClosure (geomCurve Ω C)) < 1)
    (hπ : ∀ f ∈ F (geomData Ω C), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (geomData Ω C)) : FFClosure (geomCurve Ω C)))
    (hgen' : 0 < (curveGenus Ω' (geomCurve Ω' C')).toNat)
    (hVV' : geomOpen Ω' C' ≤ V') (hV'y : (V' : Set (geomCurve Ω' C'))ᶜ = {y})
    (hW₁ : IsCentredOn (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord
      Ω' C')) ⊤ W₁) (hW₁V' : ¬ IsCentredOn (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω'
      (transcendental_geomCoord Ω' C')) V' W₁)
    {π' : (F (geomData Ω' C'))ˣ}
    (hπW' : W₁.valuation ((π' : F (geomData Ω' C')) : FFClosure (geomCurve Ω' C')) < 1)
    (hπ' : ∀ f ∈ F (geomData Ω' C'), W₁.valuation f < 1 →
      W₁.valuation f ≤ W₁.valuation ((π' : F (geomData Ω' C')) : FFClosure (geomCurve Ω' C')))
    (hI : (cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω _) (geomOpen Ω C) W₀).map
        (geomEquivOfDelta Φ (hΔ C hc C' hc' Φ)).toMulEquiv.toMonoidHom =
      cuspInertia (geomData Ω' C') (geomCurve Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω'
        C')) (curveGaloisData_H_le Ω' _) (geomOpen Ω' C') W₁)
    (β : ZHatOne (F (geomData Ω C)) (FFClosure (geomCurve Ω C)) ≃*
      ZHatOne (F (geomData Ω' C')) (FFClosure (geomCurve Ω' C')))
    (βn : ∀ (n : ℕ) [NeZero n], Mu n (FFClosure (geomCurve Ω C)) ≃*
      Mu n (FFClosure (geomCurve Ω' C')))
    (hβ : ∀ (n : ℕ) [NeZero n] (z : ZHatOne (F (geomData Ω C)) (FFClosure (geomCurve Ω C))),
      ZHatOne.proj (kIdx (geomData Ω' C') n) (β z) = βn n (ZHatOne.proj (kIdx (geomData Ω C) n) z))
    (hdeg : DegOneChernPreserved (curveGaloisData_H_le Ω _) (curveEquivL_algebraMap Ω _)
      (curveEquivL_τ Ω _) (curveGaloisData_H_le Ω' _) (curveEquivL_algebraMap Ω' _)
      (curveEquivL_τ Ω' _) hgen hgen'
      (fillEquivPadic p p' Φ (hΔ C hc C' hc' Φ) hUU' hU'x hW₀ hW₀U' hVV' hV'y hW₁ hW₁V' hI) βn)
    (i : cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω _) (geomOpen Ω C) W₀) :
    CuspCentral.cuspInertiaZHatEquiv (curveEquivL_algebraMap Ω' _) (curveEquivL_τ Ω' _) hgen' V'
        hV'y hW₁ hW₁V' hπW' hπ'
        ⟨fillOpen (geomData Ω' C') (curveEquivL Ω' (transcendental_geomCoord Ω' C')) hVV'
          (geomEquivOfDelta Φ (hΔ C hc C' hc' Φ) i), by
          rw [← map_cuspInertia_fillOpen (hH := curveGaloisData_H_le Ω' _) hVV' W₁, ← hI]
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ i.2)⟩ =
      β (CuspCentral.cuspInertiaZHatEquiv (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) hgen U'
        hU'x hW₀ hW₀U' hπW hπ
        ⟨fillOpen (geomData Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C)) hUU' i, by
          rw [← map_cuspInertia_fillOpen (hH := curveGaloisData_H_le Ω _) hUU' W₀]
          exact Subgroup.mem_map_of_mem _ i.2⟩) :=
  rigidity_cuspInertia_fill (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _)
    (curveEquivL_algebraMap Ω' _) (curveEquivL_τ Ω' _) hgen hUU' hU'x hW₀ hW₀U' hπW hπ hgen' hVV'
    hV'y hW₁ hW₁V' hπW' hπ' (geomEquivOfDelta Φ (hΔ C hc C' hc' Φ)) hI
    (map_ker_fillOpen_padic p p' Φ (hΔ C hc C' hc' Φ) hUU' hU'x hW₀.1 hW₀U' hVV' hV'y hW₁.1 hW₁V'
      hI) β βn hβ hdeg i

end Assembly

end CurvesJacobian.CuspRigidity
