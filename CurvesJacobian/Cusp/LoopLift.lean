/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BranchBaseChange
import Oka.Analytification.Pi1.BranchedCoordinateSpec
import Oka.Analytification.Pi1.Comparison

/-!
# Lifting small loops around a cusp through a branch

Let `X = Spec R'` be an affine scheme of finite type over `ℂ`, `T' ∈ R'`, `Y' ⟶ X` finite étale,
and `b` a branch of `Y'` at the cusp `j` (`CurvesJacobian.Cusp.CuspBranch`): `A` étale over
`ℂ[s]`, a point `z₀` of `Spec A` with `s(z₀) = 0`, and `Spec A[1/s] ⟶ Y'` over `X`, where `T'`
becomes `s`, `1 + s`, resp. `1/2 + 1/s`. Analytically, `s` is a local coordinate of `(Spec A)^an`
at `z₀` (étale morphisms analytify to local homeomorphisms), so a small disc around `0` has a
continuous section `σ` of `s`. Every loop `w` in the punctured disc thus lifts to the closed loop
`m^an ∘ σ ∘ w` in `Y'^an`, lying over the loop `T'(w)` of `X^an`
(`CurvesJacobian.Cusp.CuspBranch.exists_closed_lift`).

* `CurvesJacobian.Cusp.evalPoint_appTop`: values of pulled back global sections at analytic
  points (naturality of `ComplexAnalytic.evalPoint`).
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology Metric

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Eval

variable {V W : SchemeLFTℂ.{u}}

/-- **Naturality of evaluation at analytic points**: the value of `g^*(a)` at `v` is the value of
`a` at `g^an(v)`. -/
lemma evalPoint_appTop (g : V ⟶ W) (v : analytification.obj V) (a : Γ(W.obj.left, ⊤)) :
    evalPoint V v (g.hom.left.appTop a) =
      evalPoint W ((analytification.map g).toLRSHom.base v) a := by
  refine (congrArg (fun t ↦ (analytification.obj V).eval (U := ⊤) v trivial t)
    (analytificationΓ_naturality g a)).trans ?_
  exact AnalyticSpace.eval_c_app (analytification.map g).toLRSHom (analytification.map g).isCLinear
    (U := ⊤) v trivial _

end Eval

section Section

variable {A : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]

/-- The coordinate `s` on `(Spec A)^an`. -/
abbrev sCoord (s : A) : C(analytification.obj (specLFT A), ℂ) :=
  coordFun (specCoord s) (specCoord_comp_C s)

lemma evalPoint_sCoord (s : A) (v : analytification.obj (specLFT A)) :
    evalPoint (specLFT A) v ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) = sCoord s v := by
  have h := evalPoint_eq_eval_coordFun (specCoord s) (specCoord_comp_C s) v (MvPolynomial.X 0)
  simp only [MvPolynomial.map_X, MvPolynomial.eval_X] at h
  rw [← h]
  change _ = evalPoint _ v ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (MvPolynomial.aeval (fun _ : Fin 1 ↦ s) (MvPolynomial.X 0)))
  rw [MvPolynomial.aeval_X]

/-- **An étale coordinate is a local homeomorphism** on `(Spec A)^an`. -/
lemma isLocalHomeomorph_sCoord {s : A}
    (h : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ s).toRingHom.Etale) :
    IsLocalHomeomorph (sCoord s) := by
  have het : (specCoord s).Etale :=
    RingHom.Etale.respectsIso.1 _
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm h
  haveI := SchemeLFTℂ.etale_toAffineSpace (specCoord s) (specCoord_comp_C s) het
  haveI := isLocalIso_analytification_map_of_etale
    (SchemeLFTℂ.toAffineSpace (specCoord s) (specCoord_comp_C s))
  haveI := AnalyticSpace.isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
  exact coordHomeomorph.isLocalHomeomorph.comp (AnalyticSpace.IsLocalIso.isLocalHomeomorph
    (f := analytification.map (SchemeLFTℂ.toAffineSpace (specCoord s) (specCoord_comp_C s)) ≫
      (analytificationAffineSpaceIso.{u} 1).hom))

/-- **A point where `s` vanishes**: a `ℂ`-point `ε` of `A` with `ε(s) = 0` is a point of
`(Spec A)^an` with `s = 0`. -/
lemma exists_sCoord_eq_zero {s : A} (ε : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ) (hε : ε s = 0) :
    ∃ z₀ : analytification.obj (specLFT A), sCoord s z₀ = 0 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let M : Ideal Γ((specLFT A).obj.left, ⊤) := (RingHom.ker ε).comap e.toRingHom
  haveI : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun c ↦ ⟨algebraMap _ A c, ε.commutes c⟩)
  haveI : M.IsMaximal := Ideal.comap_isMaximal_of_equiv e
  obtain ⟨z₀, hz₀⟩ := exists_idealOfPoint_eq (specLFT A) M
  refine ⟨z₀, ?_⟩
  rw [← evalPoint_sCoord, ← RingHom.mem_ker, ker_evalPoint, hz₀]
  change e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom s) ∈ RingHom.ker ε
  have : e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom s) = s := by
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom s) = s
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [this]
  exact hε

/-- **A local section of an étale coordinate**: near a zero `z₀` of `s` there is a continuous
section `σ` of `s` on a disc around `0`. -/
lemma exists_section_sCoord {s : A}
    (h : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ s).toRingHom.Etale)
    (ε : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ) (hε : ε s = 0) :
    ∃ r > (0 : ℝ), ∃ σ : ℂ → analytification.obj (specLFT A),
      ContinuousOn σ (ball 0 r) ∧ ∀ w ∈ ball (0 : ℂ) r, sCoord s (σ w) = w := by
  obtain ⟨z₀, hz₀⟩ := exists_sCoord_eq_zero ε hε
  obtain ⟨φ, hz, hφ⟩ := isLocalHomeomorph_sCoord h z₀
  have h0 : (0 : ℂ) ∈ φ.target := by
    rw [← hz₀, hφ]
    exact φ.map_source hz
  obtain ⟨r, hr, hrt⟩ := isOpen_iff.1 φ.open_target 0 h0
  refine ⟨r, hr, φ.symm, φ.continuousOn_symm.mono hrt, fun w hw ↦ ?_⟩
  rw [hφ]
  exact φ.right_inv (hrt hw)

/-- `A[1/s]`'s global sections on `D(s) ⊆ Spec A`. -/
lemma appTop_basicOpenIsoSpecAway_algebraMap (s : A) (a : A) :
    (basicOpenIsoSpecAway (R := .of A) s).hom.appTop
        ((Scheme.ΓSpecIso (.of (Localization.Away s))).inv (algebraMap A _ a)) =
      ((specLFT A).restrictι (PrimeSpectrum.basicOpen s)).hom.left.appTop
        ((Scheme.ΓSpecIso (.of A)).inv a) := by
  have h1 := congrArg (fun φ ↦ φ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A (Localization.Away s))))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1
  rw [SchemeLFTℂ.restrictι_hom_left]
  change _ = (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen s)).appTop _
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of A) s, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, ← h1]

/-- **A section of `s` on the punctured disc, inside `D(s)`**: points `σ'(w)` of `D(s)^an` with
`s(σ'(w)) = w`, depending continuously on `w` in a punctured disc. -/
lemma exists_section_basicOpen {s : A}
    (h : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ s).toRingHom.Etale)
    (ε : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ) (hε : ε s = 0) :
    ∃ r > (0 : ℝ),
      ∃ σ' : ℂ → analytification.obj ((specLFT A).restrict (PrimeSpectrum.basicOpen s)),
      ContinuousOn σ' {w | w ∈ ball (0 : ℂ) r ∧ w ≠ 0} ∧
      ∀ w, w ∈ ball (0 : ℂ) r → w ≠ 0 →
        evalPoint _ (σ' w) ((basicOpenIsoSpecAway (R := .of A) s).hom.appTop
          ((Scheme.ΓSpecIso (.of (Localization.Away s))).inv (algebraMap A _ s))) = w := by
  obtain ⟨r, hr, σ, hσc, hσ⟩ := exists_section_sCoord h ε hε
  let Z := specLFT A
  let D : Z.obj.left.Opens := PrimeSpectrum.basicOpen s
  let jD := (analytification.map (Z.restrictι D)).toLRSHom.base
  have hjD : IsOpenEmbedding jD := isOpenEmbedding_analytification_map_restrictι Z D
  have hrange : ∀ w, w ∈ ball (0 : ℂ) r → w ≠ 0 → σ w ∈ Set.range jD := by
    intro w hw hw0
    rw [range_analytification_map_restrictι]
    have h' := mem_basicOpen_of_evalPoint_ne_zero Z (σ w) ((Scheme.ΓSpecIso (.of A)).inv s)
      (by rw [evalPoint_sCoord, hσ w hw]; exact hw0)
    have h'' : (analytificationπLRS Z).base (σ w) ∈
        (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv s) := h'
    rw [basicOpen_eq_of_affine] at h''
    exact h''
  have hw₀ : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hw₀' : ((r / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : r / 2 ≠ 0)
  haveI : Nonempty (analytification.obj (Z.restrict D)) :=
    ⟨(hrange _ hw₀ hw₀').choose⟩
  let eD := hjD.toOpenPartialHomeomorph jD
  have htarget : eD.target = Set.range jD := by
    simp [eD, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  refine ⟨r, hr, fun w ↦ eD.symm (σ w), ?_, fun w hw hw0 ↦ ?_⟩
  · refine eD.continuousOn_symm.comp (hσc.mono fun w hw ↦ hw.1) fun w hw ↦ ?_
    rw [htarget]
    exact hrange w hw.1 hw.2
  · rw [appTop_basicOpenIsoSpecAway_algebraMap, evalPoint_appTop]
    have hj : jD (eD.symm (σ w)) = σ w := eD.right_inv (by rw [htarget]; exact hrange w hw hw0)
    change evalPoint Z (jD (eD.symm (σ w))) _ = w
    rw [hj, evalPoint_sCoord, hσ w hw]

end Section

section Lift

/-- `D(s) ≅ Spec A[1/s] ⟶ Spec R'` over `ℂ`, for a `ℂ`-algebra map `θ : R' → A[1/s]`. -/
lemma basicOpenIsoSpecAway_specMap_comp {A R' : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A]
    [CommRing R'] [Algebra (ULift.{u} ℂ) R'] (s : A)
    (θ : R' →ₐ[ULift.{u} ℂ] Localization.Away s) :
    (basicOpenIsoSpecAway (R := .of A) s).hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) R')) =
      Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A)) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of A) s, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [← IsScalarTower.algebraMap_apply]

/-- `θ(r)` as a global section of `D(s)`. -/
lemma appTop_basicOpenIsoSpecAway_specMap {A R' : Type u} [CommRing A] [CommRing R'] (s : A)
    (θ : R' →+* Localization.Away s) (r : R') :
    ((basicOpenIsoSpecAway (R := .of A) s).hom ≫ Spec.map (CommRingCat.ofHom θ)).appTop
        ((Scheme.ΓSpecIso (.of R')).inv r) =
      (basicOpenIsoSpecAway (R := .of A) s).hom.appTop
        ((Scheme.ΓSpecIso (.of (Localization.Away s))).inv (θ r)) := by
  have h1 := congrArg (fun φ ↦ φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom θ))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← h1]

variable {R' : Type u} [CommRing R'] [Algebra (ULift.{u} ℂ) R']
  [Algebra.FiniteType (ULift.{u} ℂ) R'] {T' : R'}
  {Y' : AlgebraicGeometry.FiniteEtale (Spec (.of R'))} {j : Fin 3}
  (b : CuspBranch (ULift.{u} ℂ) T' Y'.hom j)

/-- The open `D(s) ⊆ Spec A` of a branch. -/
abbrev CuspBranch.D : (specLFT b.A).obj.left.Opens := PrimeSpectrum.basicOpen b.s

/-- **The branch as a morphism of schemes locally of finite type over `ℂ`**:
`D(s) ≅ Spec A[1/s] ⟶ Y'`. -/
def CuspBranch.toCover :
    (specLFT b.A).restrict b.D ⟶ SchemeLFTℂ.ofFiniteEtale (specLFT R') Y' :=
  ObjectProperty.homMk (Over.homMk ((basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫ b.m) (by
    change ((basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫ b.m) ≫
        (Y'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) R'))) =
      b.D.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) b.A))
    have e1 : ((basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫ b.m) ≫
        (Y'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) R'))) =
        (basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫ (b.m ≫ Y'.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) R')) := by
      simp only [Category.assoc]
    have e2 := congrArg (fun g ↦ (basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫ g ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) R'))) b.hm
    exact e1.trans (e2.trans (basicOpenIsoSpecAway_specMap_comp b.s b.θ))))

include b in
/-- **Closed lifts of small loops around the cusp.** For a branch `b` at the cusp `j`, there is
`r > 0` such that every loop `w` in the punctured disc of radius `r` lifts to a closed loop `Λ`
in `Y'^an` lying over a loop of `X^an` whose coordinate `T'` is related to `w` by `CuspRel j`
(`T' = w`, `1 + w`, `1/2 + 1/w`). -/
theorem CuspBranch.exists_closed_lift :
    ∃ r > (0 : ℝ), ∀ w : C(unitInterval, ℂ), w 0 = w 1 → (∀ θ, w θ ∈ ball (0 : ℂ) r ∧ w θ ≠ 0) →
      ∃ Λ : C(unitInterval, ((analytificationFiniteEtale (specLFT R')).obj Y').left), Λ 0 = Λ 1 ∧
        ∀ θ, CuspRel j (evalPoint (specLFT R')
          (((analytificationFiniteEtale (specLFT R')).obj Y').hom.toLRSHom.base (Λ θ))
          ((Scheme.ΓSpecIso (.of R')).inv T')) (w θ) := by
  obtain ⟨r, hr, σ', hσ'c, hσ'⟩ := exists_section_basicOpen b.etale b.pt b.pt_s
  refine ⟨r, hr, fun w h01 hw ↦ ?_⟩
  let F := (analytification.map b.toCover).toLRSHom.base
  let Λ : C(unitInterval, ((analytificationFiniteEtale (specLFT R')).obj Y').left) :=
    ⟨fun θ ↦ F (σ' (w θ)), F.hom.continuous.comp
      (hσ'c.comp_continuous w.continuous fun θ ↦ hw θ)⟩
  refine ⟨Λ, by simp [Λ, h01], fun θ ↦ ?_⟩
  let v := σ' (w θ)
  let Φ : Localization.Away b.s →+* ℂ := (evalPoint _ v).comp
    ((basicOpenIsoSpecAway (R := .of b.A) b.s).hom.appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Localization.Away b.s))).inv.hom)
  have hrel := CuspRel.map Φ b.rel
  have hW : Φ (algebraMap b.A _ b.s) = w θ := hσ' (w θ) (hw θ).1 (hw θ).2
  have hm : (b.toCover ≫ SchemeLFTℂ.ofFiniteEtaleHom (specLFT R') Y').hom.left =
      (basicOpenIsoSpecAway (R := .of b.A) b.s).hom ≫
        Spec.map (CommRingCat.ofHom b.θ.toRingHom) :=
    (Category.assoc _ _ _).trans (congrArg (fun g ↦ (basicOpenIsoSpecAway (R := .of b.A) b.s).hom
      ≫ g) b.hm)
  have hV : evalPoint (specLFT R')
      (((analytificationFiniteEtale (specLFT R')).obj Y').hom.toLRSHom.base (Λ θ))
      ((Scheme.ΓSpecIso (.of R')).inv T') = Φ (b.θ T') := by
    have e1 : ((analytificationFiniteEtale (specLFT R')).obj Y').hom.toLRSHom.base (Λ θ) =
        (analytification.map
          (b.toCover ≫ SchemeLFTℂ.ofFiniteEtaleHom (specLFT R') Y')).toLRSHom.base v := by
      rw [Functor.map_comp]
      rfl
    refine (congrArg (fun z ↦ evalPoint (specLFT R') z ((Scheme.ΓSpecIso (.of R')).inv T'))
      e1).trans ((evalPoint_appTop _ v _).symm.trans ?_)
    refine (congrArg (fun g : ((specLFT b.A).restrict b.D).obj.left ⟶ Spec (.of R') ↦
      evalPoint _ v (g.appTop ((Scheme.ΓSpecIso (.of R')).inv T'))) hm).trans ?_
    exact congrArg (evalPoint _ v) (appTop_basicOpenIsoSpecAway_specMap b.s b.θ.toRingHom T')
  exact Eq.mp (congrArg₂ (CuspRel j) hV.symm hW) hrel

end Lift

end CurvesJacobian.Cusp
