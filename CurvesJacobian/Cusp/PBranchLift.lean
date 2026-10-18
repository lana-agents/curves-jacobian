/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.PBranch
import CurvesJacobian.Cusp.LineAnalytic

/-!
# Base change of `PBranch`es and lifting small loops through them

The analogues for `CurvesJacobian.Cusp.PBranch` (a branch with coordinate relation
`T · Q(s) = P(s)`) of `CurvesJacobian.Cusp.CuspBranch.baseChange` and
`CurvesJacobian.Cusp.CuspBranch.exists_closed_lift`:

* `CurvesJacobian.Cusp.PBranch.baseChange`: for a field extension `Ω / K`, a branch of
  `Y ⟶ Spec R` with relation `T · Q(s) = P(s)` gives a branch of the base change
  `Y_Ω ⟶ Spec (Ω ⊗[K] R)` with relation `(1 ⊗ T) · Q_Ω(s) = P_Ω(s)`;
* `CurvesJacobian.Cusp.PBranch.exists_closed_lift`: over `ℂ`, every loop `w` in a small
  punctured disc lifts to a closed loop `Λ` of `Y'^an` lying over a loop of `X^an` whose
  coordinate `z = T'(Λ θ)` satisfies `z · Q(w θ) = P(w θ)`.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology Metric Polynomial
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Base change -/

section Branch

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] {T : R}
  {Y : AlgebraicGeometry.FiniteEtale (Spec (.of R))} {P Q : K[X]}
  (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- `A[1/s] → (Ω ⊗ A)[1/(1 ⊗ s)]`. -/
def PBranch.awayBaseChange (b : PBranch K T Y.hom P Q) :
    Localization.Away b.s →ₐ[K] Localization.Away ((1 : Ω) ⊗ₜ[K] b.s) :=
  IsLocalization.Away.liftAlgHom b.s
    (f := (IsScalarTower.toAlgHom K (Ω ⊗[K] b.A) (Localization.Away ((1 : Ω) ⊗ₜ[K] b.s))).comp
      Algebra.TensorProduct.includeRight)
    (by
      have hu : IsUnit (algebraMap (Ω ⊗[K] b.A) (Localization.Away ((1 : Ω) ⊗ₜ[K] b.s))
          ((1 : Ω) ⊗ₜ[K] b.s)) := IsLocalization.Away.algebraMap_isUnit _
      simpa using hu)

lemma PBranch.awayBaseChange_algebraMap (b : PBranch K T Y.hom P Q) (a : b.A) :
    b.awayBaseChange Ω (algebraMap b.A _ a) = algebraMap _ _ ((1 : Ω) ⊗ₜ[K] a) := by
  simp [PBranch.awayBaseChange]

/-- The base change `Ω ⊗ R → (Ω ⊗ A)[1/(1 ⊗ s)]` of `θ`. -/
def PBranch.thetaBaseChange (b : PBranch K T Y.hom P Q) :
    Ω ⊗[K] R →ₐ[Ω] Localization.Away ((1 : Ω) ⊗ₜ[K] b.s) :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω _) ((b.awayBaseChange Ω).comp b.θ)
    (fun _ _ ↦ Commute.all _ _)

lemma PBranch.thetaBaseChange_tmul (b : PBranch K T Y.hom P Q) (r : R) :
    b.thetaBaseChange Ω ((1 : Ω) ⊗ₜ r) = b.awayBaseChange Ω (b.θ r) := by
  simp [PBranch.thetaBaseChange, Algebra.TensorProduct.lift_tmul]

/-- **Base change of a branch** along a field extension `Ω / K`: a branch with relation
`T · Q(s) = P(s)` of `Y ⟶ Spec R` gives a branch with relation `(1 ⊗ T) · Q_Ω(s) = P_Ω(s)` of
the base change `Y_Ω ⟶ Spec (Ω ⊗[K] R)`. -/
def PBranch.baseChange (b : PBranch K T Y.hom P Q) :
    PBranch Ω ((1 : Ω) ⊗ₜ[K] T)
      ((AlgebraicGeometry.FiniteEtale.pullback
        (AlgebraicGeometry.FiniteEtale.baseChangeSpec K Ω R)).obj Y).hom
      (P.map (algebraMap K Ω)) (Q.map (algebraMap K Ω)) where
  A := Ω ⊗[K] b.A
  s := (1 : Ω) ⊗ₜ[K] b.s
  etale := etale_mvAeval_baseChange b.etale
  pt := Algebra.TensorProduct.lift (Algebra.ofId Ω Ω) ((Algebra.ofId K Ω).comp b.pt)
    (fun _ _ ↦ Commute.all _ _)
  pt_s := by simp [Algebra.TensorProduct.lift_tmul, b.pt_s]
  θ := b.thetaBaseChange Ω
  rel := by
    have h := congrArg (b.awayBaseChange Ω) b.rel
    rw [map_mul, ← aeval_algHom_apply, ← aeval_algHom_apply] at h
    rw [aeval_map_algebraMap, aeval_map_algebraMap, PBranch.thetaBaseChange_tmul,
      ← PBranch.awayBaseChange_algebraMap]
    exact h
  m := Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (b.awayBaseChange Ω).toRingHom) ≫ b.m)
    (Spec.map (CommRingCat.ofHom (b.thetaBaseChange Ω).toRingHom)) (by
      refine (Category.assoc _ _ _).trans
        ((congrArg (fun g ↦ Spec.map (CommRingCat.ofHom (b.awayBaseChange Ω).toRingHom) ≫ g)
          b.hm).trans ?_)
      exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (CommRingCat.hom_ext
        (RingHom.ext fun r ↦ (b.thetaBaseChange_tmul Ω r).symm))).trans (Spec.map_comp _ _)))
  hm := Limits.pullback.lift_snd _ _ _

end Branch

/-! ### Sections of an étale coordinate on `D(s)` -/

section Section

variable {A : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]

/-- **A section of `s` on the punctured disc, inside `D(s)`, with the values of all functions**:
points `σ'(w)` of `D(s)^an`, depending continuously on `w` in a punctured disc, lying over points
`v` of `(Spec A)^an` with `s(v) = w`. -/
lemma exists_section_basicOpen_eval {s : A}
    (h : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ s).toRingHom.Etale)
    (ε : A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ) (hε : ε s = 0) :
    ∃ r > (0 : ℝ),
      ∃ σ' : ℂ → analytification.obj ((specLFT A).restrict (PrimeSpectrum.basicOpen s)),
      ContinuousOn σ' {w | w ∈ ball (0 : ℂ) r ∧ w ≠ 0} ∧
      ∀ w, w ∈ ball (0 : ℂ) r → w ≠ 0 → ∃ v : analytification.obj (specLFT A),
        (evalAlgHom v s).down = w ∧ ∀ a : A,
        evalPoint _ (σ' w) ((basicOpenIsoSpecAway (R := .of A) s).hom.appTop
          ((Scheme.ΓSpecIso (.of (Localization.Away s))).inv (algebraMap A _ a))) =
          (evalAlgHom v a).down := by
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
  refine ⟨r, hr, fun w ↦ eD.symm (σ w), ?_, fun w hw hw0 ↦ ⟨σ w, ?_, fun a ↦ ?_⟩⟩
  · refine eD.continuousOn_symm.comp (hσc.mono fun w hw ↦ hw.1) fun w hw ↦ ?_
    rw [htarget]
    exact hrange w hw.1 hw.2
  · rw [← sCoord_eq_evalAlgHom, hσ w hw]
  · rw [appTop_basicOpenIsoSpecAway_algebraMap, evalPoint_appTop]
    have hj : jD (eD.symm (σ w)) = σ w := eD.right_inv (by rw [htarget]; exact hrange w hw hw0)
    change evalPoint Z (jD (eD.symm (σ w))) _ = _
    rw [hj, evalAlgHom_apply]

end Section

/-! ### Closed lifts of small loops -/

section Lift

variable {R' : Type u} [CommRing R'] [Algebra (ULift.{u} ℂ) R']
  [Algebra.FiniteType (ULift.{u} ℂ) R'] {T' : R'}
  {Y' : AlgebraicGeometry.FiniteEtale (Spec (.of R'))} {P Q : (ULift.{u} ℂ)[X]}
  (b : PBranch (ULift.{u} ℂ) T' Y'.hom P Q)

/-- The open `D(s) ⊆ Spec A` of a branch. -/
abbrev PBranch.D : (specLFT b.A).obj.left.Opens := PrimeSpectrum.basicOpen b.s

/-- **The branch as a morphism of schemes locally of finite type over `ℂ`**:
`D(s) ≅ Spec A[1/s] ⟶ Y'`. -/
def PBranch.toCover :
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
/-- **Closed lifts of small loops around the cusp.** For a branch `b` with relation
`T' · Q(s) = P(s)`, there is `r > 0` such that every loop `w` in the punctured disc of radius `r`
lifts to a closed loop `Λ` in `Y'^an` lying over a loop of `X^an` whose coordinate
`z = T'(Λ θ)` satisfies `z · Q(w θ) = P(w θ)` (in `ULift ℂ`). -/
theorem PBranch.exists_closed_lift :
    ∃ r > (0 : ℝ), ∀ w : C(unitInterval, ℂ), w 0 = w 1 → (∀ θ, w θ ∈ ball (0 : ℂ) r ∧ w θ ≠ 0) →
      ∃ Λ : C(unitInterval, ((analytificationFiniteEtale (specLFT R')).obj Y').left), Λ 0 = Λ 1 ∧
        ∀ θ, (ULift.up (evalPoint (specLFT R')
          (((analytificationFiniteEtale (specLFT R')).obj Y').hom.toLRSHom.base (Λ θ))
          ((Scheme.ΓSpecIso (.of R')).inv T')) : ULift.{u} ℂ) * aeval (ULift.up (w θ)) Q =
          aeval (ULift.up (w θ)) P := by
  obtain ⟨r, hr, σ', hσ'c, hσ'⟩ := exists_section_basicOpen_eval b.etale b.pt b.pt_s
  refine ⟨r, hr, fun w h01 hw ↦ ?_⟩
  let F := (analytification.map b.toCover).toLRSHom.base
  let Λ : C(unitInterval, ((analytificationFiniteEtale (specLFT R')).obj Y').left) :=
    ⟨fun θ ↦ F (σ' (w θ)), F.hom.continuous.comp
      (hσ'c.comp_continuous w.continuous fun θ ↦ hw θ)⟩
  refine ⟨Λ, by simp [Λ, h01], fun θ ↦ ?_⟩
  let v := σ' (w θ)
  obtain ⟨v₀, hv₀s, hv₀⟩ := hσ' (w θ) (hw θ).1 (hw θ).2
  let Φ : Localization.Away b.s →+* ℂ := (evalPoint _ v).comp
    ((basicOpenIsoSpecAway (R := .of b.A) b.s).hom.appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Localization.Away b.s))).inv.hom)
  have hΦ : ∀ a : b.A, Φ (algebraMap b.A _ a) = (evalAlgHom v₀ a).down := hv₀
  let Ψ : Localization.Away b.s →ₐ[ULift.{u} ℂ] ULift.{u} ℂ :=
    { toRingHom := ULift.ringEquiv.symm.toRingHom.comp Φ
      commutes' := fun c ↦ by
        change ULift.up (Φ (algebraMap (ULift.{u} ℂ) _ c)) = c
        rw [IsScalarTower.algebraMap_apply (ULift.{u} ℂ) b.A (Localization.Away b.s), hΦ,
          AlgHom.commutes]
        rfl }
  have hrel := congrArg Ψ b.rel
  rw [map_mul, ← aeval_algHom_apply, ← aeval_algHom_apply] at hrel
  have hW : Ψ (algebraMap b.A _ b.s) = ULift.up (w θ) := by
    change ULift.up (Φ _) = _
    rw [hΦ, hv₀s]
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
  have hT : Ψ (b.θ T') = ULift.up (evalPoint (specLFT R')
      (((analytificationFiniteEtale (specLFT R')).obj Y').hom.toLRSHom.base (Λ θ))
      ((Scheme.ΓSpecIso (.of R')).inv T')) := by
    rw [hV]
    rfl
  rw [hW, hT] at hrel
  exact hrel

end Lift

end CurvesJacobian.Cusp
