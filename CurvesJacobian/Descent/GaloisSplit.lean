/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisScheme
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.Field

/-!
# `T ×_k L` splits for `T` over `L`, and `X₀ ×_k L ≅ X`

Let `L / k` be finite Galois with group `G` and `T` a scheme over `Spec L` (via `t`). Then
`T ×_k L = ∐_{g ∈ G} T`: the sections `δ_g = δ ≫ (id × Spec g)` of `T ×_k L ⟶ T`, where
`δ = (𝟙, t)`, are open immersions (base changes of the diagonal of the unramified
`Spec L ⟶ Spec k`) with pairwise disjoint images covering `T ×_k L`.

* `CurvesJacobian.GaloisDescent.splitEquiv`: for a scheme `X` over `Spec L` with a semilinear
  `G`-action, `G`-equivariant `L`-morphisms `T ×_k L ⟶ X` are the same as `L`-morphisms
  `T ⟶ X` (restriction along `δ`).
* **`CurvesJacobian.GaloisDescent.isIso_descCounit`**: the counit `X₀ ×_k L ⟶ X` of the Galois
  descent `X₀` of `X` (`descScheme`) is an isomorphism.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

instance {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q)
    (g : Gal(L/k)) : IsIso (a.act g) :=
  ⟨⟨a.act g⁻¹, a.act_act_inv g, a.act_inv_act g⟩⟩

instance [FiniteDimensional k L] [IsGalois k L] : FormallyUnramified (sL k L) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified), CommRingCat.hom_ofHom,
    RingHom.formallyUnramified_algebraMap]
  exact Algebra.FormallyUnramified.of_isSeparable k L

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L))

variable (k) in
/-- The diagonal section `δ = (𝟙, t) : T ⟶ T ×_k L`. -/
def diagL : T ⟶ pullback (t ≫ sL k L) (sL k L) :=
  pullback.lift (𝟙 T) t (by simp)

@[reassoc (attr := simp)]
lemma diagL_fst : diagL k t ≫ pullback.fst (t ≫ sL k L) (sL k L) = 𝟙 T := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma diagL_snd : diagL k t ≫ pullback.snd (t ≫ sL k L) (sL k L) = t := pullback.lift_snd _ _ _

instance [FiniteDimensional k L] [IsGalois k L] : IsOpenImmersion (diagL k t) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pullback_lift_diagonal_isPullback t (sL k L)) inferInstance

variable (k) in
/-- The sections `δ_g = δ ≫ (id × Spec g)`. -/
def diagG (g : Gal(L/k)) : T ⟶ pullback (t ≫ sL k L) (sL k L) :=
  diagL k t ≫ (baseAct (t ≫ sL k L)).act g

instance [FiniteDimensional k L] [IsGalois k L] (g : Gal(L/k)) : IsOpenImmersion (diagG k t g) := by
  unfold diagG
  infer_instance

@[reassoc (attr := simp)]
lemma diagG_fst (g : Gal(L/k)) : diagG k t g ≫ pullback.fst (t ≫ sL k L) (sL k L) = 𝟙 T := by
  simp [diagG]

@[reassoc]
lemma diagG_snd (g : Gal(L/k)) :
    diagG k t g ≫ pullback.snd (t ≫ sL k L) (sL k L) = t ≫ specGal g := by
  rw [diagG, Category.assoc, GalAction.act_comp, diagL_snd_assoc]

lemma diagG_one : diagG k t 1 = diagL k t := by
  rw [diagG, GalAction.act_one, Category.comp_id]

@[reassoc]
lemma diagG_act (g h : Gal(L/k)) :
    diagG k t g ≫ (baseAct (t ≫ sL k L)).act h = diagG k t (g * h) := by
  rw [diagG, diagG, Category.assoc, GalAction.act_mul]

/-- **The images of distinct `δ_g` are disjoint.** -/
lemma isEmpty_pullback_diagG {g h : Gal(L/k)} (hgh : g ≠ h) :
    IsEmpty ↥(pullback (diagG k t g) (diagG k t h)) := by
  refine ⟨fun p ↦ hgh ?_⟩
  have e1 : pullback.fst (diagG k t g) (diagG k t h) =
      pullback.snd (diagG k t g) (diagG k t h) := by
    have := congrArg (· ≫ pullback.fst (t ≫ sL k L) (sL k L)) (pullback.condition
      (f := diagG k t g) (g := diagG k t h))
    simpa using this
  have e2 := congrArg (· ≫ pullback.snd (t ≫ sL k L) (sL k L)) (pullback.condition
      (f := diagG k t g) (g := diagG k t h))
  simp only [Category.assoc, diagG_snd, ← e1] at e2
  let m := (pullback (diagG k t g) (diagG k t h)).fromSpecResidueField p ≫
    pullback.fst (diagG k t g) (diagG k t h) ≫ t
  have e3 : m ≫ specGal g = m ≫ specGal h := by
    simp only [m, Category.assoc]
    rw [e2]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective m
  rw [← hφ, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e3
  apply AlgEquiv.ext
  intro l
  have := congrArg (fun ψ : CommRingCat.of L ⟶ _ ↦ ψ l) e3
  exact φ.hom.injective this

lemma diagL_bcL {T' : Scheme.{u}} (h : T' ⟶ T) :
    diagL k (h ≫ t) ≫ bcL (t ≫ sL k L) h (Category.assoc _ _ _).symm = h ≫ diagL k t := by
  apply pullback.hom_ext <;> simp

variable [FiniteDimensional k L] [IsGalois k L]

/-- **The `δ_g` cover `T ×_k L`.** -/
lemma exists_diagG_apply_eq (z : ↥(pullback (t ≫ sL k L) (sL k L))) :
    ∃ (g : Gal(L/k)) (τ : T), diagG k t g τ = z := by
  obtain ⟨W, hW, hτW, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := pullback.fst (t ≫ sL k L) (sL k L) z) (U := ⊤) trivial
  haveI : IsAffine W := hW
  obtain ⟨w, hw⟩ := mem_range_bcL (t ≫ sL k L) W.ι (Category.assoc _ _ _).symm z ⟨_, hτW⟩ rfl
  have hfst : pullback.fst ((W.ι ≫ t) ≫ sL k L) (sL k L) (diagL k (W.ι ≫ t) ⟨_, hτW⟩) =
      pullback.fst ((W.ι ≫ t) ≫ sL k L) (sL k L) w := by
    rw [← Scheme.Hom.comp_apply, diagL_fst]
    apply Subtype.ext
    change _ = W.ι _
    rw [← Scheme.Hom.comp_apply, ← bcL_fst (t ≫ sL k L) W.ι (Category.assoc _ _ _).symm,
      Scheme.Hom.comp_apply, hw]
    rfl
  obtain ⟨g, hg⟩ := exists_baseAct_apply_eq ((W.ι ≫ t) ≫ sL k L) _ _ hfst
  have key : diagL k (W.ι ≫ t) ≫ (baseAct ((W.ι ≫ t) ≫ sL k L)).act g ≫
      bcL (t ≫ sL k L) W.ι (Category.assoc _ _ _).symm = W.ι ≫ diagG k t g := by
    rw [baseAct_bcL, ← Category.assoc, diagL_bcL, Category.assoc]
    rfl
  refine ⟨g, W.ι ⟨_, hτW⟩, Eq.trans ?_ hw⟩
  rw [← hg]
  have := congrArg (fun m ↦ m ⟨_, hτW⟩) key
  simp only [Scheme.Hom.comp_apply] at this
  exact this.symm

/-- The open cover of `T ×_k L` by the `δ_g`. -/
def splitCover : (pullback (t ≫ sL k L) (sL k L)).OpenCover :=
  Scheme.Cover.mkOfCovers Gal(L/k) (fun _ ↦ T) (diagG k t) (fun z ↦ exists_diagG_apply_eq t z)

variable {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of L)} (aX : GalAction (k := k) X q)

/-- The equivariant extension `T ×_k L ⟶ X` of `φ : T ⟶ X`: `φ ≫ act g` on `δ_g(T)`. -/
def splitGlue (φ : T ⟶ X) : pullback (t ≫ sL k L) (sL k L) ⟶ X :=
  (splitCover t).glueMorphisms (fun g ↦ φ ≫ aX.act g) (fun g h ↦ by
    by_cases hgh : g = h
    · subst hgh
      have : pullback.fst (diagG k t g) (diagG k t g) = pullback.snd _ _ :=
        (cancel_mono (diagG k t g)).1 pullback.condition
      change pullback.fst (diagG k t g) (diagG k t g) ≫ _ = pullback.snd _ _ ≫ _
      rw [this]
    · haveI : IsEmpty ↥(pullback ((splitCover t).f g) ((splitCover t).f h)) :=
        isEmpty_pullback_diagG t hgh
      exact isInitialOfIsEmpty.hom_ext _ _)

@[reassoc]
lemma diagG_splitGlue (φ : T ⟶ X) (g : Gal(L/k)) :
    diagG k t g ≫ splitGlue t aX φ = φ ≫ aX.act g :=
  (splitCover t).ι_glueMorphisms _ _ g

/-- **Equivariant morphisms out of `T ×_k L = ∐_G T`** are morphisms out of `T`. -/
def splitEquiv : EqMor (t ≫ sL k L) aX ≃ {φ : T ⟶ X // φ ≫ q = t} where
  toFun f := ⟨diagL k t ≫ f.1, by rw [Category.assoc, f.2.1, diagL_snd]⟩
  invFun φ := ⟨splitGlue t aX φ.1, (splitCover t).hom_ext _ _ fun g ↦ by
      change diagG k t g ≫ _ = diagG k t g ≫ _
      rw [diagG_splitGlue_assoc, GalAction.act_comp, reassoc_of% φ.2, diagG_snd],
    fun h ↦ (splitCover t).hom_ext _ _ fun g ↦ by
      change diagG k t g ≫ _ = diagG k t g ≫ _
      rw [diagG_act_assoc, diagG_splitGlue, diagG_splitGlue_assoc, GalAction.act_mul]⟩
  left_inv f := Subtype.ext ((splitCover t).hom_ext _ _ fun g ↦ by
      change diagG k t g ≫ _ = diagG k t g ≫ f.1
      rw [diagG_splitGlue, diagG]
      simp only [Category.assoc]
      exact congrArg (diagL k t ≫ ·) (f.2.2 g).symm)
  right_inv φ := Subtype.ext (by
      change diagL k t ≫ splitGlue t aX φ.1 = φ.1
      rw [← diagG_one, diagG_splitGlue, GalAction.act_one, Category.comp_id])

omit [FiniteDimensional k L] [IsGalois k L] in
lemma diagL_bcL_eq {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of k)}
    (m : T ⟶ pullback y (sL k L)) (hm : m ≫ pullback.snd y (sL k L) = t) :
    diagL k t ≫ bcL y (m ≫ pullback.fst y (sL k L))
      (by rw [Category.assoc, pullback.condition, reassoc_of% hm]) = m := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcL_fst, diagL_fst_assoc]
  · rw [Category.assoc, bcL_snd, diagL_snd, hm]

section Counit

variable (hcov : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ aX.IsStable V ∧ x ∈ V)

/-- The counit `X₀ ×_k L ⟶ X` of the Galois descent: the universal equivariant morphism. -/
def descCounit : EqMor (descScheme aX hcov).hom aX :=
  (descRepresentableBy aX hcov).homEquiv (𝟙 _)

lemma descRepresentableBy_homEquiv {Y : Over (Spec (CommRingCat.of k))}
    (a : Y ⟶ descScheme aX hcov) :
    (descRepresentableBy aX hcov).homEquiv a =
      EqMor.pull _ aX a.left (Over.w a) (descCounit aX hcov) := by
  have := (descRepresentableBy aX hcov).homEquiv_comp a (𝟙 _)
  rw [Category.comp_id] at this
  exact this

omit [FiniteDimensional k L] [IsGalois k L] in
lemma comp_fst_comp {Y T' : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of k)}
    {s : T' ⟶ Spec (CommRingCat.of L)} (m : T' ⟶ pullback y (sL k L))
    (h : m ≫ pullback.snd y (sL k L) = s) :
    (m ≫ pullback.fst y (sL k L)) ≫ y = s ≫ sL k L := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, h]

lemma comp_descCounit {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of L))
    (m : T' ⟶ pullback (descScheme aX hcov).hom (sL k L))
    (h : m ≫ pullback.snd (descScheme aX hcov).hom (sL k L) = s) :
    m ≫ (descCounit aX hcov).1 = (splitEquiv s aX (EqMor.pull _ aX
      (m ≫ pullback.fst _ _) (comp_fst_comp m h) (descCounit aX hcov))).1 := by
  change _ = diagL k s ≫ bcL _ (m ≫ pullback.fst _ _) (comp_fst_comp m h) ≫ _
  rw [← Category.assoc, diagL_bcL_eq s m h]

/-- **`X₀ ×_k L ≅ X`**: the counit of the Galois descent is an isomorphism. -/
theorem isIso_descCounit : IsIso (descCounit aX hcov).1 := by
  refine isIso_of_yoneda_map_bijective _ fun T ↦ ⟨fun m₁ m₂ hm ↦ ?_, fun ψ ↦ ?_⟩
  · have hm' : m₁ ≫ (descCounit aX hcov).1 = m₂ ≫ (descCounit aX hcov).1 := hm
    obtain ⟨s, hs⟩ : ∃ s, m₂ ≫ pullback.snd (descScheme aX hcov).hom (sL k L) = s := ⟨_, rfl⟩
    have h₁ : m₁ ≫ pullback.snd (descScheme aX hcov).hom (sL k L) = s := by
      rw [← hs, ← (descCounit aX hcov).2.1, reassoc_of% hm']
    have e := (comp_descCounit aX hcov s m₁ h₁).symm.trans
      (hm'.trans (comp_descCounit aX hcov s m₂ hs))
    have e' := (splitEquiv s aX).injective (Subtype.ext e)
    let a₁ : Over.mk (s ≫ sL k L) ⟶ descScheme aX hcov :=
      Over.homMk (m₁ ≫ pullback.fst _ _) (comp_fst_comp m₁ h₁)
    let a₂ : Over.mk (s ≫ sL k L) ⟶ descScheme aX hcov :=
      Over.homMk (m₂ ≫ pullback.fst _ _) (comp_fst_comp m₂ hs)
    have E₁ : (descRepresentableBy aX hcov).homEquiv a₁ = EqMor.pull _ aX
        (m₁ ≫ pullback.fst _ _) (comp_fst_comp m₁ h₁) (descCounit aX hcov) :=
      descRepresentableBy_homEquiv aX hcov a₁
    have E₂ : (descRepresentableBy aX hcov).homEquiv a₂ = EqMor.pull _ aX
        (m₂ ≫ pullback.fst _ _) (comp_fst_comp m₂ hs) (descCounit aX hcov) :=
      descRepresentableBy_homEquiv aX hcov a₂
    have e'' : m₁ ≫ pullback.fst _ _ = m₂ ≫ pullback.fst _ _ :=
      congrArg CommaMorphism.left ((descRepresentableBy aX hcov).homEquiv.injective
        (E₁.trans (e'.trans E₂.symm)))
    apply pullback.hom_ext
    · exact e''
    · rw [h₁, hs]
  · obtain ⟨s, hs⟩ : ∃ s, ψ ≫ q = s := ⟨_, rfl⟩
    let e : (descFunctor aX).obj (op (Over.mk (s ≫ sL k L))) := (splitEquiv s aX).symm ⟨ψ, hs⟩
    let a := (descRepresentableBy aX hcov).homEquiv.symm e
    let aL : T ⟶ (descScheme aX hcov).left := a.left
    have hw : aL ≫ (descScheme aX hcov).hom = s ≫ sL k L := Over.w a
    refine ⟨pullback.lift aL s hw, ?_⟩
    have h1 : pullback.lift aL s hw ≫ pullback.fst _ _ = aL := pullback.lift_fst _ _ _
    have h2 : EqMor.pull _ aX aL hw (descCounit aX hcov) = e :=
      (descRepresentableBy_homEquiv aX hcov a).symm.trans (Equiv.apply_symm_apply _ _)
    change pullback.lift aL s hw ≫ (descCounit aX hcov).1 = ψ
    rw [comp_descCounit aX hcov s _ (pullback.lift_snd _ _ _),
      EqMor.pull_congr _ aX h1 _ hw, h2, Equiv.apply_symm_apply]

end Counit

end CurvesJacobian.GaloisDescent
