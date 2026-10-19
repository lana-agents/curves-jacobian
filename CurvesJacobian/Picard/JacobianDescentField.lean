/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianDensity
import CurvesJacobian.Picard.JacobianField
import CurvesJacobian.Descent.GaloisStable
import CurvesJacobian.Descent.GaloisTwist

/-!
# The Jacobian as a `k`-scheme (JAC R2, R4′)

Let `C` be a curve over a perfect field `k` with a rational point `σ` and `Ω ⊇ k` an algebraic
closure. Combining the finitely many good classes over `Ω` (`exists_finset_good`) with
`exists_hasTranslates_ge`, there is a finite Galois subextension `L` of `Ω/k`
(`CurvesJacobian.jacFieldD`) such that

* `Pic_{C_L/L,σ}` is representable, with Jacobian `J_L = jacD C σ hσ Ω` representing
  `Pic⁰_{C/k,σ}` on `(Sch/L)` (`jacDRepresentableBy`);
* every Galois orbit of a point of `J_L` lies in a chart `V(c, A)` (`exists_descent_field`), so
  that `J_L` is covered by `Gal(L/k)`-stable affine opens `⋂_g g⁻¹ V(c, A)`
  (**`CurvesJacobian.jacD_hcov`**, the hypothesis of the Galois descent `descScheme`).

**`CurvesJacobian.jacK C σ hσ Ω`** is the descended `k`-scheme, representing `Gal(L/k)`-equivariant
morphisms `T ×_k L ⟶ J_L` (`jacKRepresentableBy`).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Function

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi Scheme.OpenSubfunctor GaloisDescent

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "sΩ" => specAlgebraMap (k₀ := k) Ω

section Degree

/-- Degrees of a point over a field are unique. -/
lemma picDeg_unique {K : Type u} [Field K] {d e : ℤ}
    {x : (sigmaG G).obj (op (Spec (CommRingCat.of K)))}
    (hd : picDeg σ hσ (curveToP1 k C) d _ x) (he : picDeg σ hσ (curveToP1 k C) e _ x) :
    d = e := by
  have h1 := hd _ (isField_ΓSpec' K) (𝟙 _)
  have h2 := he _ (isField_ΓSpec' K) (𝟙 _)
  linarith

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] in
/-- The degree of a class over `L` is read off over `Ω`. -/
lemma picDeg_of_specIncl (L : IntermediateField k Ω) {d : ℤ}
    (cL : (G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L))))
    (h : picDeg σ hσ (curveToP1 k C) d SΩ ⟨sΩ, ((G).map (Over.homMk (specIncl Ω L)
      (specIncl_comp Ω L) : Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom cL⟩) :
    picDeg σ hσ (curveToP1 k C) d (Spec (CommRingCat.of L))
      ⟨specAlgebraMap (k₀ := k) L, cL⟩ := by
  haveI : Subsingleton (Spec (CommRingCat.of L)) :=
    have : Subsingleton (PrimeSpectrum L) := inferInstance
    this
  obtain ⟨e, he⟩ : ∃ e : ℤ, picDeg σ hσ (curveToP1 k C) e (Spec (CommRingCat.of L))
      ⟨specAlgebraMap (k₀ := k) L, cL⟩ := by
    obtain ⟨U, hU1, -, hU3⟩ := exists_degree_decomposition σ hσ (curveToP1 k C)
      (isSheaf_picSigmaSch_curve k C σ hσ)
      (⟨specAlgebraMap (k₀ := k) L, cL⟩ : (sigmaG G).obj (op (Spec (CommRingCat.of L))))
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of L)) :=
      have : Nonempty (PrimeSpectrum L) := inferInstance
      this
    have hp : p ∈ ⨆ d, U d := by rw [hU3]; trivial
    obtain ⟨d, hpd⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    refine ⟨d, ?_⟩
    have := (hU1 d _ (𝟙 _)).2 (by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim ((𝟙 (Spec (CommRingCat.of L)) : _ ⟶ _) q) p]
      exact hpd)
    rwa [op_id, Functor.map_id_apply] at this
  have he' := picDeg_map_sigmaG C σ hσ (specIncl Ω L) he
  rw [sigmaG_map_mk, sigma_mk_homMk C σ hσ (specIncl_comp Ω L) _ rfl (specIncl_comp Ω L)] at he'
  rw [picDeg_unique C σ hσ h he']
  exact he

end Degree

/-- **The field of definition of the descent data**: a finite Galois subextension `L` of `Ω/k`
with the translate property, finitely many classes `c ∈ Pic_{C/k,σ}(L)` of degree `g`, such
that for every representing object `X` of `Pic⁰_{C/k,σ}` on `(Sch/L)` every point of `X` lies in
all the charts `V(g^* c, A)`, `g ∈ Gal(L/k)`, for one of them. -/
theorem exists_descent_field : ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L)
    (_ : IsGalois k L) (_ : HasTranslates C σ hσ Ω L)
    (s : Finset ((G).obj (op (Over.mk (specAlgebraMap (k₀ := k) L))))),
    (∀ c ∈ s, picDeg σ hσ (curveToP1 k C) (genusNat k C) (Spec (CommRingCat.of L))
      ⟨specAlgebraMap (k₀ := k) L, c⟩) ∧
    ∀ (X : Over (Spec (CommRingCat.of L)))
      (R : ((Over.map (specAlgebraMap (k₀ := k) L)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
        forget AddCommGrpCat).RepresentableBy X) (x : X.left), ∃ c ∈ s, ∀ g : L ≃ₐ[k] L,
      x ∈ chartA C σ hσ R (conjClass C σ hσ (specGalI_comp g) c) (chartOpenA C σ hσ Ω) := by
  classical
  obtain ⟨s₀, hdeg, hcov⟩ := exists_finset_good C σ hσ Ω
  choose Lc hLc hdef using fun c : s₀ ↦ exists_definedOver_any C σ hσ Ω c.1
  let L₀ : IntermediateField k Ω := ⨆ c : s₀, Lc c
  haveI : FiniteDimensional k L₀ := by
    haveI : ∀ c : s₀, FiniteDimensional k (Lc c) := hLc
    exact IntermediateField.finiteDimensional_iSup_of_finite
  obtain ⟨L, hL1, hL2, hL₀L, hL⟩ := exists_hasTranslates_ge C σ hσ Ω L₀
  have hdefL : ∀ c : s₀, DefinedOver C σ hσ Ω c.1 L := fun c ↦
    (hdef c).mono C σ hσ Ω ((le_iSup Lc c).trans hL₀L)
  choose cL hcL using hdefL
  refine ⟨L, hL1, hL2, hL, s₀.attach.image cL, ?_, ?_⟩
  · intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hc
    refine picDeg_of_specIncl C σ hσ Ω L _ ?_
    rw [← hcL c']
    exact hdeg c'.1 c'.2
  intro X R x
  haveI : Normal k Ω := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  -- the residue field and its algebraic closure `Ω' ⊇ Ω`
  let K := X.left.residueField x
  let f := X.left.fromSpecResidueField x
  let t := f ≫ X.hom
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
  let f' := h ≫ f
  have hf' : f' ≫ X.hom = j ≫ specIncl Ω L := by rw [Category.assoc, hjt]
  have hf's : (f' ≫ X.hom) ≫ specAlgebraMap (k₀ := k) L = j ≫ sΩ := by
    rw [hf', Category.assoc, specIncl_comp]
  -- the point of `J_Ω` over `Ω'`
  let y := R.homEquiv (Over.homMk f' rfl : Over.mk (f' ≫ X.hom) ⟶ X)
  let RΩ := jacobianBCRepresentableBy C σ hσ Ω
  let y'' : picZeroGrp (curveToP1 k C) σ hσ (j ≫ sΩ) :=
    ⟨((G).map (Over.homMk (𝟙 _) ((Category.id_comp _).trans hf's) :
      Over.mk (j ≫ sΩ) ⟶ Over.mk ((f' ≫ X.hom) ≫ specAlgebraMap (k₀ := k) L)).op).hom y.1, by
      have h0 : picDeg σ hσ (curveToP1 k C) 0 (Spec (CommRingCat.of Ω'))
          ⟨(f' ≫ X.hom) ≫ specAlgebraMap (k₀ := k) L, y.1⟩ := y.2
      have := picDeg_map_sigmaG C σ hσ (𝟙 (Spec (CommRingCat.of Ω'))) h0
      rwa [sigmaG_map_mk, sigma_mk_homMk C σ hσ ((Category.id_comp _).trans hf's) _ rfl
        ((Category.id_comp _).trans hf's)] at this⟩
  let bO : Over.mk j ⟶ jacOmega C σ hσ Ω := RΩ.homEquiv.symm y''
  let b : Spec (CommRingCat.of Ω') ⟶ (jacOmega C σ hσ Ω).left := bO.left
  have hb : b ≫ (jacOmega C σ hσ Ω).hom = j := Over.w bO
  obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of Ω')) :=
    have : Nonempty (PrimeSpectrum Ω') := inferInstance
    this
  haveI : Subsingleton (Spec (CommRingCat.of Ω')) :=
    have : Subsingleton (PrimeSpectrum Ω') := inferInstance
    this
  haveI : Subsingleton (Spec K) :=
    have : Subsingleton (PrimeSpectrum K) := inferInstance
    this
  obtain ⟨c₀, hc₀s, hτ⟩ := hcov (b q)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, cL ⟨c₀, hc₀s⟩ = c₁ := ⟨_, rfl⟩
  have hc : c₀ = ((G).map (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
      Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L)).op).hom c₁ := by
    rw [← hc₁]
    exact hcL ⟨c₀, hc₀s⟩
  refine ⟨c₁, hc₁ ▸ Finset.mem_image_of_mem _ (Finset.mem_attach _ _), fun g ↦ ?_⟩
  let τ : Ω ≃ₐ[k] Ω := g.liftNormal Ω
  have hτL : specAut τ ≫ specIncl Ω L = specIncl Ω L ≫ specGalI g := by
    rw [specAut, specIncl, specGalI, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact AlgEquiv.liftNormal_commutes g Ω a
  have hbr : Set.range b ⊆ chartA C σ hσ RΩ (conjΩ C σ hσ τ c₀) (chartOpenA C σ hσ Ω) := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a q]
    exact hτ τ
  have hA := (range_subset_chartA_iff C σ hσ RΩ _ _ b).1 hbr
  -- comparison of the two points of `Pic_{C/k,σ}` over `Ω'`
  have key : (sigmaG G).map b.op (chartTranslate C σ hσ RΩ (conjΩ C σ hσ τ c₀)) =
      (sigmaG G).map f'.op (chartTranslate C σ hσ R
        (conjClass C σ hσ (specGalI_comp g) c₁)) := by
    have eL : b ≫ (jacOmega C σ hσ Ω).hom ≫ sΩ = j ≫ sΩ := by rw [← Category.assoc, hb]
    have eR : f' ≫ X.hom ≫ specAlgebraMap (k₀ := k) L = j ≫ sΩ := by
      rw [← Category.assoc]
      exact hf's
    rw [map_chartTranslate, map_chartTranslate]
    refine (sigma_mk_homMk_add C σ hσ (T := Spec (CommRingCat.of Ω')) eL _ b
      (Category.assoc _ _ _) (by rw [Category.assoc]; exact eL) rfl eL _
      (chartUniv C σ hσ RΩ)).trans ((sigma_mk_homMk_add C σ hσ (T := Spec (CommRingCat.of Ω'))
        eR _ f' (Category.assoc _ _ _) (by rw [Category.assoc]; exact eR) rfl eR _
        (chartUniv C σ hσ R)).trans ?_).symm
    refine Sigma.ext rfl (heq_of_eq ?_)
    change _ + _ = _ + _
    congr 1
    · -- the translates
      dsimp only [conjΩ, conjClass]
      rw [hc]
      have w0 : (f' ≫ X.hom ≫ specGalI g) ≫ specAlgebraMap (k₀ := k) L = j ≫ sΩ := by
        rw [Category.assoc f' (X.hom ≫ specGalI g), Category.assoc X.hom, specGalI_comp,
          ← Category.assoc]
        exact hf's
      refine (mapG_mapG_eq C σ hσ (Over.homMk (f' ≫ X.hom) hf's :
        Over.mk (j ≫ sΩ) ⟶ Over.mk (specAlgebraMap (k₀ := k) L))
        (Over.homMk (specGalI g) (specGalI_comp g) : Over.mk (specAlgebraMap (k₀ := k) L) ⟶
          Over.mk (specAlgebraMap (k₀ := k) L))
        (Over.homMk (f' ≫ X.hom ≫ specGalI g) w0) rfl _).trans ?_
      have w2 : (specAut τ ≫ specIncl Ω L) ≫ specAlgebraMap (k₀ := k) L = sΩ := by
        rw [Category.assoc, specIncl_comp, specAut_comp_sΩ]
      have w1 : (b ≫ (jacOmega C σ hσ Ω).hom) ≫ sΩ = j ≫ sΩ := by rw [hb]
      have w3 : ((b ≫ (jacOmega C σ hσ Ω).hom) ≫ specAut τ ≫ specIncl Ω L) ≫
          specAlgebraMap (k₀ := k) L = j ≫ sΩ := by
        rw [Category.assoc, w2, w1]
      refine Eq.trans ?_ (congrArg _ (mapG_mapG_eq C σ hσ
        (Over.homMk (specAut τ) (specAut_comp_sΩ τ) : Over.mk sΩ ⟶ Over.mk sΩ)
        (Over.homMk (specIncl Ω L) (specIncl_comp Ω L) :
          Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L))
        (Over.homMk (specAut τ ≫ specIncl Ω L) w2) rfl _)).symm
      refine Eq.trans ?_ (mapG_mapG_eq C σ hσ
        (Over.homMk (b ≫ (jacOmega C σ hσ Ω).hom) w1 : Over.mk (j ≫ sΩ) ⟶ Over.mk sΩ)
        (Over.homMk (specAut τ ≫ specIncl Ω L) w2 :
          Over.mk sΩ ⟶ Over.mk (specAlgebraMap (k₀ := k) L))
        (Over.homMk ((b ≫ (jacOmega C σ hσ Ω).hom) ≫ specAut τ ≫ specIncl Ω L) w3) rfl _).symm
      refine mapG_congr_left C σ hσ ?_ _
      change f' ≫ X.hom ≫ specGalI g = (b ≫ (jacOmega C σ hσ Ω).hom) ≫ specAut τ ≫ specIncl Ω L
      rw [hb, hτL, ← Category.assoc, hf', Category.assoc]
    · -- the universal points
      have e1 : (Over.homMk b hb : Over.mk j ⟶ jacOmega C σ hσ Ω) = bO :=
        Over.OverMorphism.ext rfl
      have h1 := homEquiv_homMk_val C σ hσ RΩ b j hb eL
      rw [e1, Equiv.apply_symm_apply] at h1
      have h2 := homEquiv_homMk_val C σ hσ R f' (f' ≫ X.hom) rfl (Category.assoc _ _ _).symm
      refine Eq.trans ?_ h1
      change _ = ((G).map _).hom y.1
      rw [show y.1 = _ from h2]
      exact (mapG_mapG_eq C σ hσ (Over.homMk (𝟙 _) ((Category.id_comp _).trans hf's) :
        Over.mk (j ≫ sΩ) ⟶ Over.mk ((f' ≫ X.hom) ≫ specAlgebraMap (k₀ := k) L))
        (Over.homMk f' (Category.assoc _ _ _).symm :
          Over.mk ((f' ≫ X.hom) ≫ specAlgebraMap (k₀ := k) L) ⟶
            Over.mk (X.hom ≫ specAlgebraMap (k₀ := k) L))
        (Over.homMk f' eR) (Category.id_comp _) _).symm
  rw [key, ← map_map_sigmaG] at hA
  have hF : picF σ hσ (curveToP1 k C) (Spec K) ((sigmaG G).map f.op (chartTranslate C σ hσ R
      (conjClass C σ hσ (specGalI_comp g) c₁))) := by
    refine picF_of_map C (curveToP1 k C) σ hσ h _ ?_
    obtain ⟨a, -, ha⟩ := hA
    exact (picF_iff_exists_xiWk C σ hσ _).2 ⟨a, ha⟩
  have hsurj : Function.Surjective h := fun a ↦ ⟨q, Subsingleton.elim _ _⟩
  have := (range_subset_chartA_iff C σ hσ R _ _ f).2 (hA.of_map C σ hσ h hsurj hF)
  rw [Scheme.range_fromSpecResidueField] at this
  exact this (Set.mem_singleton x)

/-- **The field of definition of `J`**: a finite Galois subextension of `Ω/k` as in
`exists_descent_field`. -/
def jacFieldD : IntermediateField k Ω := (exists_descent_field C σ hσ Ω).choose

instance : FiniteDimensional k (jacFieldD C σ hσ Ω) :=
  (exists_descent_field C σ hσ Ω).choose_spec.1

instance : IsGalois k (jacFieldD C σ hσ Ω) :=
  (exists_descent_field C σ hσ Ω).choose_spec.2.1

instance : PerfectField (jacFieldD C σ hσ Ω) := Algebra.IsAlgebraic.perfectField k

lemma hasTranslates_jacFieldD : HasTranslates C σ hσ Ω (jacFieldD C σ hσ Ω) :=
  (exists_descent_field C σ hσ Ω).choose_spec.2.2.1

local notation "LD" => jacFieldD C σ hσ Ω

instance isRepresentable_jacFieldD :
    (picSigmaSch (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) LD) ↘ Spec (CommRingCat.of LD))
      (sigmaExt C σ hσ LD) (sigmaExt_comp C σ hσ LD)).IsRepresentable :=
  isRepresentable_of_hasTranslates C σ hσ Ω LD (hasTranslates_jacFieldD C σ hσ Ω)

/-- **The Jacobian `J_L` over `L = jacFieldD C σ hσ Ω`** (the Jacobian of `C_L`). -/
abbrev jacD : Over (Spec (CommRingCat.of LD)) :=
  Jacobian (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) LD)) (sigmaExt C σ hσ LD)
    (sigmaExt_comp C σ hσ LD)

/-- `J_L` represents `Pic⁰_{C/k,σ}` on `(Sch/L)`. -/
def jacDRepresentableBy :
    ((Over.map (specAlgebraMap (k₀ := k) LD)).op ⋙ picZero C σ hσ (curveToP1 k C) ⋙
      forget AddCommGrpCat).RepresentableBy (jacD C σ hσ Ω) :=
  jacobianBCRepresentableBy C σ hσ LD

/-- **The semilinear `Gal(L/k)`-action on `J_L`** (Yoneda twists, `twistGalAction`). -/
def jacDAction : GalAction (k := k) (jacD C σ hσ Ω).left (jacD C σ hσ Ω).hom :=
  twistGalAction (picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat)
    (jacDRepresentableBy C σ hσ Ω)

/-- **`J_L` is covered by `Gal(L/k)`-stable affine opens** (JAC R2): for `x ∈ J_L` take the
chart `V(c, A)` of `exists_descent_field` and `V = ⋂_g g⁻¹ V(c, A)`. -/
theorem jacD_hcov (x : (jacD C σ hσ Ω).left) :
    ∃ V : (jacD C σ hσ Ω).left.Opens, IsAffineOpen V ∧ (jacDAction C σ hσ Ω).IsStable V ∧
      x ∈ V := by
  obtain ⟨hdeg, hcov⟩ := (exists_descent_field C σ hσ Ω).choose_spec.2.2.2.choose_spec
  obtain ⟨c, hcs, hc⟩ := hcov (jacD C σ hσ Ω) (jacDRepresentableBy C σ hσ Ω) x
  refine ⟨(jacDAction C σ hσ Ω).stableInf (chartA C σ hσ (jacDRepresentableBy C σ hσ Ω) c
    (chartOpenA C σ hσ Ω)), ?_, (jacDAction C σ hσ Ω).isStable_stableInf _, ?_⟩
  · haveI : IsSeparated (jacD C σ hσ Ω).hom := isSeparated_of_grpObj_field _
    exact (jacDAction C σ hσ Ω).isAffineOpen_stableInf
      (isAffineOpen_chartA C σ hσ _ c (hdeg c hcs) (isAffineOpen_chartOpenA C σ hσ Ω))
  · rw [GalAction.mem_stableInf_iff]
    intro g
    have h := hc g
    rw [← twistLeft_preimage_chartA] at h
    exact h

/-- **The Jacobian of `C` as a `k`-scheme** (JAC R4′): the Galois descent of `J_L` along
`Spec L ⟶ Spec k`. -/
def jacK : Over Sk := descScheme (jacDAction C σ hσ Ω) (jacD_hcov C σ hσ Ω)

/-- `Hom_k(T, J_k) ≃ Hom^{Gal(L/k)}_L(T ×_k L, J_L)`. -/
def jacKRepresentableBy : (descFunctor (jacDAction C σ hσ Ω)).RepresentableBy (jacK C σ hσ Ω) :=
  descRepresentableBy (jacDAction C σ hσ Ω) (jacD_hcov C σ hσ Ω)

end CurvesJacobian
