/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.AbelInj
import CurvesJacobian.Picard.ZeroSchemeDivisor
import CurvesJacobian.Picard.OpenSubfunctorLocal
import CurvesJacobian.Picard.TranslateRep

/-!
# `F` is an open subscheme of `Hilb^g` (Stacks, Lemma 44.6.4, Tag 0B9X)

Let `C` be a curve of genus `g` over a perfect field `k` with a rational point `σ` and a finite
`π : C → ℙ¹_k`. Let `ξ ∈ Pic_{C/k,σ}(Hilb^g)` be the Abel class of the universal divisor
(`xiHilb`, from `abelMap`), and `W ⊆ Hilb^g` the largest open over which `ξ` lies in the open
subfunctor `F` of Stacks, Lemma 44.6.2 (Tag 0B9V) (`picF`). Then `(W, ξ|_W)` represents `F`:
* `CurvesJacobian.injective_xiW`: `a ↦ ξ|_a` is injective on `T`-points of `W`, `T` affine;
* `CurvesJacobian.picF_iff_exists_xiW`: `x ∈ F(T)` iff `x = ξ|_a` for some `a : T ⟶ W`.
These are exactly the hypotheses `hinj`, `hrange` of `isRepresentable_of_translate`
(Stacks, Lemma 44.5.1, Tag 0B9Q).

As in Stacks, injectivity says that a divisor in `F` is the zero scheme of a generator of
`H⁰` of its line bundle (`eq_of_abelClass_eq`), and surjectivity takes, locally on `T`, the zero
scheme of a generator of `H⁰` of `L ⊗ f^*N⁻¹` (`exists_relEffCartier_of_cyclic`), a relative
effective Cartier divisor of degree `g`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi Scheme.OpenSubfunctor

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

variable (k) in
/-- The genus of `C` as a natural number. -/
def genusNat : ℕ := haveI := IsCurveOver.isIntegral k C; (curveGenus k C).toNat

/-- The Abel class of the universal divisor on `Hilb^g`. -/
def xiHilb : (sigmaG G).obj (op (hilbCurve k C (genusNat k C))) :=
  yonedaEquiv (abelMap C σ hσ (genusNat k C))

lemma map_xiHilb {T : Scheme.{u}} (a : T ⟶ hilbCurve k C (genusNat k C)) :
    (sigmaG G).map a.op (xiHilb C σ hσ) = (abelMap C σ hσ (genusNat k C)).app (op T) a :=
  map_yonedaEquiv (F := picSigmaSch (C ↘ Sk) σ hσ) _ a

/-- The open `W ⊆ Hilb^g` over which the Abel class of the universal divisor lies in `F`. -/
def opensW (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]
    (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G)) :
    (hilbCurve k C (genusNat k C)).Opens :=
  Classical.choose (exists_opens_of_isAffine (F := sheafG G hG)
    (isLocalPredicate_picF σ hσ π hG) (picF_open σ hσ π) (xiHilb C σ hσ))

lemma picF_map_xiHilb_iff (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    {T : Scheme.{u}} (a : T ⟶ hilbCurve k C (genusNat k C)) :
    picF σ hσ π T ((sigmaG G).map a.op (xiHilb C σ hσ)) ↔ Set.range a ⊆ opensW C σ hσ π hG :=
  Classical.choose_spec (exists_opens_of_isAffine (F := sheafG G hG)
    (isLocalPredicate_picF σ hσ π hG) (picF_open σ hσ π) (xiHilb C σ hσ)) T a

/-- `ξ|_W`. -/
def xiW (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G)) :
    (sigmaG G).obj (op (opensW C σ hσ π hG).toScheme) :=
  (sigmaG G).map (opensW C σ hσ π hG).ι.op (xiHilb C σ hσ)

/-- **Injectivity** on `Hilb^g` over `F`. -/
theorem eq_of_map_xiHilb_eq {T : Scheme.{u}} [IsAffine T]
    (a b : T ⟶ hilbCurve k C (genusNat k C))
    (hF : picF σ hσ π T ((sigmaG G).map b.op (xiHilb C σ hσ)))
    (h : (sigmaG G).map a.op (xiHilb C σ hσ) = (sigmaG G).map b.op (xiHilb C σ hσ)) :
    a = b := by
  rw [map_xiHilb, map_xiHilb] at h
  rw [map_xiHilb] at hF
  apply (hilbCurveEquiv k C (genusNat k C) T).injective
  rw [abelMap_app, abelMap_app] at h
  rw [abelMap_app] at hF
  generalize hilbCurveEquiv k C (genusNat k C) T a = Pa at h hF ⊢
  generalize hilbCurveEquiv k C (genusNat k C) T b = Pb at h hF ⊢
  obtain ⟨ga, Da, hDa⟩ := Pa
  obtain ⟨gb, Db, hDb⟩ := Pb
  obtain ⟨rfl, hab⟩ := Sigma.mk.inj_iff.mp h
  have hab' := eq_of_heq hab
  have := eq_of_abelClass_eq σ hσ π ga Da Db hDa hDb hab' hF
  subst this
  rfl

/-- **Injectivity** (`hinj` of `isRepresentable_of_translate`). -/
theorem injective_xiW (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    (T : Scheme.{u}) [IsAffine T] :
    Function.Injective fun a : T ⟶ (opensW C σ hσ π hG).toScheme ↦
      (sigmaG G).map a.op (xiW C σ hσ π hG) := by
  intro a b hab
  change (sigmaG G).map a.op ((sigmaG G).map (opensW C σ hσ π hG).ι.op (xiHilb C σ hσ)) =
    (sigmaG G).map b.op ((sigmaG G).map (opensW C σ hσ π hG).ι.op (xiHilb C σ hσ)) at hab
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp] at hab
  refine (cancel_mono (opensW C σ hσ π hG).ι).mp
    (eq_of_map_xiHilb_eq C σ hσ π _ _ ?_ hab)
  rw [picF_map_xiHilb_iff C σ hσ π hG]
  rintro _ ⟨t, rfl⟩
  simp

/-- **Surjectivity** (`hrange` of `isRepresentable_of_translate`, `⇒`): every point of `F` over
an affine scheme comes from `W`. -/
theorem exists_map_xiW (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    {T : Scheme.{u}} [IsAffine T] (x : (sigmaG G).obj (op T)) (hx : picF σ hσ π T x) :
    ∃ a : T ⟶ (opensW C σ hσ π hG).toScheme, (sigmaG G).map a.op (xiW C σ hσ π hG) = x := by
  refine exists_of_locally (F := sheafG G hG) (xiW C σ hσ π hG) (injective_xiW C σ hσ π hG) x
    fun t ↦ ?_
  obtain ⟨g, y⟩ := x
  have hFC : FCond π g (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) := by
    have := hx T (𝟙 T)
    rwa [op_id, Functor.map_id_apply] at this
  letI : T.Over Sk := ⟨g⟩
  haveI : Scheme.Modules.IsInvertible (X := pullback (C ↘ Sk) (T ↘ Sk))
      (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) :=
    inferInstanceAs (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1).IsInvertible
  obtain ⟨r, htr, hcyc⟩ := exists_basicOpen_H0_cyclic π (T := T)
    (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) hFC t
  let U : T.Opens := T.basicOpen r
  letI : U.toScheme.Over T := ⟨U.ι⟩
  obtain ⟨s, hs⟩ := hcyc U (by rintro _ ⟨u, rfl⟩; exact u.2)
  let φ := bcMap (C ↘ Sk) U.ι g (U.ι ≫ g) rfl
  have hFU : FCond π (U.ι ≫ g) ((Scheme.Modules.pullback φ).obj
      (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1)) :=
    (fPoint_map_iff σ hσ π U.ι g y).mp (hx U U.ι)
  obtain ⟨D, hdeg, hpic⟩ := exists_relEffCartier_of_cyclic π (U.ι ≫ g) _ hFU s hs
  have hdegN : ∀ t, D.degree t = genusNat k C := fun t ↦ by
    rw [genusNat, ← hdeg t, Int.toNat_natCast]
  let aU : U.toScheme ⟶ hilbCurve k C (genusNat k C) :=
    (hilbCurveEquiv k C (genusNat k C) U).symm ⟨U.ι ≫ g, D, hdegN⟩
  have habel : abelClass (C ↘ Sk) σ hσ D = picSigmaMap (C ↘ Sk) σ hσ U.ι g (U.ι ≫ g) rfl y := by
    apply Subtype.ext
    rw [coe_abelClass, coe_picSigmaMap, hpic, mk_pullback_rep]
    have hy : Scheme.Pic.map (secT (C ↘ Sk) σ hσ g) (y : picSigmaGrp (C ↘ Sk) σ hσ g).1 = 0 :=
      (y : picSigmaGrp (C ↘ Sk) σ hσ g).2
    have h0 : Scheme.Pic.map (secT (C ↘ Sk) σ hσ (U.ι ≫ g)) (Scheme.Pic.map φ y.1) = 0 := by
      rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, secT_bcMap, Scheme.Pic.map_comp,
        AddMonoidHom.comp_apply, hy, map_zero]
    rw [h0, map_zero, sub_zero]
  have hmap : (sigmaG G).map aU.op (xiHilb C σ hσ) =
      (sigmaG G).map U.ι.op ⟨g, y⟩ := by
    have e : hilbCurveEquiv k C (genusNat k C) U aU = ⟨U.ι ≫ g, D, hdegN⟩ :=
      Equiv.apply_symm_apply _ _
    rw [map_xiHilb, abelMap_app, e, sigmaG_map_mk]
    exact Sigma.ext rfl (heq_of_eq habel)
  have hrange : Set.range aU ⊆ opensW C σ hσ π hG := by
    rw [← picF_map_xiHilb_iff C σ hσ π hG, hmap]
    exact (isLocalPredicate_picF σ hσ π hG).map U.ι _ hx
  refine ⟨U, htr, IsOpenImmersion.lift (opensW C σ hσ π hG).ι aU
    (by rwa [Scheme.Opens.range_ι]), ?_⟩
  change (sigmaG G).map _ ((sigmaG G).map (opensW C σ hσ π hG).ι.op (xiHilb C σ hσ)) = _
  rw [← Functor.map_comp_apply, ← op_comp, IsOpenImmersion.lift_fac]
  exact hmap

/-- **`(W, ξ|_W)` represents `F` on affine schemes** (Stacks, Lemma 44.6.4, Tag 0B9X; the
`hrange` input of `isRepresentable_of_translate`). -/
theorem picF_iff_exists_xiW (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)) :
    picF σ hσ π T x ↔
      ∃ a : T ⟶ (opensW C σ hσ π hG).toScheme, (sigmaG G).map a.op (xiW C σ hσ π hG) = x := by
  refine ⟨exists_map_xiW C σ hσ π hG x, ?_⟩
  rintro ⟨a, rfl⟩
  change picF σ hσ π T ((sigmaG G).map a.op ((sigmaG G).map (opensW C σ hσ π hG).ι.op
    (xiHilb C σ hσ)))
  rw [← Functor.map_comp_apply, ← op_comp, picF_map_xiHilb_iff C σ hσ π hG]
  rintro _ ⟨t, rfl⟩
  simp

end CurvesJacobian
