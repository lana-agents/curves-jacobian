/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RigidUnique

/-!
# Gluing rigidified sheaves

This file is generic. In the setting of `CurvesJacobian.Picard.RigidUnique` (`r : Y ⟶ T` with a
section `s`, `r^♯` surjective on all opens), let `V i` be saturated opens covering `Y` and `M i`
sheaves of modules invertible on `V i` with evaluations `χ i` along `s`. Any section-wise
isomorphisms `M i|_{V i ∩ V j} ≅ M j|_{V i ∩ V j}` can be replaced by rigid ones, which then
satisfy the cocycle condition by uniqueness; hence they form gluing data
(`glueDataOfRigid`). The glued sheaf carries an evaluation along `s` on all of `Y`
(`GlueData.rig`), i.e. a trivialisation of its pullback along `s`, and is section-wise
isomorphic to `M i` on `V i` (`GlueData.locIso`).

Conversely, an invertible sheaf with an evaluation along `s` on `Y` which is section-wise
trivial on every `V i` is trivial (`nonempty_iso_unit_of_rig`).

This is the gluing of rigidified invertible sheaves behind the Zariski sheaf property of
`Pic_{X/S,σ}` (Stacks, Section 44.6, Tag 0B9R; proof of Lemma 44.4.3, Tag 0B9N).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}} {r : Y ⟶ T} {s : T ⟶ Y}

variable {ι : Type u} {V : ι → Y.Opens} {M : ι → Y.Modules}

/-- A rigid section-wise isomorphism, chosen by `LocIso.exists_isRigid`. -/
def LocIso.rigidify (hsr : s ≫ r = 𝟙 T) {N P : Y.Modules} {W VN VP : Y.Opens}
    (hW : r ⁻¹ᵁ (s ⁻¹ᵁ W) = W) (hNW : IsInvOn N W) (χN : Rig s N VN) (χP : Rig s P VP)
    (hN : W ≤ VN) (hP : W ≤ VP) (Φ : LocIso N P W) : LocIso N P W :=
  Classical.choose (LocIso.exists_isRigid hsr hW hNW χN χP hN hP Φ)

lemma LocIso.isRigid_rigidify (hsr : s ≫ r = 𝟙 T) {N P : Y.Modules} {W VN VP : Y.Opens}
    (hW : r ⁻¹ᵁ (s ⁻¹ᵁ W) = W) (hNW : IsInvOn N W) (χN : Rig s N VN) (χP : Rig s P VP)
    (hN : W ≤ VN) (hP : W ≤ VP) (Φ : LocIso N P W) :
    (Φ.rigidify hsr hW hNW χN χP hN hP).IsRigid χN χP hN hP :=
  Classical.choose_spec (LocIso.exists_isRigid hsr hW hNW χN χP hN hP Φ)

lemma sat_inf (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i) (i j : ι) :
    r ⁻¹ᵁ (s ⁻¹ᵁ (V i ⊓ V j)) = V i ⊓ V j := by
  simp only [Scheme.Hom.preimage_inf, hV]

lemma sat_inf₃ (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i) (i j k : ι) :
    r ⁻¹ᵁ (s ⁻¹ᵁ (V i ⊓ V j ⊓ V k)) = V i ⊓ V j ⊓ V k := by
  simp only [Scheme.Hom.preimage_inf, hV]

/-- The rigidified transition isomorphisms. -/
def rigTrans (hsr : s ≫ r = 𝟙 T) (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i)
    (hM : ∀ i, IsInvOn (M i) (V i)) (χ : ∀ i, Rig s (M i) (V i))
    (Φ : ∀ i j, LocIso (M i) (M j) (V i ⊓ V j)) (i j : ι) : LocIso (M i) (M j) (V i ⊓ V j) :=
  (Φ i j).rigidify hsr (sat_inf hV i j) ((hM i).mono inf_le_left) (χ i) (χ j) inf_le_left
    inf_le_right

lemma isRigid_rigTrans (hsr : s ≫ r = 𝟙 T) (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i)
    (hM : ∀ i, IsInvOn (M i) (V i)) (χ : ∀ i, Rig s (M i) (V i))
    (Φ : ∀ i j, LocIso (M i) (M j) (V i ⊓ V j)) (i j : ι) :
    (rigTrans hsr hV hM χ Φ i j).IsRigid (χ i) (χ j) inf_le_left inf_le_right :=
  LocIso.isRigid_rigidify _ _ _ _ _ _ _ _

/-- Gluing data from arbitrary section-wise isomorphisms on overlaps, made rigid. -/
def glueDataOfRigid (hsr : s ≫ r = 𝟙 T) (hΓ : ∀ U : T.Opens, Function.Surjective (r.app U))
    (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i) (hM : ∀ i, IsInvOn (M i) (V i))
    (χ : ∀ i, Rig s (M i) (V i)) (Φ : ∀ i j, LocIso (M i) (M j) (V i ⊓ V j)) :
    GlueData V M where
  ψ i j W hi hj := (rigTrans hsr hV hM χ Φ i j).φ W (le_inf hi hj)
  ψ_smul i j W hi hj c m := (rigTrans hsr hV hM χ Φ i j).φ_smul W _ c m
  ψ_rs i j W W' hi hj h m := (rigTrans hsr hV hM χ Φ i j).φ_rs W W' _ h m
  ψ_self i W hi m := by
    have := LocIso.ext_of_isRigid hsr hΓ (sat_inf hV i i) ((hM i).mono inf_le_left)
      (isRigid_rigTrans hsr hV hM χ Φ i i) (LocIso.isRigid_refl (χ i) inf_le_left) W
      (le_inf hi hi) m
    rw [LocIso.refl_φ] at this
    exact this
  ψ_comp i j k W hi hj hk m := by
    have h1 : V i ⊓ V j ⊓ V k ≤ V i ⊓ V j := inf_le_left
    have h2 : V i ⊓ V j ⊓ V k ≤ V j ⊓ V k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h3 : V i ⊓ V j ⊓ V k ≤ V i ⊓ V k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have := LocIso.ext_of_isRigid hsr hΓ (sat_inf₃ hV i j k)
      ((hM i).mono (h1.trans inf_le_left))
      (((isRigid_rigTrans hsr hV hM χ Φ i j).restrict h1).trans
        ((isRigid_rigTrans hsr hV hM χ Φ j k).restrict h2))
      ((isRigid_rigTrans hsr hV hM χ Φ i k).restrict h3) W (le_inf (le_inf hi hj) hk) m
    simp only [LocIso.trans_φ, LocIso.restrict_φ] at this
    exact this

lemma glueDataOfRigid_isRigid (hsr : s ≫ r = 𝟙 T)
    (hΓ : ∀ U : T.Opens, Function.Surjective (r.app U)) (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i)
    (hM : ∀ i, IsInvOn (M i) (V i)) (χ : ∀ i, Rig s (M i) (V i))
    (Φ : ∀ i j, LocIso (M i) (M j) (V i ⊓ V j)) (i j : ι) (W : Y.Opens) (hi : W ≤ V i)
    (hj : W ≤ V j) (m : Γ(M i, W)) :
    (χ j).χ W hj ((glueDataOfRigid hsr hΓ hV hM χ Φ).ψ i j W hi hj m) = (χ i).χ W hi m :=
  isRigid_rigTrans hsr hV hM χ Φ i j W (le_inf hi hj) m

namespace GlueData

variable (D : GlueData V M)

/-- The `i`-th components of a glued section, evaluated along `s`, agree on overlaps. -/
lemma rig_compat (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m)
    {W : Y.Opens} (x : D.sec W) (i j : ι) (U' : T.Opens) (h1 : U' ≤ s ⁻¹ᵁ rV V i W)
    (h2 : U' ≤ s ⁻¹ᵁ rV V j W) :
    rr h1 ((χ i).χ (rV V i W) (rV_le_V V i W) (x.1 i)) =
      rr h2 ((χ j).χ (rV V j W) (rV_le_V V j W) (x.1 j)) := by
  have hU : U' ≤ s ⁻¹ᵁ (rV V i W ⊓ rV V j W) := le_inf h1 h2
  have hi : rV V i W ⊓ rV V j W ≤ V i := inf_le_left.trans (rV_le_V V i W)
  have hj : rV V i W ⊓ rV V j W ≤ V j := inf_le_right.trans (rV_le_V V j W)
  have e1 := (χ i).χ_rs (rV V i W) (rV V i W ⊓ rV V j W) (rV_le_V V i W) inf_le_left (x.1 i)
  have e2 := (χ j).χ_rs (rV V j W) (rV V i W ⊓ rV V j W) (rV_le_V V j W) inf_le_right (x.1 j)
  have e3 := hD i j _ hi hj (rs (M i) inf_le_left (x.1 i))
  rw [D.compat' x i j _ hi hj inf_le_left inf_le_right] at e3
  calc rr h1 ((χ i).χ (rV V i W) (rV_le_V V i W) (x.1 i))
      = rr hU (rr (s.preimage_mono inf_le_left)
          ((χ i).χ (rV V i W) (rV_le_V V i W) (x.1 i))) := (rr_rr _ _ _).symm
    _ = rr hU (rr (s.preimage_mono inf_le_right)
          ((χ j).χ (rV V j W) (rV_le_V V j W) (x.1 j))) := by
        rw [← e1, ← e2, e3]
    _ = rr h2 ((χ j).χ (rV V j W) (rV_le_V V j W) (x.1 j)) := rr_rr _ _ _

/-- Sections over `s⁻¹ W` are determined by their restrictions to the `s⁻¹ (V i ∩ W)`. -/
lemma rig_ext (hcov : ∀ y : Y, ∃ i, y ∈ V i) {W : Y.Opens} {g g' : Γ(T, s ⁻¹ᵁ W)}
    (h : ∀ i, rr (s.preimage_mono (rV_le V i W)) g = rr (s.preimage_mono (rV_le V i W)) g') :
    g = g' := by
  refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun t ht ↦ ?_
  obtain ⟨i, hi⟩ := hcov (s.base t)
  refine ⟨s ⁻¹ᵁ rV V i W, s.preimage_mono (rV_le V i W), ?_, h i⟩
  change s.base t ∈ rV V i W
  rw [rV_eq]
  exact ⟨hi, ht⟩

lemma rig_exists (hcov : ∀ y : Y, ∃ i, y ∈ V i) (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m)
    {W : Y.Opens} (x : D.sec W) :
    ∃ g : Γ(T, s ⁻¹ᵁ W), ∀ i, rr (s.preimage_mono (rV_le V i W)) g =
      (χ i).χ (rV V i W) (rV_le_V V i W) (x.1 i) := by
  choose idx hidx using hcov
  have hmem : ∀ t : s ⁻¹ᵁ W, t.1 ∈ s ⁻¹ᵁ rV V (idx (s.base t.1)) W := fun t ↦ by
    change s.base t.1 ∈ rV V _ W
    rw [rV_eq]
    exact ⟨hidx _, t.2⟩
  obtain ⟨g, hg⟩ := CurvesJacobian.sheaf_exists_glue T.sheaf (V := s ⁻¹ᵁ W)
    (fun t ↦ s ⁻¹ᵁ rV V (idx (s.base t.1)) W) (fun t ↦ s.preimage_mono (rV_le V _ W)) hmem
    (fun t ↦ (χ _).χ (rV V _ W) (rV_le_V V _ W) (x.1 (idx (s.base t.1))))
    (fun t t' ↦ D.rig_compat χ hD x _ _ _ inf_le_left inf_le_right)
  have hg' : ∀ t : s ⁻¹ᵁ W, rr (s.preimage_mono (rV_le V (idx (s.base t.1)) W)) g =
      (χ _).χ (rV V _ W) (rV_le_V V _ W) (x.1 (idx (s.base t.1))) := hg
  refine ⟨g, fun i ↦ CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun t ht ↦ ?_⟩
  have htW : t ∈ s ⁻¹ᵁ W := s.preimage_mono (rV_le V i W) ht
  refine ⟨s ⁻¹ᵁ rV V i W ⊓ s ⁻¹ᵁ rV V (idx (s.base t)) W, inf_le_left,
    ⟨ht, hmem ⟨t, htW⟩⟩, ?_⟩
  change rr inf_le_left (rr _ g) = rr inf_le_left _
  rw [rr_rr, D.rig_compat χ hD x i (idx (s.base t)) _ inf_le_left inf_le_right,
    ← hg' ⟨t, htW⟩, rr_rr]

/-- The evaluation along `s` of a glued section. -/
def rigFun (hcov : ∀ y : Y, ∃ i, y ∈ V i) (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m)
    {W : Y.Opens} (x : D.sec W) : Γ(T, s ⁻¹ᵁ W) :=
  Classical.choose (D.rig_exists hcov χ hD x)

section rigFun

variable (hcov : ∀ y : Y, ∃ i, y ∈ V i) (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m)

lemma rigFun_spec {W : Y.Opens} (x : D.sec W) (i : ι) :
    rr (s.preimage_mono (rV_le V i W)) (D.rigFun hcov χ hD x) =
      (χ i).χ (rV V i W) (rV_le_V V i W) (x.1 i) :=
  Classical.choose_spec (D.rig_exists hcov χ hD x) i

lemma rigFun_add {W : Y.Opens} (x y : D.sec W) :
    D.rigFun hcov χ hD (x + y) = D.rigFun hcov χ hD x + D.rigFun hcov χ hD y := by
  refine rig_ext hcov fun i ↦ ?_
  rw [rigFun_spec, rr, map_add, ← rr, ← rr, rigFun_spec, rigFun_spec]
  exact map_add _ _ _

lemma rigFun_smul {W : Y.Opens} (c : Γ(Y, W)) (x : D.sec W) :
    D.rigFun hcov χ hD (c • x) = s.app W c * D.rigFun hcov χ hD x := by
  refine rig_ext hcov fun i ↦ ?_
  rw [rigFun_spec, rr_mul, rigFun_spec, smul_coe, (χ i).χ_smul, app_rr]

lemma rigFun_rs {W W' : Y.Opens} (h : W' ≤ W) (x : D.sec W) :
    D.rigFun hcov χ hD (D.restrictSec h x) = rr (s.preimage_mono h) (D.rigFun hcov χ hD x) := by
  refine rig_ext hcov fun i ↦ ?_
  rw [rigFun_spec, restrictSec_coe,
    (χ i).χ_rs (rV V i W) (rV V i W') (rV_le_V V i W) (rV_mono V i h) (x.1 i),
    ← rigFun_spec D hcov χ hD x i, rr_rr, rr_rr]

end rigFun

/-- The glued sheaf is section-wise isomorphic to `M i` on `V i`. -/
def locIso (D : GlueData V M) (i : ι) : LocIso D.glued (M i) (V i) where
  φ W hW :=
    { toFun := fun x ↦ rs (M i) (rV_eq_self V i hW).ge ((x : D.sec W).1 i)
      map_zero' := map_zero _
      map_add' := fun _ _ ↦ map_add _ _ _ }
  φ_smul W hW c x := by
    change rs (M i) _ ((c • (show D.sec W from x)).1 i) =
      c • rs (M i) _ ((show D.sec W from x).1 i)
    rw [smul_coe, rs_smul, rr_rr, rr_self]
  φ_rs W W' hW h x := by
    change rs (M i) _ ((D.restrictSec h x).1 i) = rs (M i) h (rs (M i) _ ((x : D.sec W).1 i))
    rw [restrictSec_coe, rs_rs, rs_rs]
  bij W hW := by
    refine ⟨fun x y hxy ↦ ?_, fun m ↦ ⟨D.ext i hW m, ?_⟩⟩
    · have hxy' : rs (M i) (rV_eq_self V i hW).symm.le ((x : D.sec W).1 i) =
          rs (M i) (rV_eq_self V i hW).symm.le ((y : D.sec W).1 i) := hxy
      exact D.sec_ext_of_le i hW ((rs_bijective_of_eq (M i) (rV_eq_self V i hW).symm).1 hxy')
    · change rs (M i) _ ((D.ext i hW m).1 i) = m
      rw [ext_coe_self, rs_rs, rs_self]

lemma locIso_φ (i : ι) (W : Y.Opens) (hW : W ≤ V i) (x : D.sec W) :
    (D.locIso i).φ W hW x = rs (M i) (rV_eq_self V i hW).ge (x.1 i) :=
  rfl

/-- The components of a basis of the glued sheaf are bases. -/
lemma isBasisOn_coe {W : Y.Opens} {x : D.sec W} (hx : D.glued.IsBasisOn W x) (i : ι) :
    (M i).IsBasisOn (rV V i W) (x.1 i) := by
  have h := (D.locIso i).isBasisOn_φ (rV_le_V V i W) (isBasisOn_rs hx (rV_le V i W))
  have e : (D.locIso i).φ (rV V i W) (rV_le_V V i W) (rs D.glued (rV_le V i W) x) = x.1 i := by
    change rs (M i) _ ((D.restrictSec (rV_le V i W) x).1 i) = x.1 i
    rw [restrictSec_coe, rs_rs, rs_self]
  rwa [e] at h

lemma isUnit_rigFun (hcov : ∀ y : Y, ∃ i, y ∈ V i) (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m)
    {W : Y.Opens} {x : D.sec W} (hx : D.glued.IsBasisOn W x) :
    IsUnit (D.rigFun hcov χ hD x) := by
  refine T.toRingedSpace.isUnit_of_isUnit_germ _ _ fun t ht ↦ ?_
  obtain ⟨i, hi⟩ := hcov (s.base t)
  have htU : t ∈ s ⁻¹ᵁ rV V i W := by
    change s.base t ∈ rV V i W
    rw [rV_eq]
    exact ⟨hi, ht⟩
  have hu : IsUnit (rr (s.preimage_mono (rV_le V i W)) (D.rigFun hcov χ hD x)) := by
    rw [rigFun_spec]
    exact (χ i).isUnit_χ _ _ _ (D.isBasisOn_coe hx i)
  have := hu.map (T.presheaf.germ _ t htU).hom
  rwa [rr, TopCat.Presheaf.germ_res_apply] at this

/-- The evaluation along `s` of the glued sheaf, if the transition maps are rigid. -/
def rig (D : GlueData V M) (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (_hM : ∀ i, IsInvOn (M i) (V i)) (χ : ∀ i, Rig s (M i) (V i))
    (hD : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (m : Γ(M i, W)),
      (χ j).χ W hj (D.ψ i j W hi hj m) = (χ i).χ W hi m) :
    Rig s D.glued ⊤ where
  χ W _ := AddMonoidHom.mk' (fun x ↦ D.rigFun hcov χ hD (x : D.sec W))
    (fun x y ↦ D.rigFun_add hcov χ hD x y)
  χ_smul _ _ c x := D.rigFun_smul hcov χ hD c x
  χ_rs _ _ _ h x := D.rigFun_rs hcov χ hD h x
  isUnit_χ _ _ _ hx := D.isUnit_rigFun hcov χ hD hx

end GlueData

lemma rs_unit_one {U W : Y.Opens} (h : W ≤ U) :
    rs (SheafOfModules.unit Y.ringCatSheaf) h (1 : Y.ringCatSheaf.obj.obj (op U)) =
      (1 : Y.ringCatSheaf.obj.obj (op W)) := by
  change Y.ringCatSheaf.obj.map (homOfLE h).op 1 = 1
  exact map_one _

/-- An invertible sheaf with an evaluation along `s` which is section-wise trivial on every
member of a saturated open cover is trivial. -/
theorem nonempty_iso_unit_of_rig (hsr : s ≫ r = 𝟙 T)
    (hΓ : ∀ U : T.Opens, Function.Surjective (r.app U)) (hV : ∀ i, r ⁻¹ᵁ (s ⁻¹ᵁ V i) = V i)
    (hcov : ∀ y : Y, ∃ i, y ∈ V i) (L : Y.Modules) [L.IsInvertible] (χ : Rig s L ⊤)
    (Φ : ∀ i, LocIso (SheafOfModules.unit Y.ringCatSheaf) L (V i)) :
    Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  let O := SheafOfModules.unit Y.ringCatSheaf
  have hO : ∀ W, IsInvOn O W := fun W ↦ isInvOn_of_isInvertible O W
  let Ψ : ∀ i, LocIso O L (V i) := fun i ↦
    (Φ i).rigidify hsr (hV i) (hO _) (Rig.unit s ⊤) χ le_top le_top
  have hΨ : ∀ i, (Ψ i).IsRigid (Rig.unit s ⊤) χ le_top le_top := fun i ↦
    LocIso.isRigid_rigidify _ _ _ _ _ _ _ _
  let e : ∀ i, Γ(L, V i) := fun i ↦ (Ψ i).φ (V i) le_rfl (1 : Y.ringCatSheaf.obj.obj (op (V i)))
  have key : ∀ i j, rs L (inf_le_left : V i ⊓ V j ≤ V i) (e i) = rs L inf_le_right (e j) := by
    intro i j
    have := LocIso.ext_of_isRigid hsr hΓ (sat_inf hV i j) (hO _)
      ((hΨ i).restrict inf_le_left) ((hΨ j).restrict inf_le_right) (V i ⊓ V j) le_rfl
      (1 : Y.ringCatSheaf.obj.obj (op (V i ⊓ V j)))
    simp only [LocIso.restrict_φ] at this
    change rs L _ ((Ψ i).φ (V i) le_rfl _) = rs L _ ((Ψ j).φ (V j) le_rfl _)
    rw [← (Ψ i).φ_rs, ← (Ψ j).φ_rs, rs_unit_one, rs_unit_one]
    exact this
  choose idx hidx using hcov
  obtain ⟨g, hg⟩ := CurvesJacobian.sheaf_exists_glue (GlueData.sh L) (V := ⊤)
    (fun y ↦ V (idx y.1)) (fun _ ↦ le_top) (fun y ↦ hidx y.1) (fun y ↦ e (idx y.1))
    (fun y z ↦ key _ _)
  have hg' : ∀ y : (⊤ : Y.Opens), rs L (le_top : V (idx y.1) ≤ ⊤) g = e (idx y.1) := hg
  have : IsIso (homOfSection g) := by
    refine Scheme.Modules.isIso_of_isBasisOn _ fun y ↦
      ⟨V (idx y), (1 : Y.ringCatSheaf.obj.obj (op (V (idx y)))), hidx y,
        Scheme.PresheafOfModules.isBasisOn_unit _, ?_⟩
    have he : (homOfSection g).app (V (idx y))
        (1 : Y.ringCatSheaf.obj.obj (op (V (idx y)))) = e (idx y) := by
      rw [homOfSection_app, one_smul]
      exact hg' ⟨y, trivial⟩
    rw [he]
    exact (Ψ _).isBasisOn_φ le_rfl (Scheme.PresheafOfModules.isBasisOn_unit _)
  exact ⟨(asIso (homOfSection g)).symm⟩

end CurvesJacobian.ModulesGlue
