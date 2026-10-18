/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicFOpen
import CurvesJacobian.Picard.TranslateRep

/-!
# The open subfunctor `F ⊆ Pic_{X/k,σ}` (Stacks, Lemma 44.6.2, Tag 0B9V)

Let `C` be a curve over a perfect field `k` with a rational point `σ` and a finite map
`π : C → ℙ¹_k`. For a scheme `T` and `x ∈ Pic_{C/k,σ}(T)` (`picSigmaSch`), `CurvesJacobian.picF`
says that for every affine `T'` and `T' ⟶ T` the pullback of `x` satisfies the `F`-condition
(`FCond`: Čech `H¹ = 0` and Čech `H⁰` an invertible `Γ(T')`-module for the chart covering of
`C ×_k T'`, i.e. `Rf_{T'*}L` is an invertible module placed in degree `0`).

* `CurvesJacobian.isLocalPredicate_picF`: `picF` is a Zariski-local predicate;
* `CurvesJacobian.picF_open`: the subfunctor `F` is open in `Pic_{C/k,σ}` when tested on affine
  schemes — exactly the hypotheses `hp`, `hopen` of `isRepresentable_of_translate`
  (Stacks, Lemma 44.5.1, Tag 0B9Q).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (σ : Spec (CommRingCat.of k) ⟶ C) (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 _)
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- The `F`-condition for a point of `Pic_{C/k,σ}` over `T`, on its representative. -/
def fPoint {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) : Prop :=
  FCond π x.1 (Scheme.Pic.rep (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1).1)

/-- **The subfunctor `F ⊆ Pic_{C/k,σ}`** (Stacks, Lemma 44.6.2, Tag 0B9V): `x ∈ F(T)` iff every
pullback of `x` to an affine scheme satisfies the `F`-condition. -/
def picF (T : Scheme.{u}) (x : (sigmaG G).obj (op T)) : Prop :=
  ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T), fPoint σ hσ π ((sigmaG G).map h.op x)

lemma fPoint_map_iff {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ Sk)
    (y : picSigmaGrp (C ↘ Sk) σ hσ g) :
    fPoint σ hσ π ((sigmaG G).map h.op ⟨g, y⟩) ↔
      FCond π (h ≫ g) ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h g (h ≫ g) rfl)).obj
        (Scheme.Pic.rep y.1)) := by
  change FCond π (h ≫ g) (Scheme.Pic.rep (Scheme.Pic.map (bcMap (C ↘ Sk) h g (h ≫ g) rfl)
    y.1)) ↔ _
  exact fCond_congr π _ (Scheme.Pic.rep_mk _).some

lemma map_map_sigmaG {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (h' : T'' ⟶ T')
    (x : (sigmaG G).obj (op T)) :
    (sigmaG G).map h'.op ((sigmaG G).map h.op x) = (sigmaG G).map (h' ≫ h).op x := by
  rw [op_comp, Functor.map_comp_apply]

variable [PerfectField k] [IsCurveOver k C] [IsFinite π]

/-- **Openness of `F` on affine schemes, pointwise form.** -/
theorem exists_opens_fPoint {T : Scheme.{u}} [IsAffine T] (x : (sigmaG G).obj (op T)) :
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
      fPoint σ hσ π ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U := by
  obtain ⟨g, y⟩ := x
  letI : T.Over Sk := ⟨g⟩
  haveI : Scheme.Modules.IsInvertible (X := pullback (C ↘ Sk) (T ↘ Sk))
      (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) :=
    inferInstanceAs (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1).IsInvertible
  obtain ⟨U, hU⟩ := exists_opens_fCond (T := T) π
    (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1)
  exact ⟨U, fun T' _ h ↦ (fPoint_map_iff σ hσ π h g y).trans (hU T' h)⟩

/-- **`F ⊆ Pic_{C/k,σ}` is open** (Stacks, Lemma 44.6.2, Tag 0B9V), tested on affine schemes. -/
theorem picF_open (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)) :
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
      picF σ hσ π T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U := by
  obtain ⟨U, hU⟩ := exists_opens_fPoint σ hσ π x
  refine ⟨U, fun T' _ h ↦ ⟨fun hF ↦ ?_, fun hr T'' _ h' ↦ ?_⟩⟩
  · have := hF T' (𝟙 T')
    rw [map_map_sigmaG, Category.id_comp] at this
    exact (hU T' h).mp this
  · rw [map_map_sigmaG]
    refine (hU T'' (h' ≫ h)).mpr ?_
    rintro _ ⟨t, rfl⟩
    exact hr ⟨h' t, rfl⟩

/-- **`F` is a Zariski-local predicate.** -/
theorem isLocalPredicate_picF (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G)) :
    Scheme.OpenSubfunctor.IsLocalPredicate (sheafG G hG) (picF σ hσ π) := by
  refine ⟨fun h x hx T'' _ h' ↦ ?_, fun x hx T'' _ h ↦ ?_⟩
  · change fPoint σ hσ π ((sigmaG G).map h'.op ((sigmaG G).map h.op x))
    rw [map_map_sigmaG]
    exact hx T'' (h' ≫ h)
  · obtain ⟨U'', hU''⟩ := exists_opens_fPoint σ hσ π ((sigmaG G).map h.op x)
    have htop : Set.range (𝟙 T'') ⊆ U'' := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨U, htU, hUx⟩ := hx (h s)
      obtain ⟨_, ⟨V₀, hV, rfl⟩, hsV, hVU⟩ := T''.isBasis_affineOpens.exists_subset_of_mem_open
        (show s ∈ h ⁻¹ᵁ U from htU) (h ⁻¹ᵁ U).2
      let V : T''.Opens := V₀
      haveI : IsAffine V := hV
      have hrange : Set.range (V.ι ≫ h) ⊆ Set.range U.ι := by
        rintro _ ⟨v, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hVU v.2
      let l := IsOpenImmersion.lift U.ι (V.ι ≫ h) hrange
      have hl : l ≫ U.ι = V.ι ≫ h := IsOpenImmersion.lift_fac _ _ _
      have h1 := hUx V l
      change fPoint σ hσ π ((sigmaG G).map l.op ((sigmaG G).map U.ι.op x)) at h1
      rw [map_map_sigmaG, hl, ← map_map_sigmaG] at h1
      have h2 := (hU'' V V.ι).mp h1
      exact h2 ⟨⟨s, hsV⟩, rfl⟩
    have := (hU'' T'' (𝟙 T'')).mpr htop
    rwa [op_id, Functor.map_id_apply] at this

end CurvesJacobian
