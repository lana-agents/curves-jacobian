/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierCurve

/-!
# The divisor of a section

Let `C` be a curve over a perfect field `k`, `T` a `k`-scheme and `s : T → X_T = C ×_k T` a
section of the projection `X_T → T`. Since `X_T → T` is separated, `s` is a closed immersion;
its image (the closed subscheme cut out by `ker s`) maps isomorphically to `T`, so it is finite
locally free of rank `1` over `T`, hence (Stacks, Lemma 44.3.1, Tag 0B9D, "(1) ⇒ (2)",
`RelEffCartier.ofFiniteFlat`) a relative effective Cartier divisor of degree `1`
(`RelEffCartier.ofSection`, `RelEffCartier.degree_ofSection`).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  {T : Scheme.{u}} (gT : T ⟶ Spec (CommRingCat.of k))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) gT
local notation "fT" => pullback.snd (C ↘ Sk) gT

section Section

/-- A section of `X_T → T` is a closed immersion. -/
lemma isClosedImmersion_of_section [IsSeparated (C ↘ Sk)] (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) :
    IsClosedImmersion s := by
  haveI : IsClosedImmersion (s ≫ fT) := by rw [hs]; infer_instance
  haveI : IsSeparated (fT) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  exact IsClosedImmersion.of_comp s (fT)

/-- The image of a section maps isomorphically to `T`. -/
lemma isIso_kerSubschemeι_comp [IsSeparated (C ↘ Sk)] (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) :
    IsIso (s.ker.subschemeι ≫ fT) := by
  haveI := isClosedImmersion_of_section C gT s hs
  have e : s.ker.subschemeι = inv s.toImage ≫ s := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc, hs, Category.comp_id]
  infer_instance

end Section

variable [PerfectField k] [Belyi.IsCurveOver k C]

/-- The relative effective Cartier divisor of a section `s : T → C ×_k T` of the projection: the
image of `s` (Stacks, Lemma 44.3.1, Tag 0B9D, "(1) ⇒ (2)", applied to the closed subscheme
`s(T) ≅ T`). -/
def RelEffCartier.ofSection (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) : RelEffCartier (fT) :=
  haveI := isIso_kerSubschemeι_comp C gT s hs
  RelEffCartier.ofFiniteFlat C gT s.ker

@[simp]
lemma RelEffCartier.ofSection_ideal (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) :
    (RelEffCartier.ofSection C gT s hs).ideal = s.ker := rfl

/-- The divisor of a section has degree `1` everywhere. -/
lemma RelEffCartier.degree_ofSection (s : T ⟶ XT) (hs : s ≫ fT = 𝟙 T) :
    (RelEffCartier.ofSection C gT s hs).degree = 1 := by
  haveI := isIso_kerSubschemeι_comp C gT s hs
  exact Scheme.Hom.finrank_eq_one_of_isIso (s.ker.subschemeι ≫ fT)

end CurvesJacobian
