/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDegScheme
import CurvesJacobian.Picard.HilbLft

/-!
# The Picard scheme is locally of finite presentation over `k`

Let `k` be a separably closed perfect field and `C` a curve over `k` with a rational point `σ`.
We show that the Picard scheme `Pic_{C/k,σ}` (`picSchX`, `picScheme`) is locally of finite
type, hence locally of finite presentation, over `k`
(`CurvesJacobian.locallyOfFinitePresentation_picScheme`), and so are the open subschemes
`Pic^d` (`locallyOfFinitePresentation_picDegScheme`). This is part of Stacks, Lemma 44.6.7
(Tag 0BA0), which says that `Pic^d` is smooth and proper of dimension `g`.

Proof: as in the proof of representability (Stacks, Lemma 44.5.1, Tag 0B9Q), `Pic` is covered by
the translates `F_c = {x | c + x ∈ F}` of the open subfunctor `F` of Stacks, Lemma 44.6.4
(Tag 0B9X); each `F_c` is represented by the open subscheme `W ⊆ Hilb^g_{C/k}`, and by
`OpenSubfunctor.exists_iso_opens` the open subscheme of `Pic` representing `F_c` is isomorphic
to `W` over `k` (`exists_opens_iso_of_translate`, generic). Finally `Hilb^g_{C/k}` is locally of
finite type over `k` (`locallyOfFiniteType_hilbCurveHom`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

section Generic

variable {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})

open Scheme.OpenSubfunctor in
/-- In the situation of Stacks, Lemma 44.5.1 (Tag 0B9Q, `isRepresentable_of_translate`), let
`ξX ∈ G(X)` represent `G`. Then every point of `X` has an open neighbourhood `O` isomorphic to
`Y` (the representing scheme of `F`), compatibly with the structure morphisms to `S`. -/
theorem exists_opens_iso_of_translate
    (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    {p : ∀ T : Scheme.{u}, (sigmaG G).obj (op T) → Prop}
    (hp : IsLocalPredicate (sheafG G hG) p)
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U)
    {Y : Scheme.{u}} (ξ : (sigmaG G).obj (op Y))
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ (sigmaG G).map a.op ξ)
    (hrange : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)),
      p T x ↔ ∃ a : T ⟶ Y, (sigmaG G).map a.op ξ = x)
    (hfield : ∀ (K : CommRingCat.{u}), IsField K → ∀ x : (sigmaG G).obj (op (Spec K)),
      ∃ c : G.obj (op (Over.mk (𝟙 S))), p _ (translate G c x))
    {X : Scheme.{u}} (ξX : (sigmaG G).obj (op X))
    (hX : ∀ T : Scheme.{u}, Function.Bijective fun a : T ⟶ X ↦ (sigmaG G).map a.op ξX)
    (z : X) :
    ∃ (O : X.Opens) (e : O.toScheme ≅ Y), z ∈ O ∧ O.ι ≫ ξX.1 = e.hom ≫ ξ.1 := by
  let K := X.residueField z
  have hK : IsField K := Field.toIsField _
  obtain ⟨c, hc⟩ := hfield K hK ((sigmaG G).map (X.fromSpecResidueField z).op ξX)
  have hpc : IsLocalPredicate (sheafG G hG) (fun T x ↦ p T (translate G c x)) :=
    ⟨fun h x hx ↦ by
      change p _ (translate G c ((sigmaG G).map h.op x))
      rw [← map_translate]
      exact hp.map h _ hx, fun x hx ↦ by
      refine hp.of_forall _ fun t ↦ ?_
      obtain ⟨U, htU, hU⟩ := hx t
      refine ⟨U, htU, ?_⟩
      change p _ ((sigmaG G).map U.ι.op (translate G c x))
      rw [map_translate]
      exact hU⟩
  obtain ⟨O, e, hO, he⟩ := exists_iso_opens (F := sheafG G hG) hpc
    (fun T _ x ↦ by
      obtain ⟨U, hU⟩ := hopen T (translate G c x)
      exact ⟨U, fun T' _ h ↦ by
        change p T' (translate G c ((sigmaG G).map h.op x)) ↔ _
        rw [← map_translate]
        exact hU T' h⟩)
    ξX (fun T ↦ (hX T).1) (fun T x ↦ (hX T).2 x) (translate G (-c) ξ)
    (fun T _ a b hab ↦ by
      refine hinj T ?_
      change (sigmaG G).map a.op (translate G (-c) ξ) =
        (sigmaG G).map b.op (translate G (-c) ξ) at hab
      rw [map_translate, map_translate] at hab
      exact translate_injective G (-c) T hab)
    (fun T _ x ↦ by
      change p T (translate G c x) ↔ ∃ a : T ⟶ Y, (sigmaG G).map a.op (translate G (-c) ξ) = x
      rw [hrange]
      simp only [map_translate, translate_neg_eq_iff])
  refine ⟨O, e, ?_, ?_⟩
  · have := (hO (Spec K) (X.fromSpecResidueField z)).1 hc
    rw [Scheme.range_fromSpecResidueField] at this
    exact this rfl
  · have := congrArg Sigma.fst he
    exact this.symm

end Generic

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [Belyi.IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

omit [IsSepClosed k] in
lemma xiHilb_fst : (xiHilb C σ hσ).1 = hilbCurveHom k C (genusNat k C) := by
  have h := map_xiHilb C σ hσ (𝟙 _)
  rw [op_id, Functor.map_id_apply] at h
  rw [h, abelMap_app, hilbCurveEquiv_fst, Category.id_comp]

/-- **The Picard scheme is locally of finite type over `k`.** -/
theorem locallyOfFiniteType_picScheme :
    LocallyOfFiniteType (OverSigmaRep.base (picSchRepr C σ hσ)) := by
  haveI : IsAlgClosed k := IsSepClosed.isAlgClosed_of_perfectField k
  obtain ⟨π₀, hπ⟩ := IsCurveOver.exists_finite_to_P1 k C
  let π : C ⟶ ProjectiveLine.scheme k := π₀
  haveI : IsFinite π := hπ
  have hG := isSheaf_picSigmaSch_curve k C σ hσ
  have hX (T : Scheme.{u}) : Function.Bijective fun a : T ⟶ picSchX C σ hσ ↦
      (sigmaG G).map a.op (picUniv C σ hσ) := by
    have : (fun a : T ⟶ picSchX C σ hσ ↦ (sigmaG G).map a.op (picUniv C σ hσ)) =
        (picSchRepr C σ hσ).homEquiv :=
      funext fun a ↦ (OverSigmaRep.homEquiv_eq (picSchRepr C σ hσ) a).symm
    rw [this]
    exact (picSchRepr C σ hσ).homEquiv.bijective
  have key (z : picSchX C σ hσ) : ∃ O : (picSchX C σ hσ).Opens, z ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ OverSigmaRep.base (picSchRepr C σ hσ)) := by
    obtain ⟨O, e, hz, he⟩ := exists_opens_iso_of_translate G hG
      (isLocalPredicate_picF σ hσ π hG) (picF_open σ hσ π) (xiW C σ hσ π hG)
      (injective_xiW C σ hσ π hG) (picF_iff_exists_xiW C σ hσ π hG)
      (exists_picF_translate C π σ hσ) (picUniv C σ hσ) hX z
    refine ⟨O, hz, ?_⟩
    have hW : (xiW C σ hσ π hG).1 = (opensW C σ hσ π hG).ι ≫ hilbCurveHom k C (genusNat k C) := by
      change (opensW C σ hσ π hG).ι ≫ (xiHilb C σ hσ).1 = _
      rw [xiHilb_fst]
    change O.ι ≫ (picUniv C σ hσ).1 = _ at he
    haveI := locallyOfFiniteType_hilbCurveHom k C (genusNat k C)
    change LocallyOfFiniteType (O.ι ≫ (picUniv C σ hσ).1)
    rw [he, hW]
    infer_instance
  choose O hzO hO using key
  exact IsZariskiLocalAtSource.of_iSup_eq_top O
    (top_unique fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzO z⟩) hO

/-- **The Picard scheme is locally of finite presentation over `k`** (part of Stacks,
Lemma 44.6.7, Tag 0BA0). -/
instance locallyOfFinitePresentation_picScheme :
    LocallyOfFinitePresentation (picScheme C σ hσ).hom := by
  haveI := locallyOfFiniteType_picScheme C σ hσ
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    (inferInstanceAs (LocallyOfFiniteType (OverSigmaRep.base (picSchRepr C σ hσ))))

/-- **`Pic^d_{C/k,σ}` is locally of finite presentation over `k`.** -/
instance locallyOfFinitePresentation_picDegScheme (π : C ⟶ ProjectiveLine.scheme k)
    [IsFinite π] (d : ℤ) : LocallyOfFinitePresentation (picDegScheme C σ hσ π d).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    ((picDegOpens C σ hσ π d).ι ≫ (picScheme C σ hσ).hom))

end CurvesJacobian
