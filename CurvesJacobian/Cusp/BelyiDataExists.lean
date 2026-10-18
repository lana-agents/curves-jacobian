/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiArithSpec
import CurvesJacobian.Cusp.FillSeq
import CurvesJacobian.Cusp.HypBaseChange
import CurvesJacobian.Cusp.P1Curve
import Belyi.Anabelian.BelyiInputNumberField

/-!
# Existence of Belyi data for curves of strictly Belyi type (MR8.5)

[AbsTopII] Definition 3.5 (`Topics in Absolute Anabelian Geometry II.txt` l.4615–4617): "We shall
say that `X` is of *strictly Belyi type* if it is defined over a number field and isogenous [cf.
§0] to a hyperbolic curve of genus zero." Example 3.6 (ii) (l.4655–4680) then uses finite étale
coverings `V → X`, `V → Q` with an open immersion `Q → P` into a copy `P` of the projective line
minus three points, a nonempty open `U ⊆ V` descending to the given `U_X ⊆ X`, and a Belyi map
`β : W → P` with `W ⊆ U` (Example 3.6 (i), l.4628–4636).

`StrictlyBelyiInput CX M` is the input of Example 3.6 (ii) for an affine hyperbolic curve
`CX = (X̄, X)` over a number field `K`: over a number field `M ⊇ K`, a hyperbolic curve `V` with a
cusp, finite étale `V ⟶ X` (over `Spec M ⟶ Spec K`) and finite étale `V ⟶ Q` onto an open
`Q ⊆ ℙ¹_M ∖ {0, 1, ∞}`. (This is Definition 3.5 after replacing the number field by a finite
extension over which the genus-zero curve becomes an open of `ℙ¹` and three of its cusps become
`0, 1, ∞`.)

**Main theorem** (`CurvesJacobian.Cusp.exists_belyiData`): for every nonempty open `U_X ⊆ X`
there are a finite extension `M'` of `M` inside `Ω`, Belyi data `D : BelyiData CX` over `M'`
and an index `j ≤ D.r` such that the `j`-th open of the run of fillings `W ⊆ … ⊆ V_{M'}` is
`U = V_{M'} ×_X U_X` (`D.UW j = V_{M'} ∩ FV⁻¹(U_X)`). With `belyiCandidate_spec` (`m = r - j`)
the corresponding candidate of the Belyi chain is `Π_U ↠ Π_V ↪ Π_X` ([AbsTopII] Cor 3.7 (a)).

Construction: `U₀ = V ×_X U_X ⊆ V`; belyi's `exists_belyi_open_le_finSub` gives a finite extension
`M'` and a finite `f : V̄_{M'} ⟶ ℙ¹_{M'}` with `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞}) ⊆ (U₀)_{M'}` and
`f|_W` finite étale; `CW = (V̄_{M'}, W)`, `CQ = (ℙ¹_{M'}, Q_{M'})`, runs of fillings
`W ⊆ … ⊆ (U₀)_{M'} ⊆ … ⊆ V_{M'}` and `Q_{M'} ⊆ … ⊆ ℙ¹ ∖ {0, 1, ∞}` (`exists_fillSeq`), the maps
`V_{M'} ⟶ V ⟶ X`, `V_{M'} ⟶ Q_{M'}` (base change of `V ⟶ Q`) and `β = f|_W`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian IntermediateField

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

/-- **Input of [AbsTopII] Example 3.6 (ii)** (Definition 3.5, *strictly Belyi type*, normalised)
for an affine hyperbolic curve `CX` over `K`: over a number field `M ⊇ K`, a hyperbolic curve
`CV = (V̄, V)` with a cusp, a finite étale `FV : V ⟶ X` over `Spec M ⟶ Spec K` and a finite étale
`FQ : V ⟶ Q` over `M` onto an open `Q ⊆ ℙ¹_M ∖ {0, 1, ∞}`. -/
structure StrictlyBelyiInput (CX : HypCurve K) (M : Type u) [Field M] [NumberField M]
    [Algebra K M] where
  /-- The curve `(V̄, V)`. -/
  CV : HypCurve M
  hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty
  /-- `V ⟶ X`. -/
  FV : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U)
  [finFV : IsFiniteEtale FV]
  hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K M))
  /-- The genus-zero curve `Q ⊆ ℙ¹ ∖ {0, 1, ∞}`. -/
  Q : (P1 M).Opens
  hQ : Q ≤ puncturedLine M
  hQne : (Q : Set (P1 M)).Nonempty
  /-- `V ⟶ Q`. -/
  FQ : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(P1 M, Q)
  [finFQ : IsFiniteEtale FQ]
  hFQ : FQ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(P1 M, Q))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U)))

attribute [instance] StrictlyBelyiInput.finFV StrictlyBelyiInput.finFQ

section FinSub

variable (Ω : Type u) [Field Ω] [Algebra M Ω]

instance numberField_finSub' (M' : FinSub M Ω) : NumberField M'.1 :=
  haveI := M'.2
  haveI : CharZero M'.1 := charZero_of_injective_algebraMap (algebraMap M M'.1).injective
  { to_finiteDimensional := Module.Finite.trans M M'.1 }

end FinSub

/-! ### Topological lemmas -/

section Topology

variable {X : Scheme.{u}}

/-- Nonemptiness of the complement passes to smaller opens. -/
lemma compl_nonempty_of_le {U U' : X.Opens} (h : U ≤ U') (hc : (U' : Set X)ᶜ.Nonempty) :
    (U : Set X)ᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := hc
  exact ⟨x, fun hx' ↦ hx (h hx')⟩

/-- Finiteness of the complement passes to larger opens. -/
lemma compl_finite_of_le {U U' : X.Opens} (h : U ≤ U') (hf : (U : Set X)ᶜ.Finite) :
    (U' : Set X)ᶜ.Finite :=
  hf.subset fun _ hx hx' ↦ hx (h hx')

/-- A finite étale morphism to a connected scheme from a nonempty scheme is surjective. -/
lemma surjective_of_isFiniteEtale {Y : Scheme.{u}} (g : Y ⟶ X) [IsFiniteEtale g]
    [ConnectedSpace X] [Nonempty Y] : Function.Surjective g := by
  have ho : IsOpen (Set.range g) := g.isOpenMap.isOpen_range
  have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
  exact Set.range_eq_univ.mp (IsClopen.eq_univ ⟨hc, ho⟩ (Set.range_nonempty g))

end Topology

/-! ### Hyperbolicity along runs of fillings -/

section Hyp

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- If `2 < 2g + r(U)` and `U' ⊆ U` has finite complement, then `2 < 2g + r(U')`. -/
lemma hyp_of_le {U U' : X.Opens} (h : U' ≤ U) (hf : (U' : Set X)ᶜ.Finite) {g : ℕ}
    (hyp : 2 < 2 * g + Anabelian.cuspDegree k X U) :
    2 < 2 * g + Anabelian.cuspDegree k X U' :=
  lt_of_lt_of_le hyp (Nat.add_le_add_left (cuspDegree_anti h hf) _)

end Hyp

/-! ### The construction -/

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic M Ω] {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)
  (S : StrictlyBelyiInput CX M)

namespace StrictlyBelyiInput

omit [NumberField K] in
lemma isAffineOpen_V : IsAffineOpen S.CV.U := isAffineOpen_U S.CV S.hcV

/-- `U₀ = V ×_X U_X` as an open of `V̄`. -/
def U₀ (UX : CX.Xbar.Opens) : S.CV.Xbar.Opens :=
  (S.isAffineOpen_V).fromSpec ''ᵁ (S.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX))

lemma U₀_le (UX : CX.Xbar.Opens) : S.U₀ hcX UX ≤ S.CV.U := by
  rintro _ ⟨x, -, rfl⟩
  change _ ∈ (S.CV.U : Set S.CV.Xbar)
  rw [← (S.isAffineOpen_V).range_fromSpec]
  exact ⟨x, rfl⟩

lemma U₀_nonempty (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ((S.U₀ hcX UX : S.CV.Xbar.Opens) : Set S.CV.Xbar).Nonempty := by
  haveI := isIntegral_specSections CX hcX
  haveI := isIntegral_specSections S.CV S.hcV
  obtain ⟨x, hx⟩ := hUXne
  have hx' : x ∈ Set.range (isAffineOpen_U CX hcX).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]; exact hUX hx
  obtain ⟨t, rfl⟩ := hx'
  obtain ⟨s, rfl⟩ := surjective_of_isFiniteEtale S.FV t
  exact ⟨_, ⟨s, hx, rfl⟩⟩

end StrictlyBelyiInput

/-- `Spec.map (algebraMap R R) = 𝟙`. -/
lemma specMap_algebraMap_self (R : Type u) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- `Spec` of `g.appLE` is compatible with the structure maps of schemes over `Spec R`. -/
lemma specMap_appLE_algebraMap {X Y : Scheme.{u}} (g : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [g.IsOver (Spec (.of R))] (U : Y.Opens)
    (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) :
    Spec.map (g.appLE U V h) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (FiniteEtale.appLE_comp_algebraMap g R U V h)

/-- The complement of an open with positive cusp degree is nonempty. -/
lemma compl_nonempty_of_cuspDegree_pos {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {U : X.Opens} (h : 0 < Anabelian.cuspDegree k X U) :
    (U : Set X)ᶜ.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  rw [Anabelian.cuspDegree, he, finsum_mem_empty] at h
  exact lt_irrefl 0 h

include S in
/-- **Existence of Belyi data** ([AbsTopII] Example 3.6, Corollary 3.7 (a)): for an affine
hyperbolic curve `CX` over a number field `K` of strictly Belyi type (`S`) and a nonempty open
`U_X ⊆ X`, there are a finite extension `M'` of `M` in `Ω`, Belyi data `D` over `M'` and `j ≤ r`
such that the `j`-th open of the run of fillings `W ⊆ … ⊆ V` is `V ×_X U_X`, i.e. the preimage of
`U_X` under `V ≅ Spec Γ(V) ⟶ Spec Γ(X) ≅ X` (`FV`). -/
theorem exists_belyiData (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) CX) (j : ℕ) (hj : j ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨j, Nat.lt_succ_of_le hj⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) := by
  classical
  obtain ⟨M', f, hfo, -, hWU, hWne, hfinP, hetP⟩ :=
    exists_belyi_open_le_finSub M Ω S.CV.Xbar (S.U₀ hcX UX) (S.U₀_nonempty hcX UX hUX hUXne)
  haveI := M'.2
  -- the curve `V̄_L` and its opens
  set Xw := bcX M M'.1 S.CV.Xbar with hXw
  set π := bcπ M M'.1 S.CV.Xbar with hπ
  have hπs : Function.Surjective π := surjective_bcπ M M'.1 S.CV.Xbar
  set W : Xw.Opens := f ⁻¹ᵁ puncturedLine M'.1 with hWdef
  set Vb : Xw.Opens := π ⁻¹ᵁ S.CV.U with hVb
  set Ub : Xw.Opens := π ⁻¹ᵁ S.U₀ hcX UX with hUb
  have hWUb : W ≤ Ub := hWU
  have hUbVb : Ub ≤ Vb := fun x hx ↦ S.U₀_le hcX UX hx
  have hWfin : (W : Set Xw)ᶜ.Finite := finite_compl_of_isCurveOver (k := M'.1) Xw W hWne
  have hcVb : (Vb : Set Xw)ᶜ.Nonempty := by
    obtain ⟨c, hc⟩ := S.hcV
    obtain ⟨x, rfl⟩ := hπs c
    exact ⟨x, hc⟩
  haveI := IsCurveOver.isIntegral M S.CV.Xbar
  haveI := IsCurveOver.isIntegral M'.1 Xw
  have hypVb : 2 < 2 * Anabelian.curveGenus M'.1 Xw + Anabelian.cuspDegree M'.1 Xw Vb :=
    lt_of_lt_of_le S.CV.hyperbolic (Nat.add_le_add (Nat.mul_le_mul_left 2
      (curveGenus_le_bc M M'.1 S.CV.Xbar)) (cuspDegree_le_bc M M'.1 S.CV.Xbar S.CV.U S.CV.nonempty))
  have hypW : ∀ U' : Xw.Opens, W ≤ U' → U' ≤ Vb →
      2 < 2 * Anabelian.curveGenus M'.1 Xw + Anabelian.cuspDegree M'.1 Xw U' := fun U' h₁ h₂ ↦
    hyp_of_le h₂ (compl_finite_of_le h₁ hWfin) hypVb
  -- the run of fillings `W ⊆ … ⊆ U_b ⊆ … ⊆ V_b`
  obtain ⟨r, j, hj, UW, xW, hW0, hWlast, hWmid, hleW, hleWV, hmonoW, hxW1, hxW2, hxW3⟩ :=
    exists_fillSeq W Ub Vb hWUb hUbVb (hWfin.subset fun _ hx ↦ hx.2)
      (fun _ hx ↦ isClosed_singleton_of_not_mem (k := M'.1) Xw W hWne hx.2)
  let CW : HypCurve M'.1 :=
    { Xbar := Xw, U := W, nonempty := hWne, cusps_finite := hWfin
      hyperbolic := hypW W le_rfl (hWUb.trans hUbVb) }
  -- the line `ℙ¹_L` and its opens
  set Pm := P1.mapOfAlgebra M M'.1 with hPm
  have hPsq := P1.isPullback_mapOfAlgebra M M'.1
  haveI : Surjective Pm := MorphismProperty.of_isPullback (P := @Surjective) hPsq.flip
    inferInstance
  set Q' : (P1 M'.1).Opens := Pm ⁻¹ᵁ S.Q with hQ'
  have hpre : Pm ⁻¹ᵁ puncturedLine M = puncturedLine M'.1 := by
    rw [← opensRange_puncturedι, ← opensRange_puncturedι]
    exact mapOfAlgebra_preimage_opensRange_puncturedι M M'.1
  have hQ'P : Q' ≤ puncturedLine M'.1 := by
    rw [← hpre]; exact fun x hx ↦ S.hQ hx
  have hQ'ne : (Q' : Set (P1 M'.1)).Nonempty := by
    obtain ⟨q, hq⟩ := S.hQne
    obtain ⟨x, rfl⟩ := Pm.surjective q
    exact ⟨x, hq⟩
  have hQ'fin : (Q' : Set (P1 M'.1))ᶜ.Finite :=
    finite_compl_of_isCurveOver (k := M'.1) (P1 M'.1) Q' hQ'ne
  have h3 := three_le_cuspDegree_puncturedLine M'.1
  have hcP : (puncturedLine M'.1 : Set (P1 M'.1))ᶜ.Nonempty :=
    compl_nonempty_of_cuspDegree_pos (k := M'.1) (by omega)
  have hypQ : ∀ U' : (P1 M'.1).Opens, Q' ≤ U' → U' ≤ puncturedLine M'.1 →
      2 < 2 * Anabelian.curveGenus M'.1 (P1 M'.1) + Anabelian.cuspDegree M'.1 (P1 M'.1) U' :=
    fun U' h₁ h₂ ↦ hyp_of_le (k := M'.1) h₂ (compl_finite_of_le h₁ hQ'fin) (by omega)
  obtain ⟨l, j', hj', UQ, xQ, hQ0, hQlast, -, hleQ, hleQP, hmonoQ, hxQ1, hxQ2, hxQ3⟩ :=
    exists_fillSeq Q' (puncturedLine M'.1) (puncturedLine M'.1) hQ'P le_rfl
      (hQ'fin.subset fun _ hx ↦ hx.2)
      (fun _ hx ↦ isClosed_singleton_of_not_mem (k := M'.1) (P1 M'.1) Q' hQ'ne hx.2)
  let CQ : HypCurve M'.1 :=
    { Xbar := P1 M'.1, U := Q', nonempty := hQ'ne, cusps_finite := hQ'fin
      hyperbolic := hypQ Q' le_rfl hQ'P }
  -- the maps
  have hsqV := isPullback_bcπ M M'.1 S.CV.Xbar
  have hQaff : IsAffineOpen S.Q :=
    isAffineOpen_of_isCurveOver (k := M) (P1 M) S.Q S.hQne
      (finite_compl_of_isCurveOver (k := M) (P1 M) S.Q S.hQne)
      (compl_nonempty_of_le S.hQ (compl_nonempty_of_cuspDegree_pos (k := M)
        (by have := three_le_cuspDegree_puncturedLine M; omega)))
  have hsqVΓ := isPullback_specΓ π hsqV hWlast S.isAffineOpen_V
  have hsqQΓ := isPullback_specΓ Pm hPsq (V := Q') rfl hQaff
  set aV := Spec.map (π.appLE S.CV.U (UW (Fin.last r)) hWlast.le) with haV
  set aQ := Spec.map (Pm.appLE S.Q Q' le_rfl) with haQ
  haveI : IsFiniteEtale aV := isFiniteEtale_specΓ π hsqV hWlast S.isAffineOpen_V
  have hwV : (aV ≫ S.FQ) ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(P1 M, S.Q))) =
      Spec.map (CommRingCat.ofHom (algebraMap M'.1 Γ(Xw, UW (Fin.last r)))) ≫
        specAlgebraMap M M'.1 := by
    rw [Category.assoc, S.hFQ]; exact hsqVΓ.w
  let FQ' := hsqQΓ.lift (aV ≫ S.FQ) _ hwV
  have htop : IsPullback aV FQ' S.FQ aQ := by
    refine IsPullback.of_bot ?_ (hsqQΓ.lift_fst _ _ hwV).symm hsqQΓ
    convert hsqVΓ using 1
    · exact hsqQΓ.lift_snd _ _ hwV
    · exact S.hFQ
  haveI : IsFiniteEtale FQ' := MorphismProperty.of_isPullback (P := @IsFiniteEtale) htop
    inferInstance
  have hβeq : W = f ⁻¹ᵁ UQ (Fin.last l) := by rw [hQlast]
  have hβle : W ≤ f ⁻¹ᵁ UQ (Fin.last l) := hβeq.le
  have hPaff : IsAffineOpen (UQ (Fin.last l)) := by
    rw [hQlast]
    exact isAffineOpen_of_isCurveOver (k := M'.1) (P1 M'.1) _ (hQ'ne.mono hQ'P)
      (compl_finite_of_le hQ'P hQ'fin) hcP
  have hWaff : IsAffineOpen W :=
    isAffineOpen_of_isCurveOver (k := M'.1) Xw W hWne hWfin
      (compl_nonempty_of_le (hWUb.trans hUbVb) hcVb)
  haveI : IsFinite (f ∣_ UQ (Fin.last l)) := by rw [hQlast]; exact hfinP
  haveI : Etale (f ∣_ UQ (Fin.last l)) := by rw [hQlast]; exact hetP
  haveI : IsFiniteEtale (Spec.map (f.appLE (UQ (Fin.last l)) W hβle)) :=
    isFiniteEtale_specMap_appLE f _ W hβeq hPaff hWaff
  haveI : f.IsOver (Spec (.of M'.1)) := ⟨hfo⟩
  let D : BelyiData (M := M'.1) CX :=
    { CQ := CQ, hcQ := compl_nonempty_of_le hQ'P hcP, l := l, UQ := UQ, hUQ0 := hQ0
      hleQ := hleQ, hmonoQ := hmonoQ
      hcUQ := fun i ↦ compl_nonempty_of_le (hleQP i) hcP
      hypQ := fun i ↦ hypQ _ (hleQ i) (hleQP i)
      xQ := xQ, hxUQ := hxQ1, hxUQ' := hxQ2, hxQ := hxQ3
      CW := CW, hcW := compl_nonempty_of_le (hWUb.trans hUbVb) hcVb, r := r, UW := UW
      hUW0 := hW0, hleW := hleW, hmonoW := hmonoW
      hcUW := fun i ↦ compl_nonempty_of_le (hleWV i) hcVb
      hypW := fun i ↦ hypW _ (hleW i) (hleWV i)
      xW := xW, hxUW := hxW1, hxUW' := hxW2, hxW := hxW3
      FV := aV ≫ S.FV
      hFV := by
        rw [Category.assoc, S.hFV, ← Category.assoc, hsqVΓ.w, Category.assoc]
        exact congrArg _ (specAlgebraMap_comp_specAlgebraMap K M M'.1)
      FQ := FQ'
      hFQ := (hsqQΓ.lift_snd _ _ hwV).trans
        (by rw [specMap_algebraMap_self, Category.comp_id])
      β := Spec.map (f.appLE (UQ (Fin.last l)) W hβle)
      hβ := by
        rw [specMap_appLE_algebraMap f M'.1 _ W hβle, specMap_algebraMap_self, Category.comp_id] }
  have hVa : IsAffineOpen (D.UW (Fin.last D.r)) := by
    change IsAffineOpen (UW (Fin.last r))
    rw [hWlast]
    exact isAffineOpen_of_isPullback π hsqV rfl S.isAffineOpen_V
  refine ⟨M', D, j, hj, hVa, ?_⟩
  change UW _ = hVa.fromSpec ''ᵁ ((aV ≫ S.FV) ⁻¹ᵁ _)
  rw [hWmid]
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec π S.isAffineOpen_V hVa hWlast.le
  have e : ∀ t, S.isAffineOpen_V.fromSpec (aV t) = π (hVa.fromSpec t) := fun t ↦ by
    change (aV ≫ S.isAffineOpen_V.fromSpec) t = (hVa.fromSpec ≫ π) t
    rw [hcomm]
  have hrV : ∀ s, S.isAffineOpen_V.fromSpec s ∈ (S.CV.U : Set S.CV.Xbar) := fun s ↦
    S.isAffineOpen_V.range_fromSpec ▸ Set.mem_range_self s
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hxV : x ∈ (UW (Fin.last r) : Set Xw) := by
      rw [hWlast]
      change π x ∈ (S.CV.U : Set S.CV.Xbar)
      rw [← hsx]
      exact hrV s
    have hxV' : x ∈ Set.range hVa.fromSpec := by
      rw [hVa.range_fromSpec]; exact hxV
    obtain ⟨t, rfl⟩ := hxV'
    refine ⟨t, ?_, rfl⟩
    have ht : S.isAffineOpen_V.fromSpec (aV t) = S.isAffineOpen_V.fromSpec s :=
      (e t).trans hsx.symm
    have h2 : aV t = s := S.isAffineOpen_V.fromSpec.isOpenEmbedding.injective ht
    have h3 : (aV ≫ S.FV) t = S.FV s := by
      change S.FV (aV t) = S.FV s
      rw [h2]
    change (aV ≫ S.FV) t ∈ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX : Set _)
    rw [h3]
    exact hs
  · rintro ⟨t, ht, rfl⟩
    exact ⟨aV t, ht, e t⟩

end CurvesJacobian.Cusp
