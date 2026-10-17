/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierBaseChange
import CurvesJacobian.Picard.RelEffCartierFinite
import CurvesJacobian.Picard.FinrankFibre

/-!
# Degrees of relative effective Cartier divisors add

Stacks, Lemma 44.3.2 (Tag 0B9E): for `X → S` smooth of relative dimension `1` and closed
subschemes `D₁, D₂ ⊂ X` finite locally free over `S` of degrees `d₁, d₂`, the sum `D₁ + D₂` is
finite locally free over `S` of degree `d₁ + d₂`. Following the proof there, we base change to
the fibres and compute the degree as a sum of local contributions, where `D₁`, `D₂` are cut out
by nonzerodivisors `g`, `h` and `D₁ + D₂` by `gh`.

* `RelEffCartier.degree_add`: for relative effective Cartier divisors `D₁, D₂` on any `X/S`
  such that `D₁`, `D₂` and `D₁ + D₂` are finite over `S`,
  `(D₁ + D₂).degree s = D₁.degree s + D₂.degree s`.
* `CurvesJacobian.degree_add_curve`: the curve situation `C ×_k T → T` (`C` a curve over a
  perfect field `k`), where all relative effective Cartier divisors are finite over `T`.
* `RelEffCartier.baseChange_add`: base change commutes with the sum of divisors.
-/

open CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

open Scheme CurvesJacobian

namespace Scheme.IdealSheafData

variable {X X' : Scheme.{u}}

/-- Pulling back ideal sheaves commutes with products. -/
lemma comap_mul (I J : X.IdealSheafData) (φ : X' ⟶ X) :
    (I * J).comap φ = I.comap φ * J.comap φ := by
  let ι := {p : X.affineOpens × X'.affineOpens // p.2.1 ≤ φ ⁻¹ᵁ p.1.1}
  refine ext_of_iSup_eq_top (ι := ι) (fun p ↦ p.1.2) ?_ fun p ↦ ?_
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (Opens.mem_top (φ x))
    obtain ⟨W', hW', hxW', hW'W⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
      (show x ∈ φ ⁻¹ᵁ W from hxW)
    exact Opens.mem_iSup.mpr ⟨⟨(⟨W, hW⟩, ⟨W', hW'⟩), hW'W⟩, hxW'⟩
  · obtain ⟨⟨W, W'⟩, h⟩ := p
    change ((I * J).comap φ).ideal W' = (I.comap φ).ideal W' * (J.comap φ).ideal W'
    rw [ideal_comap_of_le _ φ W W' h, ideal_comap_of_le _ φ W W' h,
      ideal_comap_of_le _ φ W W' h, ideal_mul, Pi.mul_apply, Ideal.map_mul]

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The `Γ(S, ⊤)`-algebra structure on the stalk `𝒪_{X, x}` given by `f : X ⟶ S`. -/
abbrev stalkAlgebra (x : X) : Algebra Γ(S, ⊤) (X.presheaf.stalk x) :=
  (S.presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x).hom.toAlgebra

/-- The `Γ(S, ⊤)`-rank of `𝒪_{X, x} / I(U) 𝒪_{X, x}`, for an affine open `U ∋ x`. -/
def quotStalkRank (U : X.affineOpens) (x : X) (hx : x ∈ U.1) : ℕ :=
  letI := stalkAlgebra f x
  Module.finrank Γ(S, ⊤) (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hx).hom)

/-- The stalk of the closed subscheme `Z(I)` at `y` is `𝒪_{X, x} / I(U) 𝒪_{X, x}`, compatibly
with the algebra structures over `Γ(S, ⊤)`. -/
lemma exists_ringEquiv_stalk (U : X.affineOpens) (y : I.subscheme) (hy : I.subschemeι y ∈ U.1) :
    ∃ e : (X.presheaf.stalk (I.subschemeι y) ⧸
        (I.ideal U).map (X.presheaf.germ U (I.subschemeι y) hy).hom) ≃+*
        I.subscheme.presheaf.stalk y,
      ∀ k, e (Ideal.Quotient.mk _ ((S.presheaf.germ ⊤ (f (I.subschemeι y)) trivial ≫
        f.stalkMap (I.subschemeι y)) k)) =
        (S.presheaf.germ ⊤ ((I.subschemeι ≫ f) y) trivial ≫
          (I.subschemeι ≫ f).stalkMap y) k := by
  have hU' : IsAffineOpen (I.subschemeι ⁻¹ᵁ U.1) := U.2.preimage _
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨I.subschemeι y, hy⟩ : U.1)
  letI := TopCat.Presheaf.algebra_section_stalk I.subscheme.presheaf
    (⟨y, hy⟩ : (I.subschemeι ⁻¹ᵁ U.1 : I.subscheme.Opens))
  let P := U.2.primeIdealOf ⟨I.subschemeι y, hy⟩
  let Q := hU'.primeIdealOf ⟨y, hy⟩
  have : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (I.subschemeι y)) :=
    U.2.isLocalization_stalk ⟨I.subschemeι y, hy⟩
  have hQ : IsLocalization Q.asIdeal.primeCompl (I.subscheme.presheaf.stalk y) :=
    hU'.isLocalization_stalk ⟨y, hy⟩
  let g : Γ(X, U.1) →+* Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) := (I.subschemeι.app U).hom
  have hcomap : Q.asIdeal.comap g = P.asIdeal := by
    have := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := I.subschemeι) U.1 U.2 _ hU' le_rfl hy)
    rw [PrimeSpectrum.comap_asIdeal, ← Scheme.Hom.app_eq_appLE] at this
    exact this
  have hsurj : Function.Surjective g := I.subschemeι_app_surjective U
  have hT : P.asIdeal.primeCompl.map g = Q.asIdeal.primeCompl := by
    ext a
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact fun h ↦ hr (hcomap ▸ h)
    · intro ha
      obtain ⟨r, rfl⟩ := hsurj a
      exact ⟨r, fun h ↦ ha (by rw [← hcomap] at h; exact h), rfl⟩
  have : IsLocalization (P.asIdeal.primeCompl.map g) (I.subscheme.presheaf.stalk y) := hT ▸ hQ
  let φ : X.presheaf.stalk (I.subschemeι y) →+* I.subscheme.presheaf.stalk y :=
    IsLocalization.map (M := P.asIdeal.primeCompl) _ g (hT.symm ▸ P.asIdeal.primeCompl.le_comap_map)
  have hφs : Function.Surjective φ :=
    IsLocalization.map_surjective_of_surjective P.asIdeal.primeCompl _ _ hsurj
  have hker : RingHom.ker φ =
      (I.ideal U).map (X.presheaf.germ U (I.subschemeι y) hy).hom := by
    rw [IsLocalization.ker_map _ g hT, I.ker_subschemeι_app U]
    rfl
  have hφ : φ = (I.subschemeι.stalkMap y).hom := by
    refine IsLocalization.ringHom_ext P.asIdeal.primeCompl ?_
    rw [IsLocalization.map_comp]
    change _ = ((X.presheaf.germ U (I.subschemeι y) hy) ≫ I.subschemeι.stalkMap y).hom
    rw [Scheme.Hom.germ_stalkMap]
    rfl
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφs),
    fun k ↦ ?_⟩
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    hφ, Scheme.Hom.stalkMap_comp]
  rfl

lemma stalkRank_eq_quotStalkRank (U : X.affineOpens) (y : I.subscheme)
    (hy : I.subschemeι y ∈ U.1) :
    (I.subschemeι ≫ f).stalkRank y = I.quotStalkRank f U (I.subschemeι y) hy := by
  obtain ⟨e, he⟩ := I.exists_ringEquiv_stalk f U y hy
  letI := stalkAlgebra f (I.subschemeι y)
  exact (Module.finrank_eq_of_ringEquiv (F := Γ(S, ⊤)) e _ fun k ↦ by exact he k).symm

lemma map_germ_eq_top (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : x ∉ I.support) :
    (I.ideal U).map (X.presheaf.germ U x hxU).hom = ⊤ := by
  rw [mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨a, ha, hxa⟩ := hx
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
    ((Scheme.mem_basicOpen X a x hxU).mp hxa)

lemma quotStalkRank_eq_zero (hF : IsField Γ(S, ⊤)) (U : X.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hx : x ∉ I.support) : I.quotStalkRank f U x hxU = 0 := by
  have : Nontrivial Γ(S, ⊤) := ⟨hF.exists_pair_ne⟩
  letI := stalkAlgebra f x
  have : Subsingleton (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hxU).hom) :=
    Ideal.Quotient.subsingleton_iff.mpr (I.map_germ_eq_top U x hxU hx)
  exact Module.finrank_zero_of_subsingleton

lemma not_mem_support_of_not_mem_range {x : X} (h : ¬∃ y, I.subschemeι y = x) :
    x ∉ I.support := fun hx ↦ by
  rw [← SetLike.mem_coe, ← I.range_subschemeι] at hx
  exact h hx

/-- If `Z(I) → S` is finite and `Γ(S, ⊤)` is a field, then `𝒪_{X, x} / I(U) 𝒪_{X, x}` is
finite-dimensional over `Γ(S, ⊤)`. -/
lemma finite_quot [IsAffine S] (hF : IsField Γ(S, ⊤)) [IsFinite (I.subschemeι ≫ f)]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    letI := stalkAlgebra f x
    Module.Finite Γ(S, ⊤) (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hx).hom) := by
  letI := stalkAlgebra f x
  by_cases h : ∃ y, I.subschemeι y = x
  · obtain ⟨y, rfl⟩ := h
    obtain ⟨e, he⟩ := I.exists_ringEquiv_stalk f U y hx
    have := (I.subschemeι ≫ f).finite_stalk hF y
    letI := stalkAlgebra (I.subschemeι ≫ f) y
    have he' : ∀ k, e.symm (algebraMap Γ(S, ⊤) (I.subscheme.presheaf.stalk y) k) =
        algebraMap Γ(S, ⊤) _ k := fun k ↦ by
      rw [RingEquiv.symm_apply_eq]
      exact (he k).symm
    exact Module.Finite.equiv (AlgEquiv.ofRingEquiv (f := e.symm) he').toLinearEquiv
  · have : Subsingleton (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hx).hom) :=
      Ideal.Quotient.subsingleton_iff.mpr
        (I.map_germ_eq_top U x hx (I.not_mem_support_of_not_mem_range h))
    infer_instance

/-- The local contribution of `x` to the degree of `Z(I) → S`: the rank of the stalk of `Z(I)`
at the point over `x`, and `0` if `x ∉ Z(I)`. -/
def localDegree (x : X) : ℕ :=
  Function.extend I.subschemeι (I.subschemeι ≫ f).stalkRank 0 x

lemma localDegree_eq (hF : IsField Γ(S, ⊤)) (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    I.localDegree f x = I.quotStalkRank f U x hx := by
  by_cases h : ∃ y, I.subschemeι y = x
  · obtain ⟨y, rfl⟩ := h
    rw [localDegree, I.subschemeι.isClosedEmbedding.injective.extend_apply,
      stalkRank_eq_quotStalkRank]
  · rw [localDegree, Function.extend_apply' _ _ _ h, Pi.zero_apply,
      quotStalkRank_eq_zero f I hF _ _ _ (I.not_mem_support_of_not_mem_range h)]

lemma support_localDegree_subset : Function.support (I.localDegree f) ⊆ Set.range I.subschemeι :=
  fun x hx ↦ by
    by_contra h
    exact hx (by rw [localDegree, Function.extend_apply' _ _ _ h, Pi.zero_apply])

/-- Over an affine base whose ring of global sections is a field, the rank of a finite flat
closed subscheme `Z(I) → S` is the sum of the local contributions. -/
lemma finrank_eq_finsum_localDegree [IsAffine S] (hF : IsField Γ(S, ⊤))
    [Flat (I.subschemeι ≫ f)] [IsFinite (I.subschemeι ≫ f)] (s : S) :
    (I.subschemeι ≫ f).finrank s = ∑ᶠ x, I.localDegree f x := by
  have hinj := I.subschemeι.isClosedEmbedding.injective
  rw [Scheme.Hom.finrank_eq_finsum_stalkRank hF]
  calc ∑ᶠ y, (I.subschemeι ≫ f).stalkRank y = ∑ᶠ y, I.localDegree f (I.subschemeι y) :=
        finsum_congr fun y ↦ (hinj.extend_apply _ _ _).symm
    _ = ∑ᶠ x ∈ Set.range I.subschemeι, I.localDegree f x := (finsum_mem_range hinj).symm
    _ = ∑ᶠ x, I.localDegree f x := by
        rw [← finsum_mem_univ (I.localDegree f)]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.mpr (I.support_localDegree_subset f)]

lemma finite_support_localDegree [IsAffine S] (hF : IsField Γ(S, ⊤))
    [IsFinite (I.subschemeι ≫ f)] : (Function.support (I.localDegree f)).Finite :=
  have := (I.subschemeι ≫ f).finite_of_isField hF
  (Set.finite_range _).subset (I.support_localDegree_subset f)

/-- The local contributions are additive: if `I(W) = (g)` and `J(W) = (h)` with `g` a
nonzerodivisor, then `𝒪_x/(gh)` has rank `rk(𝒪_x/g) + rk(𝒪_x/h)`. -/
lemma quotStalkRank_mul (hF : IsField Γ(S, ⊤)) (I J : X.IdealSheafData) (W : X.affineOpens)
    {g h : Γ(X, W.1)} (hI : I.ideal W = Ideal.span {g}) (hg : IsSMulRegular Γ(X, W.1) g)
    (hJ : J.ideal W = Ideal.span {h}) (x : X) (hx : x ∈ W.1)
    (hfin : letI := stalkAlgebra f x
      Module.Finite Γ(S, ⊤)
        (X.presheaf.stalk x ⧸ ((I * J).ideal W).map (X.presheaf.germ W x hx).hom)) :
    (I * J).quotStalkRank f W x hx = I.quotStalkRank f W x hx + J.quotStalkRank f W x hx := by
  letI := hF.toField
  letI := stalkAlgebra f x
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : W.1)
  have : IsLocalization (W.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    W.2.isLocalization_stalk ⟨x, hx⟩
  have hg' : IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ W x hx g) :=
    isSMulRegular_algebraMap_of_isLocalization (W.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hg
  have e1 : (I.ideal W).map (X.presheaf.germ W x hx).hom =
      Ideal.span {X.presheaf.germ W x hx g} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  have e2 : (J.ideal W).map (X.presheaf.germ W x hx).hom =
      Ideal.span {X.presheaf.germ W x hx h} := by
    rw [hJ, Ideal.map_span, Set.image_singleton]
  have e12 : ((I * J).ideal W).map (X.presheaf.germ W x hx).hom =
      Ideal.span {X.presheaf.germ W x hx g * X.presheaf.germ W x hx h} := by
    rw [ideal_mul, Pi.mul_apply, Ideal.map_mul, e1, e2, Ideal.span_singleton_mul_span_singleton]
  unfold quotStalkRank
  rw [e12] at hfin ⊢
  rw [e1, e2]
  have := Module.rankAtStalk_quotient_mul (A := Γ(S, ⊤)) hg' (X.presheaf.germ W x hx h)
    ⟨⊥, Ideal.isPrime_bot⟩
  simpa using this

end Local

end Scheme.IdealSheafData

namespace RelEffCartier

variable {X S T : Scheme.{u}} {f : X ⟶ S}

lemma ext_ideal {D E : RelEffCartier f} (h : D.ideal = E.ideal) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Base change commutes with the sum of relative effective Cartier divisors. -/
lemma baseChange_add (D₁ D₂ : RelEffCartier f) (g : T ⟶ S) :
    (D₁.add D₂).baseChange g = (D₁.baseChange g).add (D₂.baseChange g) :=
  ext_ideal (D₁.ideal.comap_mul D₂.ideal _)

section Degree

variable (D₁ D₂ : RelEffCartier f)

/-- Over an affine base whose ring of global sections is a field (e.g. a fibre `Spec κ(s)`), the
degree of `D₁ + D₂` is the sum of the degrees. -/
theorem degree_add_of_isField [IsAffine S] (hF : IsField Γ(S, ⊤))
    [IsFinite (D₁.ideal.subschemeι ≫ f)] [IsFinite (D₂.ideal.subschemeι ≫ f)]
    [IsFinite ((D₁.add D₂).ideal.subschemeι ≫ f)] (s : S) :
    (D₁.add D₂).degree s = D₁.degree s + D₂.degree s := by
  have := D₁.flat
  have := D₂.flat
  have := (D₁.add D₂).flat
  have hfin := (D₁.add D₂).ideal.finite_quot f hF
  change ((D₁.add D₂).ideal.subschemeι ≫ f).finrank s =
    (D₁.ideal.subschemeι ≫ f).finrank s + (D₂.ideal.subschemeι ≫ f).finrank s
  change ∀ U x hx, _ at hfin
  rw [IdealSheafData.finrank_eq_finsum_localDegree f _ hF (s := s),
    IdealSheafData.finrank_eq_finsum_localDegree f _ hF (s := s),
    IdealSheafData.finrank_eq_finsum_localDegree f _ hF (s := s),
    ← finsum_add_distrib (D₁.ideal.finite_support_localDegree f hF)
      (D₂.ideal.finite_support_localDegree f hF)]
  refine finsum_congr fun x ↦ ?_
  obtain ⟨W, g, h, hxW, -, hgI, hg, hhJ, -⟩ := exists_affine_principal_principal
    D₁.locally_principal D₂.locally_principal x ⊤ trivial
  rw [IdealSheafData.localDegree_eq f _ hF W x hxW, IdealSheafData.localDegree_eq f _ hF W x hxW,
    IdealSheafData.localDegree_eq f _ hF W x hxW]
  exact IdealSheafData.quotStalkRank_mul f hF _ _ W hgI hg hhJ x hxW (hfin W x hxW)

/-- The base change of a divisor finite over `S` is finite over `T`. -/
lemma isFinite_baseChange (D : RelEffCartier f) [IsFinite (D.ideal.subschemeι ≫ f)]
    (g : T ⟶ S) : IsFinite ((D.baseChange g).ideal.subschemeι ≫ pullback.snd f g) := by
  have sq : IsPullback (pullback.snd (pullback.fst f g) D.ideal.subschemeι)
      (pullback.fst (pullback.fst f g) D.ideal.subschemeι ≫ pullback.snd f g)
      (D.ideal.subschemeι ≫ f) g :=
    (IsPullback.of_hasPullback (pullback.fst f g) D.ideal.subschemeι).flip.paste_vert
      (IsPullback.of_hasPullback f g)
  have : IsFinite (pullback.fst (pullback.fst f g) D.ideal.subschemeι ≫ pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  rw [baseChange_ideal, ← IdealSheafData.comapIso_hom_fst, Category.assoc]
  infer_instance

/-- **Degrees of relative effective Cartier divisors add** (Stacks, Lemma 44.3.2, Tag 0B9E):
if `D₁`, `D₂` and `D₁ + D₂` are finite over `S`, then
`(D₁ + D₂).degree s = D₁.degree s + D₂.degree s` for all `s : S`. -/
@[stacks 0B9E]
theorem degree_add [IsFinite (D₁.ideal.subschemeι ≫ f)] [IsFinite (D₂.ideal.subschemeι ≫ f)]
    [IsFinite ((D₁.add D₂).ideal.subschemeι ≫ f)] (s : S) :
    (D₁.add D₂).degree s = D₁.degree s + D₂.degree s := by
  let g := S.fromSpecResidueField s
  let t : Spec (S.residueField s) := IsLocalRing.closedPoint _
  have ht : g t = s := S.fromSpecResidueField_apply s t
  have hF : IsField Γ(Spec (S.residueField s), ⊤) :=
    (Scheme.ΓSpecIso (S.residueField s)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField _)
  have := D₁.isFinite_baseChange g
  have := D₂.isFinite_baseChange g
  have : IsFinite (((D₁.baseChange g).add (D₂.baseChange g)).ideal.subschemeι ≫
      pullback.snd f g) := by
    rw [← baseChange_add]
    exact (D₁.add D₂).isFinite_baseChange g
  rw [← ht, ← degree_baseChange, ← degree_baseChange, ← degree_baseChange, baseChange_add]
  exact degree_add_of_isField _ _ hF t

end Degree

end RelEffCartier

end AlgebraicGeometry

namespace CurvesJacobian

open AlgebraicGeometry

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [Belyi.IsCurveOver k C] {T : Scheme.{u}}
  (gT : T ⟶ Spec (CommRingCat.of k))

/-- **Stacks, Lemma 44.3.2 (Tag 0B9E)** for `C ×_k T → T`, `C` a curve over a perfect field `k`:
the degree of `D₁ + D₂` is the sum of the degrees. -/
theorem degree_add_curve (D₁ D₂ : RelEffCartier (pullback.snd (C ↘ Spec (CommRingCat.of k)) gT))
    (t : T) : (D₁.add D₂).degree t = D₁.degree t + D₂.degree t :=
  haveI := D₁.isFinite C gT
  haveI := D₂.isFinite C gT
  haveI := (D₁.add D₂).isFinite C gT
  D₁.degree_add D₂ t

end CurvesJacobian

end
