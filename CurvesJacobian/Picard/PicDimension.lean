/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicTangentKer

/-!
# The Picard scheme of a curve of genus `g` is smooth of relative dimension `g`

Let `k` be a separably closed perfect field and `C` a curve over `k` of genus `g` with a
rational point `σ`. Then `Pic_{C/k,σ}` and its open subschemes `Pic^d` are smooth of relative
dimension `g` over `k` (`CurvesJacobian.smoothOfRelativeDimension_picScheme`,
`smoothOfRelativeDimension_picDegScheme`; Stacks, Lemma 44.6.7, Tag 0BA0, "smooth of dimension
`g`").

Proof. `Pic` is smooth (`CurvesJacobian.smooth_picScheme`), so near every point it is the
spectrum of a standard smooth `k`-algebra `A`, and it suffices to see `rank_A Ω_{A/k} = g`. Take
a `k`-point `x : A → k` (Nullstellensatz). The tangent vectors at `x` with values in a
`k`-module `M`, i.e. the lifts `A → k[M]` of `x`, are `Hom(Ω_A ⊗ k_x, M) ≅ M^ι` with
`#ι = rank Ω` (`TangentAlg.tanFun`), naturally in `M`; by representability they are the classes
in `Pic(C_{k[M]})` restricting to `x` (`PicTangent.θ`), i.e. (after translating by `x`) the kernel
of `Pic(C_{k[M]}) → Pic(C)`. For `M = k` this kernel is `Ȟ¹(C, 𝒪) ≅ k^g` through the twists
`c₁ a = [𝒪(1 + aε)]` (`PicTangent.c₁_eq_c₁_iff`, `exists_c₁_eq`), and the naturality for the
maps `k[ε₁, ε₂] → k[ε]` and `ε ↦ λε` makes the resulting bijection `Ȟ¹ ≅ k^ι` linear
(`TangentAlg.linearEquivOfNatural`). Hence `#ι = h¹(𝒪) = g`
(`CurvesJacobian.finrank_cechH1_eq_curveGenus`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TrivSqZeroExt

universe u

noncomputable section

namespace CurvesJacobian

open Scheme Cech PicTangent Belyi

/-! ### `k`-points of finite type algebras -/

lemma exists_algHom_of_finiteType {R A : Type u} [Field R] [IsAlgClosed R] [CommRing A]
    [Nontrivial A] [Algebra R A] [Algebra.FiniteType R A] : Nonempty (A →ₐ[R] R) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType R (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R m)
      (Ideal.Quotient.mkₐ_surjective R m)
  haveI : Module.Finite R (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := R) (K := A ⧸ m)
  exact ⟨((AlgEquiv.ofBijective (Algebra.ofId R (A ⧸ m)) hb).symm.toAlgHom).comp
    (Ideal.Quotient.mkₐ R m)⟩

namespace PicTangent

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "R₀" => Γ(Sk, ⊤)

/-! ### Points of the Picard scheme over `Spec B` -/

variable (k) in
/-- `Spec B` as a scheme over `k`. -/
abbrev TB (B : Type u) [CommRing B] [Algebra R₀ B] : Over Sk := Over.mk (gB (S := Sk) B)

/-- The morphism of `k`-schemes `Spec B' ⟶ Spec B` of an algebra map. -/
def homB {B B' : Type u} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B']
    (φ : B →ₐ[R₀] B') : TB k B' ⟶ TB k B :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (spec_map_comp_gB B φ)

omit [PerfectField k] [IsSepClosed k] in
lemma homB_comp {B B' B'' : Type u} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B']
    [CommRing B''] [Algebra R₀ B''] (φ : B →ₐ[R₀] B') (ψ : B' →ₐ[R₀] B'') :
    homB ψ ≫ homB φ = homB (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

omit [PerfectField k] [IsSepClosed k] in
lemma homB_id {B : Type u} [CommRing B] [Algebra R₀ B] : homB (AlgHom.id R₀ B) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

/-- The class in `Pic(C_Y)` of a `Y`-point of the Picard scheme. -/
def clsY {Y : Over Sk} (f : Y ⟶ picScheme C σ hσ) : (pullback (C ↘ Sk) Y.hom).Pic :=
  ((picSchemeRepresentableBy C σ hσ).homEquiv f).1

/-- The class in `Pic(C_B)` of a `Spec B`-point of the Picard scheme. -/
def cls {B : Type u} [CommRing B] [Algebra R₀ B] (f : TB k B ⟶ picScheme C σ hσ) :
    (CT k C B).Pic :=
  clsY C σ hσ (Y := TB k B) f

lemma cls_comp {B B' : Type u} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B']
    (φ : B →ₐ[R₀] B') (f : TB k B ⟶ picScheme C σ hσ) :
    cls C σ hσ (homB φ ≫ f) = Scheme.Pic.map (bc φ) (cls C σ hσ f) := by
  unfold cls clsY
  rw [picScheme_homEquiv_comp]
  rfl

lemma cls_injective {B : Type u} [CommRing B] [Algebra R₀ B] :
    Function.Injective (cls C σ hσ (B := B)) := fun _ _ h ↦
  (picSchemeRepresentableBy C σ hσ).homEquiv.injective (Subtype.ext h)

lemma exists_cls_eq {B : Type u} [CommRing B] [Algebra R₀ B] [IsLocalRing B]
    (ξ : (CT k C B).Pic) : ∃ f, cls C σ hσ f = ξ := by
  haveI : IsLocalRing (CommRingCat.of B) := ‹IsLocalRing B›
  have hξ : ξ ∈ picSigmaGrp (C ↘ Sk) σ hσ (gB (S := Sk) B) :=
    (mem_picSigmaGrp (C ↘ Sk) σ hσ ξ).mpr (Subsingleton.elim _ _)
  refine ⟨(picSchemeRepresentableBy C σ hσ).homEquiv.symm ⟨ξ, hξ⟩, ?_⟩
  unfold cls clsY
  rw [Equiv.apply_symm_apply]

variable {C σ hσ}

section Points

variable (V : (picScheme C σ hσ).left.Opens) [IsAffine V]
  [Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(V, ⊤)]
  (hA : ∀ r, algebraMap Γ(Spec (CommRingCat.of k), ⊤) Γ(V, ⊤) r =
    (V.ι ≫ (picScheme C σ hσ).hom).appTop r)

omit [IsAffine V] in
include hA in
lemma comp_ofHom_eq {B : Type u} [CommRing B] [Algebra R₀ B] (φ : Γ(V, ⊤) →ₐ[R₀] B) :
    (V.ι ≫ (picScheme C σ hσ).hom).appTop ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap R₀ B) := by
  ext r
  change φ ((V.ι ≫ (picScheme C σ hσ).hom).appTop r) = algebraMap R₀ B r
  rw [← hA, φ.commutes]

/-- The `Spec B`-point of `Pic` given by an algebra map `Γ(V) → B`. -/
def fv {B : Type u} [CommRing B] [Algebra R₀ B] (φ : Γ(V, ⊤) →ₐ[R₀] B) :
    TB k B ⟶ picScheme C σ hσ :=
  Over.homMk (ptOf (CommRingCat.ofHom φ.toRingHom) ≫ V.ι) (by
    rw [Category.assoc]
    exact (ptOf_comp_eq_gB_iff B (V.ι ≫ (picScheme C σ hσ).hom) _).mpr
      (comp_ofHom_eq V hA φ))

lemma homB_fv {B B' : Type u} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B']
    (φ : Γ(V, ⊤) →ₐ[R₀] B) (φ' : B →ₐ[R₀] B') :
    homB φ' ≫ fv V hA φ = fv V hA (φ'.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ ptOf _ ≫ V.ι = ptOf _ ≫ V.ι
  rw [← Category.assoc, map_comp_ptOf]
  rfl

lemma fv_injective {B : Type u} [CommRing B] [Algebra R₀ B] {φ φ' : Γ(V, ⊤) →ₐ[R₀] B}
    (h : fv V hA φ = fv V hA φ') : φ = φ' := by
  have h1 : ptOf (CommRingCat.ofHom φ.toRingHom) ≫ V.ι =
      ptOf (CommRingCat.ofHom φ'.toRingHom) ≫ V.ι := congrArg (fun f ↦ f.left) h
  have h2 := ptOf_injective ((cancel_mono V.ι).mp h1)
  ext a
  exact congrArg (fun ψ : Γ(V, ⊤) ⟶ CommRingCat.of B ↦ ψ a) h2

/-- **Points over an infinitesimal thickening of a point of `V` lie in `V`.** -/
lemma exists_fv_eq {B : Type u} [CommRing B] [Algebra R₀ B] (aug : B →ₐ[R₀] R₀)
    (hs : Function.Surjective aug) (hsq : MatLift.SqZero (CommRingCat.ofHom aug.toRingHom).hom)
    (x : Γ(V, ⊤) →ₐ[R₀] R₀) (f : TB k B ⟶ picScheme C σ hσ) (hf : homB aug ≫ f = fv V hA x) :
    ∃ φ : Γ(V, ⊤) →ₐ[R₀] B, fv V hA φ = f ∧ aug.comp φ = x := by
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom aug.toRingHom)).base :=
    SmoothLift.surjective_of_thickening _ (SmoothLift.surjective_appTop_spec_map _ hs)
      (SmoothLift.sqZero_appTop_spec_map _ hsq)
  have hfl : Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ f.left =
      ptOf (CommRingCat.ofHom x.toRingHom) ≫ V.ι := congrArg (fun g ↦ g.left) hf
  have hrange : Set.range f.left.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p₀, rfl⟩ := hsurj p
    refine ⟨(ptOf (CommRingCat.ofHom x.toRingHom)) p₀, ?_⟩
    exact (congrArg (fun h ↦ h.base p₀) hfl).symm
  obtain ⟨f', hf'⟩ : ∃ f', f' ≫ V.ι = f.left :=
    ⟨_, IsOpenImmersion.lift_fac V.ι f.left hrange⟩
  obtain ⟨ψ, hψ⟩ := exists_ptOf f'
  have hψV : ptOf ψ ≫ V.ι = f.left := (congrArg (· ≫ V.ι) hψ).trans hf'
  have hover : ptOf ψ ≫ (V.ι ≫ (picScheme C σ hσ).hom) = gB (S := Sk) B := by
    rw [← Category.assoc, hψV]
    exact Over.w f
  have hψ' := (ptOf_comp_eq_gB_iff B _ ψ).mp hover
  let φ : Γ(V, ⊤) →ₐ[R₀] B :=
    { ψ.hom with
      commutes' := fun r ↦ by
        change ψ (algebraMap R₀ Γ(V, ⊤) r) = algebraMap R₀ B r
        rw [hA]
        exact congrArg (fun g : R₀ ⟶ CommRingCat.of B ↦ g r) hψ' }
  have hφψ : CommRingCat.ofHom φ.toRingHom = ψ := rfl
  have hfφ : fv V hA φ = f := by
    apply Over.OverMorphism.ext
    change ptOf (CommRingCat.ofHom φ.toRingHom) ≫ V.ι = f.left
    rw [hφψ]
    exact hψV
  refine ⟨φ, hfφ, fv_injective V hA ?_⟩
  rw [← homB_fv, hfφ, hf]

/-! ### The tangent maps `θ_M` -/

variable {ι : Type u} [Fintype ι]
  (b : Module.Basis ι Γ(V, ⊤) Ω[Γ(V, ⊤)⁄Γ(Spec (CommRingCat.of k), ⊤)])
  (x : Γ(V, ⊤) →ₐ[Γ(Spec (CommRingCat.of k), ⊤)] Γ(Spec (CommRingCat.of k), ⊤))

/-- **The tangent map**: `v ∈ M^ι` ↦ the class of the point `x + ε v` minus the class of `x`. -/
def θ (M : Type u) [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M]
    (v : ι → M) : (CT k C (TrivSqZeroExt R₀ M)).Pic :=
  cls C σ hσ (fv V hA (TangentAlg.tanFun x b M v)) -
    cls C σ hσ (homB (Algebra.ofId R₀ (TrivSqZeroExt R₀ M)) ≫ fv V hA x)

variable (M : Type u) [AddCommGroup M] [Module Γ(Spec (CommRingCat.of k), ⊤) M]
  [Module Γ(Spec (CommRingCat.of k), ⊤)ᵐᵒᵖ M] [IsCentralScalar Γ(Spec (CommRingCat.of k), ⊤) M]

omit [IsAffine V] in
lemma aug_comp_tanFun (v : ι → M) : (augM k M).comp (TangentAlg.tanFun x b M v) = x := by
  ext a
  exact TangentAlg.fst_tanFun x b M v a

omit [PerfectField k] [IsSepClosed k] in
lemma homB_aug_ofId : homB (augM k M) ≫ homB (Algebra.ofId R₀ (TrivSqZeroExt R₀ M)) =
    𝟙 _ := by
  rw [homB_comp, ← homB_id]
  congr 1

lemma θ_injective : Function.Injective (θ V hA b x M) := by
  intro v w h
  have h' : cls C σ hσ (fv V hA (TangentAlg.tanFun x b M v)) =
      cls C σ hσ (fv V hA (TangentAlg.tanFun x b M w)) := sub_left_injective h
  exact TangentAlg.tanFun_injective x b M (fv_injective V hA (cls_injective C σ hσ h'))

lemma map_aug_θ (v : ι → M) : Scheme.Pic.map (bc (augM k M)) (θ V hA b x M v) = 0 := by
  rw [θ, map_sub, ← cls_comp, ← cls_comp, homB_fv, aug_comp_tanFun, ← Category.assoc,
    homB_aug_ofId, Category.id_comp, sub_self]

lemma exists_θ_eq [IsLocalRing (TrivSqZeroExt R₀ M)] (κ : (CT k C (TrivSqZeroExt R₀ M)).Pic)
    (hκ : Scheme.Pic.map (bc (augM k M)) κ = 0) : ∃ v, θ V hA b x M v = κ := by
  obtain ⟨f, hf⟩ := exists_cls_eq C σ hσ
    (κ + cls C σ hσ (homB (Algebra.ofId R₀ (TrivSqZeroExt R₀ M)) ≫ fv V hA x))
  have h1 : homB (augM k M) ≫ f = fv V hA x := by
    refine cls_injective C σ hσ ?_
    rw [cls_comp, hf, map_add, hκ, zero_add, ← cls_comp, ← Category.assoc, homB_aug_ofId,
      Category.id_comp]
  have hsq : MatLift.SqZero (CommRingCat.ofHom (augM k M).toRingHom).hom := by
    intro a b ha hb
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [ha]
    · simp [ha, hb]
  obtain ⟨φ, hφ, hφx⟩ := exists_fv_eq V hA (augM k M) (fun r ↦ ⟨inl r, rfl⟩) hsq x f h1
  obtain ⟨v, hv⟩ := TangentAlg.exists_tanFun_eq x b M φ fun a ↦
    congrArg (fun g : Γ(V, ⊤) →ₐ[R₀] R₀ ↦ g a) hφx
  refine ⟨v, ?_⟩
  rw [θ, hv, hφ, hf, add_sub_cancel_right]

lemma map_θ {M' : Type u} [AddCommGroup M'] [Module R₀ M'] [Module R₀ᵐᵒᵖ M']
    [IsCentralScalar R₀ M'] (l : M →ₗ[R₀] M') (v : ι → M) :
    Scheme.Pic.map (bc (TrivSqZeroExt.map l)) (θ V hA b x M v) = θ V hA b x M' (l ∘ v) := by
  rw [θ, θ, map_sub, ← cls_comp, ← cls_comp, homB_fv, TangentAlg.map_tanFun, ← Category.assoc,
    homB_comp, Subsingleton.elim ((TrivSqZeroExt.map l).comp (Algebra.ofId R₀ (TrivSqZeroExt R₀ M)))
      (Algebra.ofId R₀ (TrivSqZeroExt R₀ M'))]

end Points

/-! ### The dimension -/

variable (C σ hσ) in
/-- **The tangent space at a point of `Pic` has dimension `g`.** For an affine open `V ⊆ Pic`,
a `k`-point `x` of `V` and a basis `b` of `Ω_{Γ(V)/k}`, the number of elements of `b` is the
genus of `C`. -/
theorem card_eq_curveGenus (V : (picScheme C σ hσ).left.Opens) [IsAffine V]
    [Algebra R₀ Γ(V, ⊤)]
    (hA : ∀ r, algebraMap R₀ Γ(V, ⊤) r = (V.ι ≫ (picScheme C σ hσ).hom).appTop r)
    {ι : Type u} [Fintype ι] (b : Module.Basis ι Γ(V, ⊤) Ω[Γ(V, ⊤)⁄R₀])
    (x : Γ(V, ⊤) →ₐ[R₀] R₀) :
    Fintype.card ι = genusNat k C := by
  haveI : IsIntegral C := IsCurveOver.isIntegral k C
  haveI := isLocalRing_trivSqZeroExt (R := R₀) (M := R₀) isField_ΓSpec
  haveI := isLocalRing_trivSqZeroExt (R := R₀) (M := R₀ × R₀) isField_ΓSpec
  obtain ⟨⟨U₁, hU⟩, ⟨U₂, hV⟩, hcov⟩ := IsCurveOver.exists_two_affine_cover k C
  have hW := IsCurveOver.isAffineOpen_inf k C hU hV
  let e := TangentAlg.linearEquivOfNatural
    (Submodule.mkQ (LinearMap.range (TwoCech.d
      (resLin Sk C (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (resLin Sk C (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))))
    (Submodule.mkQ_surjective _)
    (θ V hA b x R₀) (θ V hA b x (R₀ × R₀)) (θ_injective V hA b x R₀)
    (Scheme.Pic.map (bc (prFst k))) (Scheme.Pic.map (bc (prSnd k)))
    (Scheme.Pic.map (bc (prSum k))) (fun r ↦ Scheme.Pic.map (bc (scal k r)))
    (fun v ↦ map_θ V hA b x (R₀ × R₀) (LinearMap.fst R₀ R₀ R₀) v)
    (fun v ↦ map_θ V hA b x (R₀ × R₀) (LinearMap.snd R₀ R₀ R₀) v)
    (fun v ↦ map_θ V hA b x (R₀ × R₀) (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀) v)
    (fun r v ↦ map_θ V hA b x R₀ (r • LinearMap.id) v)
    (c₁ (k := k) C _ _ hcov) (fun a a' ↦ (c₁_eq_c₁_iff hcov hU hV hW a a').trans
      (Submodule.Quotient.eq _).symm)
    (fun a ↦ exists_θ_eq V hA b x R₀ _ (map_c₁_aug (k := k) C hcov a))
    (fun v ↦ exists_c₁_eq hcov hU hV hW _ (map_aug_θ V hA b x R₀ v))
    (c₂ (k := k) C _ _ hcov)
    (fun a a' ↦ exists_θ_eq V hA b x (R₀ × R₀) _ (map_c₂_aug (k := k) C hcov a a'))
    (map_c₂_fst (k := k) C hcov) (map_c₂_snd (k := k) C hcov)
    (map_c₂_add (k := k) C hcov) (map_c₁_smul (k := k) C hcov)
  have h1 := e.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := finrank_cechH1_eq_curveGenus k C hU hV hcov
  have h3 : genusNat k C = (curveGenus k C).toNat := rfl
  rw [h3, ← h2, Int.toNat_natCast]
  exact h1.symm

end PicTangent

open PicTangent

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "R₀" => Γ(Sk, ⊤)

/-- **The Picard scheme of a curve of genus `g` is smooth of relative dimension `g`** (Stacks,
Lemma 44.6.7, Tag 0BA0). -/
instance smoothOfRelativeDimension_picScheme :
    SmoothOfRelativeDimension (genusNat k C) (picScheme C σ hσ).hom := by
  constructor
  intro z
  obtain ⟨U', hU', V, hV, hz, e, hstd⟩ := Smooth.exists_isStandardSmooth (picScheme C σ hσ).hom z
  refine ⟨U', hU', V, hV, hz, e, ?_⟩
  have hU'top : U' = ⊤ := by
    refine eq_top_iff.mpr fun p _ ↦ ?_
    have : p = (picScheme C σ hσ).hom z :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact e hz
  subst hU'top
  haveI : IsAffine V := hV
  letI : Algebra R₀ Γ(V, ⊤) := (V.ι ≫ (picScheme C σ hσ).hom).appTop.hom.toAlgebra
  have hA : ∀ r, algebraMap R₀ Γ(V, ⊤) r = (V.ι ≫ (picScheme C σ hσ).hom).appTop r :=
    fun _ ↦ rfl
  have key : (V.ι ≫ (picScheme C σ hσ).hom).appTop ≫ V.topIso.hom =
      (picScheme C σ hσ).hom.appLE ⊤ V e := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      Scheme.Hom.appLE, Category.assoc]
    erw [← Functor.map_comp]
    rfl
  have hq : (V.ι ≫ (picScheme C σ hσ).hom).appTop.hom.IsStandardSmooth := by
    rw [← RingHom.isStandardSmooth_respectsIso.cancel_right_isIso _ V.topIso.hom,
      ← CommRingCat.hom_comp, key]
    exact hstd
  haveI : Algebra.IsStandardSmooth R₀ Γ(V, ⊤) := hq
  haveI : Nonempty (⊤ : (V : Scheme).Opens) := ⟨⟨⟨z, hz⟩, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial _ _
  let b := Module.Free.chooseBasis Γ(V, ⊤) Ω[Γ(V, ⊤)⁄R₀]
  obtain ⟨x⟩ : Nonempty (Γ(V, ⊤) →ₐ[R₀] R₀) := by
    letI : Field R₀ := isField_ΓSpec.toField
    haveI : IsAlgClosed R₀ := IsAlgClosed.of_ringEquiv k R₀
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
    exact exists_algHom_of_finiteType
  have hcard := card_eq_curveGenus C σ hσ V hA b x
  have hrank : Module.rank Γ(V, ⊤) Ω[Γ(V, ⊤)⁄R₀] = (genusNat k C : Cardinal) := by
    rw [rank_eq_card_basis b, hcard]
  have hrel : Algebra.IsStandardSmoothOfRelativeDimension (genusNat k C) R₀ Γ(V, ⊤) :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).mpr hrank
  have hq' : (V.ι ≫ (picScheme C σ hσ).hom).appTop.hom.IsStandardSmoothOfRelativeDimension
      (genusNat k C) := hrel
  rw [← key, CommRingCat.hom_comp]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_right_isIso _
    V.topIso.hom).mpr hq'

/-- **`Pic^d_{C/k,σ}` is smooth of relative dimension `g`.** -/
instance smoothOfRelativeDimension_picDegScheme (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]
    (d : ℤ) : SmoothOfRelativeDimension (genusNat k C) (picDegScheme C σ hσ π d).hom :=
  IsZariskiLocalAtSource.comp (smoothOfRelativeDimension_picScheme C σ hσ)
    (picDegOpens C σ hσ π d).ι

end CurvesJacobian
