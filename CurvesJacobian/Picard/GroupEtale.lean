/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CommAlg.EtaleOfDerivation
import CurvesJacobian.Picard.PicTangentSetup
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Multiplication by `n` on a smooth commutative group scheme is étale

Let `k` be a field and `G` a commutative group scheme over `k` (a commutative group object of
`Over (Spec k)`), smooth over `k`, and let `n` be invertible in `k`.

* **`CurvesJacobian.GrpEtale.bijective_pow_tangent`**: for every point `x : Spec κ ⟶ G`
  (`κ` a field over `k`), `v ↦ v ^ n` is a bijection from the tangent vectors
  `Spec κ[ε] ⟶ G` at `x` to those at `x ^ n`. No computation of the group law on tangent spaces
  is needed: on the kernel `P` of `G(κ[ε]) → G(κ)` the operators `s_t = G(ε ↦ tε)` satisfy
  `s_{t+t'} = s_t · s_{t'}`, tested on `κ[ε₁, ε₂]` (two points of `G` over `Spec κ[ε₁, ε₂]`
  that agree on both projections to `Spec κ[ε]` are equal, as both factor through one affine
  open: `eq_of_pr_eq`); hence `s_n = (·)ⁿ` on `P`, with inverse `s_{1/n}`.
* **`CurvesJacobian.GrpEtale.etale_pow`**: `[n] : G ⟶ G` is étale, by the ring criterion
  `CurvesJacobian.etale_of_bijective_lift` applied on affine opens.
* **`CurvesJacobian.GrpEtale.surjective_pow`**: if moreover `G` is proper and connected, `[n]` is
  surjective (étale ⇒ open, proper ⇒ closed).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TrivSqZeroExt CategoryTheory.MonObj

universe u

noncomputable section

namespace CurvesJacobian.GrpEtale

open PicTangent

variable {k : Type u} [Field k]

variable (k) in
/-- The ring `Γ(Spec k, ⊤)` (isomorphic to `k`) over which `k`-schemes are algebras. -/
abbrev R₀ : CommRingCat.{u} := Γ(Spec (CommRingCat.of k), ⊤)


/-! ### Points with values in `k`-algebras -/

section Points

variable (k) in
/-- `Spec B` as a scheme over `k`. -/
abbrev TB (B : Type u) [CommRing B] [Algebra (R₀ k) B] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (gB (S := (Spec (CommRingCat.of k))) B)

/-- The morphism of `k`-schemes `Spec B' ⟶ Spec B` of an algebra map. -/
def homB {B B' : Type u} [CommRing B] [Algebra (R₀ k) B] [CommRing B'] [Algebra (R₀ k) B']
    (φ : B →ₐ[R₀ k] B') : TB k B' ⟶ TB k B :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (spec_map_comp_gB B φ)

lemma homB_comp {B B' B'' : Type u} [CommRing B] [Algebra (R₀ k) B] [CommRing B']
    [Algebra (R₀ k) B']
    [CommRing B''] [Algebra (R₀ k) B''] (φ : B →ₐ[R₀ k] B') (ψ : B' →ₐ[R₀ k] B'') :
    homB ψ ≫ homB φ = homB (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

lemma homB_comp_assoc {B B' B'' : Type u} [CommRing B] [Algebra (R₀ k) B] [CommRing B']
    [Algebra (R₀ k) B'] [CommRing B''] [Algebra (R₀ k) B''] (φ : B →ₐ[R₀ k] B')
    (ψ : B' →ₐ[R₀ k] B'')
    {Z : Over (Spec (CommRingCat.of k))} (f : TB k B ⟶ Z) :
    homB ψ ≫ homB φ ≫ f = homB (ψ.comp φ) ≫ f := by
  rw [← Category.assoc, homB_comp]

lemma homB_id {B : Type u} [CommRing B] [Algebra (R₀ k) B] :
    homB (AlgHom.id (R₀ k) B) = 𝟙 (TB k B) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

variable {X : Over (Spec (CommRingCat.of k))}

/-- The structure map `Γ(k) → Γ(X, V)`. -/
abbrev strV (V : X.left.Opens) : (R₀ k) →+* Γ(X.left, V) :=
  (X.hom.appLE ⊤ V (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom

lemma gB_eq (B : Type u) [CommRing B] [Algebra (R₀ k) B] :
    gB (S := (Spec (CommRingCat.of k))) B = Spec.map (CommRingCat.ofHom (algebraMap (R₀ k) B)) ≫
      (isAffineOpen_top (Spec (CommRingCat.of k))).fromSpec := by
  rw [gB, IsAffineOpen.fromSpec_top]

variable {V : X.left.Opens} (hV : IsAffineOpen V)

lemma pt_comp_hom {B : Type u} [CommRing B] [Algebra (R₀ k) B] (ψ : Γ(X.left, V) →+* B)
    (hψ : ψ.comp (strV V) = algebraMap (R₀ k) B) :
    (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ X.hom =
      gB (S := (Spec (CommRingCat.of k))) B := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hV le_top,
    ← Category.assoc, ← Spec.map_comp, gB_eq]
  congr 2
  exact CommRingCat.hom_ext hψ

/-- The `Spec B`-point of `X` given by a ring map `Γ(X, V) → B` over `k`. -/
def pt {B : Type u} [CommRing B] [Algebra (R₀ k) B] (ψ : Γ(X.left, V) →+* B)
    (hψ : ψ.comp (strV V) = algebraMap (R₀ k) B) : TB k B ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (pt_comp_hom hV ψ hψ)

lemma pt_left {B : Type u} [CommRing B] [Algebra (R₀ k) B] (ψ : Γ(X.left, V) →+* B)
    (hψ : ψ.comp (strV V) = algebraMap (R₀ k) B) :
    (pt hV ψ hψ).left = Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec := rfl

lemma pt_injective {B : Type u} [CommRing B] [Algebra (R₀ k) B] {ψ ψ' : Γ(X.left, V) →+* B}
    {hψ : ψ.comp (strV V) = algebraMap (R₀ k) B} {hψ' : ψ'.comp (strV V) = algebraMap (R₀ k) B}
    (h : pt hV ψ hψ = pt hV ψ' hψ') : ψ = ψ' := by
  have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom ψ') ≫ hV.fromSpec := congrArg (fun f ↦ f.left) h
  have h2 := Spec.map_injective ((cancel_mono hV.fromSpec).mp h1)
  exact congrArg CommRingCat.Hom.hom h2

lemma homB_pt {B B' : Type u} [CommRing B] [Algebra (R₀ k) B] [CommRing B'] [Algebra (R₀ k) B']
    (φ : B →ₐ[R₀ k] B') (ψ : Γ(X.left, V) →+* B) (hψ : ψ.comp (strV V) = algebraMap (R₀ k) B) :
    homB φ ≫ pt hV ψ hψ = pt hV (φ.toRingHom.comp ψ) (by
      rw [RingHom.comp_assoc, hψ]; exact φ.comp_algebraMap) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ ≫ hV.fromSpec = Spec.map _ ≫ hV.fromSpec
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Points whose image lies in `V` come from ring maps. -/
lemma exists_pt {B : Type u} [CommRing B] [Algebra (R₀ k) B] (f : TB k B ⟶ X)
    (hf : Set.range f.left.base ⊆ V) :
    ∃ ψ hψ, pt (B := B) hV ψ hψ = f := by
  have hr : Set.range f.left.base ⊆ Set.range hV.fromSpec.base := by
    rw [hV.range_fromSpec]; exact hf
  obtain ⟨g, hg⟩ : ∃ g : Spec (CommRingCat.of B) ⟶ Spec Γ(X.left, V), g ≫ hV.fromSpec = f.left :=
    ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  have hover : (Spec.map ψ ≫ hV.fromSpec) ≫ X.hom = gB (S := Spec (CommRingCat.of k)) B := by
    rw [hg]
    exact Over.w f
  have hψ : ψ.hom.comp (strV V) = algebraMap (R₀ k) B := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hV
      le_top, ← Category.assoc, ← Spec.map_comp, gB_eq] at hover
    have := Spec.map_injective ((cancel_mono _).mp hover)
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨ψ.hom, hψ, ?_⟩
  apply Over.OverMorphism.ext
  exact hg

/-- **Points of `X` over a first-order thickening of a point of `V` lie in `V`.** -/
lemma range_subset_of_thickening {B B₀ : Type u} [CommRing B] [Algebra (R₀ k) B] [CommRing B₀]
    [Algebra (R₀ k) B₀] (aug : B →ₐ[R₀ k] B₀) (hs : Function.Surjective aug)
    (hsq : MatLift.SqZero (CommRingCat.ofHom aug.toRingHom).hom) (f : TB k B ⟶ X)
    (hf : Set.range (homB aug ≫ f).left.base ⊆ V) : Set.range f.left.base ⊆ V := by
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom aug.toRingHom)).base :=
    SmoothLift.surjective_of_thickening _ (SmoothLift.surjective_appTop_spec_map _ hs)
      (SmoothLift.sqZero_appTop_spec_map _ hsq)
  rintro _ ⟨p, rfl⟩
  obtain ⟨p₀, rfl⟩ := hsurj p
  exact hf ⟨p₀, rfl⟩

omit [Field k] in
lemma appLE_eq_of_eq {X' Y' : Scheme.{u}} {f g : X' ⟶ Y'} (h : f = g) {U : Y'.Opens}
    {V' : X'.Opens} (e : V' ≤ f ⁻¹ᵁ U) : f.appLE U V' e = g.appLE U V' (h ▸ e) := by
  subst h; rfl

/-- `appLE` of a morphism over `k` commutes with the structure maps. -/
lemma strV_comp {Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) {U : Y.left.Opens}
    (e : V ≤ f.left ⁻¹ᵁ U) :
    (f.left.appLE U V e).hom.comp (strV U) = strV V := by
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (Over.w f)]

/-- Morphisms of `k`-schemes compose with points through `appLE`. -/
lemma pt_comp {Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) {U : Y.left.Opens}
    (hU : IsAffineOpen U)
    (e : V ≤ f.left ⁻¹ᵁ U) {B : Type u} [CommRing B] [Algebra (R₀ k) B] (ψ : Γ(X.left, V) →+* B)
    (hψ : ψ.comp (strV V) = algebraMap (R₀ k) B) :
    pt hV ψ hψ ≫ f = pt hU (ψ.comp (f.left.appLE U V e).hom) (by
      rw [RingHom.comp_assoc, strV_comp f e, hψ]) := by
  apply Over.OverMorphism.ext
  change (Spec.map _ ≫ hV.fromSpec) ≫ f.left = Spec.map _ ≫ hU.fromSpec
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f.left hU hV e, ← Category.assoc,
    ← Spec.map_comp]
  rfl

end Points

/-! ### Tangent vectors and the operators `s_t` -/

section Tangent

variable {κ : Type u} [CommRing κ] [Algebra (R₀ k) κ]

variable (κ) in
/-- The dual numbers `κ[ε]`. -/
abbrev E₁ := TrivSqZeroExt κ κ

variable (κ) in
/-- `κ[ε₁, ε₂] = κ[ε] ×_κ κ[ε]`. -/
abbrev E₂ := TrivSqZeroExt κ (κ × κ)

variable (k κ) in
/-- The augmentation `κ[ε] → κ`. -/
def aug : E₁ κ →ₐ[R₀ k] κ := fstHom _ κ κ

variable (k κ) in
/-- The augmentation `κ[ε₁, ε₂] → κ`. -/
def aug₂ : E₂ κ →ₐ[R₀ k] κ := fstHom _ κ (κ × κ)

variable (k κ) in
/-- The constants `κ → κ[ε]`. -/
def incl : κ →ₐ[R₀ k] E₁ κ := inlAlgHom _ κ κ

variable (k) in
/-- `ε ↦ t ε`. -/
def scal (t : κ) : E₁ κ →ₐ[R₀ k] E₁ κ :=
  (TrivSqZeroExt.map (t • LinearMap.id : κ →ₗ[κ] κ)).restrictScalars _

variable (k) in
/-- `ε ↦ t ε₁ + t' ε₂`. -/
def phi (t t' : κ) : E₁ κ →ₐ[R₀ k] E₂ κ :=
  (TrivSqZeroExt.map ((t • LinearMap.id : κ →ₗ[κ] κ).prod (t' • LinearMap.id))).restrictScalars _

variable (k κ) in
/-- `ε₁ ↦ ε, ε₂ ↦ 0`. -/
def pr₁ : E₂ κ →ₐ[R₀ k] E₁ κ :=
  (TrivSqZeroExt.map (LinearMap.fst κ κ κ)).restrictScalars _

variable (k κ) in
/-- `ε₁ ↦ 0, ε₂ ↦ ε`. -/
def pr₂ : E₂ κ →ₐ[R₀ k] E₁ κ :=
  (TrivSqZeroExt.map (LinearMap.snd κ κ κ)).restrictScalars _

variable (k κ) in
/-- `ε₁, ε₂ ↦ ε`. -/
def sm : E₂ κ →ₐ[R₀ k] E₁ κ :=
  (TrivSqZeroExt.map (LinearMap.fst κ κ κ + LinearMap.snd κ κ κ)).restrictScalars _

variable (k κ) in
/-- `ε ↦ ε₁`. -/
def in₁ : E₁ κ →ₐ[R₀ k] E₂ κ :=
  (TrivSqZeroExt.map (LinearMap.inl κ κ κ)).restrictScalars _

variable (k κ) in
/-- `ε ↦ ε₂`. -/
def in₂ : E₁ κ →ₐ[R₀ k] E₂ κ :=
  (TrivSqZeroExt.map (LinearMap.inr κ κ κ)).restrictScalars _

lemma aug_comp_scal (t : κ) : (aug k κ).comp (scal k t) = aug k κ := by
  refine AlgHom.ext fun x ↦ ?_; simp [aug, scal]

lemma scal_comp_scal (t t' : κ) : (scal k t).comp (scal k t') = scal k (t * t') := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_
  · simp [scal]
  · simp [scal, mul_smul]

lemma scal_one : scal k (1 : κ) = AlgHom.id _ _ := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [scal]

lemma scal_zero : scal k (0 : κ) = (incl k κ).comp (aug k κ) := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [scal, incl, aug]

lemma aug_comp_incl : (aug k κ).comp (incl k κ) = AlgHom.id _ _ := by
  refine AlgHom.ext fun x ↦ ?_; simp [aug, incl]

lemma pr₁_comp_phi (t t' : κ) : (pr₁ k κ).comp (phi k t t') = scal k t := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₁, phi, scal]

lemma pr₂_comp_phi (t t' : κ) : (pr₂ k κ).comp (phi k t t') = scal k t' := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₂, phi, scal]

lemma sm_comp_phi (t t' : κ) : (sm k κ).comp (phi k t t') = scal k (t + t') := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [sm, phi, scal, add_smul]

lemma pr₁_comp_in₁ : (pr₁ k κ).comp (in₁ k κ) = scal k 1 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₁, in₁, scal]

lemma pr₁_comp_in₂ : (pr₁ k κ).comp (in₂ k κ) = scal k 0 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₁, in₂, scal]

lemma pr₂_comp_in₁ : (pr₂ k κ).comp (in₁ k κ) = scal k 0 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₂, in₁, scal]

lemma pr₂_comp_in₂ : (pr₂ k κ).comp (in₂ k κ) = scal k 1 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [pr₂, in₂, scal]

lemma sm_comp_in₁ : (sm k κ).comp (in₁ k κ) = scal k 1 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [sm, in₁, scal]

lemma sm_comp_in₂ : (sm k κ).comp (in₂ k κ) = scal k 1 := by
  refine AlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [sm, in₂, scal]

lemma aug_comp_pr₁ : (aug k κ).comp (pr₁ k κ) = aug₂ k κ := by
  refine AlgHom.ext fun x ↦ ?_; simp [aug, pr₁, aug₂]

lemma surjective_aug₂ : Function.Surjective (aug₂ k κ) := fun r ↦ ⟨inl r, by simp [aug₂]⟩

lemma sqZero_aug₂ : MatLift.SqZero (CommRingCat.ofHom (aug₂ k κ).toRingHom).hom := by
  intro a b ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [ha]
  · simp [ha, hb]

/-- **Two points over `κ[ε₁, ε₂]` agreeing on both projections are equal** (`Spec κ` a point). -/
lemma eq_of_pr_eq [Nontrivial κ] [Subsingleton (PrimeSpectrum κ)]
    {X : Over (Spec (CommRingCat.of k))} {u u' : TB k (E₂ κ) ⟶ X}
    (h₁ : homB (pr₁ k κ) ≫ u = homB (pr₁ k κ) ≫ u')
    (h₂ : homB (pr₂ k κ) ≫ u = homB (pr₂ k κ) ≫ u') : u = u' := by
  have h0 : homB (aug₂ k κ) ≫ u = homB (aug₂ k κ) ≫ u' := by
    rw [← aug_comp_pr₁, ← homB_comp, Category.assoc, h₁, ← Category.assoc, homB_comp]
  let p₀ : Spec (CommRingCat.of κ) := Classical.choice (inferInstance : Nonempty (PrimeSpectrum κ))
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens)
    (show (homB (aug₂ k κ) ≫ u).left.base p₀ ∈ (⊤ : X.left.Opens) from trivial)
  have hpt : ∀ v : TB k (E₂ κ) ⟶ X, homB (aug₂ k κ) ≫ v = homB (aug₂ k κ) ≫ u →
      ∃ ψ hψ, pt (B := E₂ κ) hV ψ hψ = v := fun v hv ↦ by
    refine exists_pt hV v (range_subset_of_thickening (aug₂ k κ) surjective_aug₂ sqZero_aug₂ v ?_)
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum κ) p p₀
    rw [hv]
    exact hqV
  obtain ⟨ψ, hψ, rfl⟩ := hpt u rfl
  obtain ⟨ψ', hψ', rfl⟩ := hpt _ h0.symm
  rw [homB_pt, homB_pt] at h₁ h₂
  have e₁ := pt_injective hV h₁
  have e₂ := pt_injective hV h₂
  have : ψ = ψ' := by
    ext r
    · simpa [pr₁] using congrArg (fun f : Γ(X.left, V) →+* E₁ κ ↦ (f r).fst) e₁
    · simpa [pr₁] using congrArg (fun f : Γ(X.left, V) →+* E₁ κ ↦ (f r).snd) e₁
    · simpa [pr₂] using congrArg (fun f : Γ(X.left, V) →+* E₁ κ ↦ (f r).snd) e₂
  subst this
  rfl

variable {G : Over (Spec (CommRingCat.of k))} [GrpObj G] [IsCommMonObj G]

variable (k) in
/-- The operator `s_t : G(κ[ε]) → G(κ[ε])` induced by `ε ↦ tε`. -/
def sOp (t : κ) (w : TB k (E₁ κ) ⟶ G) : TB k (E₁ κ) ⟶ G := homB (scal k t) ≫ w

omit [GrpObj G] [IsCommMonObj G] in
lemma homB_scal_comp (t : κ) (w : TB k (E₁ κ) ⟶ G) : homB (scal k t) ≫ w = sOp k t w := rfl

omit [GrpObj G] [IsCommMonObj G] in
lemma aug_sOp (t : κ) (w : TB k (E₁ κ) ⟶ G) : homB (aug k κ) ≫ sOp k t w = homB (aug k κ) ≫ w := by
  rw [sOp, ← Category.assoc, homB_comp, aug_comp_scal]

omit [GrpObj G] [IsCommMonObj G] in
lemma sOp_sOp (t t' : κ) (w : TB k (E₁ κ) ⟶ G) : sOp k t (sOp k t' w) = sOp k (t * t') w := by
  rw [sOp, sOp, sOp, ← Category.assoc, homB_comp, scal_comp_scal]

omit [GrpObj G] [IsCommMonObj G] in
lemma sOp_one (w : TB k (E₁ κ) ⟶ G) : sOp k (1 : κ) w = w := by
  rw [sOp, scal_one, homB_id, Category.id_comp]

lemma sOp_zero {w : TB k (E₁ κ) ⟶ G} (hw : homB (aug k κ) ≫ w = 1) : sOp k (0 : κ) w = 1 := by
  rw [sOp, scal_zero, ← homB_comp, Category.assoc, hw, comp_one]

lemma sOp_add [Nontrivial κ] [Subsingleton (PrimeSpectrum κ)] {w : TB k (E₁ κ) ⟶ G}
    (hw : homB (aug k κ) ≫ w = 1) (t t' : κ) :
    sOp k (t + t') w = sOp k t w * sOp k t' w := by
  have key : homB (phi k t t') ≫ w =
      homB (in₁ k κ) ≫ sOp k t w * homB (in₂ k κ) ≫ sOp k t' w := by
    apply eq_of_pr_eq
    · rw [comp_mul, homB_comp_assoc, homB_comp_assoc, ← Category.assoc, homB_comp, pr₁_comp_phi,
        pr₁_comp_in₁, pr₁_comp_in₂, scal_one, homB_id, Category.id_comp]
      have hz : homB (scal k (0 : κ)) ≫ sOp k t' w = 1 := sOp_zero (by rw [aug_sOp, hw])
      rw [hz, _root_.mul_one]
      rfl
    · rw [comp_mul, homB_comp_assoc, homB_comp_assoc, ← Category.assoc, homB_comp, pr₂_comp_phi,
        pr₂_comp_in₁, pr₂_comp_in₂, scal_one, homB_id, Category.id_comp]
      have hz : homB (scal k (0 : κ)) ≫ sOp k t w = 1 := sOp_zero (by rw [aug_sOp, hw])
      rw [hz, _root_.one_mul]
      rfl
  have := congrArg (homB (sm k κ) ≫ ·) key
  rw [comp_mul, homB_comp_assoc, homB_comp_assoc, ← Category.assoc, homB_comp, sm_comp_phi,
    sm_comp_in₁, sm_comp_in₂, scal_one, homB_id, Category.id_comp, Category.id_comp] at this
  exact this

lemma sOp_natCast [Nontrivial κ] [Subsingleton (PrimeSpectrum κ)] {w : TB k (E₁ κ) ⟶ G}
    (hw : homB (aug k κ) ≫ w = 1) (n : ℕ) :
    sOp k (n : κ) w = w ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, sOp_zero hw, pow_zero]
  | succ n ih => rw [Nat.cast_succ, sOp_add hw, ih, sOp_one, pow_succ]

variable [Nontrivial κ] [Subsingleton (PrimeSpectrum κ)]

/-- **`v ↦ vⁿ` is bijective on the tangent vectors at the identity** (`n` invertible in `κ`). -/
lemma pow_bijective_tan₀ {n : ℕ} (hn : IsUnit (n : κ)) :
    (∀ w w' : TB k (E₁ κ) ⟶ G, homB (aug k κ) ≫ w = 1 → homB (aug k κ) ≫ w' = 1 →
      w ^ n = w' ^ n → w = w') ∧
    ∀ w' : TB k (E₁ κ) ⟶ G, homB (aug k κ) ≫ w' = 1 →
      ∃ w, homB (aug k κ) ≫ w = 1 ∧ w ^ n = w' := by
  set a : κ := ↑hn.unit⁻¹
  have inv : ∀ w : TB k (E₁ κ) ⟶ G, homB (aug k κ) ≫ w = 1 → sOp k a (w ^ n) = w :=
    fun w hw ↦ by rw [← sOp_natCast hw, sOp_sOp, hn.val_inv_mul, sOp_one]
  refine ⟨fun w w' hw hw' h ↦ by rw [← inv w hw, ← inv w' hw', h], fun w' hw' ↦ ?_⟩
  have hw : homB (aug k κ) ≫ sOp k a w' = 1 := by rw [aug_sOp, hw']
  refine ⟨sOp k a w', hw, ?_⟩
  rw [← sOp_natCast hw, sOp_sOp, hn.mul_val_inv, sOp_one]

/-- **`v ↦ vⁿ` is a bijection from the tangent vectors at `x` to those at `xⁿ`**, for every
point `x : Spec κ ⟶ G` and `n` invertible in `κ`. -/
theorem bijective_pow_tangent {n : ℕ} (hn : IsUnit (n : κ)) (x : TB k κ ⟶ G) :
    (∀ v v' : TB k (E₁ κ) ⟶ G, homB (aug k κ) ≫ v = x → homB (aug k κ) ≫ v' = x →
      v ^ n = v' ^ n → v = v') ∧
    ∀ y : TB k (E₁ κ) ⟶ G, homB (aug k κ) ≫ y = x ^ n →
      ∃ v, homB (aug k κ) ≫ v = x ∧ v ^ n = y := by
  set c : TB k (E₁ κ) ⟶ G := homB (incl k κ) ≫ x
  have hc : homB (aug k κ) ≫ c = x := by
    rw [← Category.assoc, homB_comp, aug_comp_incl, homB_id, Category.id_comp]
  have hcn : homB (aug k κ) ≫ c ^ n = x ^ n := by rw [comp_pow, hc]
  obtain ⟨hinj, hsurj⟩ := pow_bijective_tan₀ (G := G) hn
  refine ⟨fun v v' hv hv' h ↦ ?_, fun y hy ↦ ?_⟩
  · have e := hinj (v * c⁻¹) (v' * c⁻¹) (by rw [comp_mul, GrpObj.comp_inv, hv, hc, mul_inv_cancel])
      (by rw [comp_mul, GrpObj.comp_inv, hv', hc, mul_inv_cancel]) (by rw [mul_pow, mul_pow, h])
    simpa using e
  · obtain ⟨w, hw, hwn⟩ := hsurj (y * (c ^ n)⁻¹)
      (by rw [comp_mul, GrpObj.comp_inv, hy, hcn, mul_inv_cancel])
    refine ⟨w * c, by rw [comp_mul, hw, hc, _root_.one_mul], ?_⟩
    rw [mul_pow, hwn, inv_mul_cancel_right]

end Tangent

/-! ### `[n]` is étale -/

section Etale

lemma pt_congr {X : Over (Spec (CommRingCat.of k))} {V : X.left.Opens} (hV : IsAffineOpen V)
    {B : Type u} [CommRing B] [Algebra (R₀ k) B]
    {ψ ψ' : Γ(X.left, V) →+* B} (h : ψ = ψ') (hψ : ψ.comp (strV V) = algebraMap _ B)
    (hψ' : ψ'.comp (strV V) = algebraMap _ B) : pt hV ψ hψ = pt hV ψ' hψ' := by
  subst h; rfl

lemma range_pt_subset {X : Over (Spec (CommRingCat.of k))} {V : X.left.Opens}
    (hV : IsAffineOpen V) {B : Type u} [CommRing B] [Algebra (R₀ k) B]
    (ψ : Γ(X.left, V) →+* B) (hψ : ψ.comp (strV V) = algebraMap _ B) :
    Set.range (pt hV ψ hψ).left.base ⊆ V := by
  rintro _ ⟨p, rfl⟩
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

lemma surjective_aug {κ : Type u} [CommRing κ] [Algebra (R₀ k) κ] :
    Function.Surjective (aug k κ) := fun r ↦ ⟨inl r, by simp [aug]⟩

lemma sqZero_aug {κ : Type u} [CommRing κ] [Algebra (R₀ k) κ] :
    MatLift.SqZero (CommRingCat.ofHom (aug k κ).toRingHom).hom := by
  intro a b ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [ha]
  · simp [ha, hb]

lemma isUnit_natCast_of {n : ℕ} (hn : (n : k) ≠ 0) (C : Type u) [CommRing C]
    [Algebra (R₀ k) C] : IsUnit (n : C) := by
  set e := Scheme.ΓSpecIso (CommRingCat.of k)
  have h1 : e.inv.hom ((n : k)⁻¹) * (n : (R₀ k)) = 1 := by
    rw [← map_natCast e.inv.hom, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have h2 := congrArg (algebraMap (R₀ k) C) h1
  rw [map_mul, map_natCast, map_one] at h2
  exact IsUnit.of_mul_eq_one_right _ h2

variable {G : Over (Spec (CommRingCat.of k))} [GrpObj G] [IsCommMonObj G]

/-- **Multiplication by `n` on a smooth commutative group scheme over `k` is étale** if `n` is
invertible in `k`. -/
theorem etale_pow [Smooth G.hom] {n : ℕ} (hn : (n : k) ≠ 0) :
    Etale ((𝟙 G : G ⟶ G) ^ n).left := by
  set N : G ⟶ G := (𝟙 G : G ⟶ G) ^ n
  have hN : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ G), v ≫ N = v ^ n := fun v ↦ by
    rw [comp_pow, Category.comp_id]
  rw [HasRingHomProperty.iff_appLE (P := @Etale)]
  intro U V e
  letI : Algebra (R₀ k) Γ(G.left, U) := (strV (X := G) U).toAlgebra
  letI : Algebra (R₀ k) Γ(G.left, V) := (strV (X := G) V).toAlgebra
  letI : Algebra Γ(G.left, U) Γ(G.left, V) := (N.left.appLE U V e).hom.toAlgebra
  haveI : IsScalarTower (R₀ k) Γ(G.left, U) Γ(G.left, V) :=
    IsScalarTower.of_algebraMap_eq' (strV_comp N e).symm
  have hsm := (HasRingHomProperty.iff_appLE (P := @Smooth)).mp ‹Smooth G.hom›
  haveI : Algebra.Smooth (R₀ k) Γ(G.left, V) :=
    hsm ⟨⊤, isAffineOpen_top _⟩ V (by rw [Scheme.Hom.preimage_top]; exact le_top)
  haveI : Algebra.Smooth (R₀ k) Γ(G.left, U) :=
    hsm ⟨⊤, isAffineOpen_top _⟩ U (by rw [Scheme.Hom.preimage_top]; exact le_top)
  change Algebra.Etale Γ(G.left, U) Γ(G.left, V)
  refine etale_of_bijective_lift (R₀ k) _ _ fun m _ ↦ ?_
  set κ := Γ(G.left, V) ⧸ m
  haveI : Nontrivial κ := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top ‹_›)
  haveI : Subsingleton (PrimeSpectrum κ) := ⟨fun p q ↦ by
    letI := Ideal.Quotient.field m
    exact Subsingleton.elim (α := PrimeSpectrum κ) p q⟩
  have hnκ : IsUnit (n : κ) := isUnit_natCast_of hn κ
  -- the point `x` of `G` given by `m`
  have hx : (Ideal.Quotient.mk m).comp (strV (X := G) V) =
      algebraMap (R₀ k) κ := rfl
  set x : TB k κ ⟶ G := pt V.2 (Ideal.Quotient.mk m) hx
  -- lifts are tangent vectors at `x`
  have hlift : ∀ ψ : Γ(G.left, V) →ₐ[R₀ k] E₁ κ,
      (∀ b, (ψ b).fst = Ideal.Quotient.mk m b) →
        homB (aug k κ) ≫ pt V.2 ψ.toRingHom ψ.comp_algebraMap = x := fun ψ hψ ↦ by
    rw [homB_pt]
    exact pt_congr _ (RingHom.ext hψ) _ _
  have hcomp : ∀ ψ : Γ(G.left, V) →ₐ[R₀ k] E₁ κ,
      pt V.2 ψ.toRingHom ψ.comp_algebraMap ≫ N =
        pt U.2 (ψ.comp (IsScalarTower.toAlgHom _ Γ(G.left, U) Γ(G.left, V))).toRingHom
          (AlgHom.comp_algebraMap (ψ.comp (IsScalarTower.toAlgHom _ _ _))) := fun ψ ↦ by
    rw [pt_comp V.2 N U.2 e]
    rfl
  obtain ⟨hinj, hsurj⟩ := bijective_pow_tangent (G := G) hnκ x
  refine ⟨fun ψ ψ' hψ hψ' h ↦ ?_, fun ψ' hψ' ↦ ?_⟩
  · have e1 := hinj _ _ (hlift ψ hψ) (hlift ψ' hψ') (by
      rw [← hN, ← hN, hcomp, hcomp]; congr 1; exact congrArg AlgHom.toRingHom h)
    exact AlgHom.coe_ringHom_injective (pt_injective V.2 e1)
  · have hy : homB (aug k κ) ≫ pt U.2 ψ'.toRingHom ψ'.comp_algebraMap = x ^ n := by
      rw [← hN, pt_comp V.2 N U.2 e, homB_pt]
      exact pt_congr _ (RingHom.ext hψ') _ _
    obtain ⟨v, hv, hvn⟩ := hsurj _ hy
    obtain ⟨ψ, hψ, rfl⟩ := exists_pt V.2 v (range_subset_of_thickening (aug k κ) surjective_aug
      sqZero_aug v (by rw [hv]; exact range_pt_subset _ _ _))
    let ψA : Γ(G.left, V) →ₐ[R₀ k] E₁ κ :=
      { ψ with commutes' := fun r ↦ congrArg (fun f ↦ f r) hψ }
    have hψA : pt V.2 ψA.toRingHom ψA.comp_algebraMap = pt V.2 ψ hψ := rfl
    refine ⟨ψA, fun b ↦ ?_, ?_⟩
    · rw [← hψA, homB_pt] at hv
      have := pt_injective V.2 hv
      exact congrArg (fun f ↦ f b) this
    · rw [← hψA, ← hN, hcomp] at hvn
      exact AlgHom.coe_ringHom_injective (pt_injective U.2 hvn)

/-- **Multiplication by `n` on a proper smooth connected commutative group scheme over `k` is
surjective** if `n` is invertible in `k` (`[n]` is étale, hence open, and proper, hence closed). -/
theorem surjective_pow [Smooth G.hom] [IsProper G.hom] [ConnectedSpace G.left] {n : ℕ}
    (hn : (n : k) ≠ 0) : Surjective ((𝟙 G : G ⟶ G) ^ n).left := by
  set N : G ⟶ G := (𝟙 G : G ⟶ G) ^ n
  haveI : Etale N.left := etale_pow hn
  haveI : UniversallyClosed (N.left ≫ G.hom) := by rw [Over.w N]; infer_instance
  haveI : UniversallyClosed N.left := UniversallyClosed.of_comp_of_isSeparated N.left G.hom
  refine ⟨fun y ↦ ?_⟩
  have hcl : IsClopen (Set.range N.left.base) :=
    ⟨N.left.isClosedMap.isClosed_range, N.left.isOpenMap.isOpen_range⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty G.left)
  have : y ∈ Set.range N.left.base := by rw [hcl.eq_univ ⟨_, z, rfl⟩]; trivial
  exact this

/-- **Divisibility of the `K`-points** of a proper smooth connected commutative group scheme
over `k`, for `K` algebraically closed and `n` invertible in `k`: every `K`-point is an `n`-th
power. -/
theorem exists_pow_eq [Smooth G.hom] [IsProper G.hom] [ConnectedSpace G.left] {n : ℕ}
    (hn : (n : k) ≠ 0) (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (y : Over.mk t ⟶ G) :
    ∃ x : Over.mk t ⟶ G, x ^ n = y := by
  set N : G ⟶ G := (𝟙 G : G ⟶ G) ^ n
  have hN : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ G), v ≫ N = v ^ n := fun v ↦ by
    rw [comp_pow, Category.comp_id]
  haveI : Etale N.left := etale_pow hn
  haveI : Surjective N.left := surjective_pow hn
  haveI : UniversallyClosed (N.left ≫ G.hom) := by rw [Over.w N]; infer_instance
  haveI : UniversallyClosed N.left := UniversallyClosed.of_comp_of_isSeparated N.left G.hom
  let P := pullback (C := Scheme.{u}) N.left y.left
  let s' : P ⟶ Spec (CommRingCat.of K) := pullback.snd N.left y.left
  haveI : Surjective s' := MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
  haveI : LocallyOfFiniteType s' :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  haveI : QuasiCompact s' := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace s'
  obtain ⟨q, -⟩ := s'.surjective (IsLocalRing.closedPoint K)
  obtain ⟨p, -, hp⟩ := (isClosed_univ (X := P)).exists_closed_singleton ⟨q, Set.mem_univ _⟩
  set σ := pointOfClosedPoint s' p hp
  have hσ : σ ≫ s' = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hxN : (σ ≫ pullback.fst N.left y.left) ≫ N.left = y.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ y.left) hσ).trans (Category.id_comp _)
  refine ⟨Over.homMk (σ ≫ pullback.fst N.left y.left) ?_, ?_⟩
  · change (σ ≫ pullback.fst N.left y.left) ≫ G.hom = t
    have := congrArg (· ≫ G.hom) hxN
    simp only [Category.assoc, Over.w N] at this ⊢
    exact this.trans (Over.w y)
  · rw [← hN]
    exact Over.OverMorphism.ext hxN

end Etale

end CurvesJacobian.GrpEtale
