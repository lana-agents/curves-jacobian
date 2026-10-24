/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Order

/-!
# The topology on the `L`-points of a scheme

For a scheme `X` and a topological field `L`, the set `X(L) = (Spec L ⟶ X)` carries the coarsest
topology for which, for every open `U ⊆ X` and every section `a ∈ Γ(X, U)`, the set of points
landing in `U` is open and `x ↦ a(x)` is continuous on it.

* `CurvesJacobian.PointTopology.ev x U h : Γ(X, U) →+* R`: evaluation of sections at a point
  `x : Spec R ⟶ X` with `x⁻¹ U = ⊤`;
* `ev_comp`, `ev_specMap_comp`, `ev_res`: naturality;
* `eq_specMap_ev_fromSpec`, `ext_of_ev`: a point landing in an affine open `U` is determined by
  its evaluation `Γ(X, U) → R`; `ev_specMap_fromSpec` (every ring map arises);
* `lands_basicOpen_iff`: for a field `K`, `x` lands in `D(r)` iff `r(x) ≠ 0`;
* the topology `pointTopology`, `continuous_comp` (morphisms of schemes induce continuous maps)
  and `tendsto_iff` (convergence is convergence of all evaluations).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Topology Filter

noncomputable section

namespace CurvesJacobian.PointTopology

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- **Evaluation of sections at a point**: for `x : Spec R ⟶ X` with `x⁻¹ U = Spec R`, the ring
map `Γ(X, U) → Γ(Spec R, ⊤) ≅ R`. -/
def ev (x : Spec R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom).hom

lemma lands_comp {x : Spec R ⟶ X} {f : X ⟶ Y} {V : Y.Opens} {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V :=
  fun _ _ ↦ hUV (h trivial)

lemma lands_specMap_comp {x : Spec R ⟶ X} (φ : R ⟶ S) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (Spec.map φ ≫ x) ⁻¹ᵁ U :=
  fun _ _ ↦ h trivial

lemma lands_mono {x : Spec R ⟶ X} {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ x ⁻¹ᵁ V :=
  fun _ hp ↦ hUV (h hp)

/-- Naturality of `ev` in the scheme. -/
lemma ev_comp (x : Spec R ⟶ X) (f : X ⟶ Y) {V : Y.Opens} {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(Y, V)) :
    ev (x ≫ f) V (lands_comp hUV h) b = ev x U h (f.appLE V U hUV b) := by
  simp only [ev, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- Restriction of sections. -/
lemma ev_res (x : Spec R ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, V)) :
    ev x V (lands_mono hUV h) a = ev x U h (X.presheaf.map (homOfLE hUV).op a) := by
  simp only [ev, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- Naturality of `ev` in the ring. -/
lemma ev_specMap_comp (x : Spec R ⟶ X) (φ : R ⟶ S) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a : Γ(X, U)) : ev (Spec.map φ ≫ x) U (lands_specMap_comp φ h) a = φ (ev x U h a) := by
  have e0 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop := rfl
  have e1 : (Spec.map φ ≫ x).appLE U ⊤ (lands_specMap_comp φ h) =
      x.appLE U ⊤ h ≫ (Spec.map φ).appTop := by
    rw [← e0]
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map φ) x U ⊤ ⊤ h le_top).symm
  simp only [ev, e1, Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]

/-- `Spec R ⟶ Spec Γ(Spec R, ⊤)` from `ΓSpecIso`. -/
lemma isAffineOpen_top_fromSpec_Spec :
    (isAffineOpen_top (Spec R)).fromSpec = Spec.map (Scheme.ΓSpecIso R).inv := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- **A point landing in an affine open `U` is determined by its evaluation on `Γ(X, U)`.** -/
lemma eq_specMap_ev_fromSpec (x : Spec R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : x = Spec.map (CommRingCat.ofHom (ev x U h)) ≫ hU.fromSpec := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec R)) h
  rw [isAffineOpen_top_fromSpec_Spec] at e
  have e2 : CommRingCat.ofHom (ev x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom := rfl
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id]
  exact (Category.id_comp x).symm

lemma ext_of_ev {x y : Spec R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : ∀ a, ev x U hx a = ev y U hy a) : x = y := by
  rw [eq_specMap_ev_fromSpec x hU hx, eq_specMap_ev_fromSpec y hU hy]
  congr 2
  ext a
  exact e a

lemma lands_specMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) ⟶ R) :
    ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U :=
  lands_specMap_comp φ (by rw [hU.fromSpec_preimage_self])

lemma ev_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    ev hU.fromSpec U (by rw [hU.fromSpec_preimage_self]) a = a := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hsub : (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h0).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  have key : hU.fromSpec.appLE U ⊤ h0 ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc, hsub, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
  change (hU.fromSpec.appLE U ⊤ h0 ≫ (Scheme.ΓSpecIso Γ(X, U)).hom) a = a
  rw [key, CommRingCat.id_apply]

/-- **Every ring map `Γ(X, U) → R` is the evaluation of a point** (`U` affine). -/
lemma ev_specMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) ⟶ R) (a : Γ(X, U)) :
    ev (Spec.map φ ≫ hU.fromSpec) U (lands_specMap_fromSpec hU φ) a = φ a := by
  rw [ev_specMap_comp _ φ (by rw [hU.fromSpec_preimage_self]), ev_fromSpec]

/-- For a point with values in a field, landing in `D(r)` means `r(x) ≠ 0`. -/
lemma lands_basicOpen_iff {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (r : Γ(X, U)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen r ↔ ev x U h r ≠ 0 := by
  have e : x ⁻¹ᵁ X.basicOpen r = (Spec (CommRingCat.of K)).basicOpen (x.appLE U ⊤ h r) := by
    rw [Scheme.basicOpen_appLE]
    exact (top_inf_eq _).symm
  rw [e, basicOpen_eq_of_affine']
  change ⊤ ≤ PrimeSpectrum.basicOpen (ev x U h r) ↔ _
  constructor
  · intro H h0
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have := H (Set.mem_univ p)
    simp [h0] at this
  · intro H p _
    simp only [PrimeSpectrum.mem_basicOpen]
    rw [Ideal.eq_bot_of_prime p.asIdeal]
    simpa using H

/-! ### The topology -/

variable (L : Type u) [Field L] [TopologicalSpace L] (X)

/-- The subbasic open sets `{x ∈ U(L) | a(x) ∈ O}`. -/
def subbasis : Set (Set (Spec (CommRingCat.of L) ⟶ X)) :=
  {s | ∃ (U : X.Opens) (a : Γ(X, U)) (O : Set L), IsOpen O ∧
    s = {x : Spec (CommRingCat.of L) ⟶ X | ∃ h : ⊤ ≤ x ⁻¹ᵁ U, ev x U h a ∈ O}}

/-- **The topology on `X(L)`**, generated by the sets `{x ∈ U(L) | a(x) ∈ O}`. -/
instance pointTopology : TopologicalSpace (Spec (CommRingCat.of L) ⟶ X) :=
  .generateFrom (subbasis X L)

variable {L X}

lemma isOpen_setOf_ev (U : X.Opens) (a : Γ(X, U)) {O : Set L} (hO : IsOpen O) :
    IsOpen {x : Spec (CommRingCat.of L) ⟶ X | ∃ h : ⊤ ≤ x ⁻¹ᵁ U, ev x U h a ∈ O} :=
  TopologicalSpace.GenerateOpen.basic _ ⟨U, a, O, hO, rfl⟩

lemma isOpen_setOf_lands (U : X.Opens) :
    IsOpen {x : Spec (CommRingCat.of L) ⟶ X | ⊤ ≤ x ⁻¹ᵁ U} := by
  convert isOpen_setOf_ev U 0 isOpen_univ using 1
  ext x
  simp

/-- **Morphisms of schemes induce continuous maps on `L`-points.** -/
lemma continuous_comp (f : X ⟶ Y) :
    Continuous fun x : Spec (CommRingCat.of L) ⟶ X ↦ x ≫ f := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro s ⟨V, b, O, hO, rfl⟩
  convert isOpen_setOf_ev (f ⁻¹ᵁ V) (f.app V b) hO using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hb⟩
    refine ⟨h, ?_⟩
    rwa [ev_comp x f le_rfl h, Scheme.Hom.appLE_eq_app] at hb
  · rintro ⟨h, hb⟩
    refine ⟨lands_comp le_rfl h, ?_⟩
    rwa [ev_comp x f le_rfl h, Scheme.Hom.appLE_eq_app]

/-- **Convergence in `X(L)`**: `y → x` iff for every open `U ∋ x`, `a ∈ Γ(X, U)` and open
`O ∋ a(x)`, eventually `y` lands in `U` with `a(y) ∈ O`. -/
lemma tendsto_iff {α : Type*} {l : Filter α} {y : α → (Spec (CommRingCat.of L) ⟶ X)}
    {x : Spec (CommRingCat.of L) ⟶ X} :
    Tendsto y l (𝓝 x) ↔ ∀ (U : X.Opens) (a : Γ(X, U)) (O : Set L), IsOpen O →
      ∀ h : ⊤ ≤ x ⁻¹ᵁ U, ev x U h a ∈ O → ∀ᶠ i in l, ∃ h : ⊤ ≤ y i ⁻¹ᵁ U, ev (y i) U h a ∈ O := by
  rw [TopologicalSpace.nhds_generateFrom, tendsto_iInf]
  simp only [tendsto_iInf, tendsto_principal]
  constructor
  · intro H U a O hO h ha
    exact H {x' | ∃ h : ⊤ ≤ x' ⁻¹ᵁ U, ev x' U h a ∈ O} ⟨⟨h, ha⟩, U, a, O, hO, rfl⟩
  · rintro H s ⟨hxs, U, a, O, hO, rfl⟩
    obtain ⟨h, ha⟩ := hxs
    exact H U a O hO h ha

end CurvesJacobian.PointTopology
