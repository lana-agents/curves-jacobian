/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Pullback

/-!
# Gluing sheaves of modules along an open cover (Zariski descent)

This file is generic (a candidate for upstreaming). Let `Y` be a scheme, `V i` (`i : ι`) opens of
`Y` and `M i` sheaves of `𝒪_Y`-modules, of which only the restrictions to `V i` matter. A
*gluing datum* (`GlueData`) consists of `𝒪`-linear maps `ψ i j : Γ(M i, W) ⟶ Γ(M j, W)` for all
opens `W ⊆ V i ∩ V j`, compatible with restrictions, with `ψ i i = id` and the cocycle condition
`ψ j k ∘ ψ i j = ψ i k` on `W ⊆ V i ∩ V j ∩ V k`. (This is the section-wise form of a descent
datum for the Zariski covering `{V i ⊆ Y}`, Stacks, Tag 00AK / 04TP for sheaves on spaces.)

We construct the glued sheaf of modules `D.glued`: its sections over `W` are families
`(s i ∈ Γ(M i, V i ∩ W))_i` with `ψ i j (s i) = s j` on `V i ∩ V j ∩ W` (`GlueData.sec`); here
`V i ∩ W` is written as `(V i).ι ''ᵁ (V i).ι ⁻¹ᵁ W` (`rV`), the opens over which the sections
of the restriction `(M i)|_{V i}` live.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme

variable {Y : Scheme.{u}}

/-- Restriction of sections of a sheaf of modules. -/
abbrev rs (N : Y.Modules) {U W : Y.Opens} (h : W ≤ U) (m : Γ(N, U)) : Γ(N, W) :=
  N.presheaf.map (homOfLE h).op m

/-- Restriction of functions. -/
abbrev rr {U W : Y.Opens} (h : W ≤ U) (r : Γ(Y, U)) : Γ(Y, W) :=
  Y.presheaf.map (homOfLE h).op r

lemma rs_rs (N : Y.Modules) {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (m : Γ(N, U)) :
    rs N h' (rs N h m) = rs N (h'.trans h) m := by
  rw [rs, rs, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma rs_self (N : Y.Modules) {U : Y.Opens} (h : U ≤ U) (m : Γ(N, U)) : rs N h m = m := by
  rw [rs, show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma rs_smul (N : Y.Modules) {U W : Y.Opens} (h : W ≤ U) (r : Γ(Y, U)) (m : Γ(N, U)) :
    rs N h (r • m) = rr h r • rs N h m :=
  Scheme.Modules.map_smul N (homOfLE h) r m

lemma rr_rr {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (r : Γ(Y, U)) :
    rr h' (rr h r) = rr (h'.trans h) r := by
  rw [rr, rr, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma rr_self {U : Y.Opens} (h : U ≤ U) (r : Γ(Y, U)) : rr h r = r := by
  rw [rr, show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma rs_bijective_of_eq (N : Y.Modules) {U W : Y.Opens} (e : W = U) :
    Function.Bijective (rs N e.le) := by
  subst e
  have : rs N (le_refl W) = id := funext (rs_self N _)
  rw [this]
  exact Function.bijective_id

lemma rr_bijective_of_eq {U W : Y.Opens} (e : W = U) :
    Function.Bijective (rr (Y := Y) e.le) := by
  subst e
  have : rr (Y := Y) (le_refl W) = id := funext (rr_self _)
  rw [this]
  exact Function.bijective_id

variable {ι : Type u} (V : ι → Y.Opens)

/-- `rV V i W = V i ∩ W`, written as the image of the preimage of `W` in `V i`. -/
def rV (i : ι) (W : Y.Opens) : Y.Opens := (V i).ι ''ᵁ ((V i).ι ⁻¹ᵁ W)

lemma rV_eq (i : ι) (W : Y.Opens) : rV V i W = V i ⊓ W := by
  rw [rV, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma rV_le_V (i : ι) (W : Y.Opens) : rV V i W ≤ V i := by
  rw [rV_eq]; exact inf_le_left

lemma rV_le (i : ι) (W : Y.Opens) : rV V i W ≤ W := by
  rw [rV_eq]; exact inf_le_right

lemma rV_mono (i : ι) {W W' : Y.Opens} (h : W' ≤ W) : rV V i W' ≤ rV V i W := by
  rw [rV_eq, rV_eq]; exact inf_le_inf_left _ h

lemma le_rV (i : ι) {U W : Y.Opens} (h₁ : U ≤ V i) (h₂ : U ≤ W) : U ≤ rV V i W := by
  rw [rV_eq]; exact le_inf h₁ h₂

lemma rV_eq_self (i : ι) {W : Y.Opens} (h : W ≤ V i) : rV V i W = W := by
  rw [rV_eq]; exact inf_eq_right.2 h

variable (M : ι → Y.Modules)

/-- Section-wise gluing data for the sheaves `M i` along the opens `V i`. -/
structure GlueData where
  /-- the transition maps -/
  ψ : ∀ (i j : ι) (W : Y.Opens), W ≤ V i → W ≤ V j → Γ(M i, W) →+ Γ(M j, W)
  ψ_smul : ∀ (i j : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (r : Γ(Y, W))
    (m : Γ(M i, W)), ψ i j W hi hj (r • m) = r • ψ i j W hi hj m
  ψ_rs : ∀ (i j : ι) (W W' : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (h : W' ≤ W)
    (m : Γ(M i, W)),
    ψ i j W' (h.trans hi) (h.trans hj) (rs (M i) h m) = rs (M j) h (ψ i j W hi hj m)
  ψ_self : ∀ (i : ι) (W : Y.Opens) (hi : W ≤ V i) (m : Γ(M i, W)), ψ i i W hi hi m = m
  ψ_comp : ∀ (i j k : ι) (W : Y.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k)
    (m : Γ(M i, W)), ψ j k W hj hk (ψ i j W hi hj m) = ψ i k W hi hk m

namespace GlueData

variable {V M} (D : GlueData V M)

/-- The compatibility condition on a family of sections over `W`. -/
def Compat (W : Y.Opens) (s : ∀ i, Γ(M i, rV V i W)) : Prop :=
  ∀ i j, D.ψ i j (rV V i W ⊓ rV V j W) (inf_le_left.trans (rV_le_V V i W))
    (inf_le_right.trans (rV_le_V V j W)) (rs (M i) inf_le_left (s i)) =
      rs (M j) inf_le_right (s j)

/-- The sections of the glued sheaf over `W`. -/
def sec (W : Y.Opens) : AddSubgroup (∀ i, Γ(M i, rV V i W)) where
  carrier := {s | D.Compat W s}
  zero_mem' i j := by
    simp only [Pi.zero_apply, rs, map_zero]
  add_mem' {s t} hs ht i j := by
    simp only [Pi.add_apply, rs, map_add] at hs ht ⊢
    rw [hs i j, ht i j]
  neg_mem' {s} hs i j := by
    simp only [Pi.neg_apply, rs, map_neg] at hs ⊢
    rw [hs i j]

lemma compat (W : Y.Opens) (s : D.sec W) (i j : ι) :
    D.ψ i j (rV V i W ⊓ rV V j W) (inf_le_left.trans (rV_le_V V i W))
      (inf_le_right.trans (rV_le_V V j W)) (rs (M i) inf_le_left (s.1 i)) =
      rs (M j) inf_le_right (s.1 j) :=
  s.2 i j

/-- A general form of the compatibility: on any `U ⊆ V i ∩ V j ∩ W`. -/
lemma compat' {W : Y.Opens} (s : D.sec W) (i j : ι) (U : Y.Opens) (hi : U ≤ V i)
    (hj : U ≤ V j) (hUi : U ≤ rV V i W) (hUj : U ≤ rV V j W) :
    D.ψ i j U hi hj (rs (M i) hUi (s.1 i)) = rs (M j) hUj (s.1 j) := by
  have hU : U ≤ rV V i W ⊓ rV V j W := le_inf hUi hUj
  have := congrArg (rs (M j) hU) (D.compat W s i j)
  rw [← D.ψ_rs, rs_rs, rs_rs] at this
  exact this

instance (W : Y.Opens) : SMul Γ(Y, W) (D.sec W) where
  smul r s := ⟨fun i ↦ rr (rV_le V i W) r • s.1 i, fun i j ↦ by
    rw [rs_smul, rs_smul, D.ψ_smul, D.compat W s i j, rr_rr, rr_rr]⟩

lemma smul_coe (W : Y.Opens) (r : Γ(Y, W)) (s : D.sec W) (i : ι) :
    (r • s).1 i = rr (rV_le V i W) r • s.1 i :=
  rfl

instance (W : Y.Opens) : Module Γ(Y, W) (D.sec W) where
  one_smul s := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) 1 • s.1 i = s.1 i
    rw [rr, map_one, one_smul]
  mul_smul r r' s := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) (r * r') • s.1 i = rr (rV_le V i W) r • rr (rV_le V i W) r' • s.1 i
    rw [rr, map_mul, mul_smul]
  smul_zero r := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) r • (0 : Γ(M i, rV V i W)) = 0
    rw [smul_zero]
  smul_add r s t := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) r • (s.1 i + t.1 i) =
      rr (rV_le V i W) r • s.1 i + rr (rV_le V i W) r • t.1 i
    rw [smul_add]
  add_smul r r' s := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) (r + r') • s.1 i =
      rr (rV_le V i W) r • s.1 i + rr (rV_le V i W) r' • s.1 i
    rw [rr, map_add, add_smul]
  zero_smul s := Subtype.ext <| funext fun i ↦ by
    change rr (rV_le V i W) 0 • s.1 i = 0
    rw [rr, map_zero, zero_smul]

/-- Restriction of glued sections. -/
def restrictSec {W W' : Y.Opens} (h : W' ≤ W) : D.sec W →+ D.sec W' where
  toFun s := ⟨fun i ↦ rs (M i) (rV_mono V i h) (s.1 i), fun i j ↦ by
    rw [rs_rs, rs_rs]
    exact D.compat' s i j _ _ _ _ _⟩
  map_zero' := Subtype.ext <| funext fun i ↦ map_zero _
  map_add' s t := Subtype.ext <| funext fun i ↦ map_add _ _ _

lemma restrictSec_coe {W W' : Y.Opens} (h : W' ≤ W) (s : D.sec W) (i : ι) :
    (D.restrictSec h s).1 i = rs (M i) (rV_mono V i h) (s.1 i) :=
  rfl

/-- The glued presheaf of abelian groups. -/
def pre : (Y.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (D.sec W.unop)
  map f := AddCommGrpCat.ofHom (D.restrictSec f.unop.le)
  map_id W := by
    ext s i
    exact rs_self _ _ _
  map_comp f g := by
    ext s i
    exact (rs_rs _ _ _ _).symm

instance (W : Y.Opensᵒᵖ) : Module (Y.ringCatSheaf.obj.obj W) (D.pre.obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (D.sec W.unop))

/-- The glued presheaf of modules. -/
def preMod : Y.PresheafOfModules :=
  _root_.PresheafOfModules.ofPresheaf D.pre (fun {W W'} f r s ↦ by
    refine Subtype.ext <| funext fun i ↦ ?_
    change rs (M i) _ (rr _ r • s.1 i) = rr _ (rr f.unop.le r) • rs (M i) _ (s.1 i)
    rw [rs_smul, rr_rr, rr_rr])

/-- The sheaf `M i` as a sheaf of abelian groups. -/
abbrev sh (N : Y.Modules) : TopCat.Sheaf Ab.{u} Y := ⟨N.presheaf, N.isSheaf⟩

theorem isSheaf_pre : TopCat.Presheaf.IsSheaf D.pre := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hsf
  -- glue componentwise
  have hc : ∀ i, ∃! t : Γ(M i, rV V i (iSup U)), ∀ a,
      (M i).presheaf.map (homOfLE (rV_mono V i (le_iSup U a))).op t = (sf a).1 i := by
    intro i
    refine (sh (M i)).existsUnique_gluing' (fun a ↦ rV V i (U a)) (rV V i (iSup U))
      (fun a ↦ homOfLE (rV_mono V i (le_iSup U a))) ?_ (fun a ↦ (sf a).1 i) ?_
    · rw [rV_eq, inf_iSup_eq]
      exact iSup_mono fun a ↦ (rV_eq V i (U a)).ge
    · intro a b
      have h := congrArg (fun s : D.sec (U a ⊓ U b) ↦ rs (M i)
        (le_rV V i (inf_le_left.trans (rV_le_V V i _))
          (le_inf (inf_le_left.trans (rV_le V i _)) (inf_le_right.trans (rV_le V i _))))
        (s.1 i)) (hsf a b)
      simp only at h
      change rs (M i) _ ((sf a).1 i) = rs (M i) _ ((sf b).1 i)
      change rs (M i) _ (rs (M i) _ ((sf a).1 i)) = rs (M i) _ (rs (M i) _ ((sf b).1 i)) at h
      rwa [rs_rs, rs_rs] at h
  choose t ht huniq using hc
  have ht' : ∀ i a, rs (M i) (rV_mono V i (le_iSup U a)) (t i) = (sf a).1 i := ht
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun a ↦ Subtype.ext <| funext fun i ↦ ht i a, ?_⟩
  · refine CurvesJacobian.sheaf_eq_of_locally_eq (sh (M j)) _ _ fun x hx ↦ ?_
    obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp (rV_le V i _ hx.1)
    have hW : rV V i (U a) ⊓ rV V j (U a) ≤ rV V i (iSup U) ⊓ rV V j (iSup U) :=
      inf_le_inf (rV_mono V i (le_iSup U a)) (rV_mono V j (le_iSup U a))
    refine ⟨_, hW, ⟨by rw [rV_eq]; exact ⟨(rV_le_V V i _ hx.1), hxa⟩,
      by rw [rV_eq]; exact ⟨(rV_le_V V j _ hx.2), hxa⟩⟩, ?_⟩
    change rs (M j) hW (D.ψ i j _ _ _ (rs (M i) _ (t i))) = rs (M j) hW (rs (M j) _ (t j))
    rw [← D.ψ_rs, rs_rs, rs_rs, ← rs_rs (M i) (rV_mono V i (le_iSup U a)) inf_le_left, ht',
      ← rs_rs (M j) (rV_mono V j (le_iSup U a)) inf_le_right, ht']
    exact D.compat _ (sf a) i j
  · intro s hs
    refine Subtype.ext <| funext fun i ↦ huniq i (s.1 i) fun a ↦ ?_
    exact congrArg (fun s : D.sec (U a) ↦ s.1 i) (hs a)

/-- The glued sheaf of modules. -/
def glued : Y.Modules where
  val := D.preMod
  isSheaf := D.isSheaf_pre

lemma glued_sections (W : Y.Opens) : Γ(D.glued, W) = AddCommGrpCat.of (D.sec W) := rfl

/-! ### Extending a section of `M i` to a glued section -/

/-- A section `m` of `M i` over `U ⊆ V i` gives the glued section `(ψ i j m)_j`. -/
def ext (i : ι) {U : Y.Opens} (hU : U ≤ V i) (m : Γ(M i, U)) : D.sec U :=
  ⟨fun j ↦ D.ψ i j (rV V j U) ((rV_le V j U).trans hU) (rV_le_V V j U)
    (rs (M i) (rV_le V j U) m), fun j k ↦ by
      rw [← D.ψ_rs, ← D.ψ_rs, rs_rs, rs_rs, D.ψ_comp]⟩

lemma ext_coe (i : ι) {U : Y.Opens} (hU : U ≤ V i) (m : Γ(M i, U)) (j : ι) :
    (D.ext i hU m).1 j = D.ψ i j (rV V j U) ((rV_le V j U).trans hU) (rV_le_V V j U)
      (rs (M i) (rV_le V j U) m) :=
  rfl

lemma ext_coe_self (i : ι) {U : Y.Opens} (hU : U ≤ V i) (m : Γ(M i, U)) :
    (D.ext i hU m).1 i = rs (M i) (rV_le V i U) m :=
  D.ψ_self _ _ _ _

lemma ext_smul (i : ι) {U : Y.Opens} (hU : U ≤ V i) (r : Γ(Y, U)) (m : Γ(M i, U)) :
    D.ext i hU (r • m) = r • D.ext i hU m := by
  refine Subtype.ext <| funext fun j ↦ ?_
  change D.ψ i j _ _ _ (rs (M i) _ (r • m)) = rr (rV_le V j U) r • D.ψ i j _ _ _ _
  rw [rs_smul, D.ψ_smul]

lemma restrictSec_ext (i : ι) {U U' : Y.Opens} (hU : U ≤ V i) (h : U' ≤ U)
    (m : Γ(M i, U)) : D.restrictSec h (D.ext i hU m) = D.ext i (h.trans hU) (rs (M i) h m) := by
  refine Subtype.ext <| funext fun j ↦ ?_
  change rs (M j) _ (D.ψ i j _ _ _ _) = D.ψ i j _ _ _ (rs (M i) _ (rs (M i) h m))
  rw [← D.ψ_rs, rs_rs, rs_rs]

/-- Glued sections over `U ⊆ V i` are determined by their `i`-th component. -/
lemma sec_ext_of_le (i : ι) {U : Y.Opens} (hU : U ≤ V i) {s t : D.sec U}
    (h : s.1 i = t.1 i) : s = t := by
  refine Subtype.ext <| funext fun j ↦ ?_
  have hj : rV V j U ≤ rV V i U := le_rV V i ((rV_le V j U).trans hU) (rV_le V j U)
  have hs := D.compat' s i j (rV V j U) ((rV_le V j U).trans hU) (rV_le_V V j U) hj le_rfl
  have ht := D.compat' t i j (rV V j U) ((rV_le V j U).trans hU) (rV_le_V V j U) hj le_rfl
  rw [rs_self] at hs ht
  rw [← hs, ← ht, h]

lemma eq_ext_of_le (i : ι) {U : Y.Opens} (hU : U ≤ V i) (s : D.sec U) :
    s = D.ext i hU (rs (M i) (rV_eq_self V i hU).ge (s.1 i)) := by
  refine D.sec_ext_of_le i hU ?_
  rw [ext_coe_self, rs_rs, rs_self]

/-- The restriction maps of the glued sheaf. -/
lemma glued_res {U U' : Y.Opens} (h : U' ≤ U) (s : D.sec U) :
    Scheme.PresheafOfModules.res ((Scheme.Modules.toPresheafOfModules Y).obj D.glued) h s =
      D.restrictSec h s :=
  rfl

lemma bijective_smul_ext (i : ι) {U : Y.Opens} (hU : U ≤ V i) {b : Γ(M i, U)}
    (hb : (M i).IsBasisOn U b) :
    Function.Bijective (fun r : Γ(Y, U) ↦ (r • D.ext i hU b : D.sec U)) := by
  have hb' := hb (rV_le V i U)
  have hrr := rr_bijective_of_eq (Y := Y) (rV_eq_self V i hU)
  have hcomp : (fun r : Γ(Y, U) ↦ ((r • D.ext i hU b : D.sec U).1 i)) =
      (fun r' ↦ r' • Scheme.PresheafOfModules.res ((Scheme.Modules.toPresheafOfModules Y).obj
        (M i)) (rV_le V i U) b) ∘ rr (rV_eq_self V i hU).le := by
    funext r
    change rr (rV_le V i U) r • (D.ext i hU b).1 i = _
    rw [ext_coe_self]
    rfl
  have hbij : Function.Bijective (fun r : Γ(Y, U) ↦ ((r • D.ext i hU b : D.sec U).1 i)) := by
    rw [hcomp]
    exact hb'.comp hrr
  refine ⟨fun r r' e ↦ hbij.1 (congrArg (fun s : D.sec U ↦ s.1 i) e), fun s ↦ ?_⟩
  obtain ⟨r, hr⟩ := hbij.2 (s.1 i)
  exact ⟨r, D.sec_ext_of_le i hU hr⟩

/-- A basis of `M i` on `U ⊆ V i` extends to a basis of the glued sheaf on `U`. -/
theorem isBasisOn_ext (i : ι) {U : Y.Opens} (hU : U ≤ V i) {b : Γ(M i, U)}
    (hb : (M i).IsBasisOn U b) : D.glued.IsBasisOn U (D.ext i hU b) := by
  intro U' h
  change Function.Bijective (fun r : Γ(Y, U') ↦ r • D.restrictSec h (D.ext i hU b))
  rw [restrictSec_ext]
  exact D.bijective_smul_ext i (h.trans hU) (hb.restrict h)

/-- If the `V i` cover `Y` and every `M i` is invertible on `V i`, the glued sheaf is
invertible. -/
theorem isInvertible_glued (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (hM : ∀ (i : ι) (y : Y), y ∈ V i → ∃ (U : Y.Opens) (b : Γ(M i, U)), U ≤ V i ∧ y ∈ U ∧
      (M i).IsBasisOn U b) :
    D.glued.IsInvertible where
  exists_basis y := by
    obtain ⟨i, hi⟩ := hV y
    obtain ⟨U, b, hU, hyU, hb⟩ := hM i y hi
    exact ⟨U, D.ext i hU b, hyU, D.isBasisOn_ext i hU hb⟩

/-! ### The restriction of the glued sheaf to `V i` -/

lemma image_le_rV (i : ι) (U : (V i).toScheme.Opens) :
    (V i).ι ''ᵁ U ≤ rV V i ((V i).ι ''ᵁ U) :=
  le_rV V i (by
    have := Scheme.Hom.image_le_opensRange (V i).ι U
    rwa [Scheme.Opens.opensRange_ι] at this) le_rfl

lemma natural_aux (i : ι) {W W' : Y.Opens} (hW' : W' ≤ W) (h₁ : W ≤ rV V i W)
    (h₂ : W' ≤ rV V i W') (s : D.sec W) :
    rs (M i) h₂ ((D.restrictSec hW' s).1 i) = rs (M i) hW' (rs (M i) h₁ (s.1 i)) := by
  rw [restrictSec_coe, rs_rs, rs_rs]

/-- The projection from the glued sheaf to `M i`, on `V i`. -/
def projPre (i : ι) :
    (D.glued.restrict (V i).ι).presheaf ⟶ ((M i).restrict (V i).ι).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s ↦ rs (M i) (image_le_rV (V := V) i U.unop) ((s : D.sec _).1 i)
      map_zero' := map_zero _
      map_add' := fun _ _ ↦ map_add _ _ _ }
  naturality U U' f := by
    ext s
    exact D.natural_aux i ((V i).ι.opensFunctor.map f.unop).le (image_le_rV (V := V) i U.unop)
      (image_le_rV (V := V) i U'.unop) s

lemma projPre_app (i : ι) (U : (V i).toScheme.Opens) (s : D.sec ((V i).ι ''ᵁ U)) :
    (D.projPre i).app (op U) s = rs (M i) (image_le_rV (V := V) i U) (s.1 i) :=
  rfl

/-- The projection `(glued)|_{V i} ⟶ (M i)|_{V i}`. -/
def proj (i : ι) : D.glued.restrict (V i).ι ⟶ (M i).restrict (V i).ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (_root_.PresheafOfModules.homMk (D.projPre i) (fun U r s ↦ by
      change rs (M i) (image_le_rV (V := V) i U.unop) ((((V i).ι.appIso U.unop).inv r •
        (show D.sec ((V i).ι ''ᵁ U.unop) from s)).1 i) =
        ((V i).ι.appIso U.unop).inv r • rs (M i) (image_le_rV (V := V) i U.unop)
          ((show D.sec ((V i).ι ''ᵁ U.unop) from s).1 i)
      rw [smul_coe, rs_smul, rr_rr, rr_self]))

lemma proj_app (i : ι) (U : (V i).toScheme.Opens) (s : D.sec ((V i).ι ''ᵁ U)) :
    (D.proj i).app U s = rs (M i) (image_le_rV (V := V) i U) (s.1 i) :=
  rfl

/-- **Gluing**: the restriction of the glued sheaf to `V i` is `M i` restricted to `V i`,
provided `M i` is invertible on `V i`. -/
theorem isIso_proj (i : ι)
    (hM : ∀ y : Y, y ∈ V i → ∃ (U : Y.Opens) (b : Γ(M i, U)), U ≤ V i ∧ y ∈ U ∧
      (M i).IsBasisOn U b) : IsIso (D.proj i) := by
  refine Scheme.Modules.isIso_of_isBasisOn _ fun x ↦ ?_
  obtain ⟨U, b, hU, hxU, hb⟩ := hM ((V i).ι x) x.2
  let U' : (V i).toScheme.Opens := (V i).ι ⁻¹ᵁ U
  have hU' : (V i).ι ''ᵁ U' ≤ U := Scheme.Hom.image_preimage_le _ _
  refine ⟨U', D.ext i (hU'.trans hU) (rs (M i) hU' b), hxU, ?_, ?_⟩
  · exact Scheme.Modules.IsBasisOn.restrict_of
      (D.isBasisOn_ext i (hU'.trans hU) (hb.restrict hU'))
  · refine Scheme.Modules.IsBasisOn.restrict_of ?_
    rw [proj_app, ext_coe_self]
    exact ((hb.restrict _).restrict _).restrict _

/-- The restriction of the glued sheaf to `V i` is isomorphic to that of `M i`. -/
def restrictIso (i : ι)
    (hM : ∀ y : Y, y ∈ V i → ∃ (U : Y.Opens) (b : Γ(M i, U)), U ≤ V i ∧ y ∈ U ∧
      (M i).IsBasisOn U b) :
    D.glued.restrict (V i).ι ≅ (M i).restrict (V i).ι :=
  haveI := D.isIso_proj i hM
  asIso (D.proj i)

end GlueData

end CurvesJacobian.ModulesGlue
