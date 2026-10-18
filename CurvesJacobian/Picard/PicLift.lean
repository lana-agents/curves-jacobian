/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.MatLift
import CurvesJacobian.Picard.SmoothLift
import CurvesJacobian.Picard.ChartCoord
import CurvesJacobian.Picard.CechBaseChange
import CurvesJacobian.Picard.PushoutAlgebra
import CurvesJacobian.Picard.PicMap

/-!
# Lifting invertible sheaves along square-zero thickenings of two-chart schemes

Let `T → S` be a morphism of affine schemes which on global sections is surjective with
square-zero kernel (a first-order thickening `T ⊆ S`), let `Y` be an `S`-scheme and
`Y₀ = Y ×_S T`, with `i : Y₀ → Y` the first projection. Suppose `Y = U ∪ V` with `U`, `V`
affine and `U ∩ V` a basic open of `U` and of `V` (e.g. a curve with the preimages of the
two standard charts of `ℙ¹` under a finite map). Then **every invertible sheaf on `Y₀` lifts
to `Y`**: `i^* : Pic(Y) → Pic(Y₀)` is surjective (`CurvesJacobian.PicLift.surjective_map_fst`).

The obstruction to such a lift lies in `H²(Y, 𝒪 ⊗ ker)`, which vanishes for a covering by two
affines. Concretely (`CurvesJacobian.MatSheaf`, `CurvesJacobian.MatLift`): present `L₀` on the
two charts by idempotent matrices `ē_U`, `ē_V` (generators `ε`, `δ` of the finite projective
modules `Γ(L₀, U₀)`, `Γ(L₀, V₀)` with splittings) and gluing matrices `Φ̄`, `Ψ̄` on the
overlap (`ChartCoord.exists_coord`); lift the idempotents and the gluing matrices; the sheaf of
the lifted matrix data is invertible (rank one lifts) and pulls back to `L₀`
(`MatSheaf.Data.nonempty_iso_pullback_sheaf`). This is the infinitesimal lifting property
behind the smoothness of the Picard scheme of a curve (the obstruction space `H²(C, 𝒪)`
vanishes).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Matrix

universe u

noncomputable section

namespace CurvesJacobian.PicLift

open Scheme ModulesGlue MatSheaf MatLift

/-! ### Generalities -/

lemma isBasisOn_self {X : Scheme.{u}} {L : X.Modules} {W : X.Opens} {b : Γ(L, W)}
    (hb : L.IsBasisOn W b) : Function.Bijective (fun r : Γ(X, W) ↦ r • b) := by
  have := hb (le_refl W)
  have e : Scheme.PresheafOfModules.res ((Scheme.Modules.toPresheafOfModules X).obj L)
      (le_refl W) b = b := rs_self L _ b
  rwa [e] at this

lemma map_sum_of_add {M N : Type*} [AddCommGroup M] [AddCommGroup N] (c : M → N)
    (hc : ∀ x y, c (x + y) = c x + c y) {ι : Type*} (s : Finset ι) (f : ι → M) :
    c (∑ i ∈ s, f i) = ∑ i ∈ s, c (f i) :=
  map_sum (AddMonoidHom.mk' c hc) f s

lemma rs_sum_smul {X : Scheme.{u}} (L : X.Modules) {A B : X.Opens} (h : B ≤ A) {n : ℕ}
    (r : Fin n → Γ(X, A)) (x : Fin n → Γ(L, A)) :
    rs L h (∑ i, r i • x i) = ∑ i, ρ h (r i) • rs L h (x i) := by
  rw [map_sum_of_add (rs L h) (Data.rs_add L h)]
  exact Finset.sum_congr rfl fun i _ ↦ rs_smul L h (r i) (x i)

/-- Sections of an invertible sheaf over an affine open: generators with a splitting. -/
lemma exists_split {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) : ∃ (n : ℕ) (ε : Fin n → Γ(L, U))
      (s : Γ(L, U) →ₗ[Γ(X, U)] (Fin n → Γ(X, U))), ∀ x, ∑ i, s x i • ε i = x := by
  haveI := Scheme.Modules.finite_sections L hU
  haveI := Scheme.Modules.projective_sections L hU
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Γ(X, U) Γ(L, U)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i ↦ π fun j ↦ if i = j then 1 else 0, s, fun x ↦ ?_⟩
  rw [← LinearMap.pi_apply_eq_sum_univ π (s x)]
  exact LinearMap.congr_fun hs x

/-- The idempotent matrix of a splitting. -/
def splitMat {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} {n : ℕ} (ε : Fin n → Γ(L, U))
    (s : Γ(L, U) →ₗ[Γ(X, U)] (Fin n → Γ(X, U))) : Matrix (Fin n) (Fin n) Γ(X, U) :=
  Matrix.of fun i k ↦ s (ε k) i

lemma splitMat_mul {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} {n : ℕ}
    (ε : Fin n → Γ(L, U)) (s : Γ(L, U) →ₗ[Γ(X, U)] (Fin n → Γ(X, U)))
    (hs : ∀ x, ∑ i, s x i • ε i = x) : splitMat ε s * splitMat ε s = splitMat ε s := by
  ext i k
  simp only [splitMat, mul_apply, of_apply]
  have := congrFun (congrArg s (hs (ε k))) i
  rw [map_sum] at this
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-! ### The thickening -/

variable {S T Y : Scheme.{u}} [IsAffine S] [IsAffine T] [Y.Over S] [T.Over S]

section Thickening

variable (hsurj : Function.Surjective (T ↘ S).appTop) (hsq : SqZero (T ↘ S).appTop.hom)

include hsurj in
lemma isClosedImmersion_over : IsClosedImmersion (T ↘ S) :=
  IsClosedImmersion.of_surjective_of_isAffine _ hsurj

include hsurj hsq in
lemma surjective_fst : Function.Surjective (pullback.fst (Y ↘ S) (T ↘ S)).base := by
  haveI : AlgebraicGeometry.Surjective (T ↘ S) :=
    (surjective_iff _).mpr (SmoothLift.surjective_of_thickening (T ↘ S) hsurj hsq)
  exact (surjective_iff _).mp inferInstance

include hsurj in
lemma app_surjective_fst (O : Y.Opens) (hO : IsAffineOpen O) :
    Function.Surjective ((pullback.fst (Y ↘ S) (T ↘ S)).app O) := by
  haveI := isClosedImmersion_over hsurj
  exact Scheme.Hom.app_surjective _ O hO

include hsurj hsq in
lemma sqZero_app_fst (O : Y.Opens) (hO : IsAffineOpen O) :
    SqZero ((pullback.fst (Y ↘ S) (T ↘ S)).app O).hom := by
  have hP := (Cech.isPushout_sections (S := S) (X := Y) (T := T) O hO _ rfl).flip
  have happ : (T ↘ S).appLE ⊤ ⊤ (by simp) = (T ↘ S).appTop :=
    Scheme.Hom.appLE_eq_app (f := T ↘ S) (U := ⊤)
  rw [happ] at hP
  have hker := ker_inl_of_isPushout hP hsurj
  have hI : RingHom.ker (T ↘ S).appTop.hom * RingHom.ker (T ↘ S).appTop.hom = ⊥ := by
    refine le_bot_iff.mp (Ideal.mul_le.2 fun a ha b hb ↦ ?_)
    rw [Ideal.mem_bot]
    exact hsq a b ha hb
  intro a b ha hb
  have ha' : a ∈ RingHom.ker ((pullback.fst (Y ↘ S) (T ↘ S)).appLE O _ le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]; exact ha
  have hb' : b ∈ RingHom.ker ((pullback.fst (Y ↘ S) (T ↘ S)).appLE O _ le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]; exact hb
  rw [hker] at ha' hb'
  have := Ideal.mul_mem_mul ha' hb'
  rw [← Ideal.map_mul, hI, Ideal.map_bot, Ideal.mem_bot] at this
  exact this

end Thickening

/-! ### Rank-one data on a chart -/

section Chart

set_option hygiene false in
/-- The projection `Y ×_S T → Y`. -/
local notation "fst₀" => pullback.fst (Y ↘ S) (T ↘ S)

variable (hsurj : Function.Surjective (T ↘ S).appTop) (hsq : SqZero (T ↘ S).appTop.hom)

include hsurj hsq in
/-- Near every point of the thickened chart, the lifted idempotent `e` has rank one, with a
column evaluating to a basis of `L₀`. -/
theorem exists_rankOne_chart (U : Y.Opens) (hU : IsAffineOpen U)
    (L₀ : (pullback (Y ↘ S) (T ↘ S)).Modules) [L₀.IsInvertible] {n : ℕ}
    (ε : Fin n → Γ(L₀, pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U))
    (s : Γ(L₀, pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U) →ₗ[Γ(pullback (Y ↘ S) (T ↘ S),
      pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U)] (Fin n → Γ(pullback (Y ↘ S) (T ↘ S),
        pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U)))
    (hs : ∀ x, ∑ i, s x i • ε i = x) (e : Matrix (Fin n) (Fin n) Γ(Y, U)) (he : e * e = e)
    (hemap : e.map ((pullback.fst (Y ↘ S) (T ↘ S)).app U).hom = splitMat ε s)
    (t : (pullback (Y ↘ S) (T ↘ S) : Scheme.{u}))
    (ht : (pullback.fst (Y ↘ S) (T ↘ S)).base t ∈ U) :
    ∃ (O : Y.Opens) (hO : O ≤ U) (p l : Fin n → Γ(Y, O)),
      (pullback.fst (Y ↘ S) (T ↘ S)).base t ∈ O ∧ e.map (ρ hO) = vecMulVec p l ∧
        l ⬝ᵥ p = 1 ∧ L₀.IsBasisOn (pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ O)
          (Data.lc (pullback.fst (Y ↘ S) (T ↘ S)) L₀ ε hO p) := by
  haveI := isClosedImmersion_over hsurj
  haveI : IsAffineHom (pullback.fst (Y ↘ S) (T ↘ S)) := inferInstance
  have hU₀ : IsAffineOpen (fst₀ ⁻¹ᵁ U) := hU.preimage fst₀
  obtain ⟨O₀, β, htO₀, hβ⟩ := Scheme.Modules.IsInvertible.exists_basis (L := L₀) t
  obtain ⟨f₀, hf₀, htf₀⟩ := hU₀.exists_basicOpen_le ⟨t, htO₀⟩ ht
  obtain ⟨g, rfl⟩ := app_surjective_fst hsurj U hU f₀
  have hO : Y.basicOpen g ≤ U := Y.basicOpen_le g
  have hpre : fst₀ ⁻¹ᵁ Y.basicOpen g = (pullback (Y ↘ S) (T ↘ S)).basicOpen ((fst₀).app U g) :=
    Scheme.preimage_basicOpen fst₀ g
  obtain ⟨c, c1, c2, c3, c4⟩ := ChartCoord.exists_coord L₀ hU₀ ε s hs ((fst₀).app U g)
    (fst₀ ⁻¹ᵁ Y.basicOpen g) ((fst₀).preimage_mono hO) hpre
  have hO₀ : fst₀ ⁻¹ᵁ Y.basicOpen g ≤ O₀ := hpre.le.trans hf₀
  obtain ⟨β', hβ'def⟩ : ∃ β', β' = rs L₀ hO₀ β := ⟨_, rfl⟩
  have hβ' : L₀.IsBasisOn (fst₀ ⁻¹ᵁ Y.basicOpen g) β' := by
    rw [hβ'def]
    exact Scheme.PresheafOfModules.IsBasisOn.restrict hβ hO₀
  have hβb := isBasisOn_self hβ'
  have hl : ∀ k, ∃ r : Γ(pullback (Y ↘ S) (T ↘ S), fst₀ ⁻¹ᵁ Y.basicOpen g), r • β' =
      rs L₀ ((fst₀).preimage_mono hO) (ε k) := fun k ↦ hβb.2 _
  choose l₀ hl₀ using hl
  have hE : (e.map (ρ hO)).map ((fst₀).app (Y.basicOpen g)).hom = vecMulVec (c β') l₀ := by
    ext a k
    simp only [map_apply, vecMulVec_apply]
    have h0 : ((fst₀).app (Y.basicOpen g)).hom (ρ hO (e a k)) =
        ρ ((fst₀).preimage_mono hO) (((fst₀).app U).hom (e a k)) := app_rr fst₀ hO (e a k)
    have h1 : ((fst₀).app U).hom (e a k) = s (ε k) a := congrFun (congrFun hemap a) k
    have h2 : c (rs L₀ ((fst₀).preimage_mono hO) (ε k)) a =
        ρ ((fst₀).preimage_mono hO) (s (ε k) a) :=
      congrFun (c1 (ε k)) a
    rw [h0, h1, ← h2, ← hl₀ k, c3, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hdot : l₀ ⬝ᵥ c β' = 1 := by
    have h := c2 β'
    simp only [← hl₀, smul_smul, ← Finset.sum_smul] at h
    have h' : (∑ x, c β' x * l₀ x) • β' =
        (1 : Γ(pullback (Y ↘ S) (T ↘ S), fst₀ ⁻¹ᵁ Y.basicOpen g)) • β' := by
      rw [h, one_smul]
    rw [dotProduct, ← hβb.1 h']
    exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _
  have hOaff : IsAffineOpen (Y.basicOpen g) := hU.basicOpen g
  have heO : e.map (ρ hO) * e.map (ρ hO) = e.map (ρ hO) := by rw [← Matrix.map_mul, he]
  obtain ⟨p, l, hpl, hlp, hpmap⟩ := exists_rankOne_lift (app_surjective_fst hsurj _ hOaff)
    (sqZero_app_fst hsurj hsq _ hOaff) (e.map (ρ hO)) heO (c β') l₀ hE hdot
  refine ⟨Y.basicOpen g, hO, p, l, ?_, hpl, hlp, ?_⟩
  · change t ∈ fst₀ ⁻¹ᵁ Y.basicOpen g
    rw [hpre]
    exact htf₀
  · have : Data.lc fst₀ L₀ ε hO p = β' := by
      rw [Data.lc]
      conv_rhs => rw [← c2 β']
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      congr 1
      exact congrFun hpmap k
    rw [this]
    exact hβ'

end Chart

/-! ### The lifting theorem -/

variable (hsurj : Function.Surjective (T ↘ S).appTop) (hsq : SqZero (T ↘ S).appTop.hom)

include hsurj hsq in
/-- **Invertible sheaves lift along square-zero thickenings** of a scheme covered by two affine
opens whose intersection is a basic open in each: `Pic(Y) → Pic(Y ×_S T)` is surjective. -/
theorem surjective_map_fst (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (τ : Γ(Y, U)) (hτ : U ⊓ V = Y.basicOpen τ) (τ' : Γ(Y, V))
    (hτ' : U ⊓ V = Y.basicOpen τ') :
    Function.Surjective (Scheme.Pic.map (pullback.fst (Y ↘ S) (T ↘ S))) := by
  intro x
  obtain ⟨L₀, hL₀, rfl⟩ := Scheme.Pic.mk_surjective x
  haveI := isClosedImmersion_over hsurj
  haveI : IsAffineHom (pullback.fst (Y ↘ S) (T ↘ S)) := inferInstance
  set i := pullback.fst (Y ↘ S) (T ↘ S) with hi
  have hU₀ : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hV₀ : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
  have hUVaff : IsAffineOpen (U ⊓ V) := by rw [hτ]; exact hU.basicOpen τ
  obtain ⟨n, ε, sU, hsU⟩ := exists_split L₀ hU₀
  obtain ⟨m, δ, sV, hsV⟩ := exists_split L₀ hV₀
  -- lift the idempotents
  obtain ⟨eU, heU, heUmap⟩ := exists_idempotent_lift (app_surjective_fst hsurj U hU)
    (sqZero_app_fst hsurj hsq U hU) (splitMat ε sU) (splitMat_mul ε sU hsU)
  obtain ⟨eV, heV, heVmap⟩ := exists_idempotent_lift (app_surjective_fst hsurj V hV)
    (sqZero_app_fst hsurj hsq V hV) (splitMat δ sV) (splitMat_mul δ sV hsV)
  -- coordinates on the overlap
  have hWU : i ⁻¹ᵁ (U ⊓ V) ≤ i ⁻¹ᵁ U := i.preimage_mono inf_le_left
  have hWV : i ⁻¹ᵁ (U ⊓ V) ≤ i ⁻¹ᵁ V := i.preimage_mono inf_le_right
  obtain ⟨cU, cU1, cU2, cU3, cU4⟩ := ChartCoord.exists_coord L₀ hU₀ ε sU hsU (i.app U τ)
    (i ⁻¹ᵁ (U ⊓ V)) hWU (by rw [hτ]; exact Scheme.preimage_basicOpen i τ)
  obtain ⟨cV, cV1, cV2, cV3, cV4⟩ := ChartCoord.exists_coord L₀ hV₀ δ sV hsV (i.app V τ')
    (i ⁻¹ᵁ (U ⊓ V)) hWV (by rw [hτ']; exact Scheme.preimage_basicOpen i τ')
  have cUsum : ∀ (k : ℕ) (r : Fin k → Γ(pullback (Y ↘ S) (T ↘ S), i ⁻¹ᵁ (U ⊓ V)))
      (x : Fin k → Γ(L₀, i ⁻¹ᵁ (U ⊓ V))), cU (∑ j, r j • x j) = ∑ j, r j • cU (x j) := by
    intro k r x
    rw [map_sum_of_add cU cU4]
    exact Finset.sum_congr rfl fun j _ ↦ cU3 _ _
  have cVsum : ∀ (k : ℕ) (r : Fin k → Γ(pullback (Y ↘ S) (T ↘ S), i ⁻¹ᵁ (U ⊓ V)))
      (x : Fin k → Γ(L₀, i ⁻¹ᵁ (U ⊓ V))), cV (∑ j, r j • x j) = ∑ j, r j • cV (x j) := by
    intro k r x
    rw [map_sum_of_add cV cV4]
    exact Finset.sum_congr rfl fun j _ ↦ cV3 _ _
  let Φ₀ : Matrix (Fin n) (Fin m) Γ(pullback (Y ↘ S) (T ↘ S), i ⁻¹ᵁ (U ⊓ V)) :=
    Matrix.of fun a j ↦ cU (rs L₀ hWV (δ j)) a
  let Ψ₀ : Matrix (Fin m) (Fin n) Γ(pullback (Y ↘ S) (T ↘ S), i ⁻¹ᵁ (U ⊓ V)) :=
    Matrix.of fun j a ↦ cV (rs L₀ hWU (ε a)) j
  -- the restricted lifted idempotents reduce to the coordinates of the generators
  have heU' : ∀ a k, (i.app (U ⊓ V)).hom (ρ (inf_le_left : U ⊓ V ≤ U) (eU a k)) =
      cU (rs L₀ hWU (ε k)) a := by
    intro a k
    have h0 : (i.app (U ⊓ V)).hom (ρ (inf_le_left : U ⊓ V ≤ U) (eU a k)) =
        ρ hWU ((i.app U).hom (eU a k)) := app_rr i inf_le_left (eU a k)
    have h1 : (i.app U).hom (eU a k) = sU (ε k) a := congrFun (congrFun heUmap a) k
    rw [h0, h1]
    exact (congrFun (cU1 (ε k)) a).symm
  have heV' : ∀ a k, (i.app (U ⊓ V)).hom (ρ (inf_le_right : U ⊓ V ≤ V) (eV a k)) =
      cV (rs L₀ hWV (δ k)) a := by
    intro a k
    have h0 : (i.app (U ⊓ V)).hom (ρ (inf_le_right : U ⊓ V ≤ V) (eV a k)) =
        ρ hWV ((i.app V).hom (eV a k)) := app_rr i inf_le_right (eV a k)
    have h1 : (i.app V).hom (eV a k) = sV (δ k) a := congrFun (congrFun heVmap a) k
    rw [h0, h1]
    exact (congrFun (cV1 (δ k)) a).symm
  have hΦΨ : Φ₀ * Ψ₀ = (eU.map (ρ (inf_le_left : U ⊓ V ≤ U))).map (i.app (U ⊓ V)).hom := by
    ext a a'
    rw [mul_apply]
    simp only [map_apply, heU']
    have h := congrFun (cUsum m (fun j ↦ cV (rs L₀ hWU (ε a')) j) (fun j ↦ rs L₀ hWV (δ j))) a
    rw [cV2, Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    change ∑ j, cU (rs L₀ hWV (δ j)) a * cV (rs L₀ hWU (ε a')) j = _
    rw [h]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hΨΦ : Ψ₀ * Φ₀ = (eV.map (ρ (inf_le_right : U ⊓ V ≤ V))).map (i.app (U ⊓ V)).hom := by
    ext j j'
    rw [mul_apply]
    simp only [map_apply, heV']
    have h := congrFun (cVsum n (fun a ↦ cU (rs L₀ hWV (δ j')) a) (fun a ↦ rs L₀ hWU (ε a))) j
    rw [cU2, Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    change ∑ a, cV (rs L₀ hWU (ε a)) j * cU (rs L₀ hWV (δ j')) a = _
    rw [h]
    exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  have heUΦ : (eU.map (ρ (inf_le_left : U ⊓ V ≤ U))).map (i.app (U ⊓ V)).hom * Φ₀ = Φ₀ := by
    ext a j
    rw [mul_apply]
    simp only [map_apply, heU']
    change ∑ k, cU (rs L₀ hWU (ε k)) a * cU (rs L₀ hWV (δ j)) k = cU (rs L₀ hWV (δ j)) a
    conv_rhs => rw [← cU2 (rs L₀ hWV (δ j)), cUsum n, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hΦeV : Φ₀ * (eV.map (ρ (inf_le_right : U ⊓ V ≤ V))).map (i.app (U ⊓ V)).hom = Φ₀ := by
    ext a j
    rw [mul_apply]
    simp only [map_apply, heV']
    change ∑ k, cU (rs L₀ hWV (δ k)) a * cV (rs L₀ hWV (δ j)) k = cU (rs L₀ hWV (δ j)) a
    conv_rhs => rw [← cV2 (rs L₀ hWV (δ j)), cUsum m, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  -- lift the gluing
  obtain ⟨Φ, Ψ, hΦΨ', hΨΦ', heUΦ', hΦeV', hΦmap⟩ := exists_gluing_lift
    (app_surjective_fst hsurj (U ⊓ V) hUVaff) (sqZero_app_fst hsurj hsq (U ⊓ V) hUVaff)
    (eU.map (ρ (inf_le_left : U ⊓ V ≤ U))) (eV.map (ρ (inf_le_right : U ⊓ V ≤ V)))
    (by rw [← Matrix.map_mul, heU]) (by rw [← Matrix.map_mul, heV]) Φ₀ Ψ₀ hΦΨ hΨΦ heUΦ hΦeV
  let D : Data U V :=
    { n := n, m := m, eU := eU, eV := eV, Φ := Φ, Ψ := Ψ, eU_mul := heU, eV_mul := heV,
      Φ_Ψ := hΦΨ', Ψ_Φ := hΨΦ', eU_Φ := heUΦ', Φ_eV := hΦeV' }
  have hc : D.Compat (s := i) (N := L₀) ε δ := by
    intro j
    change rs L₀ hWV (δ j) = ∑ a, (i.app (U ⊓ V)).hom (Φ a j) • rs L₀ hWU (ε a)
    have : ∀ a, (i.app (U ⊓ V)).hom (Φ a j) = cU (rs L₀ hWV (δ j)) a := fun a ↦
      congrFun (congrFun hΦmap a) j
    simp only [this]
    exact (cU2 _).symm
  have H : ∀ t, (∃ (O : Y.Opens) (R : D.RankOneU O), i.base t ∈ O ∧
        L₀.IsBasisOn (i ⁻¹ᵁ O) (Data.lc i L₀ ε R.le R.p)) ∨
      (∃ (O : Y.Opens) (R : D.RankOneV O), i.base t ∈ O ∧
        L₀.IsBasisOn (i ⁻¹ᵁ O) (Data.lc i L₀ δ R.le R.p)) := by
    intro t
    have : i.base t ∈ U ⊔ V := by rw [hUV]; trivial
    rcases Opens.mem_sup.mp this with htU | htV
    · obtain ⟨O, hO, p, l, htO, hpl, hlp, hb⟩ :=
        exists_rankOne_chart hsurj hsq U hU L₀ ε sU hsU eU heU heUmap t htU
      exact Or.inl ⟨O, ⟨hO, p, l, hpl, hlp⟩, htO, hb⟩
    · obtain ⟨O, hO, p, l, htO, hpl, hlp, hb⟩ :=
        exists_rankOne_chart hsurj hsq V hV L₀ δ sV hsV eV heV heVmap t htV
      exact Or.inr ⟨O, ⟨hO, p, l, hpl, hlp⟩, htO, hb⟩
  haveI := D.isInvertible_of_surjective (surjective_fst hsurj hsq) H
  obtain ⟨iso⟩ := D.nonempty_iso_pullback_sheaf hUV hc H
  refine ⟨Scheme.Pic.mk D.sheaf, ?_⟩
  rw [Scheme.Pic.map_mk]
  exact Scheme.Pic.mk_eq_of_iso iso

end CurvesJacobian.PicLift
