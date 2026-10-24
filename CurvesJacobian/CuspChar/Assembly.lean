/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Cuspidal
import CurvesJacobian.CuspChar.Ratio
import Mathlib.LinearAlgebra.Determinant

/-!
# Numerical cuspidality from the weight identity (step B of [AbsTopI] Lemma 4.5 (v))

Let `Π` be a topological group with a normal subgroup `D` (the geometric fundamental group `Δ`
inside `Π_U`) and `S` a set of subgroups of `D` (the cuspidal inertia groups). For an open subgroup
`H ⊆ D` and `x ∈ Π` with `x H x⁻¹ = H`, conjugation by `x` acts on the continuous characters
`H → ℤ/n` by `ξ ↦ ξ ∘ (h ↦ x h x⁻¹)`; `CurvesJacobian.CuspChar.charDet` is the determinant of
this action (the transpose of the action on `H^ab ⊗ ℤ/n`, so it has the same determinant).

The **cusp weight identity** (`CurvesJacobian.CuspChar.CuspWeightIdentity D S l χ₀ χ`) says: for
every open `H ⊆ D` there is an open subgroup `P ⊆ Π` normalising `H` on which
`det(x | Hom(H, ℤ/l^k))² = χ_k(x)^{e_H}` for all `k`, where `e_H = [D : H] χ₀ + r_H`
(`r_H` the number of cusps of `H`). For `U` a hyperbolic curve of genus `g` with `r ≥ 1` cusps
over a number field, `χ₀ = 2g - 2 + r`, `χ_k` the cyclotomic character mod `l^k` (composed with
`Π_U ↠ G_K`), this is the Kummer/Weil-pairing computation of `MR3-plan.md` (B1) plus
Riemann–Hurwitz (B2): on an open subgroup fixing the cusps of `H`, `H^ab ⊗ ℤ/m` is an extension
of `J_H[m]` by `(ℤ/m)(1)^{cusps}/diagonal` (cusp inertia `≅ ℤ̂(1)`), `det(J_H[m])² = χ^{2 g_H}`
(Weil pairing), so `det² = χ^{2 g_H + 2 r_H - 2}`, and `2 g_H - 2 + r_H = [D : H](2g - 2 + r)`.

Main result (`CurvesJacobian.CuspChar.isNumCusp_of_cuspWeightIdentity`): for a topological
isomorphism `Φ : Π ≃ₜ* Π'` with `Φ(D) = D'`, if both sides satisfy the weight identity, the
character `χ` has no nontrivial exponent on open subgroups, the numbers of `ℤ/2`-characters of `D`,
`D'` are `2^{χ₀ + 1}`, `2^{χ₀' + 1}`, and on both sides there are covers in which all cusps ramify
to order `≥ m` (`r_H m ≤ C [D : H]`), then `Φ|_D` is numerically cuspidal. With
`CurvesJacobian.CuspChar.mem_iff_map_mem_of_numCusp` (step G) it then maps the cusp groups exactly
onto the cusp groups (`CurvesJacobian.CuspChar.mem_iff_map_mem_of_cuspWeightIdentity`).
-/

namespace CurvesJacobian.CuspChar

open Module

section Det

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {D' : Type*} [Group D'] [TopologicalSpace D'] [IsTopologicalGroup D'] {p : ℕ}

lemma charSpace_ext {H : OpenSubgroup D} {ξ η : charSpace p H}
    (h : ∀ x, ξv (H : Subgroup D) ξ.1 x = ξv (H : Subgroup D) η.1 x) : ξ = η := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  rintro ⟨x, hx⟩
  have := h x
  rwa [ξv_of_mem hx, ξv_of_mem hx] at this

/-- The pull-back of characters along `Φ` with `Φ(H) = H'`. -/
noncomputable def pullEquivOf (Φ : D ≃ₜ* D') (H : OpenSubgroup D) (H' : OpenSubgroup D')
    (h : mapOpenSub Φ H = H') : charSpace p H' ≃ₗ[ZMod p] charSpace p H := by
  subst h
  exact pullEquiv Φ H

lemma ξv_pullEquivOf (Φ : D ≃ₜ* D') (H : OpenSubgroup D) (H' : OpenSubgroup D')
    (h : mapOpenSub Φ H = H') (ξ : charSpace p H') (x : D) :
    ξv (H : Subgroup D) (pullEquivOf Φ H H' h ξ).1 x = ξv (H' : Subgroup D') ξ.1 (Φ x) := by
  subst h
  exact ξv_pullChar Φ H ξ.1 x

/-- The **determinant of `τ` on the continuous characters** `H → ℤ/p`, for an automorphism `τ`
with `τ(H) = H`. -/
noncomputable def charDet (τ : D ≃ₜ* D) (H : OpenSubgroup D) (h : mapOpenSub τ H = H) :
    (ZMod p)ˣ :=
  LinearEquiv.det (pullEquivOf (p := p) τ H H h)

lemma charDet_congr {τ τ' : D ≃ₜ* D} (e : τ = τ') (H : OpenSubgroup D)
    (h : mapOpenSub τ H = H) (h' : mapOpenSub τ' H = H) :
    charDet (p := p) τ H h = charDet τ' H h' := by
  subst e
  rfl

lemma ξv_pullEquiv_symm (Φ : D ≃ₜ* D') (H : OpenSubgroup D) (ζ : charSpace p H) (x : D) :
    ξv (mapOpenSub Φ H : Subgroup D') ((pullEquiv Φ H).symm ζ).1 (Φ x) =
      ξv (H : Subgroup D) ζ.1 x := by
  have := ξv_pullChar Φ H ((pullEquiv Φ H).symm ζ).1 x
  rw [← this]
  have e : pullChar Φ H ((pullEquiv Φ H).symm ζ).1 = ζ.1 :=
    congrArg Subtype.val ((pullEquiv Φ H).apply_symm_apply ζ)
  rw [e]

/-- **Transport of the character determinant** along `Φ`. -/
lemma charDet_conj (Φ : D ≃ₜ* D') (τ : D ≃ₜ* D) (H : OpenSubgroup D)
    (h : mapOpenSub τ H = H)
    (h' : mapOpenSub (Φ.symm.trans (τ.trans Φ)) (mapOpenSub Φ H) = mapOpenSub Φ H) :
    charDet (p := p) (Φ.symm.trans (τ.trans Φ)) (mapOpenSub Φ H) h' = charDet τ H h := by
  unfold charDet
  set T := pullEquiv (p := p) Φ H
  have hA : pullEquivOf (p := p) (Φ.symm.trans (τ.trans Φ)) (mapOpenSub Φ H) (mapOpenSub Φ H) h' =
      (T.symm.symm.trans (pullEquivOf τ H H h)).trans T.symm := by
    ext1 ξ
    apply charSpace_ext
    intro y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [ξv_pullEquivOf, LinearEquiv.trans_apply, ξv_pullEquiv_symm, LinearEquiv.trans_apply,
      ξv_pullEquivOf, LinearEquiv.symm_symm]
    change _ = ξv _ (pullChar Φ H ξ.1) (τ x)
    rw [ξv_pullChar]
    congr 1
    change Φ (τ (Φ.symm (Φ x))) = _
    rw [Φ.symm_apply_apply]
  rw [hA, LinearEquiv.det_conj]

end Det

section Conj

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (D : Subgroup Γ)
  [D.Normal]

/-- Conjugation by `x ∈ Γ` as a topological automorphism of the normal subgroup `D`. -/
def conjD (x : Γ) : D ≃ₜ* D where
  toFun y := ⟨x * y * x⁻¹, Subgroup.Normal.conj_mem inferInstance _ y.2 x⟩
  invFun y := ⟨x⁻¹ * y * x, by
    have := Subgroup.Normal.conj_mem (inferInstance : D.Normal) _ y.2 x⁻¹
    rwa [inv_inv] at this⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' y z := by ext; simp [mul_assoc]
  continuous_toFun := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp] lemma conjD_apply_coe (x : Γ) (y : D) : (conjD D x y : Γ) = x * y * x⁻¹ := rfl

variable {D} {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']
  {D' : Subgroup Γ'} [D'.Normal]

omit [IsTopologicalGroup Γ] [IsTopologicalGroup Γ'] [D.Normal] [D'.Normal] in
lemma map_mem_of_map_eq (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D') (y : D) :
    Φ y ∈ D' := by
  rw [← hD]
  exact Subgroup.mem_map_of_mem _ y.2

omit [IsTopologicalGroup Γ] [IsTopologicalGroup Γ'] [D.Normal] [D'.Normal] in
lemma symm_mem_of_map_eq (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D') {y : Γ'}
    (hy0 : y ∈ D') : Φ.symm y ∈ D := by
  have hy : y ∈ D.map Φ.toMulEquiv.toMonoidHom := by rw [hD]; exact hy0
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hy
  have : Φ.symm y = z := by
    rw [← e]
    exact Φ.symm_apply_apply z
  rw [this]
  exact hz

omit [D.Normal] [D'.Normal] in
/-- The restriction `D ≃ₜ* D'` of `Φ : Γ ≃ₜ* Γ'` with `Φ(D) = D'`. -/
def resD (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D') : D ≃ₜ* D' where
  toFun y := ⟨Φ y, map_mem_of_map_eq Φ hD y⟩
  invFun y := ⟨Φ.symm y, symm_mem_of_map_eq Φ hD y.2⟩
  left_inv y := by ext; exact Φ.symm_apply_apply _
  right_inv y := by ext; exact Φ.apply_symm_apply _
  map_mul' y z := by ext; exact map_mul Φ _ _
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup Γ] [IsTopologicalGroup Γ'] [D.Normal] [D'.Normal] in
@[simp] lemma resD_apply_coe (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D') (y : D) :
    (resD Φ hD y : Γ') = Φ y := rfl

omit [IsTopologicalGroup Γ] [IsTopologicalGroup Γ'] [D.Normal] [D'.Normal] in
@[simp] lemma resD_symm_apply_coe (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D')
    (y : D') : ((resD Φ hD).symm y : Γ) = Φ.symm y := rfl

lemma resD_conj (Φ : Γ ≃ₜ* Γ') (hD : D.map Φ.toMulEquiv.toMonoidHom = D') (x : Γ) :
    (resD Φ hD).symm.trans ((conjD D x).trans (resD Φ hD)) = conjD D' (Φ x) := by
  ext y
  change Φ (x * Φ.symm (y : Γ') * x⁻¹) = Φ x * y * (Φ x)⁻¹
  rw [map_mul, map_mul, map_inv, Φ.apply_symm_apply]

end Conj

section Weight

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **The cusp weight identity** for `(Π, D, S)` at the prime `l`, with Euler characteristic
`χ₀` and characters `χ_k : Π → (ℤ/l^k)ˣ`: for every open `H ⊆ D` there is an open `P ⊆ Π`
normalising `H` with `det(x | Hom(H, ℤ/l^k))² = χ_k(x)^{[D:H] χ₀ + r_H}` for `x ∈ P`.
(For an affine hyperbolic curve over a number field: Kummer theory of the covers, Weil pairing and
Riemann–Hurwitz, see the module docstring.) -/
def CuspWeightIdentity (D : Subgroup Γ) [D.Normal] (S : Set (Subgroup D)) (l χ₀ : ℕ)
    (χ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ) : Prop :=
  ∀ H : OpenSubgroup D, ∃ P : Subgroup Γ, IsOpen (P : Set Γ) ∧
    ∃ hP : ∀ x ∈ P, mapOpenSub (conjD D x) H = H, ∀ x (hx : x ∈ P) (k : ℕ),
      charDet (p := l ^ k) (conjD D x) H (hP x hx) ^ 2 =
        χ k x ^ ((H : Subgroup D).index * χ₀ + cuspCount S (H : Subgroup D))

end Weight

section Main

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {D : Subgroup Γ} [D.Normal] [CompactSpace D]
  {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']
  {D' : Subgroup Γ'} [D'.Normal] [CompactSpace D']

omit [CompactSpace D'] [IsTopologicalGroup Γ] [D.Normal]
  [CompactSpace D] [IsTopologicalGroup Γ'] [D'.Normal] in
lemma index_mapOpenSub (Φ : D ≃ₜ* D') (H : OpenSubgroup D) :
    (mapOpenSub Φ H : Subgroup D').index = (H : Subgroup D).index :=
  Subgroup.index_map_equiv (H : Subgroup D) Φ.toMulEquiv

omit [D.Normal] in
lemma index_pos_of_open (H : OpenSubgroup D) : 0 < (H : Subgroup D).index := by
  have : Finite (D ⧸ (H : Subgroup D)) := Subgroup.quotient_finite_of_isOpen _ H.isOpen
  exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)

omit [IsTopologicalGroup Γ] [D.Normal] [CompactSpace D]
  [CompactSpace D'] [IsTopologicalGroup Γ'] [D'.Normal] in
lemma mapOpenSub_mapOpenSub_symm (Φ : D ≃ₜ* D') (H' : OpenSubgroup D') :
    mapOpenSub Φ (mapOpenSub Φ.symm H') = H' := by
  ext y
  change y ∈ ((H' : Subgroup D').map Φ.symm.toMulEquiv.toMonoidHom).map
    Φ.toMulEquiv.toMonoidHom ↔ y ∈ (H' : Subgroup D')
  rw [Subgroup.map_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    change Φ (Φ.symm z) ∈ _
    rwa [Φ.apply_symm_apply]
  · intro hy
    exact ⟨y, hy, Φ.apply_symm_apply y⟩

omit [IsTopologicalGroup Γ] [D.Normal] [CompactSpace D]
  [CompactSpace D'] [IsTopologicalGroup Γ'] [D'.Normal] in
lemma mapOpenSub_top (Φ : D ≃ₜ* D') : mapOpenSub Φ ⊤ = ⊤ := by
  ext y
  simp only [OpenSubgroup.mem_top, iff_true]
  exact (mem_mapOpenSub (Φ := Φ) (x := Φ.symm y)).2 (OpenSubgroup.mem_top _) |>
    fun h ↦ by rwa [Φ.apply_symm_apply] at h

omit [CompactSpace D'] in
/-- **Numerical cuspidality from the cusp weight identity** (step B of [AbsTopI] Lemma 4.5 (v),
replacing [CombGC] Prop 2.4 and Cor 2.7 (i)). -/
theorem isNumCusp_of_cuspWeightIdentity (Φ : Γ ≃ₜ* Γ')
    (hD : D.map Φ.toMulEquiv.toMonoidHom = D') {S : Set (Subgroup D)} {S' : Set (Subgroup D')}
    {l χ₀ χ₀' : ℕ} {χ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ} {χ' : ∀ k : ℕ, Γ' →* (ZMod (l ^ k))ˣ}
    (hW : CuspWeightIdentity D S l χ₀ χ) (hW' : CuspWeightIdentity D' S' l χ₀' χ')
    (hinf : ∀ A B : Subgroup Γ, IsOpen (A : Set Γ) → IsOpen (B : Set Γ) → ∀ N : ℕ,
      (∀ σ ∈ A ⊓ B, ∀ k, χ k σ ^ N = 1) → N = 0)
    (hχ₀ : 0 < χ₀) (hn : Nat.card (charSpace 2 (⊤ : OpenSubgroup D)) = 2 ^ (χ₀ + 1))
    (hn' : Nat.card (charSpace 2 (⊤ : OpenSubgroup D')) = 2 ^ (χ₀' + 1))
    (hfam : ∃ C, ∀ m : ℕ, ∃ H : OpenSubgroup D,
      cuspCount S (H : Subgroup D) * m ≤ C * (H : Subgroup D).index)
    (hfam' : ∃ C, ∀ m : ℕ, ∃ H : OpenSubgroup D',
      cuspCount S' (H : Subgroup D') * m ≤ C * (H : Subgroup D').index) :
    IsNumCusp (resD Φ hD) S S' := by
  set Ψ := resD Φ hD
  -- the Euler characteristics agree
  have hχeq : χ₀ = χ₀' := by
    have e := Nat.card_congr (pullEquiv (p := 2) Ψ ⊤).toEquiv
    rw [hn] at e
    have e2 : Nat.card (charSpace 2 (mapOpenSub Ψ ⊤)) = 2 ^ (χ₀' + 1) := by
      rw [mapOpenSub_top]; exact hn'
    rw [e2] at e
    have := Nat.pow_right_injective (le_refl 2) e
    omega
  subst hχeq
  set ρ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ := fun k ↦ (χ' k).comp Φ.toMulEquiv.toMonoidHom
  -- the weight identity in the form `χ^{e_H} = ρ^{e'_H}` on an open subgroup
  have hpow : ∀ H : OpenSubgroup D, ∃ A : Subgroup Γ, IsOpen (A : Set Γ) ∧ ∀ σ ∈ A, ∀ k,
      χ k σ ^ ((H : Subgroup D).index * χ₀ + cuspCount S (H : Subgroup D)) =
        ρ k σ ^ ((H : Subgroup D).index * χ₀ +
          cuspCount S' (mapOpenSub Ψ H : Subgroup D')) := by
    intro H
    obtain ⟨P, hPo, hP, hPw⟩ := hW H
    obtain ⟨P', hPo', hP', hPw'⟩ := hW' (mapOpenSub Ψ H)
    refine ⟨P ⊓ P'.comap Φ.toMulEquiv.toMonoidHom, hPo.inter (hPo'.preimage Φ.continuous),
      fun σ hσ k ↦ ?_⟩
    have h1 := hPw σ hσ.1 k
    have h2 := hPw' (Φ σ) hσ.2 k
    have hdet : charDet (p := l ^ k) (conjD D' (Φ σ)) (mapOpenSub Ψ H) (hP' _ hσ.2) =
        charDet (p := l ^ k) (conjD D σ) H (hP σ hσ.1) := by
      have hc := resD_conj Φ hD σ
      rw [← charDet_congr hc (mapOpenSub Ψ H) (hc ▸ hP' _ hσ.2) (hP' _ hσ.2)]
      exact charDet_conj Ψ (conjD D σ) H (hP σ hσ.1) _
    rw [index_mapOpenSub, hdet] at h2
    exact h1.symm.trans h2
  choose A hAo hA using hpow
  have hmul : ∀ H K : OpenSubgroup D,
      ((H : Subgroup D).index * χ₀ + cuspCount S (H : Subgroup D)) *
        ((K : Subgroup D).index * χ₀ + cuspCount S' (mapOpenSub Ψ K : Subgroup D')) =
      ((K : Subgroup D).index * χ₀ + cuspCount S (K : Subgroup D)) *
        ((H : Subgroup D).index * χ₀ + cuspCount S' (mapOpenSub Ψ H : Subgroup D')) :=
    fun H K ↦ mul_eq_mul_of_pow_eq χ ρ (hA H) (hA K) (hinf _ _ (hAo H) (hAo K))
  intro H
  refine eq_of_mul_eq_mul (fun H : OpenSubgroup D ↦
      (H : Subgroup D).index * χ₀ + cuspCount S (H : Subgroup D))
    (fun H ↦ (H : Subgroup D).index * χ₀ + cuspCount S' (mapOpenSub Ψ H : Subgroup D'))
    (fun H ↦ (H : Subgroup D).index) (fun H ↦ cuspCount S (H : Subgroup D))
    (fun H ↦ cuspCount S' (mapOpenSub Ψ H : Subgroup D')) hχ₀ (fun _ ↦ rfl) (fun _ ↦ rfl)
    hmul ?_ ?_ H
  · obtain ⟨C, hC⟩ := hfam
    exact ⟨C, fun m ↦ (hC m).imp fun H hH ↦ ⟨hH, index_pos_of_open H⟩⟩
  · obtain ⟨C, hC⟩ := hfam'
    refine ⟨C, fun m ↦ ?_⟩
    obtain ⟨H', hH'⟩ := hC m
    refine ⟨mapOpenSub Ψ.symm H', ?_, index_pos_of_open _⟩
    have hidx := index_mapOpenSub Ψ (mapOpenSub Ψ.symm H')
    rw [mapOpenSub_mapOpenSub_symm] at hidx ⊢
    rw [← hidx]
    exact hH'

/-- **[AbsTopI] Lemma 4.5 (v), abstract form**: under the cusp weight identities, an isomorphism
`Φ : Γ ≃ₜ* Γ'` with `Φ(D) = D'` maps the cusp groups of `D` exactly onto those of `D'`. -/
theorem mem_iff_map_mem_of_cuspWeightIdentity [TotallyDisconnectedSpace D] [T2Space D]
    [TotallyDisconnectedSpace D'] [T2Space D'] (Φ : Γ ≃ₜ* Γ')
    (hD : D.map Φ.toMulEquiv.toMonoidHom = D') {S : Set (Subgroup D)} {S' : Set (Subgroup D')}
    (hS : IsCuspSet S) (hS' : IsCuspSet S')
    {l χ₀ χ₀' : ℕ} {χ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ} {χ' : ∀ k : ℕ, Γ' →* (ZMod (l ^ k))ˣ}
    (hW : CuspWeightIdentity D S l χ₀ χ) (hW' : CuspWeightIdentity D' S' l χ₀' χ')
    (hinf : ∀ A B : Subgroup Γ, IsOpen (A : Set Γ) → IsOpen (B : Set Γ) → ∀ N : ℕ,
      (∀ σ ∈ A ⊓ B, ∀ k, χ k σ ^ N = 1) → N = 0)
    (hχ₀ : 0 < χ₀) (hn : Nat.card (charSpace 2 (⊤ : OpenSubgroup D)) = 2 ^ (χ₀ + 1))
    (hn' : Nat.card (charSpace 2 (⊤ : OpenSubgroup D')) = 2 ^ (χ₀' + 1))
    (hfam : ∃ C, ∀ m : ℕ, ∃ H : OpenSubgroup D,
      cuspCount S (H : Subgroup D) * m ≤ C * (H : Subgroup D).index)
    (hfam' : ∃ C, ∀ m : ℕ, ∃ H : OpenSubgroup D',
      cuspCount S' (H : Subgroup D') * m ≤ C * (H : Subgroup D').index) (I : Subgroup D) :
    I ∈ S ↔ I.map (resD Φ hD).toMulEquiv.toMonoidHom ∈ S' :=
  mem_iff_map_mem_of_numCusp (resD Φ hD) hS hS'
    (isNumCusp_of_cuspWeightIdentity Φ hD hW hW' hinf hχ₀ hn hn' hfam hfam') I

end Main

end CurvesJacobian.CuspChar
