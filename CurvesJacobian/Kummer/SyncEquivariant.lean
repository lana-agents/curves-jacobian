/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernEquivariant
import CurvesJacobian.Kummer.SyncBaseChange
import CurvesJacobian.Kummer.KummerCurve

/-!
# `Π_X`-equivariance of `M_X ≅ Ẑ(1)` (S1f) and `H¹(Π_U, M_X)`

[AbsTopIII] Prop. 1.4(ii) (`Topics in Absolute Anabelian Geometry III.txt` l.1771–1802) and
Prop. 1.6 (l.1969–2039, `κ_U : Γ(U, 𝒪^×) → H¹(Π_U, M_X)`): `M_X = Hom(H²(Δ_X, Ẑ), Ẑ)` is a
`Π_X`-module through the conjugation action of `Π_X` on `Δ_X`, and the natural
`M_X ≅ Ẑ(1)` of [Mzk19] Prop. 1.2(ii) (`Absolute Anabelian Cuspidalizations.txt` l.363–371) is an
isomorphism of `Π_X`-modules (`Π_X` acting on `Ẑ(1)` through `Π_X ↠ G_k` and the cyclotomic
character). Hence `H¹(Π_U, Ẑ(1)) = H¹(Π_U, M_X)`.

Setting: `X` a curve over `k` (char `0`), its Galois model `D₀ = curveGaloisData k hτ`
(`H = Gal(Ω/K(X))`), and the model `barData k hτ` of `X_{k̄}` (`Δ_X = DeltaBarX k hτ`,
`ρ̄ : Gal(Ω/F k̄) ↠ Δ_X`). For `h ∈ H`:

* `Kummer.conjK h`: `σ ↦ h σ h⁻¹` on `Gal(Ω/k̄(t))` (continuous), `thetaH h` its restriction to
  the group of `barData`;
* `ChernClass.descendAut`: automorphisms of `G` preserving `ker ρ` descend to `Q`;
  **`thetaBar h : Δ_X ≃ₜ* Δ_X`**, the conjugation action of `h ∈ Π_X` on `Δ_X`
  (`thetaBar_rhoBar`, `thetaBar_mul`);
* **`natIsoBar_precompMX`** (S1f mod `n`): `natIso (φ ∘ θ̄_h^*) = h · natIso φ`;
* `mxAct h : M_X/n ≃* M_X/n` (`φ ↦ φ ∘ θ̄_h^*`), and the actions of `H` and of `Π_U = Pi D₀` on
  `M_X = MXHat Δ_X (F D₀)` (`MXHat.smul_proj`; `⟨⟨S⟩⟩` acts trivially by S1f);
* **`natIsoHatPi : M_X ≃ₜ* Ẑ(1)`**, `Π_U`-equivariant (**`natIsoHatPi_smul`**, S1f);
* **`h1MXEquiv : H¹(Π_U, Ẑ(1)) ≃* H¹(Π_U, M_X)`**, **`kummerMapMX`**
  (`κ_U : Γ(U, 𝒪^×) → H¹(Π_U, M_X)`) and Prop. 1.6(i) with `M_X`-coefficients
  (`kummerMapMX_injective`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup WeilCurves.FunctionField CurvesJacobian.ChernClass CurvesJacobian.TopClass

universe u

noncomputable section

/-! ### Descending automorphisms to a quotient -/

namespace CurvesJacobian.ChernClass

section Descend

variable {G Q : Type*} [Group G] [Group Q] [TopologicalSpace G] [TopologicalSpace Q]
  (ρ : G →* Q) (hρc : Continuous ρ) (hρs : Function.Surjective ρ)
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

omit [TopologicalSpace G] [TopologicalSpace Q] in
lemma descend_wd (θ : G ≃* G) (hker : ∀ a, ρ a = 1 → ρ (θ a) = 1) {a b : G} (h : ρ a = ρ b) :
    ρ (θ a) = ρ (θ b) := by
  have h1 : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := hker _ h1
  rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

/-- The map `Q → Q` induced by an automorphism of `G` preserving `ker ρ`. -/
def descendFun (θ : G ≃* G) (q : Q) : Q := ρ (θ (Function.surjInv hρs q))

omit [TopologicalSpace G] [TopologicalSpace Q] in
lemma descendFun_apply (θ : G ≃* G) (hker : ∀ a, ρ a = 1 → ρ (θ a) = 1) (a : G) :
    descendFun ρ hρs θ (ρ a) = ρ (θ a) :=
  descend_wd ρ θ hker (Function.surjInv_eq hρs _)

include hρc hq in
/-- **Automorphisms of `G` preserving `ker ρ` descend to `Q`** (for `ρ` a quotient map). -/
def descendAut (θ : G ≃ₜ* G) (hker : ∀ a, ρ a = 1 → ρ (θ a) = 1)
    (hker' : ∀ a, ρ a = 1 → ρ (θ.symm a) = 1) : Q ≃ₜ* Q where
  toFun := descendFun ρ hρs θ.toMulEquiv
  invFun := descendFun ρ hρs θ.symm.toMulEquiv
  left_inv q := by
    obtain ⟨a, rfl⟩ := hρs q
    rw [descendFun_apply ρ hρs θ.toMulEquiv hker, descendFun_apply ρ hρs θ.symm.toMulEquiv hker']
    exact congrArg ρ (θ.symm_apply_apply a)
  right_inv q := by
    obtain ⟨a, rfl⟩ := hρs q
    rw [descendFun_apply ρ hρs θ.symm.toMulEquiv hker', descendFun_apply ρ hρs θ.toMulEquiv hker]
    exact congrArg ρ (θ.apply_symm_apply a)
  map_mul' q r := by
    obtain ⟨a, rfl⟩ := hρs q
    obtain ⟨b, rfl⟩ := hρs r
    rw [← map_mul, descendFun_apply ρ hρs θ.toMulEquiv hker,
      descendFun_apply ρ hρs θ.toMulEquiv hker, descendFun_apply ρ hρs θ.toMulEquiv hker,
      map_mul, map_mul]
  continuous_toFun := by
    refine continuous_def.2 fun S hS ↦ hq _ ?_
    have : ρ ⁻¹' (descendFun ρ hρs θ.toMulEquiv ⁻¹' S) = (fun a ↦ ρ (θ a)) ⁻¹' S := by
      ext a
      simp only [Set.mem_preimage]
      rw [descendFun_apply ρ hρs θ.toMulEquiv hker]
      rfl
    rw [this]
    exact hS.preimage (hρc.comp θ.continuous)
  continuous_invFun := by
    refine continuous_def.2 fun S hS ↦ hq _ ?_
    have : ρ ⁻¹' (descendFun ρ hρs θ.symm.toMulEquiv ⁻¹' S) = (fun a ↦ ρ (θ.symm a)) ⁻¹' S := by
      ext a
      simp only [Set.mem_preimage]
      rw [descendFun_apply ρ hρs θ.symm.toMulEquiv hker']
      rfl
    rw [this]
    exact hS.preimage (hρc.comp θ.symm.continuous)

lemma descendAut_apply (θ : G ≃ₜ* G) (hker : ∀ a, ρ a = 1 → ρ (θ a) = 1)
    (hker' : ∀ a, ρ a = 1 → ρ (θ.symm a) = 1) (a : G) :
    descendAut ρ hρc hρs hq θ hker hker' (ρ a) = ρ (θ a) :=
  descendFun_apply ρ hρs θ.toMulEquiv hker a

end Descend

end CurvesJacobian.ChernClass

/-! ### Conjugation on `Gal(Ω/k̄(t))` -/

namespace CurvesJacobian.Kummer

section Conj

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

lemma mem_kbar_map (σ : Ω ≃ₐ[K₀ k t] Ω) {y : Ω} (hy : y ∈ kbar k Ω) : σ y ∈ kbar k Ω := by
  rw [mem_algebraicClosure_iff] at hy ⊢
  exact (hy.isIntegral.map (σ.restrictScalars k).toAlgHom).isAlgebraic

lemma conj_fix_kbar (h : Ω ≃ₐ[K₀ k t] Ω) (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :
    ∀ x ∈ kbar k Ω, (h * resK₀ k t σ * h⁻¹) x = x := by
  intro y hy
  have hy' : h.symm y ∈ kbar k Ω := mem_kbar_map h⁻¹ hy
  simp only [AlgEquiv.mul_apply, resK₀_apply, AlgEquiv.aut_inv]
  rw [show σ (h.symm y) = h.symm y from
    σ.commutes ⟨h.symm y, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, hy'⟩⟩]
  exact h.apply_symm_apply y

/-- **`σ ↦ h σ h⁻¹`** on `Gal(Ω/k̄(t))`, for `h ∈ Gal(Ω/k(t))`. -/
def conjK (h : Ω ≃ₐ[K₀ k t] Ω) (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω :=
  (exists_resK₀_eq (conj_fix_kbar h σ)).choose

lemma resK₀_conjK (h : Ω ≃ₐ[K₀ k t] Ω) (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :
    resK₀ k t (conjK h σ) = h * resK₀ k t σ * h⁻¹ :=
  (exists_resK₀_eq (conj_fix_kbar h σ)).choose_spec

lemma conjK_apply (h : Ω ≃ₐ[K₀ k t] Ω) (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) (x : Ω) :
    conjK h σ x = h (σ (h.symm x)) := by
  have := DFunLike.congr_fun (resK₀_conjK h σ) x
  simpa [AlgEquiv.aut_inv] using this

lemma conjK_mul (h : Ω ≃ₐ[K₀ k t] Ω) (σ τ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :
    conjK h (σ * τ) = conjK h σ * conjK h τ :=
  resK₀_injective (by simp only [resK₀_conjK, map_mul]; group)

lemma conjK_conjK (h h' : Ω ≃ₐ[K₀ k t] Ω) (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :
    conjK h (conjK h' σ) = conjK (h * h') σ :=
  resK₀_injective (by simp only [resK₀_conjK]; group)

lemma conjK_one (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) : conjK 1 σ = σ :=
  resK₀_injective (by simp only [resK₀_conjK]; group)

variable [IsGalois (K₀ k t) Ω]

lemma continuous_conjK (h : Ω ≃ₐ[K₀ k t] Ω) : Continuous (conjK (t := t) h) := by
  haveI : T2Space (Ω ≃ₐ[K₀ k t] Ω) := krullTopology_t2
  have hemb : IsEmbedding (resK₀ k t) :=
    (continuous_resK₀.isClosedEmbedding resK₀_injective).isEmbedding
  rw [hemb.continuous_iff]
  have : (resK₀ k t ∘ conjK h) = fun σ ↦ h * resK₀ k t σ * h⁻¹ := funext (resK₀_conjK h)
  rw [this]
  exact (continuous_const.mul continuous_resK₀).mul continuous_const

variable (D : Pi1.Orbifold.GaloisData k t)

lemma conjK_mem (h : D.H) (σ : (baseChange D).H) :
    conjK (h : Ω ≃ₐ[K₀ k t] Ω) σ ∈ (baseChange D).H := by
  rw [mem_baseChange_H, resK₀_conjK]
  exact D.H.mul_mem (D.H.mul_mem h.2 ((mem_baseChange_H D).1 σ.2)) (D.H.inv_mem h.2)

/-- **Conjugation by `h ∈ H` on `Gal(Ω/F k̄)`** (the group of `baseChange D`). -/
def thetaH (h : D.H) : (baseChange D).H ≃ₜ* (baseChange D).H where
  toFun σ := ⟨conjK (h : Ω ≃ₐ[K₀ k t] Ω) σ, conjK_mem D h σ⟩
  invFun σ := ⟨conjK (h⁻¹ : D.H) σ, conjK_mem D h⁻¹ σ⟩
  left_inv σ := Subtype.ext (by
    change conjK _ (conjK _ _) = _
    rw [conjK_conjK]
    simp [conjK_one])
  right_inv σ := Subtype.ext (by
    change conjK _ (conjK _ _) = _
    rw [conjK_conjK]
    simp [conjK_one])
  map_mul' σ τ := Subtype.ext (conjK_mul _ _ _)
  continuous_toFun := ((continuous_conjK _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_conjK _).comp continuous_subtype_val).subtype_mk _

lemma thetaH_apply (h : D.H) (σ : (baseChange D).H) (x : Ω) :
    ((thetaH D h σ : (baseChange D).H) : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) x =
      (h : Ω ≃ₐ[K₀ k t] Ω) ((σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ((h : Ω ≃ₐ[K₀ k t] Ω).symm x)) :=
  conjK_apply _ _ _

lemma thetaH_symm_apply (h : D.H) (σ : (baseChange D).H) :
    (thetaH D h).symm σ = thetaH D h⁻¹ σ := rfl

lemma thetaH_mul (h h' : D.H) (σ : (baseChange D).H) :
    thetaH D (h * h') σ = thetaH D h (thetaH D h' σ) :=
  Subtype.ext (conjK_conjK _ _ _).symm

lemma thetaH_one (σ : (baseChange D).H) : thetaH D 1 σ = σ := Subtype.ext (conjK_one _)

end Conj

end CurvesJacobian.Kummer

/-! ### The conjugation action of `Π_X` on `Δ_X` and S1f modulo `n` -/

namespace CurvesJacobian.Kummer

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

variable (hτ) in
/-- `ρ̄ : Gal(Ω/F k̄) ↠ Δ_X` (the Galois action at the geometric generic point of `X_{k̄}`). -/
abbrev rhoBar : (barData k hτ).H →* DeltaBarX k hτ :=
  rhoX (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ)

lemma rhoBar_surjective : Function.Surjective (rhoBar hτ) :=
  rhoX_surjective (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)

lemma continuous_rhoBar : Continuous (rhoBar hτ) :=
  (barData k hτ).continuous_chartHom (barData_H_le k hτ) _

lemma isOpen_of_rhoBar (S : Set (DeltaBarX k hτ)) (h : IsOpen (rhoBar hτ ⁻¹' S)) : IsOpen S :=
  isOpen_of_rhoX (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) S h

/-- **Conjugation by `h ∈ Π_X` preserves `ker(ρ̄)`**: it permutes the inertia groups of the
places of `Ω` over `k̄`, all of which are centred on the proper curve `X_{k̄}`. -/
lemma rhoBar_thetaH_eq_one (h : (curveGaloisData k hτ).H) {a : (barData k hτ).H}
    (ha : rhoBar hτ a = 1) : rhoBar hτ (thetaH _ h a) = 1 := by
  have hker := (genericL_spec (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barEquivL_algebraMap k hτ) (barData_H_le k hτ) (barEquivL_tau k hτ) ⊤ (by simp)).1
  rw [GaloisPi1.kernel_eq_topologicalClosure _ (barData k hτ).isClosed_H _
    (SU_subset_H _ _ _ ⊤)] at hker
  have hcl : IsClosed ((rhoBar hτ).ker : Set (barData k hτ).H) := by
    have h1 : IsClosed ({1} : Set (DeltaBarX k hτ)) := isClosed_singleton
    exact h1.preimage continuous_rhoBar
  have hle : (rhoBar hτ).ker ≤
      (rhoBar hτ).ker.comap (thetaH _ h).toMulEquiv.toMonoidHom := by
    conv_lhs => rw [hker]
    haveI : ((rhoBar hτ).ker.comap (thetaH _ h).toMulEquiv.toMonoidHom).Normal :=
      Subgroup.Normal.comap inferInstance _
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (hcl.preimage (thetaH _ h).continuous)
    intro σ hσ
    obtain ⟨-, W, hkW, -, hin⟩ := hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_ker]
    set h' : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X := h.1
    refine rhoX_eq_one (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
      (W := W.comap (h'.symm.toRingEquiv : FFClosure X →+* FFClosure X))
      (isCentredOn_top_of (barEquivL_algebraMap k hτ) fun c ↦ ?_) ?_
    · rw [ValuationSubring.mem_comap]
      have hc : h'.symm (c : FFClosure X) ∈ kbar k (FFClosure X) := mem_kbar_map h'⁻¹ c.2
      exact hkW ⟨_, hc⟩
    · refine mem_inertia_comap h'.symm.toRingEquiv (fun x ↦ ?_) hin
      change h'.symm ((thetaH _ h σ).1 x) = _
      rw [thetaH_apply]
      exact h'.symm_apply_apply _
  exact hle ha

variable (hτ) in
/-- **The conjugation action of `h ∈ Π_X` on `Δ_X`**: `θ̄_h(ρ̄ σ) = ρ̄(h σ h⁻¹)`. -/
def thetaBar (h : (curveGaloisData k hτ).H) : DeltaBarX k hτ ≃ₜ* DeltaBarX k hτ :=
  descendAut (rhoBar hτ) continuous_rhoBar rhoBar_surjective isOpen_of_rhoBar (thetaH _ h)
    (fun _ ha ↦ rhoBar_thetaH_eq_one h ha) (fun _ ha ↦ rhoBar_thetaH_eq_one h⁻¹ ha)

lemma thetaBar_rhoBar (h : (curveGaloisData k hτ).H) (a : (barData k hτ).H) :
    thetaBar hτ h (rhoBar hτ a) = rhoBar hτ (thetaH _ h a) :=
  descendAut_apply _ _ _ _ _ _ _ a

lemma thetaBar_mul (h h' : (curveGaloisData k hτ).H) (γ : DeltaBarX k hτ) :
    thetaBar hτ (h * h') γ = thetaBar hτ h (thetaBar hτ h' γ) := by
  obtain ⟨a, rfl⟩ := rhoBar_surjective (hτ := hτ) γ
  rw [thetaBar_rhoBar, thetaBar_rhoBar, thetaBar_rhoBar, thetaH_mul]

lemma thetaBar_one (γ : DeltaBarX k hτ) : thetaBar hτ 1 γ = γ := by
  obtain ⟨a, rfl⟩ := rhoBar_surjective (hτ := hτ) γ
  rw [thetaBar_rhoBar, thetaH_one]

attribute [local instance] instTrivMu

/-- **S1f modulo `n`** ([AbsTopIII] Prop. 1.4(ii), [Mzk19] Prop. 1.2(ii)): the natural
`M_X/n ≅ μ_n` is `Π_X`-equivariant, `Π_X` acting on `M_X/n` by `φ ↦ φ ∘ θ̄_h^*` (conjugation on
`Δ_X`) and on `μ_n` through its Galois action. -/
theorem natIsoBar_precompMX (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat)
    (h : (curveGaloisData k hτ).H) (φ : MXmod (DeltaBarX k hτ) n) :
    natIsoBar hτ n hg (precompMX (thetaBar hτ h) φ) =
      (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X) • natIsoBar hτ n hg φ :=
  natIso_precompMX (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
    (h : FFClosure X ≃ₐ[K₀ k (coordT τ)] FFClosure X).toRingEquiv (thetaH _ h).toMulEquiv
    (fun σ x ↦ by
      change h.1 (σ.1 x) = (thetaH _ h σ).1 (h.1 x)
      rw [thetaH_apply, AlgEquiv.symm_apply_apply])
    (thetaBar hτ h) (fun σ ↦ (thetaBar_rhoBar h σ).symm) (autF _ h) (fun _ ↦ rfl)
    (genus_bar_pos hg) φ

end Curve

end CurvesJacobian.Kummer

/-! ### `M_X` as a topological `Π_U`-module and `H¹(Π_U, M_X)` -/

namespace CurvesJacobian.TopClass

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- `M_X/n` is discrete. -/
instance : TopologicalSpace (MXmod G n) := ⊥

instance : DiscreteTopology (MXmod G n) := ⟨rfl⟩

instance : IsTopologicalGroup (MXmod G n) where

lemma comap_congr_fun {M : Type*} [CommGroup M] [MulDistribMulAction G M] {φ ψ : G →* G}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hact : ∀ (g : G) (m : M), φ g • m = g • m)
    (hact' : ∀ (g : G) (m : M), ψ g • m = g • m) (h : ∀ g, φ g = ψ g) (c : H2lc G M) :
    H2lc.comap φ hφ hact c = H2lc.comap ψ hψ hact' c := by
  obtain rfl : φ = ψ := MonoidHom.ext h
  rfl

lemma precompMX_congr {e e' : G ≃ₜ* G} (h : ∀ g, e g = e' g) (φ : MXmod G n) :
    precompMX e φ = precompMX e' φ := by
  apply (MXmod.toHom G n).injective
  refine MonoidHom.ext fun u ↦ ?_
  change MXmod.toHom G n φ (comapE _ e u) = MXmod.toHom G n φ (comapE _ e' u)
  rw [comap_congr_fun (ψ := e'.toMulEquiv.toMonoidHom) _ e'.continuous _ (fun _ _ ↦ rfl)
    (fun g ↦ h g)]

lemma precompMX_refl (φ : MXmod G n) : precompMX (ContinuousMulEquiv.refl G) φ = φ := by
  apply (MXmod.toHom G n).injective
  refine MonoidHom.ext fun u ↦ ?_
  change MXmod.toHom G n φ (comapE _ (ContinuousMulEquiv.refl G) u) = MXmod.toHom G n φ u
  rw [comap_eq_self _ _ _ (fun _ ↦ rfl)]

/-- `precompMX` preserves the reductions `M_X/N → M_X/n`. -/
lemma isMXCompat_precompMX (e : G ≃ₜ* G) {n N : ℕ} (h : n ∣ N) {φ : MXmod G N}
    {ψ : MXmod G n} (hc : IsMXCompat G h φ ψ) :
    IsMXCompat G h (precompMX e φ) (precompMX e ψ) := fun v ↦ by
  rw [evAt_precompMX, evAt_precompMX,
    ← h2Map_comap _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (redDvd G h) (fun _ _ ↦ rfl)]
  exact hc _

variable (K : Type*) [Field K]

lemma MXHat.compat (φ : MXHat G K) {i j : KummerIndex K} (h : i ≤ j) :
    IsMXCompat G h ((φ : ∀ i, MXmod G i.n) j) ((φ : ∀ i, MXmod G i.n) i) :=
  φ.2 i j h

/-- `φ ↦ φ ∘ θ̄^*` on `M_X = lim M_X/n`. -/
def precompMXHat (e : G ≃ₜ* G) : MXHat G K ≃* MXHat G K where
  toFun φ := ⟨fun i ↦ precompMX e ((φ : ∀ i, MXmod G i.n) i), fun _ _ h ↦
    isMXCompat_precompMX e h (MXHat.compat K φ h)⟩
  invFun φ := ⟨fun i ↦ precompMX e.symm ((φ : ∀ i, MXmod G i.n) i), fun _ _ h ↦
    isMXCompat_precompMX e.symm h (MXHat.compat K φ h)⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ (precompMX e).symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ ↦ (precompMX e).apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul (precompMX e) _ _)

@[simp] lemma proj_precompMXHat (e : G ≃ₜ* G) (φ : MXHat G K) (i : KummerIndex K) :
    MXHat.proj i (precompMXHat K e φ) = precompMX e (MXHat.proj i φ) := rfl

end CurvesJacobian.TopClass

namespace CurvesJacobian.Kummer

section Module

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

variable (hτ) in
/-- **The conjugation action of `h ∈ Π_X` on `M_X/n`**: `φ ↦ φ ∘ θ̄_h^*`. -/
abbrev mxAct (n : ℕ) (h : (curveGaloisData k hτ).H) :
    MXmod (DeltaBarX k hτ) n ≃* MXmod (DeltaBarX k hτ) n :=
  precompMX (thetaBar hτ h)

lemma mxAct_mul (n : ℕ) (h h' : (curveGaloisData k hτ).H) (φ : MXmod (DeltaBarX k hτ) n) :
    mxAct hτ n (h * h') φ = mxAct hτ n h (mxAct hτ n h' φ) := by
  rw [← precompMX_trans]
  exact precompMX_congr (fun γ ↦ thetaBar_mul h h' γ) φ

lemma mxAct_one (n : ℕ) (φ : MXmod (DeltaBarX k hτ) n) : mxAct hτ n 1 φ = φ :=
  (precompMX_congr (e' := ContinuousMulEquiv.refl _) (fun γ ↦ thetaBar_one γ) φ).trans
    (precompMX_refl φ)

variable (hτ) (K : Type u) [Field K]

/-- **`M_X = Hom(H²(Δ_X, Ẑ), Ẑ) = lim_n M_X/n`** for `X_{k̄}` (`MXHat`, indexed by the Kummer
indices of `K`), as a type carrying the `Π_X`- and `Π_U`-actions. -/
def MX : Type (u + 1) := ↥(MXHat (DeltaBarX k hτ) K)

instance : CommGroup (MX hτ K) := inferInstanceAs (CommGroup (MXHat (DeltaBarX k hτ) K))

instance : TopologicalSpace (MX hτ K) :=
  inferInstanceAs (TopologicalSpace (MXHat (DeltaBarX k hτ) K))

instance : IsTopologicalGroup (MX hτ K) :=
  inferInstanceAs (IsTopologicalGroup (MXHat (DeltaBarX k hτ) K))

/-- `MX` is `MXHat` (the identity). -/
def MX.equiv : MX hτ K ≃ₜ* MXHat (DeltaBarX k hτ) K := ContinuousMulEquiv.refl _

/-- **The action of `Π_X` (i.e. of `H = Gal(Ω/K(X))`) on `M_X`**: by conjugation on `Δ_X`. -/
instance instMulDistribMulActionMX :
    MulDistribMulAction (curveGaloisData k hτ).H (MX hτ K) where
  smul h φ := precompMXHat K (thetaBar hτ h) φ
  one_smul _ := Subtype.ext (funext fun i ↦ mxAct_one i.n _)
  mul_smul h h' _ := Subtype.ext (funext fun i ↦ mxAct_mul i.n h h' _)
  smul_mul h φ ψ := map_mul (precompMXHat K (thetaBar hτ h)) φ ψ
  smul_one h := map_one (precompMXHat K (thetaBar hτ h))

variable {hτ K}

lemma MX.smul_def (h : (curveGaloisData k hτ).H) (φ : MX hτ K) :
    h • φ = (MX.equiv hτ K).symm (precompMXHat K (thetaBar hτ h) (MX.equiv hτ K φ)) := rfl

variable (hτ K) in
/-- **The natural isomorphism `M_X ≃ₜ* Ẑ(1)`** ([Mzk19] Prop. 1.2(ii)), indexed by the Kummer
indices of any field `K` (for `K = F = K(X)` the coefficients of `kummerMapZHat`). -/
def natIsoHatK (hg : 0 < (curveGenus k X).toNat) : MX hτ K ≃ₜ* ZHatOne K (FFClosure X) where
  toFun φ := ⟨fun i ↦ natIsoBar hτ i.n hg (MXHat.proj i (MX.equiv hτ K φ)), fun i j h ↦
    (isMXCompat_iff_natIso (hH := barData_H_le k hτ) (barEquivL_algebraMap k hτ)
      (barEquivL_tau k hτ) (genus_bar_pos hg) h _ _).1 (MXHat.compat K (MX.equiv hτ K φ) h)⟩
  invFun z := (MX.equiv hτ K).symm ⟨fun i ↦ (natIsoBar hτ i.n hg).symm (ZHatOne.proj i z),
    fun i j h ↦ (isMXCompat_iff_natIso (hH := barData_H_le k hτ) (barEquivL_algebraMap k hτ)
      (barEquivL_tau k hτ) (genus_bar_pos hg) h _ _).2 (by
      change Mu.transition h ((natIsoBar hτ j.n hg) ((natIsoBar hτ j.n hg).symm
          (ZHatOne.proj j z))) =
        (natIsoBar hτ i.n hg) ((natIsoBar hτ i.n hg).symm (ZHatOne.proj i z))
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact ZHatOne.transition_proj h z)⟩
  left_inv φ := Subtype.ext (funext fun i ↦ MulEquiv.symm_apply_apply _ _)
  right_inv z := Subtype.ext (funext fun i ↦ MulEquiv.apply_symm_apply _ _)
  map_mul' φ ψ := Subtype.ext (funext fun i ↦ map_mul (natIsoBar hτ i.n hg) _ _)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    have : Continuous fun a : MX hτ K ↦ MXHat.proj i (MX.equiv hτ K a) :=
      (continuous_apply i).comp (continuous_subtype_val.comp (MX.equiv hτ K).continuous)
    exact continuous_of_discreteTopology.comp this
  continuous_invFun := by
    refine (MX.equiv hτ K).symm.continuous.comp
      (Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _)
    exact continuous_of_discreteTopology.comp (ZHatOne.continuous_proj i)

lemma proj_natIsoHatK (hg : 0 < (curveGenus k X).toNat) (φ : MX hτ K) (i : KummerIndex K) :
    ZHatOne.proj i (natIsoHatK hτ K hg φ) =
      natIsoBar hτ i.n hg (MXHat.proj i (MX.equiv hτ K φ)) := rfl

/-- **S1f** ([AbsTopIII] Prop. 1.4(ii), [Mzk19] Prop. 1.2(ii)): **the natural `M_X ≅ Ẑ(1)` is
`Π_X`-equivariant** (conjugation on `Δ_X`, cyclotomic action on `Ẑ(1)`). -/
theorem natIsoHatK_smul (hg : 0 < (curveGenus k X).toNat) (h : (curveGaloisData k hτ).H)
    (φ : MX hτ K) : natIsoHatK hτ K hg (h • φ) = h • natIsoHatK hτ K hg φ :=
  Subtype.ext (funext fun i ↦ natIsoBar_precompMX i.n hg h _)

/-- `⟨⟨S⟩⟩` (generated by the inertia of the places centred on the affine curve `U`) acts
trivially on `M_X` (from S1f: it acts trivially on `Ẑ(1)`). -/
theorem kernel_smul_mx [Fact (0 < (curveGenus k X).toNat)] :
    ∀ σ ∈ GaloisPi1.kernel (curveGaloisData k hτ).H (curveGaloisData k hτ).S,
      ∀ φ : MX hτ K, σ • φ = φ := fun σ hσ φ ↦
  (natIsoHatK hτ K Fact.out).injective (by
    rw [natIsoHatK_smul]
    exact kernel_smul_zHatOne K σ hσ _)

/-- **`M_X` as a `Π_U`-module** (`Π_U = Pi D₀ = H ⧸ ⟨⟨S⟩⟩`, genus `≥ 1`). -/
instance instMulDistribMulActionPiMX [Fact (0 < (curveGenus k X).toNat)] :
    MulDistribMulAction (Pi (curveGaloisData k hτ)) (MX hτ K) :=
  MulDistribMulAction.quotientOfLeKer _ kernel_smul_mx

lemma pi_smul_mx [Fact (0 < (curveGenus k X).toNat)] (h : (curveGaloisData k hτ).H)
    (φ : MX hτ K) : ((h : Pi (curveGaloisData k hτ)) • φ) = h • φ := rfl

/-- **S1f for `Π_U`**: `M_X ≅ Ẑ(1)` is an isomorphism of `Π_U`-modules. -/
theorem natIsoHatK_pi_smul [Fact (0 < (curveGenus k X).toNat)] (g : Pi (curveGaloisData k hτ))
    (φ : MX hτ K) : natIsoHatK hτ K Fact.out (g • φ) = g • natIsoHatK hτ K Fact.out φ := by
  induction g using QuotientGroup.induction_on with
  | H h => exact natIsoHatK_smul Fact.out h φ

variable (hτ K) in
/-- **`H¹(Π_U, Ẑ(1)) ≅ H¹(Π_U, M_X)`** (continuous cohomology), induced by the `Π_U`-equivariant
`M_X ≅ Ẑ(1)` (S1f). -/
def h1MXEquiv [Fact (0 < (curveGenus k X).toNat)] :
    ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne K (FFClosure X)) ≃*
      ContH1 (Pi (curveGaloisData k hτ)) (MX hτ K) where
  toFun := ContH1.map (MonoidHom.id _) continuous_id
    (natIsoHatK hτ K Fact.out).symm.toMulEquiv.toMonoidHom
    (natIsoHatK hτ K Fact.out).symm.continuous_toFun
    fun g m ↦ by
      apply (natIsoHatK hτ K Fact.out).injective
      change natIsoHatK hτ K _ ((natIsoHatK hτ K _).symm (g • m)) =
        natIsoHatK hτ K _ (g • (natIsoHatK hτ K _).symm m)
      rw [natIsoHatK_pi_smul, ContinuousMulEquiv.apply_symm_apply,
        ContinuousMulEquiv.apply_symm_apply]
  invFun := ContH1.map (MonoidHom.id _) continuous_id
    (natIsoHatK hτ K Fact.out).toMulEquiv.toMonoidHom (natIsoHatK hτ K Fact.out).continuous_toFun
    fun g m ↦ natIsoHatK_pi_smul g m
  left_inv x := by
    induction x using ContH1.induction_on with
    | h c =>
      rw [ContH1.map_mk, ContH1.map_mk]
      congr 1
      exact Subtype.ext (funext fun g ↦ ContinuousMulEquiv.apply_symm_apply _ _)
  right_inv x := by
    induction x using ContH1.induction_on with
    | h c =>
      rw [ContH1.map_mk, ContH1.map_mk]
      congr 1
      exact Subtype.ext (funext fun g ↦ ContinuousMulEquiv.symm_apply_apply _ _)
  map_mul' := map_mul _

variable (k hτ) in
/-- **The Kummer map `κ_U : Γ(U, 𝒪^×) → H¹(Π_U, M_X)`** ([AbsTopIII] Prop. 1.6, T3 l.1969–1987):
`kummerMapZHat` followed by `h1MXEquiv`. -/
def kummerMapMX [Fact (0 < (curveGenus k X).toNat)] :
    units (curveGaloisData k hτ) →*
      ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ))) :=
  (h1MXEquiv hτ _).toMonoidHom.comp (kummerMapZHat (curveGaloisData k hτ))

variable (k hτ) in
/-- **[AbsTopIII] Prop. 1.6(i) with `M_X`-coefficients**: `κ_U : Γ(U, 𝒪^×) → H¹(Π_U, M_X)` is
injective over a torally Kummer-faithful field (number fields, finite extensions of `ℚ_p`). -/
theorem kummerMapMX_injective [Fact (0 < (curveGenus k X).toNat)]
    (hkf : IsTorallyKummerFaithful k) : Function.Injective (kummerMapMX k hτ) :=
  (h1MXEquiv hτ _).injective.comp (kummerMapZHat_injective_curve k hτ hkf)

end Module

end CurvesJacobian.Kummer
