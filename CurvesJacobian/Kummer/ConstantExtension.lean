/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.PicTorsion
import ContinuousKummerTheory.Curve.ConstantsZHat
import Pi1.Orbicurve.BaseChange

/-!
# The constant field extension `F k̄ / F` in the Galois model

Setting of `pi1` / continuous-kummer-theory: `D : GaloisData k t`, `Ω ⊇ K₀ = k(t)` Galois,
`F = F D = Ω^H`, `char k = 0`; `k̄ = kbar k Ω` is the algebraic closure of `k` in `Ω` and
`G_k = Gal(k̄/k)`. The geometric fundamental group `Δ = ker(H → G_k)` is the Galois group of the
compositum `F k̄`, which is the function field of `X_{k̄}`. We realise it as the function field of a
Galois model over `k̄`:

* `CurvesJacobian.Kummer.resK₀ : Gal(Ω/k̄(t)) →* Gal(Ω/k(t))`, continuous and injective;
* `CurvesJacobian.Kummer.baseChange D : GaloisData k̄ t` (`H' = H ∩ Gal(Ω/k̄(t))`), whose
  function field `F' = F (baseChange D)` is `F k̄` (`le_F_baseChange`, `kbar_le_F_baseChange`);
* `CurvesJacobian.Kummer.galToH : Gal(Ω/F') →* H` (continuous) with image the kernel of
  `H → G_k` (`exists_galToH_eq`): `Gal(Ω/F k̄) = Δ`;
* `CurvesJacobian.Kummer.smul_mem_F_baseChange`: `H` stabilises `F'` (it normalises `Δ`).
-/

open KummerTheory Curve AffOrbicurve

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- `k(t) ⊆ k̄(t)` as an algebra (local instance). -/
@[reducible] noncomputable def algebraK₀ : Algebra (K₀ k t) (K₀ (kbar k Ω) t) :=
  (K₀Map (K := kbar k Ω) t).toAlgebra

attribute [local instance] algebraK₀

instance isScalarTower_K₀ : IsScalarTower (K₀ k t) (K₀ (kbar k Ω) t) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (k t) in
/-- Restriction `Gal(Ω/k̄(t)) → Gal(Ω/k(t))`. -/
noncomputable def resK₀ : (Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) →* (Ω ≃ₐ[K₀ k t] Ω) :=
  AlgEquiv.restrictScalarsHom (K₀ k t)

@[simp]
lemma resK₀_apply (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) (x : Ω) : resK₀ k t σ x = σ x := rfl

lemma resK₀_injective : Function.Injective (resK₀ k t) := by
  intro σ τ h
  ext x
  exact DFunLike.congr_fun h x

open scoped Topology in
/-- A homomorphism between Krull-topologised automorphism groups that commutes with evaluation
is continuous. -/
lemma continuous_of_apply_eq {P Q : Type*} [Field P] [Field Q] [Algebra P Ω] [Algebra Q Ω]
    [Algebra.IsIntegral P Ω] (φ : (Ω ≃ₐ[P] Ω) →* (Ω ≃ₐ[Q] Ω)) (hφ : ∀ σ x, φ σ x = σ x) :
    Continuous φ := by
  refine continuous_of_continuousAt_one _ ?_
  intro V hV
  rw [map_one] at hV
  obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff Q Ω V).1 hV
  obtain ⟨T, hTfin, hadj⟩ := IntermediateField.fg_def.1 (E.fg_of_fg_toSubalgebra
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE)))
  have hmem : (⋂ x ∈ T, (MulAction.stabilizer (Ω ≃ₐ[P] Ω) x : Set (Ω ≃ₐ[P] Ω))) ∈
      𝓝 (1 : Ω ≃ₐ[P] Ω) :=
    (Filter.biInter_mem hTfin).2 fun x _ =>
      (stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)
  refine Filter.mem_map.2 (Filter.mem_of_superset hmem fun σ hσ => hEV ?_)
  simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hadj]
  refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff Q (S := T) (φ σ)).2
    fun x hx => ?_
  rw [AlgEquiv.smul_def, hφ]
  exact hσ x hx

variable [IsGalois (K₀ k t) Ω]

instance isGalois_K₀_kbar : IsGalois (K₀ (kbar k Ω) t) Ω :=
  IsGalois.tower_top_of_isGalois (K₀ k t) (K₀ (kbar k Ω) t) Ω

lemma continuous_resK₀ : Continuous (resK₀ k t) :=
  continuous_of_apply_eq _ fun _ _ => rfl

omit [IsGalois (K₀ k t) Ω] in
/-- An automorphism over `k(t)` fixing `k̄` pointwise is an automorphism over `k̄(t)`. -/
lemma exists_resK₀_eq {h : Ω ≃ₐ[K₀ k t] Ω} (hh : ∀ x ∈ kbar k Ω, h x = x) :
    ∃ σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω, resK₀ k t σ = h := by
  let h' : Ω ≃ₐ[kbar k Ω] Ω := AlgEquiv.ofRingEquiv (f := h.toRingEquiv) fun c => hh _ c.2
  have hle : K₀ (kbar k Ω) t ≤ IntermediateField.fixedField (Subgroup.zpowers h') := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro g hg
    have ht : h' ∈ MulAction.stabilizer (Ω ≃ₐ[kbar k Ω] Ω) t :=
      h.commutes ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
    exact (Subgroup.zpowers_le.2 ht) hg
  refine ⟨AlgEquiv.ofRingEquiv (f := h.toRingEquiv) fun x => ?_, by ext; rfl⟩
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) h' (Subgroup.mem_zpowers h')

variable (D : Pi1.Orbifold.GaloisData k t)

omit [IsGalois (K₀ k t) Ω] in
include D in
lemma transcendental_kbar : Transcendental (kbar k Ω) t :=
  Transcendental.extendScalars (kbar k Ω) D.transcendental

/-- **The base change of the Galois model to `k̄`**: `H' = H ∩ Gal(Ω/k̄(t))`, whose fixed field is
the compositum `F k̄` (the function field of `X_{k̄}`). -/
@[irreducible] noncomputable def baseChange : Pi1.Orbifold.GaloisData (kbar k Ω) t where
  H := D.H.comap (resK₀ k t)
  HL := D.HL.comap (resK₀ k t)
  le σ hσ := by
    rw [Subgroup.mem_comap] at hσ ⊢
    exact D.le hσ
  isOpen_HL := D.isOpen_HL.preimage (continuous_resK₀ (k := k) (t := t))
  conj_mem h hh n hn := by
    rw [Subgroup.mem_comap] at hh hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact D.conj_mem _ hh _ hn
  transcendental := transcendental_kbar (D := D)

@[simp]
lemma mem_baseChange_H {σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω} :
    σ ∈ (baseChange D).H ↔ resK₀ k t σ ∈ D.H := by
  unfold baseChange
  exact Subgroup.mem_comap

/-- `F ⊆ F k̄`. -/
lemma le_F_baseChange {x : Ω} (hx : x ∈ F D) : x ∈ F (baseChange D) := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  exact hx _ ((mem_baseChange_H D).1 hσ)

/-- `k̄ ⊆ F k̄`. -/
lemma kbar_le_F_baseChange {x : Ω} (hx : x ∈ kbar k Ω) : x ∈ F (baseChange D) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact σ.commutes ⟨x, (K₀ (kbar k Ω) t).algebraMap_mem ⟨x, hx⟩⟩

/-- Elements of `F k̄` are fixed by `Gal(Ω/F k̄)`. -/
lemma fixes_F_baseChange {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ D.H) (hσk : ∀ x ∈ kbar k Ω, σ x = x)
    {x : Ω} (hx : x ∈ F (baseChange D)) : σ x = x := by
  obtain ⟨σ', rfl⟩ := exists_resK₀_eq hσk
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ' ((mem_baseChange_H D).2 hσ)

/-- `H` stabilises `F k̄`. -/
lemma smul_mem_F_baseChange {h : Ω ≃ₐ[K₀ k t] Ω} (hh : h ∈ D.H) {x : Ω}
    (hx : x ∈ F (baseChange D)) : h x ∈ F (baseChange D) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσk : ∀ y ∈ kbar k Ω, (h⁻¹ * resK₀ k t σ * h) y = y := by
    intro y hy
    have hy' : h y ∈ kbar k Ω := by
      rw [mem_algebraicClosure_iff] at hy ⊢
      exact (hy.isIntegral.map ((h : Ω ≃ₐ[K₀ k t] Ω).restrictScalars k).toAlgHom).isAlgebraic
    simp only [AlgEquiv.mul_apply, resK₀_apply]
    rw [show σ (h y) = h y from σ.commutes ⟨h y, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, hy'⟩⟩]
    exact h.symm_apply_apply y
  have := fixes_F_baseChange D
    (D.H.mul_mem (D.H.mul_mem (D.H.inv_mem hh) ((mem_baseChange_H D).1 hσ)) hh) hσk hx
  simp only [AlgEquiv.mul_apply, resK₀_apply] at this
  have h2 := congrArg h this
  rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2
  exact h2

lemma fixingSubgroup_F : (F D).fixingSubgroup = D.H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨D.H, D.isClosed_H⟩

/-- `Gal(Ω/F k̄) → H`, `τ ↦ τ|_{k(t)}` (its image is `Δ = ker(H → G_k)`). -/
noncomputable def galToH : (Ω ≃ₐ[F (baseChange D)] Ω) →* D.H where
  toFun τ := ⟨resK₀ k t (τ.restrictScalars (K₀ (kbar k Ω) t)), by
    rw [← fixingSubgroup_F D]
    intro x
    exact τ.commutes ⟨x, le_F_baseChange D x.2⟩⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
lemma galToH_apply (τ : Ω ≃ₐ[F (baseChange D)] Ω) (x : Ω) :
    ((galToH D τ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = τ x := rfl

lemma continuous_galToH : Continuous (galToH D) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_of_apply_eq
    ((Subgroup.subtype D.H).comp (galToH D)) fun _ _ => rfl

/-- Elements of `Gal(Ω/F k̄)` fix `k̄`. -/
lemma galToH_fix_kbar (τ : Ω ≃ₐ[F (baseChange D)] Ω) {x : Ω} (hx : x ∈ kbar k Ω) : τ x = x :=
  τ.commutes ⟨x, kbar_le_F_baseChange D hx⟩

/-- **The image of `Gal(Ω/F k̄)` in `H` is the kernel of `H → G_k`.** -/
lemma exists_galToH_eq {h : D.H} (hh : ∀ x ∈ kbar k Ω, (h : Ω ≃ₐ[K₀ k t] Ω) x = x) :
    ∃ τ : Ω ≃ₐ[F (baseChange D)] Ω, galToH D τ = h := by
  obtain ⟨σ, hσ⟩ := exists_resK₀_eq hh
  have hσH : σ ∈ (baseChange D).H := by rw [mem_baseChange_H, hσ]; exact h.2
  refine ⟨toGalF (baseChange D) ⟨σ, hσH⟩, ?_⟩
  ext x
  change σ x = _
  rw [← hσ]
  rfl

/-- `Δ` is normal in `H`: conjugates of elements of `Gal(Ω/F k̄)` come from `Gal(Ω/F k̄)`. -/
lemma exists_galToH_conj (h : D.H) (τ : Ω ≃ₐ[F (baseChange D)] Ω) :
    ∃ τ' : Ω ≃ₐ[F (baseChange D)] Ω, galToH D τ' = h⁻¹ * galToH D τ * h := by
  refine exists_galToH_eq D fun x hx => ?_
  have hx' : (h : Ω ≃ₐ[K₀ k t] Ω) x ∈ kbar k Ω := by
    rw [mem_algebraicClosure_iff] at hx ⊢
    exact (hx.isIntegral.map ((h : Ω ≃ₐ[K₀ k t] Ω).restrictScalars k).toAlgHom).isAlgebraic
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, galToH_apply]
  rw [galToH_fix_kbar D τ hx', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

variable [CharZero k] [IsAlgClosed Ω]

omit [IsGalois (K₀ k t) Ω] in
lemma hToGk_eq_one_iff (h : D.H) :
    hToGk D h = 1 ↔ ∀ x ∈ kbar k Ω, (h : Ω ≃ₐ[K₀ k t] Ω) x = x := by
  constructor
  · intro h1 x hx
    have := algebraMap_hToGk_apply D h ⟨x, hx⟩
    rw [h1] at this
    exact this.symm
  · intro h1
    ext x
    change algebraMap (kbar k Ω) Ω (hToGk D h x) = (x : Ω)
    rw [algebraMap_hToGk_apply]
    exact h1 _ x.2

lemma hToGk_galToH (τ : Ω ≃ₐ[F (baseChange D)] Ω) : hToGk D (galToH D τ) = 1 :=
  (hToGk_eq_one_iff D _).2 fun _ hx => galToH_fix_kbar D τ hx

end CurvesJacobian.Kummer
