/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianPi1

/-!
# The split extension `Δ_X^{ab} ⋊ G_k` and the map `π_σ : Π_X → Δ_X^{ab} ⋊ G_k` (JAC D-d, C2)

The geometric input (★) of MR7's Route T′ (`JAC-plan.md`, "JAC agent 27", D-d.0) is an identity
in `H²(Π_X, μ_n)` between the arithmetic Chern class of a divisor and the pull-back of the
explicit theta class `θ_b ∈ H²(T ⋊ G_k, μ_n)` (`LocAn/ThetaClass.lean`) along

  `π_σ : Π_X → T ⋊ G_k`,  `u ↦ ([u σ̃(u)⁻¹], u|_{k̄})`,

where `σ̃` is the automorphism of `Π_X` over `G_k` induced by an automorphism `σ` of `X`
(`π_σ = DiffMap.diff ∘ (id, σ̃)` on `Π_{J¹}`: the fundamental group of the difference map
`δ_σ : X → J`, `x ↦ [x] − [σ x]`). This file provides the group side, for any Galois model `D`
(`Kummer/JacobianPi1.lean`):

* a topology on `SemidirectProduct N G φ` (induced from `N × G`) and
  `SemidirectProduct.isTopologicalGroup_of_continuous` (continuous action);
* **`EAb D = Δ_X^{ab} ⋊ G_k`** (`G_k` acting by `Kummer.mulDistribMulAction_deltaAb`), a
  topological group; `piE = rightHom`, `epsE = inr`, the inversion `iotaE : (t, g) ↦ (t⁻¹, g)`;
* **`piSigma D σ̃ hσ̃ : Π_X →* EAb D`** for a continuous `σ̃ : Π_X →* Π_X` over `G_k`, continuous
  (`continuous_piSigma`), with `piE ∘ piSigma = piXToGk` and functoriality
  **`map_piSigma`**: for `α : Π_{X₁} → Π_{X₂}` over `G_k` with `α ∘ σ̃₁ = σ̃₂ ∘ α`,
  `piSigma σ̃₂ ∘ α = (α^{ab} ⋊ id) ∘ piSigma σ̃₁` (the compatibility used in step 4 of T′);
* the action of `G_k` on `μ_n(Ω)` (roots of unity lie in `k̄`), and of `Π_X` and `EAb D` through
  their maps to `G_k` (`smul_mu_def`, `piX_smul_mu`, `eAb_smul_mu`).
-/

open KummerTheory Curve AffOrbicurve

set_option linter.unusedSectionVars false

/-! ### The topology of a semidirect product -/

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

/-- The product topology on `N ⋊[φ] G` (induced from `N × G`). -/
instance instTopologicalSpace [TopologicalSpace N] [TopologicalSpace G] :
    TopologicalSpace (N ⋊[φ] G) :=
  TopologicalSpace.induced (fun x => (x.left, x.right)) inferInstance

variable [TopologicalSpace N] [TopologicalSpace G]

theorem continuous_toProd : Continuous (fun x : N ⋊[φ] G => (x.left, x.right)) :=
  continuous_induced_dom

theorem continuous_left : Continuous (fun x : N ⋊[φ] G => x.left) :=
  continuous_toProd.fst

theorem continuous_right : Continuous (fun x : N ⋊[φ] G => x.right) :=
  continuous_toProd.snd

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → N ⋊[φ] G} :
    Continuous f ↔ Continuous (fun x => (f x).left) ∧ Continuous (fun x => (f x).right) := by
  constructor
  · intro h
    exact ⟨continuous_left.comp h, continuous_right.comp h⟩
  · rintro ⟨h1, h2⟩
    exact continuous_induced_rng.2 (h1.prodMk h2)

theorem continuous_mk {X : Type*} [TopologicalSpace X] {f : X → N} {g : X → G}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (⟨f x, g x⟩ : N ⋊[φ] G)) :=
  continuous_iff.2 ⟨hf, hg⟩

theorem continuous_inr : Continuous (inr : G → N ⋊[φ] G) :=
  continuous_iff.2 ⟨continuous_const, continuous_id⟩

theorem continuous_inl : Continuous (inl : N → N ⋊[φ] G) :=
  continuous_iff.2 ⟨continuous_id, continuous_const⟩

/-- **A semidirect product of topological groups with a continuous action is a topological
group.** -/
theorem isTopologicalGroup_of_continuous [IsTopologicalGroup N] [IsTopologicalGroup G]
    (hφ : Continuous fun p : G × N => φ p.1 p.2) : IsTopologicalGroup (N ⋊[φ] G) where
  continuous_mul := by
    refine continuous_iff.2 ⟨?_, ?_⟩
    · change Continuous fun p : (N ⋊[φ] G) × (N ⋊[φ] G) => p.1.left * φ p.1.right p.2.left
      exact (continuous_left.comp continuous_fst).mul
        (hφ.comp ((continuous_right.comp continuous_fst).prodMk
          (continuous_left.comp continuous_snd)))
    · exact (continuous_right.comp continuous_fst).mul (continuous_right.comp continuous_snd)
  continuous_inv := by
    refine continuous_iff.2 ⟨?_, ?_⟩
    · change Continuous fun x : N ⋊[φ] G => φ x.right⁻¹ x.left⁻¹
      exact hφ.comp (continuous_right.inv.prodMk continuous_left.inv)
    · exact continuous_right.inv

theorem continuous_map {N' G' : Type*} [Group N'] [Group G'] [TopologicalSpace N']
    [TopologicalSpace G'] {φ' : G' →* MulAut N'} (fn : N →* N') (fg : G →* G')
    (h : ∀ g : G, fn.comp (φ g).toMonoidHom = (φ' (fg g)).toMonoidHom.comp fn)
    (hfn : Continuous fn) (hfg : Continuous fg) : Continuous (map fn fg h) :=
  continuous_iff.2 ⟨hfn.comp continuous_left, hfg.comp continuous_right⟩

end SemidirectProduct

namespace CurvesJacobian.LocAn.SemiAb

open Kummer

attribute [local instance 2000] Kummer.group_piX

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-! ### The action of `G_k` on `μ_n(Ω)` -/

section Mu

variable (n : ℕ) [NeZero n]

variable {n} in
theorem mem_kbar (ζ : Mu n Ω) : ((Mu.val ζ : Ωˣ) : Ω) ∈ kbar k Ω := by
  rw [mem_algebraicClosure_iff]
  refine ⟨Polynomial.X ^ n - 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (NeZero.ne n)) 1,
    ?_⟩
  simp [← Units.val_pow_eq_pow_val, Mu.val_pow_n]

/-- `ζ` as an element of `k̄`. -/
def toKbar (ζ : Mu n Ω) : kbar k Ω := ⟨_, mem_kbar ζ⟩

theorem toKbar_ne_zero (ζ : Mu n Ω) : toKbar n (k := k) ζ ≠ 0 := fun h => by
  have h' := congrArg Subtype.val h
  exact (Mu.val ζ).ne_zero h'

theorem toKbar_pow (ζ : Mu n Ω) : toKbar n (k := k) ζ ^ n = 1 := by
  apply Subtype.ext
  change ((Mu.val ζ : Ωˣ) : Ω) ^ n = 1
  rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]

/-- An `n`-th root of unity of `k̄` as an element of `μ_n(Ω)`. -/
def ofKbar {x : kbar k Ω} (hx : x ^ n = 1) : Mu n Ω :=
  Mu.mk (Units.mk0 (x : Ω) (fun h => by
    have h0 : x = 0 := Subtype.ext h
    rw [h0, zero_pow (NeZero.ne n)] at hx
    exact zero_ne_one hx)) (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact congrArg Subtype.val hx))

@[simp] theorem val_ofKbar {x : kbar k Ω} (hx : x ^ n = 1) :
    ((Mu.val (ofKbar n hx) : Ωˣ) : Ω) = x := rfl

theorem gk_pow (g : Gk k Ω) (ζ : Mu n Ω) : (g (toKbar n ζ)) ^ n = 1 := by
  rw [← map_pow, toKbar_pow, map_one]

/-- **`G_k = Gal(k̄/k)` acts on `μ_n(Ω) ⊆ k̄`.** -/
instance mulDistribMulAction_gk_mu : MulDistribMulAction (Gk k Ω) (Mu n Ω) where
  smul g ζ := ofKbar n (gk_pow n g ζ)
  one_smul ζ := Mu.ext (Units.ext rfl)
  mul_smul g h ζ := Mu.ext (Units.ext rfl)
  smul_mul g ζ η := Mu.ext (Units.ext (by
    change ((g (toKbar n (ζ * η)) : kbar k Ω) : Ω) = (g (toKbar n ζ) : Ω) * (g (toKbar n η) : Ω)
    rw [← IntermediateField.coe_mul, ← map_mul]
    rfl))
  smul_one g := Mu.ext (Units.ext (by
    change ((g (toKbar n (1 : Mu n Ω)) : kbar k Ω) : Ω) = 1
    rw [show toKbar n (1 : Mu n Ω) = (1 : kbar k Ω) from rfl, map_one]
    rfl))

theorem smul_mu_def (g : Gk k Ω) (ζ : Mu n Ω) :
    ((Mu.val (g • ζ) : Ωˣ) : Ω) = (g (toKbar n ζ) : Ω) := rfl

/-- The action of `h ∈ H` on `μ_n(Ω)` is that of its image in `G_k`. -/
theorem hToGk_smul_mu (h : D.H) (ζ : Mu n Ω) :
    ((Mu.val (hToGk D h • ζ) : Ωˣ) : Ω) = h • ((Mu.val ζ : Ωˣ) : Ω) := by
  rw [smul_mu_def]
  exact algebraMap_hToGk_apply D h (toKbar n ζ)

/-- **`Π_X` acts on `μ_n(Ω)` through `Π_X ↠ G_k`** (the cyclotomic action). -/
noncomputable instance mulDistribMulAction_piX_mu : MulDistribMulAction (PiX D) (Mu n Ω) :=
  MulDistribMulAction.compHom _ (piXToGk D)

theorem piX_smul_mu (u : PiX D) (ζ : Mu n Ω) : u • ζ = piXToGk D u • ζ := rfl

end Mu

/-! ### `E = Δ_X^{ab} ⋊ G_k` -/

section Semi

variable [Fact (Function.Surjective (piJ1ToGk D))]

/-- The action of `G_k` on `Δ_X^{ab}`, as a homomorphism into `MulAut`. -/
noncomputable def actAb : Gk k Ω →* MulAut (DeltaAb D) :=
  MulDistribMulAction.toMulAut (Gk k Ω) (DeltaAb D)

@[simp] theorem actAb_apply (g : Gk k Ω) (m : DeltaAb D) : actAb D g m = g • m := rfl

/-- **`E = Δ_X^{ab} ⋊ G_k`.** -/
abbrev EAb : Type u := SemidirectProduct (DeltaAb D) (Gk k Ω) (actAb D)

instance isTopologicalGroup_eAb : IsTopologicalGroup (EAb D) :=
  SemidirectProduct.isTopologicalGroup_of_continuous
    (continuous_smul : Continuous fun p : Gk k Ω × DeltaAb D => p.1 • p.2)

/-- `π : E → G_k`. -/
noncomputable abbrev piE : EAb D →* Gk k Ω := SemidirectProduct.rightHom

/-- `ε : G_k → E`. -/
noncomputable abbrev epsE : Gk k Ω →* EAb D := SemidirectProduct.inr

theorem continuous_piE : Continuous (piE D) := SemidirectProduct.continuous_right

theorem continuous_epsE : Continuous (epsE D) := SemidirectProduct.continuous_inr

theorem piE_epsE (g : Gk k Ω) : piE D (epsE D g) = g := rfl

/-- The kernel of `π` is commutative. -/
theorem piE_comm (a b : EAb D) (ha : piE D a = 1) (hb : piE D b = 1) : a * b = b * a := by
  have ha' : a.right = 1 := ha
  have hb' : b.right = 1 := hb
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, ha', hb', map_one, MulAut.one_apply]
    exact mul_comm _ _
  · simp only [SemidirectProduct.mul_right, ha', hb']

/-- The inversion of `Δ_X^{ab}` commutes with the `G_k`-action. -/
theorem inv_comm (g : Gk k Ω) :
    (MulEquiv.inv (DeltaAb D)).toMonoidHom.comp (actAb D g).toMonoidHom =
      (actAb D (MonoidHom.id _ g)).toMonoidHom.comp (MulEquiv.inv (DeltaAb D)).toMonoidHom :=
  MonoidHom.ext fun m => by simp [smul_inv']

/-- **The inversion `ι : (t, g) ↦ (t⁻¹, g)`** of `E` (`π₁([-1])` on `J`). -/
noncomputable def iotaE : EAb D →* EAb D :=
  SemidirectProduct.map (MulEquiv.inv (DeltaAb D)).toMonoidHom (MonoidHom.id _) (inv_comm D)

theorem continuous_iotaE : Continuous (iotaE D) :=
  SemidirectProduct.continuous_map _ _ _ continuous_inv continuous_id

theorem iotaE_epsE (g : Gk k Ω) : iotaE D (epsE D g) = epsE D g := by
  apply SemidirectProduct.ext <;> simp [iotaE]

theorem iotaE_ker (a : EAb D) (ha : piE D a = 1) : iotaE D a = a⁻¹ := by
  have ha' : a.right = 1 := ha
  apply SemidirectProduct.ext
  · simp [iotaE, SemidirectProduct.inv_left, ha']
  · simp [iotaE, ha']

/-- `E` acts on `μ_n(Ω)` through `π : E → G_k`. -/
noncomputable instance mulDistribMulAction_eAb_mu (n : ℕ) [NeZero n] :
    MulDistribMulAction (EAb D) (Mu n Ω) :=
  MulDistribMulAction.compHom _ (piE D)

theorem eAb_smul_mu {n : ℕ} [NeZero n] (e : EAb D) (ζ : Mu n Ω) : e • ζ = piE D e • ζ := rfl

end Semi

/-! ### `π_σ : Π_X → E` -/

section PiSigma

variable [Fact (Function.Surjective (piJ1ToGk D))]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- A continuous endomorphism of `Π_X` over `G_k`. -/
structure OverGk where
  /-- The endomorphism. -/
  toHom : PiX D →* PiX D
  continuous_toHom : Continuous toHom
  piXToGk_toHom : ∀ u, piXToGk D (toHom u) = piXToGk D u

variable {D}

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem OverGk.mul_inv_mem (σ : OverGk D) (u : PiX D) : u * (σ.toHom u)⁻¹ ∈ DeltaX D := by
  change u * (σ.toHom u)⁻¹ ∈ (piXToGk D).ker
  rw [MonoidHom.mem_ker, map_mul, map_inv, σ.piXToGk_toHom, mul_inv_cancel]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- `u ↦ [u σ̃(u)⁻¹] ∈ Δ_X^{ab}`. -/
noncomputable def diffAb (σ : OverGk D) (u : PiX D) : DeltaAb D :=
  deltaAbMk D ⟨u * (σ.toHom u)⁻¹, σ.mul_inv_mem u⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem deltaAbToPiJ1_diffAb (σ : OverGk D) (u : PiX D) :
    deltaAbToPiJ1 D (diffAb σ u) = piXToPiJ1 D (u * (σ.toHom u)⁻¹) := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- **`π_σ : Π_X →* Δ_X^{ab} ⋊ G_k`**, `u ↦ ([u σ̃(u)⁻¹], u|_{k̄})`. -/
noncomputable def piSigma (σ : OverGk D) : PiX D →* EAb D where
  toFun u := ⟨diffAb σ u, piXToGk D u⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change deltaAbMk D _ = 1
      rw [deltaAbMk_eq_one_iff]
      simp only [map_one, inv_one, mul_one]
      exact (commClosure D).one_mem
    · exact map_one _
  map_mul' u v := by
    apply SemidirectProduct.ext
    · change diffAb σ (u * v) = diffAb σ u * piXToGk D u • diffAb σ v
      apply deltaAbToPiJ1_injective D
      rw [map_mul, deltaAbToPiJ1_smul D _ _ (p := piXToPiJ1 D (σ.toHom u))
        (by rw [piJ1ToGk_piXToPiJ1, σ.piXToGk_toHom]), deltaAbToPiJ1_diffAb,
        deltaAbToPiJ1_diffAb, deltaAbToPiJ1_diffAb]
      simp only [← map_inv, ← map_mul]
      congr 1
      simp only [map_mul, map_inv]
      group
    · exact map_mul _ _ _

@[simp] theorem piSigma_left (σ : OverGk D) (u : PiX D) : (piSigma σ u).left = diffAb σ u := rfl

@[simp] theorem piSigma_right (σ : OverGk D) (u : PiX D) :
    (piSigma σ u).right = piXToGk D u := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem piE_piSigma (σ : OverGk D) (u : PiX D) : piE D (piSigma σ u) = piXToGk D u := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem continuous_diffAb (σ : OverGk D) : Continuous (diffAb σ) := by
  have h : Continuous fun u : PiX D => (⟨u * (σ.toHom u)⁻¹, σ.mul_inv_mem u⟩ : DeltaX D) :=
    (continuous_id.mul σ.continuous_toHom.inv).subtype_mk _
  exact (QuotientGroup.continuous_mk (N := (commClosure D).subgroupOf (DeltaX D))).comp h

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem continuous_piSigma (σ : OverGk D) : Continuous (piSigma σ) :=
  SemidirectProduct.continuous_mk (continuous_diffAb σ) (continuous_piXToGk D)

end PiSigma

/-! ### Functoriality of `π_σ` -/

section Map

variable {D} [Fact (Function.Surjective (piJ1ToGk D))]
  {t' : Ω} {D' : Pi1.Orbifold.GaloisData k t'} [IsGalois (K₀ k t') Ω]
  [Fact (Function.Surjective (piJ1ToGk D'))]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- A homomorphism `α : Π_X → Π_{X'}` over `G_k` maps `Δ_X` into `Δ_{X'}`. -/
theorem mem_deltaX_map (α : PiX D →* PiX D') (hα : ∀ u, piXToGk D' (α u) = piXToGk D u)
    {x : PiX D} (hx : x ∈ DeltaX D) : α x ∈ DeltaX D' := by
  change α x ∈ (piXToGk D').ker
  rw [MonoidHom.mem_ker, hα]
  exact hx

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- `α` maps the closed commutator subgroup into the closed commutator subgroup. -/
theorem mem_commClosure_map (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) {x : PiX D} (hx : x ∈ commClosure D) :
    α x ∈ commClosure D' := by
  have hle : ⁅DeltaX D, DeltaX D⁆ ≤ (commClosure D').comap α := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (mem_deltaX_map α hα ha) (mem_deltaX_map α hα hb))
  have hcl : IsClosed (((commClosure D').comap α : Subgroup (PiX D)) : Set (PiX D)) :=
    (isClosed_commClosure D').preimage hαc
  exact Subgroup.topologicalClosure_minimal _ hle hcl hx

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- `α : Δ_X → Δ_{X'}`. -/
noncomputable def resDelta (α : PiX D →* PiX D') (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) :
    DeltaX D →* DeltaX D' where
  toFun x := ⟨α (x : PiX D), mem_deltaX_map α hα x.2⟩
  map_one' := Subtype.ext (map_one α)
  map_mul' x y := Subtype.ext (map_mul α (x : PiX D) y)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- **`α^{ab} : Δ_X^{ab} → Δ_{X'}^{ab}`** induced by `α : Π_X → Π_{X'}` over `G_k`. -/
noncomputable def mapAb (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) : DeltaAb D →* DeltaAb D' :=
  QuotientGroup.map _ _ (resDelta α hα)
    fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact mem_commClosure_map α hαc hα (Subgroup.mem_subgroupOf.1 hx)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem mapAb_deltaAbMk (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (x : DeltaX D) :
    mapAb α hαc hα (deltaAbMk D x) = deltaAbMk D' ⟨α x, mem_deltaX_map α hα x.2⟩ := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem deltaAbToPiJ1_mapAb (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (m : DeltaAb D) {y : PiX D}
    (hy : deltaAbToPiJ1 D m = piXToPiJ1 D y) (hyΔ : y ∈ DeltaX D) :
    deltaAbToPiJ1 D' (mapAb α hαc hα m) = piXToPiJ1 D' (α y) := by
  have hm : m = deltaAbMk D ⟨y, hyΔ⟩ := deltaAbToPiJ1_injective D (by rw [hy]; rfl)
  rw [hm, mapAb_deltaAbMk]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem continuous_mapAb (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) : Continuous (mapAb α hαc hα) := by
  refine (QuotientGroup.isQuotientMap_mk
    ((commClosure D).subgroupOf (DeltaX D))).continuous_iff.2 ?_
  change Continuous fun x : DeltaX D =>
    (QuotientGroup.mk (resDelta α hα x) : DeltaX D' ⧸ (commClosure D').subgroupOf (DeltaX D'))
  exact (QuotientGroup.continuous_mk (N := (commClosure D').subgroupOf (DeltaX D'))).comp
    ((hαc.comp continuous_subtype_val).subtype_mk _)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- `α^{ab}` is `G_k`-equivariant. -/
theorem mapAb_smul (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (g : Gk k Ω) (m : DeltaAb D) :
    mapAb α hαc hα (g • m) = g • mapAb α hαc hα m := by
  obtain ⟨x, rfl⟩ := deltaAbMk_surjective D m
  obtain ⟨q, hq⟩ := piXToPiJ1_surjective D (liftGk D g)
  have hpg : piXToGk D q = g := by
    have := piJ1ToGk_liftGk D g
    rw [← hq] at this
    exact this
  apply deltaAbToPiJ1_injective D'
  have hconj : q * (x : PiX D) * q⁻¹ ∈ DeltaX D := (normal_deltaX D).conj_mem _ x.2 q
  rw [deltaAbToPiJ1_mapAb α hαc hα (g • deltaAbMk D x) (y := q * x * q⁻¹) ?_ hconj,
    deltaAbToPiJ1_smul D' g _ (p := piXToPiJ1 D' (α q))
      (by rw [piJ1ToGk_piXToPiJ1, hα, hpg]),
    deltaAbToPiJ1_mapAb α hαc hα _ (y := x) rfl x.2]
  · simp only [map_mul, map_inv]
  · rw [deltaAbToPiJ1_smul D g _ (p := piXToPiJ1 D q) (by rw [piJ1ToGk_piXToPiJ1, hpg]),
      deltaAbToPiJ1_deltaAbMk]
    simp only [map_mul, map_inv]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- `α^{ab} ⋊ id : E → E'`. -/
noncomputable def mapE (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) : EAb D →* EAb D' :=
  SemidirectProduct.map (mapAb α hαc hα) (MonoidHom.id _)
    fun g => MonoidHom.ext fun m => mapAb_smul α hαc hα g m

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem continuous_mapE (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) : Continuous (mapE α hαc hα) :=
  SemidirectProduct.continuous_map _ _ _ (continuous_mapAb α hαc hα) continuous_id

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem piE_mapE (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (e : EAb D) :
    piE D' (mapE α hαc hα e) = piE D e :=
  DFunLike.congr_fun (SemidirectProduct.rightHom_comp_map (φ₁ := actAb D) (φ₂ := actAb D')
    (mapAb α hαc hα) (MonoidHom.id _) fun g => MonoidHom.ext fun m => mapAb_smul α hαc hα g m) e

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem mapE_epsE (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (g : Gk k Ω) :
    mapE α hαc hα (epsE D g) = epsE D' g := by
  apply SemidirectProduct.ext
  · exact map_one _
  · rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
/-- **Functoriality of `π_σ`**: if `α ∘ σ̃ = σ̃' ∘ α` then `π_{σ'} ∘ α = (α^{ab} ⋊ id) ∘ π_σ`. -/
theorem map_piSigma (σ : OverGk D) (σ' : OverGk D') (α : PiX D →* PiX D') (hαc : Continuous α)
    (hα : ∀ u, piXToGk D' (α u) = piXToGk D u) (hσα : ∀ u, α (σ.toHom u) = σ'.toHom (α u))
    (u : PiX D) : piSigma σ' (α u) = mapE α hαc hα (piSigma σ u) := by
  apply SemidirectProduct.ext
  · change diffAb σ' (α u) = mapAb α hαc hα (diffAb σ u)
    apply deltaAbToPiJ1_injective D'
    rw [deltaAbToPiJ1_mapAb α hαc hα _ (y := u * (σ.toHom u)⁻¹) rfl (σ.mul_inv_mem u),
      deltaAbToPiJ1_diffAb]
    simp only [map_mul, map_inv, hσα]
  · exact hα u

end Map

end CurvesJacobian.LocAn.SemiAb
