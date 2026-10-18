/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PointRestriction
import CurvesJacobian.Kummer.CompletionMap
import ContinuousKummerTheory.Curve.ClosedPoint

/-!
# The `Ẑ(1)`-level restriction `η|_x = s_x^*(η)` to a closed point

[AbsTopIII] Prop. 1.8 (T3 l.2078–2087) restricts `η ∈ H¹(Π_U, M_X)` to points `x ∈ U(k_x)`,
`k_x / k` finite: `η|_x := s_x^*(η) ∈ H¹(G_{k_x}, M_X)` for the (outer) homomorphism
`s_x : G_{k_x} → Π_U`. In `pi1`'s Galois model (`U = Spec R`, `D.HL = D.H`) a closed point is a
place `A ⊇ k` of `Ω` with `t ∈ A`, `k_x = Decomposition.pointField (F D) A …` (the residues of
`A ∩ F`) and `G_{k_x} = Gal(κ(A)/k_x)`, `κ(A) ≅ k̄`:

* `CurvesJacobian.Kummer.decompToGkx : D_A → Gal(κ(A)/k_x)`, continuous and surjective
  (`decompToGkx_surjective`, from continuous-kummer-theory's `range_decompositionMap`);
* `CurvesJacobian.Kummer.closedSectionMap : Gal(κ(A)/k_x) → Π_U`, the descent of
  `decompToPi : D_A → Π_U` (the inertia dies in `Π_U`), i.e. `s_x`;
* `CurvesJacobian.Kummer.restrictClosed : H¹(Π_U, Ẑ(1)) → H¹(G_{k_x}, Ẑ(1))`, `η ↦ η|_x`;
* `restrictClosed_eq_one_iff`: **`η|_x = 0` iff all level-`n` restrictions of `η` along
  `D_A → Π_U` vanish** (`H¹(-, Ẑ(1)) = lim H¹(-, μ_n)` and injectivity of inflation along
  `D_A ↠ G_{k_x}`): the formulation of `η|_x = 0` used in `Kummer/ClosedPoints.lean` and
  continuous-kummer-theory's `Curve/ClosedPoint.lean` is equivalent to `s_x^*(η) = 0`;
* `restrictClosed_kummerMapZHat`: **`κ_U(u)|_x = κ_{k_x}(u(x))`**;
* `kummerZHatEquiv_restrictClosed_constMapZHat`: for `c ∈ (kˣ)^∧`, `c|_x = c|_{G_{k_x}}`, the
  image of `c` under `(kˣ)^∧ → (k_xˣ)^∧`.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing

namespace CurvesJacobian.Kummer

universe u

section Gkx

variable {k : Type*} (F : Type*) {Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F]
  [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

/-- **`D_A → G_{k_x} = Gal(κ(A)/k_x)`**: the decomposition map, which fixes `k_x`. -/
noncomputable def decompToGkx :
    A.decompositionSubgroup F →*
      (ResidueField A ≃ₐ[Decomposition.pointField F A hk hkres] ResidueField A) where
  toFun σ :=
    { Decomposition.decompositionMap F A hk hkres σ with
      commutes' := fun y =>
        Decomposition.decompositionMap_apply_of_mem_pointField F A hk hkres σ y.2 }
  map_one' := AlgEquiv.ext fun y => by
    change Decomposition.decompositionMap F A hk hkres 1 y = y
    rw [map_one]
    rfl
  map_mul' σ τ := AlgEquiv.ext fun y => by
    change Decomposition.decompositionMap F A hk hkres (σ * τ) y = _
    rw [map_mul]
    rfl

lemma decompToGkx_apply (σ : A.decompositionSubgroup F) (y : ResidueField A) :
    decompToGkx F A hk hkres σ y = Decomposition.decompositionMap F A hk hkres σ y := rfl

lemma decompToGkx_eq_one_iff (σ : A.decompositionSubgroup F) :
    decompToGkx F A hk hkres σ = 1 ↔ Decomposition.decompositionMap F A hk hkres σ = 1 := by
  constructor
  · intro h
    exact AlgEquiv.ext fun y => DFunLike.congr_fun h y
  · intro h
    exact AlgEquiv.ext fun y => DFunLike.congr_fun h y

/-- `D_A → G_{k_x}` is continuous for the Krull topology. -/
theorem continuous_decompToGkx [Algebra.IsIntegral F Ω] :
    Continuous (decompToGkx F A hk hkres) := by
  set K := Decomposition.pointField F A hk hkres
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K _ U).1 hU
  obtain ⟨T, htfin, rfl⟩ := IntermediateField.fg_def.1
    (E.fg_of_fg_toSubalgebra (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.1 hE)))
  choose lift hlift using fun x : ResidueField A => residue_surjective x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((Filter.biInter_mem htfin).2 fun x _ =>
    ((continuous_subtype_val (p := (· ∈ A.decompositionSubgroup F)).isOpen_preimage _
      (stabilizer_isOpen_of_isIntegral ((lift x : A) : Ω))).mem_nhds
        (show (1 : Gal(Ω/F)) ∈ MulAction.stabilizer _ _ from one_mem _))) ?_
  intro σ hσ
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    at hσ
  apply hEU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff K
    (decompToGkx F A hk hkres σ)).2 (fun y hy => ?_) x hx
  rw [AlgEquiv.smul_def, decompToGkx_apply, ← hlift y, Decomposition.decompositionMap_residue]
  congr 1
  exact Subtype.ext (hσ y hy)

/-- **`D_A ↠ G_{k_x}`** ([AbsTopIII] Prop. 1.8: the decomposition group of a closed point surjects
onto the absolute Galois group of its residue field). -/
theorem decompToGkx_surjective [IsAlgClosed Ω] [IsGalois F Ω]
    [Algebra.IsIntegral k (ResidueField A)] : Function.Surjective (decompToGkx F A hk hkres) := by
  intro τ
  have hτ : τ.restrictScalars k ∈ (Decomposition.pointField F A hk hkres).fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => τ.commutes ⟨y, hy⟩
  rw [← Decomposition.range_decompositionMap] at hτ
  obtain ⟨σ, hσ⟩ := hτ
  exact ⟨σ, AlgEquiv.ext fun y => DFunLike.congr_fun hσ y⟩

end Gkx

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] [IsAlgClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)] (hHL : D.HL = D.H) (ht : t ∈ A)

/-- **The homomorphism `s_x : G_{k_x} → Π_U` of a closed point `x` of `U`**: the descent of
`D_A → Π_U` along `D_A ↠ G_{k_x}` (the inertia of `A` dies in `Π_U`). -/
noncomputable def closedSectionMap :
    (ResidueField A ≃ₐ[Decomposition.pointField (F D) A hk hkres] ResidueField A) →* Pi D :=
  (decompToGkx (F D) A hk hkres).liftOfSurjective (decompToGkx_surjective (F D) A hk hkres)
    ⟨decompToPi D A, fun σ hσ => ker_decompositionMap_le_ker_decompToPi D A hk hkres hHL ht
      ((decompToGkx_eq_one_iff (F D) A hk hkres σ).1 hσ)⟩

omit [CharZero k] in
theorem closedSectionMap_decompToGkx (σ : A.decompositionSubgroup (F D)) :
    closedSectionMap D A hk hkres hHL ht (decompToGkx (F D) A hk hkres σ) = decompToPi D A σ :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ σ

instance isIntegral_pointField :
    Algebra.IsIntegral (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
  Algebra.IsIntegral.tower_top k

omit [CharZero k] in
theorem continuous_closedSectionMap : Continuous (closedSectionMap D A hk hkres hHL ht) := by
  have hc := continuous_decompToGkx (F := F D) A hk hkres
  have hq := IsClosedMap.isQuotientMap hc.isClosedMap hc (decompToGkx_surjective (F D) A hk hkres)
  rw [hq.continuous_iff]
  have : (closedSectionMap D A hk hkres hHL ht) ∘ (decompToGkx (F D) A hk hkres) = decompToPi D A :=
    funext (closedSectionMap_decompToGkx D A hk hkres hHL ht)
  rw [this]
  exact continuous_decompToPi D A

section Level

variable (n : ℕ) [NeZero n]

/-- `s_x` is compatible with the reduction `μ_n(Ω) → μ_n(κ(A))`. -/
theorem reduceMu_closedSectionMap_smul
    (g : ResidueField A ≃ₐ[Decomposition.pointField (F D) A hk hkres] ResidueField A)
    (ζ : Mu n Ω) :
    Decomposition.reduceMu A n (NeZero.ne n) (closedSectionMap D A hk hkres hHL ht g • ζ) =
      g • Decomposition.reduceMu A n (NeZero.ne n) ζ := by
  letI := Decomposition.muAction (F D) A hk hkres n
  obtain ⟨σ, rfl⟩ := decompToGkx_surjective (F D) A hk hkres g
  rw [closedSectionMap_decompToGkx]
  exact reduceMu_decompToPi_smul D A hk hkres n σ ζ

/-- Restriction along `D_A → Π_U` factors through `s_x`: `res_{D_A} = infl ∘ s_x^*`. -/
theorem map_decompToGkx_map_closedSectionMap (η : ContH1 (Pi D) (Mu n Ω)) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToGkx (F D) A hk hkres) (continuous_decompToGkx (F D) A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl)
        (ContH1.map (closedSectionMap D A hk hkres hHL ht)
          (continuous_closedSectionMap D A hk hkres hHL ht)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_closedSectionMap_smul D A hk hkres hHL ht n) η) =
      ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) η := by
  letI := Decomposition.muAction (F D) A hk hkres n
  induction η using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk, ContH1.map_mk, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp [ContH1.cocyclesMap_apply, closedSectionMap_decompToGkx]

/-- `s_x^*` vanishes at level `n` iff the restriction along `D_A → Π_U` does (inflation along
`D_A ↠ G_{k_x}` is injective). -/
theorem map_closedSectionMap_eq_one_iff (η : ContH1 (Pi D) (Mu n Ω)) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (closedSectionMap D A hk hkres hHL ht)
        (continuous_closedSectionMap D A hk hkres hHL ht)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_closedSectionMap_smul D A hk hkres hHL ht n) η = 1 ↔
      ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) η = 1 := by
  letI := Decomposition.muAction (F D) A hk hkres n
  rw [← map_decompToGkx_map_closedSectionMap D A hk hkres hHL ht n η]
  have hinj := ContH1.map_id_injective_of_surjective (decompToGkx (F D) A hk hkres)
    (continuous_decompToGkx (F D) A hk hkres) (decompToGkx_surjective (F D) A hk hkres)
    (M := Mu n (ResidueField A)) (fun _ _ => rfl)
  rw [← map_one (ContH1.map (decompToGkx (F D) A hk hkres) (continuous_decompToGkx (F D) A hk hkres)
    (MonoidHom.id (Mu n (ResidueField A))) continuous_id (fun _ _ => rfl))]
  exact hinj.eq_iff.symm

end Level

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- `s_x` is compatible with the reduction `Ẑ(1)_Ω → Ẑ(1)_{κ(A)}`. -/
lemma reduceZHat_closedSectionMap_smul
    (g : ResidueField A ≃ₐ[Decomposition.pointField (F D) A hk hkres] ResidueField A)
    (x : ZHatOne (F D) Ω) :
    reduceZHat (k := Decomposition.pointField (F D) A hk hkres) A (F D)
        (closedSectionMap D A hk hkres hHL ht g • x) =
      g • reduceZHat (k := Decomposition.pointField (F D) A hk hkres) A (F D) x := by
  apply Subtype.ext
  funext i
  haveI : NeZero i.n := ⟨i.n_ne_zero⟩
  change Decomposition.reduceMu A i.n i.n_ne_zero
      (ZHatOne.proj (liftIndex (F D) i) (closedSectionMap D A hk hkres hHL ht g • x)) = _
  rw [proj_pi_smul]
  exact reduceMu_closedSectionMap_smul D A hk hkres hHL ht i.n g _

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **The restriction `η|_x = s_x^*(η)`** of `η ∈ H¹(Π_U, Ẑ(1))` to a closed point `x` of `U`
([AbsTopIII] Prop. 1.8, T3 l.2080–2087), with values in `H¹(G_{k_x}, Ẑ(1))`,
`G_{k_x} = Gal(κ(A)/k_x)`. -/
noncomputable def restrictClosed :
    ContH1 (Pi D) (ZHatOne (F D) Ω) →*
      ContH1 (ResidueField A ≃ₐ[Decomposition.pointField (F D) A hk hkres] ResidueField A)
        (ZHatOne (Decomposition.pointField (F D) A hk hkres) (ResidueField A)) :=
  ContH1.map (closedSectionMap D A hk hkres hHL ht)
    (continuous_closedSectionMap D A hk hkres hHL ht) (reduceZHat A (F D))
    (continuous_reduceZHat A (F D)) (reduceZHat_closedSectionMap_smul D A hk hkres hHL ht)

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- The `μ_n`-component of `η|_x`. -/
lemma h1Proj_restrictClosed (i : KummerIndex (Decomposition.pointField (F D) A hk hkres))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    h1Proj _ (ResidueField A) i (restrictClosed D A hk hkres hHL ht η) =
      ContH1.map (closedSectionMap D A hk hkres hHL ht)
        (continuous_closedSectionMap D A hk hkres hHL ht)
        (Decomposition.reduceMu A i.n (NeZero.ne i.n)) continuous_of_discreteTopology
        (reduceMu_closedSectionMap_smul D A hk hkres hHL ht i.n)
        (ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj (liftIndex (F D) i))
          (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) η) := by
  induction η using ContH1.induction_on with
  | h c => rfl

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **Closing the formulation gap of `η|_x = 0`** ([AbsTopIII] Prop. 1.8(i)): `s_x^*(η) = 0` in
`H¹(G_{k_x}, Ẑ(1))` iff for every `n` the restriction of the `μ_n`-component of `η` along
`D_A → Π_U` vanishes. -/
theorem restrictClosed_eq_one_iff (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    restrictClosed D A hk hkres hHL ht η = 1 ↔
      ∀ i : KummerIndex (F D),
        letI := Decomposition.muAction (F D) A hk hkres i.n
        ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A i.n (NeZero.ne i.n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres i.n)
          (ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i)
            (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) η) = 1 := by
  set K := Decomposition.pointField (F D) A hk hkres
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI := isAlgClosed_residueField A hk hkres
  rw [← (h1ToLimit_injective K (ResidueField A)).eq_iff, map_one]
  constructor
  · intro h i
    have hi := congrArg (fun y : H1Limit K (ResidueField A) => y.1
      ⟨i.n, Nat.cast_ne_zero.mpr i.n_ne_zero⟩) h
    simp only [h1ToLimit_apply] at hi
    rw [h1Proj_restrictClosed] at hi
    exact (map_closedSectionMap_eq_one_iff D A hk hkres hHL ht i.n _).1 hi
  · intro h
    apply Subtype.ext
    funext j
    rw [h1ToLimit_apply, h1Proj_restrictClosed]
    exact (map_closedSectionMap_eq_one_iff D A hk hkres hHL ht j.n _).2 (h (liftIndex (F D) j))

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- The value `u(x) ∈ k_xˣ` of a unit `u` of `U` at the closed point below `A`. -/
noncomputable def unitValue (u : units D) (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    (Decomposition.pointField (F D) A hk hkres)ˣ where
  val := ⟨residue A ⟨_, hu⟩, Decomposition.residue_mem_pointField (F D) A hk hkres _ hu⟩
  inv := ⟨residue A ⟨_, hu'⟩, Decomposition.residue_mem_pointField (F D) A hk hkres _ hu'⟩
  val_inv := Subtype.ext (by
    change residue A ⟨_, hu⟩ * residue A ⟨_, hu'⟩ = 1
    rw [← map_mul, ← map_one (residue A)]
    congr 1
    apply Subtype.ext
    change algebraMap (F D) Ω _ * algebraMap (F D) Ω _ = 1
    rw [← map_mul, Units.mul_inv, map_one])
  inv_val := Subtype.ext (by
    change residue A ⟨_, hu'⟩ * residue A ⟨_, hu⟩ = 1
    rw [← map_mul, ← map_one (residue A)]
    congr 1
    apply Subtype.ext
    change algebraMap (F D) Ω _ * algebraMap (F D) Ω _ = 1
    rw [← map_mul, Units.inv_mul, map_one])

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)] in
lemma coe_unitValue (u : units D) (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    (((unitValue D A hk hkres u hu hu' : (Decomposition.pointField (F D) A hk hkres)ˣ) :
      Decomposition.pointField (F D) A hk hkres) : ResidueField A) = residue A ⟨_, hu⟩ := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`κ_U(u)|_x = κ_{k_x}(u(x))`** at level `n`. -/
theorem closedSectionMap_kummerMap (n : ℕ) [NeZero n] (u : units D)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI : NeZero ((n : ℕ) : Decomposition.pointField (F D) A hk hkres) :=
      ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
    ContH1.map (closedSectionMap D A hk hkres hHL ht)
        (continuous_closedSectionMap D A hk hkres hHL ht)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_closedSectionMap_smul D A hk hkres hHL ht n) (kummerMap D n u) =
      kummer n _ (ResidueField A) (unitValue D A hk hkres u hu hu') := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI : NeZero ((n : ℕ) : Decomposition.pointField (F D) A hk hkres) :=
    ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  letI := Decomposition.muAction (F D) A hk hkres n
  refine ContH1.map_id_injective_of_surjective (decompToGkx (F D) A hk hkres)
    (continuous_decompToGkx (F D) A hk hkres) (decompToGkx_surjective (F D) A hk hkres)
    (M := Mu n (ResidueField A)) (fun _ _ => rfl) ?_
  rw [map_decompToGkx_map_closedSectionMap, decompToPi_kummerMap]
  exact map_kummer_eq_map_kummer n (A.decompositionSubgroup (F D)).subtype
    (decompToGkx (F D) A hk hkres) (fun _ _ => rfl) A.toSubring
    (Decomposition.mem_of_pow_mem_toSubring A n (NeZero.ne n))
    (Decomposition.smul_mem_toSubring (F D) A) (residue A)
    (Decomposition.residue_smul_eq (F D) A hk hkres) continuous_subtype_val
    (continuous_decompToGkx (F D) A hk hkres) _ _ hu hu' rfl

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`κ_U(u)|_x = κ_{k_x}(u(x))`** at the `Ẑ(1)`-level ([AbsTopIII] Prop. 1.8), for a closed
point `x` of `U` with residue field `k_x`. -/
theorem restrictClosed_kummerMapZHat (u : units D) (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
      IsGalois.tower_top_intermediateField _
    restrictClosed D A hk hkres hHL ht (kummerMapZHat D u) =
      kummerZHat _ (ResidueField A) (unitValue D A hk hkres u hu hu') := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  refine h1ToLimit_injective _ (ResidueField A) (Subtype.ext (funext fun j => ?_))
  have e1 : h1Proj _ (ResidueField A) j (restrictClosed D A hk hkres hHL ht (kummerMapZHat D u)) =
      kummer j.n _ (ResidueField A) (unitValue D A hk hkres u hu hu') := by
    rw [h1Proj_restrictClosed, map_proj_kummerMapZHat]
    exact closedSectionMap_kummerMap D A hk hkres hHL ht j.n u hu hu'
  exact e1.trans (h1Proj_kummerZHat _ (ResidueField A) j _).symm

section Constants

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`D_A → Π_U → G_k` is the restriction `G_{k_x} → G_k`** along `k̄ ≅ κ(A)`. -/
theorem piToGk_closedSectionMap_eq_galRestrict
    (g : ResidueField A ≃ₐ[Decomposition.pointField (F D) A hk hkres] ResidueField A) :
    letI := kbarAlgebra A hk
    haveI := isScalarTower_kbarAlgebra A hk hkres
    piToGk D (closedSectionMap D A hk hkres hHL ht g) =
      galRestrict k (Decomposition.pointField (F D) A hk hkres) (kbar k Ω) (ResidueField A) g := by
  letI := kbarAlgebra A hk
  haveI := isScalarTower_kbarAlgebra A hk hkres
  obtain ⟨σ, rfl⟩ := decompToGkx_surjective (F D) A hk hkres g
  rw [closedSectionMap_decompToGkx]
  refine AlgEquiv.ext fun y => (kbarResidue A hk).injective ?_
  have h1 := algebraMap_galRestrict_apply (K := k)
    (L := Decomposition.pointField (F D) A hk hkres) (decompToGkx (F D) A hk hkres σ) y
  change kbarResidue A hk _ = kbarResidue A hk _
  change kbarResidue A hk _ = decompToGkx (F D) A hk hkres σ (kbarResidue A hk y) at h1
  rw [h1, decompToGkx_apply, kbarResidue_piToGk_decompToPi]

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **Classes from `G_k` restrict to their restrictions to `G_{k_x}`** along `s_x`, at level
`n`. -/
theorem closedSectionMap_map_piToGk (n : ℕ) [NeZero n]
    (η : ContH1 (Gk k Ω) (Mu n (kbar k Ω))) :
    letI := kbarAlgebra A hk
    haveI := isScalarTower_kbarAlgebra A hk hkres
    ContH1.map (closedSectionMap D A hk hkres hHL ht)
        (continuous_closedSectionMap D A hk hkres hHL ht)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_closedSectionMap_smul D A hk hkres hHL ht n)
        (ContH1.map (piToGk D) (continuous_piToGk D) (muMap n (kbar k Ω) Ω)
          continuous_of_discreteTopology (muMap_piToGk_smul D n) η) =
      restriction k (Decomposition.pointField (F D) A hk hkres) (kbar k Ω) (ResidueField A) n
        η := by
  letI := kbarAlgebra A hk
  haveI := isScalarTower_kbarAlgebra A hk hkres
  rw [ContH1.map_map]
  induction η using ContH1.induction_on with
  | h c =>
    rw [restriction, ContH1.map_mk, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext g
    simp only [ContH1.cocyclesMap_apply, MonoidHom.coe_comp, Function.comp_apply]
    rw [reduceMu_muMap, piToGk_closedSectionMap_eq_galRestrict D A hk hkres hHL ht g]

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- The `μ_n`-component of `c|_x` for a constant class `c`. -/
lemma h1Proj_restrictClosed_constMapZHat
    (j : KummerIndex (Decomposition.pointField (F D) A hk hkres)) (c : KummerCompletion k) :
    h1Proj _ (ResidueField A) j (restrictClosed D A hk hkres hHL ht (constMapZHat D c)) =
      ContH1.map (closedSectionMap D A hk hkres hHL ht)
        (continuous_closedSectionMap D A hk hkres hHL ht)
        (Decomposition.reduceMu A j.n (NeZero.ne j.n)) continuous_of_discreteTopology
        (reduceMu_closedSectionMap_smul D A hk hkres hHL ht j.n)
        (ContH1.map (piToGk D) (continuous_piToGk D) (muMap j.n (kbar k Ω) Ω)
          continuous_of_discreteTopology (muMap_piToGk_smul D j.n)
          (h1Proj k (kbar k Ω) (reindex j) ((kummerZHatEquiv k (kbar k Ω)).symm c))) := by
  rw [constMapZHat_apply]
  induction (kummerZHatEquiv k (kbar k Ω)).symm c using ContH1.induction_on with
  | h c' => rfl

set_option maxHeartbeats 1000000 in
-- the rewrites below unify large `ContH1.map` terms over `Gal(κ(A)/k_x)`
set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`c|_x = c|_{G_{k_x}}`** for constant classes: under `H¹(G_{k_x}, Ẑ(1)) ≃ (k_xˣ)^∧`, the
restriction of `constMapZHat c` to the closed point `x` is the image of `c ∈ (kˣ)^∧` in
`(k_xˣ)^∧` ([AbsTopIII] Prop. 1.8(ii), `η|_{G_{k_x}}`). -/
theorem kummerZHatEquiv_restrictClosed_constMapZHat (c : KummerCompletion k) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
      IsGalois.tower_top_intermediateField _
    kummerZHatEquiv _ (ResidueField A) (restrictClosed D A hk hkres hHL ht (constMapZHat D c)) =
      completionMap (algebraMap k (Decomposition.pointField (F D) A hk hkres)) c := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  rw [← MulEquiv.eq_symm_apply]
  refine h1ToLimit_injective _ (ResidueField A) (Subtype.ext (funext fun j => ?_))
  have h2 : h1Proj k (kbar k Ω) (reindex j) ((kummerZHatEquiv k (kbar k Ω)).symm c) =
      kummerEquiv j.n k (kbar k Ω) (c.1 (reindex j)) := by
    change ((h1ZHatOneEquiv k (kbar k Ω)) ((h1ZHatOneEquiv k (kbar k Ω)).symm
      (kummerLimitEquiv k (kbar k Ω) c))).1 (reindex j) = _
    rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]
    rfl
  have h3 : h1Proj _ (ResidueField A) j ((kummerZHatEquiv _ (ResidueField A)).symm
      (completionMap (algebraMap k (Decomposition.pointField (F D) A hk hkres)) c)) =
      kummerEquiv j.n _ (ResidueField A)
        (quotMap (algebraMap k (Decomposition.pointField (F D) A hk hkres)) j.n
          (c.1 (reindex j))) := by
    change ((h1ZHatOneEquiv _ (ResidueField A)) ((h1ZHatOneEquiv _ (ResidueField A)).symm
      (kummerLimitEquiv _ (ResidueField A) _))).1 j = _
    rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]
    rfl
  have e1 : h1Proj _ (ResidueField A) j (restrictClosed D A hk hkres hHL ht (constMapZHat D c)) =
      kummerEquiv j.n _ (ResidueField A)
        (quotMap (algebraMap k (Decomposition.pointField (F D) A hk hkres)) j.n
          (c.1 (reindex j))) := by
    rw [h1Proj_restrictClosed_constMapZHat, h2]
    letI := kbarAlgebra A hk
    haveI := isScalarTower_kbarAlgebra A hk hkres
    rw [closedSectionMap_map_piToGk]
    induction c.1 (reindex j) using QuotientGroup.induction_on with
    | H a =>
      exact restriction_kummer (ΩK := kbar k Ω) (ΩL := ResidueField A) j.n a
  exact e1.trans h3.symm

end Constants

end CurvesJacobian.Kummer
