/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianH1Reduction
import CurvesJacobian.Kummer.WeilKummer

/-!
# Kummer characters of `Δ_X^{ab}` and the duality `Δ_X^{ab}/N ≅ Hom(J[N], μ_N)`

Galois model `D : GaloisData k t` (`char k = 0`, `Ω` algebraically closed and Galois over
`k(t)`), `F k̄ = F (baseChange D)`, `J(k̄)[n] = Pic(F k̄)[n]`, `Δ̃ = deltaTilde D ⊆ H` the preimage
of `Δ_X` (the elements of `H` fixing `k̄`, equivalently `F k̄`).

For `a ∈ J(k̄)[n]` with representative `n E = div f` and a Kummer root `αⁿ = f`, the **Kummer
character** `χ_a(s) = s(α)/α ∈ μ_n ⊆ k̄` of `s ∈ Δ̃` (`kChar`) does not depend on the choices
(`kVal_eq`, via `CurvesJacobian.kummer_ratio_eq`). This file shows:

* `χ_a` is a homomorphism `Δ̃ → k̄ˣ`, additive in `a` (`kChar_add`), compatible across levels
  (`kChar_ofMul`: `χ^{(n)}_{m a} = (χ^{(nm)}_a)^m`) and `H`-equivariant
  (`kVal_conj`: `χ_{h a}(h s h⁻¹) = h(χ_a(s))`);
* it is the character of `Π_{X_{k̄}}` attached to `a` by Kummer theory
  (`val_picTorsionEquivPiChars`, [Milne, *Abelian Varieties*, III.9.2] in the form
  `picTorsionEquivPiChars`), along `ι : H_{k̄} ≅ Δ̃` (`bcToDeltaTilde`);
* it kills all inertia and the closed commutator subgroup, hence **factors through `Δ_X^{ab}`**
  (`kCharAb`, `kCharAb_deltaTildeToAb`); `kerAb n = ⋂_{a ∈ J[n]} ker χ_a` is closed.

Separation of points and the duality `Δ_X^{ab} ↠ Hom(J[n], k̄ˣ)` are in
`Kummer/DeltaAbDuality.lean`.

With the Weil pairing (`weilDual_bijective_baseChange`) this is the `G_k`-equivariant
`Δ_X^{ab}/n ≅ Hom(J[n], μ_n) ≅ J[n]` of [Cusp] Prop. 2.3(i) (MR5 J4), used in
`Kummer/PrincipalEta.lean`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

set_option linter.unusedSectionVars false

/-- A representative `TorsRep` transported along an equality of classes. -/
def CurvesJacobian.TorsRep.cast' {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [IsAlgClosed κ]
    [IsFunctionField κ K] {n : ℕ} {a b : Pic κ K} (r : CurvesJacobian.TorsRep n a) (h : a = b) :
    CurvesJacobian.TorsRep n b :=
  ⟨r.D, r.f, r.f_ne, r.mk_eq.trans h, r.nsmul_eq⟩

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

/-- Shortcut instance: `k̄ → F k̄` (finding it through `K₀ k̄ t` takes several hundred ms). -/
noncomputable instance algebra_kbar_F_baseChange : Algebra (kbar k Ω) (F (baseChange D)) :=
  inferInstance

/-! ### Kummer roots and the values `s(α)/α` -/

section Values

/-- Elements of `Δ̃` act trivially on `G_k`. -/
lemma hToGk_deltaTilde (s : deltaTilde D) : hToGk D (s : D.H) = 1 := s.2

/-- Elements of `Δ̃` fix `k̄`. -/
lemma deltaTilde_fixes_kbar (s : deltaTilde D) {x : Ω} (hx : x ∈ kbar k Ω) :
    ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = x :=
  (hToGk_eq_one_iff D _).1 (hToGk_deltaTilde s) x hx

/-- Elements of `Δ̃` fix `F k̄`. -/
lemma deltaTilde_fixes (s : deltaTilde D) (x : F (baseChange D)) :
    ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) = x :=
  fixes_F_baseChange D (s : D.H).2 (fun _ hy => deltaTilde_fixes_kbar s hy) x.2

variable {n : ℕ} [NeZero n]

variable (n) in
/-- The chosen representative `n E = div f` of `a ∈ J(k̄)[n]`. -/
noncomputable def kRep (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    TorsRep n (a : Pic (kbar k Ω) (F (baseChange D))) :=
  (TorsRep.exists a.2).some

/-- The chosen Kummer root `αⁿ = f`. -/
noncomputable def kRoot (a : picTorsion (kbar k Ω) (F (baseChange D)) n) : Ω :=
  (CurvesJacobian.exists_root (Ω := Ω) (kRep n a)).choose

lemma kRoot_pow (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    kRoot a ^ n = algebraMap (F (baseChange D)) Ω (kRep n a).f :=
  (CurvesJacobian.exists_root (Ω := Ω) (kRep n a)).choose_spec

lemma root_ne_zero {a : Pic (kbar k Ω) (F (baseChange D))} (r : TorsRep n a) {β : Ω}
    (hβ : β ^ n = algebraMap (F (baseChange D)) Ω r.f) : β ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n)] at hβ
  exact r.f_ne ((algebraMap _ Ω).injective (by rw [map_zero]; exact hβ.symm))

/-- `χ_a(s) = s(α)/α`. -/
noncomputable def kVal (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) : Ω :=
  ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) (kRoot a) / kRoot a

/-- **`χ_a(s) = s(β)/β` for every representative and every Kummer root.** -/
lemma kVal_eq (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (r : TorsRep n (a : Pic (kbar k Ω) (F (baseChange D)))) {β : Ω}
    (hβ : β ^ n = algebraMap (F (baseChange D)) Ω r.f) (s : deltaTilde D) :
    kVal a s = ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) β / β := by
  have := kummer_ratio_eq (kRep n a) r (NeZero.ne n) (kRoot_pow a) hβ
    ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (fun g => deltaTilde_fixes s g)
  exact this.symm

lemma kVal_pow (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kVal a s ^ n = 1 := by
  have h0 := root_ne_zero (kRep n a) (kRoot_pow a)
  rw [kVal, div_pow, ← map_pow, kRoot_pow]
  have hf : algebraMap (F (baseChange D)) Ω (kRep n a).f ≠ 0 :=
    (map_ne_zero _).mpr (kRep n a).f_ne
  rw [show ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) (algebraMap (F (baseChange D)) Ω (kRep n a).f) =
      algebraMap (F (baseChange D)) Ω (kRep n a).f from deltaTilde_fixes s _, div_self hf]

lemma kVal_ne_zero (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kVal a s ≠ 0 := by
  have h0 := root_ne_zero (kRep n a) (kRoot_pow a)
  exact div_ne_zero ((map_ne_zero _).mpr h0) h0

lemma kVal_mem (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kVal a s ∈ kbar k Ω :=
  mem_kbar_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne n)) (kVal_pow a s)

lemma kVal_one (a : picTorsion (kbar k Ω) (F (baseChange D)) n) : kVal a 1 = 1 :=
  div_self (root_ne_zero (kRep n a) (kRoot_pow a))

lemma kVal_mul (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s s' : deltaTilde D) :
    kVal a (s * s') = kVal a s * kVal a s' := by
  have h0 := root_ne_zero (kRep n a) (kRoot_pow a)
  have h1 : ((s' : D.H) : Ω ≃ₐ[K₀ k t] Ω) (kRoot a) = kVal a s' * kRoot a := by
    rw [kVal, div_mul_cancel₀ _ h0]
  have h2 : ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) (kVal a s') = kVal a s' :=
    deltaTilde_fixes_kbar s (kVal_mem a s')
  change ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) (((s' : D.H) : Ω ≃ₐ[K₀ k t] Ω) (kRoot a)) / kRoot a = _
  rw [h1, map_mul, h2, mul_div_assoc, mul_comm]
  rfl

/-- **The Kummer character `χ_a : Δ̃ → k̄ˣ`**, `s ↦ s(α)/α`. -/
noncomputable def kChar (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    deltaTilde D →* (kbar k Ω)ˣ where
  toFun s := Units.mk0 ⟨kVal a s, kVal_mem a s⟩ fun h => kVal_ne_zero a s (congrArg Subtype.val h)
  map_one' := Units.ext (Subtype.ext (kVal_one a))
  map_mul' s s' := Units.ext (Subtype.ext (kVal_mul a s s'))

@[simp]
lemma coe_kChar (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    (((kChar a s : (kbar k Ω)ˣ) : kbar k Ω) : Ω) = kVal a s := rfl

lemma kChar_eq_one_iff (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (r : TorsRep n (a : Pic (kbar k Ω) (F (baseChange D)))) {β : Ω}
    (hβ : β ^ n = algebraMap (F (baseChange D)) Ω r.f) (s : deltaTilde D) :
    kChar a s = 1 ↔ ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) β = β := by
  have h0 := root_ne_zero r hβ
  rw [← Units.val_eq_one, ← Subtype.coe_inj, coe_kChar, kVal_eq a r hβ, IntermediateField.coe_one,
    div_eq_one_iff_eq h0]

/-- **Additivity in `a`**: `χ_{a+b} = χ_a χ_b`. -/
lemma kChar_add (a b : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kChar (a + b) s = kChar a s * kChar b s := by
  have ha := kRoot_pow a
  have hb := kRoot_pow b
  have hab : (kRoot a * kRoot b) ^ n =
      algebraMap (F (baseChange D)) Ω (((kRep n a).add (kRep n b)).f) := by
    rw [mul_pow, ha, hb, ← map_mul]; rfl
  refine Units.ext (Subtype.ext ?_)
  change kVal (a + b) s = kVal a s * kVal b s
  rw [kVal_eq (a + b) (((kRep n a).add (kRep n b)).cast' (by simp)) hab, kVal, kVal, map_mul,
    mul_div_mul_comm]

/-- **Compatibility across levels**: `χ^{(n)}_{m a} = (χ^{(nm)}_a)^m`. -/
lemma kChar_ofMul {m : ℕ} [NeZero (n * m)] (a : picTorsion (kbar k Ω) (F (baseChange D)) (n * m))
    (s : deltaTilde D) :
    kChar (⟨m • (a : Pic (kbar k Ω) (F (baseChange D))), by
      change n • m • (a : Pic (kbar k Ω) (F (baseChange D))) = 0
      rw [smul_smul]; exact a.2⟩ : picTorsion (kbar k Ω) (F (baseChange D)) n) s =
      kChar a s ^ m := by
  have hroot : (kRoot a ^ m) ^ n =
      algebraMap (F (baseChange D)) Ω ((kRep (n * m) a).ofMul m).f := by
    rw [← pow_mul, mul_comm m n, kRoot_pow a]; rfl
  refine Units.ext (Subtype.ext ?_)
  change kVal _ s = kVal a s ^ m
  rw [kVal_eq _ ((kRep (n * m) a).ofMul m) hroot, kVal, map_pow, div_pow]

/-- `h s h⁻¹` for `h ∈ H`, `s ∈ Δ̃`. -/
def conjDT (h : D.H) (s : deltaTilde D) : deltaTilde D :=
  ⟨h * s * h⁻¹, by
    haveI : (deltaTilde D).Normal := Subgroup.Normal.comap inferInstance _
    exact this.conj_mem _ s.2 h⟩

@[simp]
lemma coe_conjDT (h : D.H) (s : deltaTilde D) : ((conjDT h s : deltaTilde D) : D.H) = h * s * h⁻¹ :=
  rfl

/-- **`H`-equivariance**: `χ_{h a}(h s h⁻¹) = h(χ_a(s))`. -/
lemma kVal_conj (h : D.H) (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kVal ⟨picAct D h a, picAct_mem_picTorsion D h a.2⟩ (conjDT h s) =
      (h : Ω ≃ₐ[K₀ k t] Ω) (kVal a s) := by
  have e : picTr (autF D h : F (baseChange D) ≃+* F (baseChange D)) (constRes (autF D h))
      (constRes_spec (autF D h)) (a : Pic (kbar k Ω) (F (baseChange D))) =
      ((⟨picAct D h a, picAct_mem_picTorsion D h a.2⟩ :
        picTorsion (kbar k Ω) (F (baseChange D)) n) : Pic (kbar k Ω) (F (baseChange D))) :=
    (picMap_eq_picTr (autF D h) _).symm
  have hroot : ((h : Ω ≃ₐ[K₀ k t] Ω) (kRoot a)) ^ n =
      (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap (F (baseChange D)) Ω (kRep n a).f) := by
    rw [← map_pow, kRoot_pow]
  rw [kVal_eq _ (((kRep n a).tr _ _ (constRes_spec (autF D h))).cast' e) hroot, kVal, map_div₀]
  congr 1
  rw [coe_conjDT]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_apply]

end Values

/-! ### Kummer characters of `Π_X` over an algebraically closed field -/

section Generic

variable {κ : Type u} [Field κ] [IsAlgClosed κ] [Algebra κ Ω] (E : Pi1.Orbifold.GaloisData κ t)
  [IsGalois (K₀ κ t) Ω] [CharZero κ] {n : ℕ} [NeZero n]

/-- `charOfH c σ = c(σ)`. -/
lemma charOfH_eq_evalTriv (c : ContH1 (Ω ≃ₐ[F E] Ω) (Mu n Ω)) (σ : E.H) :
    charOfH E n c σ = ContH1.evalTriv (toGalF E σ) (galF_smul_mu E n _) c := by
  induction c using ContH1.induction_on with
  | h c => rw [charOfH_mk, ContH1.evalTriv_mk]

lemma toMul_picTorsionEquivPiChars (hn : 0 < n) (a : picTorsion κ (F E) n) (σ : E.H) :
    (Additive.toMul (picTorsionEquivPiChars E n hn a)) (QuotientGroup.mk σ) =
      charOfH E n ((Additive.toMul (picTorsionEquivUnramified E hn a) :
        unramifiedChars E n) : ContH1 _ _) σ :=
  rfl

/-- **The Kummer character of `a ∈ Pic(F)[n]` is `τ(β)/β`** for every representative and
Kummer root. -/
lemma torsionChar_mul_root (hn : 0 < n) (a : picTorsion κ (F E) n)
    (r : TorsRep n (a : Pic κ (F E))) {β : Ω} (hβ : β ^ n = algebraMap (F E) Ω r.f)
    (τ : Ω ≃ₐ[F E] Ω) :
    torsionChar E hn a τ * β = τ β := by
  obtain ⟨f, rfl⟩ := kummerToPic_surjective hn a
  rw [torsionChar, picTorsionEquivUnramified_kummerToPic, coe_kummerToUnramified]
  obtain ⟨α, hα⟩ := HasKummerRoots.exists_pow_eq (n := n) (Ω := Ω) (Additive.toMul f.1)
  have h1 := val_evalTriv_kummer_mul _ α hα τ (galF_smul_mu E n τ)
  have hα' : (α : Ω) ^ n = algebraMap (F E) Ω ((Additive.toMul f.1 : (F E)ˣ) : F E) := by
    have := congrArg Units.val hα
    rwa [Units.val_pow_eq_pow_val, Units.coe_map] at this
  let r₀ : TorsRep n ((kummerToPic hn f : picTorsion κ (F E) n) : Pic κ (F E)) :=
    ⟨kummerDivisor f, _, Units.ne_zero _, (kummerToPic_apply hn f).symm, nsmul_kummerDivisor f⟩
  have h2 := kummer_ratio_eq r₀ r (NeZero.ne n) hα' hβ τ.toRingEquiv (fun g => τ.commutes g)
  have hα0 : (α : Ω) ≠ 0 := α.ne_zero
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hβ
    exact r.f_ne ((algebraMap _ Ω).injective (by rw [map_zero]; exact hβ.symm))
  have h3 : τ β = τ α / α * β := by
    rw [← div_mul_cancel₀ (τ β) hβ0]
    exact congrArg (· * β) h2
  rw [h3, ← h1, mul_div_cancel_right₀ _ hα0]

/-- The character `picTorsionEquivPiChars a` of `Π_X` is `σ ↦ σ(β)/β`. -/
lemma val_picTorsionEquivPiChars_mul (hn : 0 < n) (a : picTorsion κ (F E) n)
    (r : TorsRep n (a : Pic κ (F E))) {β : Ω} (hβ : β ^ n = algebraMap (F E) Ω r.f) (σ : E.H) :
    ((Mu.val ((Additive.toMul (picTorsionEquivPiChars E n hn a)) (QuotientGroup.mk σ)) : Ωˣ) :
      Ω) * β = (σ : Ω ≃ₐ[K₀ κ t] Ω) β := by
  rw [toMul_picTorsionEquivPiChars, charOfH_eq_evalTriv]
  exact torsionChar_mul_root E hn a r hβ (toGalF E σ)

end Generic

/-! ### `Δ̃ ≅ H_{k̄}` and the characters of `Π_{X_{k̄}}` -/

section BaseChange

variable (D) in
/-- **`ι : H_{k̄} → Δ̃`**, `σ ↦ σ|_{k(t)}` (an isomorphism: `bcToDeltaTilde_surjective`). -/
noncomputable def bcToDeltaTilde : (baseChange D).H →* deltaTilde D where
  toFun σ := ⟨⟨resK₀ k t σ, (mem_baseChange_H D).1 σ.2⟩,
    (hToGk_eq_one_iff D ⟨resK₀ k t σ, (mem_baseChange_H D).1 σ.2⟩).2 fun x hx =>
      (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω).commutes ⟨x, (K₀ (kbar k Ω) t).algebraMap_mem ⟨x, hx⟩⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (resK₀ k t)))
  map_mul' σ τ := Subtype.ext (Subtype.ext (map_mul (resK₀ k t) σ.1 τ.1))

@[simp]
lemma bcToDeltaTilde_apply (σ : (baseChange D).H) (x : Ω) :
    (((bcToDeltaTilde D σ : deltaTilde D) : D.H) : Ω ≃ₐ[K₀ k t] Ω) x =
      (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) x := rfl

lemma continuous_bcToDeltaTilde : Continuous (bcToDeltaTilde D) :=
  (((continuous_resK₀ (k := k) (t := t)).comp continuous_subtype_val).subtype_mk _).subtype_mk _

lemma bcToDeltaTilde_surjective : Function.Surjective (bcToDeltaTilde D) := by
  intro s
  obtain ⟨σ, hσ⟩ := exists_resK₀_eq (fun x hx => deltaTilde_fixes_kbar s hx)
  have hσH : σ ∈ (baseChange D).H := by
    rw [mem_baseChange_H, hσ]
    exact (s : D.H).2
  exact ⟨⟨σ, hσH⟩, Subtype.ext (Subtype.ext hσ)⟩

/-- `ι` maps the inertia kernel of `H_{k̄}` into that of `H`. -/
lemma bcToDeltaTilde_mem_kernel {σ : (baseChange D).H}
    (hσ : σ ∈ GaloisPi1.kernel (baseChange D).H (SAll (baseChange D))) :
    ((bcToDeltaTilde D σ : deltaTilde D) : D.H) ∈ GaloisPi1.kernel D.H (SAll D) := by
  let L : Subgroup (Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) :=
    (GaloisPi1.ambientKernel D.H (SAll D)).comap (resK₀ k t)
  have hL : IsClosed (L : Set (Ω ≃ₐ[K₀ (kbar k Ω) t] Ω)) :=
    (GaloisPi1.isClosed_ambientKernel D.H (SAll D)).preimage (continuous_resK₀ (k := k) (t := t))
  have hconj : GaloisPi1.conjSet (baseChange D).H (SAll (baseChange D)) ⊆ L := by
    rintro _ ⟨h, hh, x, ⟨hxH, W, hk, hW⟩, rfl⟩
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_closure
      ⟨resK₀ k t h, (mem_baseChange_H D).1 hh, resK₀ k t x,
        ⟨(mem_baseChange_H D).1 hxH, W, fun c => hk (algebraMap k (kbar k Ω) c), hW⟩, ?_⟩)
    rw [map_mul, map_mul, map_inv]
  have hle : GaloisPi1.ambientKernel (baseChange D).H (SAll (baseChange D)) ≤ L :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le L).2 hconj) hL
  exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hσ))

variable {n : ℕ} [NeZero n]

/-- **`χ_a` is the character of `Π_{X_{k̄}}` attached to `a`** (`picTorsionEquivPiChars`), along
`ι : H_{k̄} → Δ̃`. -/
theorem val_picTorsionEquivPiChars (hn : 0 < n) (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (σ : (baseChange D).H) :
    ((Mu.val ((Additive.toMul (picTorsionEquivPiChars (baseChange D) n hn a))
      (QuotientGroup.mk σ)) : Ωˣ) : Ω) = kVal a (bcToDeltaTilde D σ) := by
  have h := val_picTorsionEquivPiChars_mul (baseChange D) hn a (kRep n a) (kRoot_pow a) σ
  rw [kVal, bcToDeltaTilde_apply, eq_div_iff (root_ne_zero _ (kRoot_pow a))]
  exact h

lemma kChar_eq_one_iff_kVal (a : picTorsion (kbar k Ω) (F (baseChange D)) n) (s : deltaTilde D) :
    kChar a s = 1 ↔ kVal a s = 1 := by
  rw [← Units.val_eq_one, ← Subtype.coe_inj, coe_kChar]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- the group structure on the quotient `PiX (baseChange D)` takes long to synthesize
/-- **`χ_a` kills inertia** (of all places containing `k`). -/
lemma kChar_eq_one_of_mem_SAll (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (s : deltaTilde D) (hs : ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ SAll D) : kChar a s = 1 := by
  obtain ⟨σ, rfl⟩ := bcToDeltaTilde_surjective s
  obtain ⟨-, W, hk, hW⟩ := hs
  have hσ : (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ∈ SAll (baseChange D) :=
    ⟨σ.2, W, fun c => kbar_mem W hk c, hW⟩
  have hmk : (QuotientGroup.mk σ : PiX (baseChange D)) = 1 :=
    (QuotientGroup.eq_one_iff σ).2 (Subgroup.mem_subgroupOf.2 (Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure ⟨1, (baseChange D).H.one_mem, σ, hσ, by simp⟩)))
  have hF := val_picTorsionEquivPiChars (Nat.pos_of_ne_zero (NeZero.ne n)) a σ
  rw [hmk, map_one, map_one, Units.val_one] at hF
  exact (kChar_eq_one_iff_kVal a _).2 hF.symm

end BaseChange

/-! ### `χ_a` factors through `Δ_X^{ab}` -/

section Factor

variable (n : ℕ) [NeZero n]

/-- `⋂_{a ∈ J[n]} ker χ_a ⊆ Δ̃`. -/
noncomputable def kerAll : Subgroup (deltaTilde D) :=
  ⨅ a : picTorsion (kbar k Ω) (F (baseChange D)) n, (kChar a).ker

variable {n}

lemma mem_kerAll {s : deltaTilde D} : s ∈ kerAll n ↔ ∀ a, kChar (n := n) a s = 1 := by
  simp only [kerAll, Subgroup.mem_iInf, MonoidHom.mem_ker]

lemma isOpen_ker_kChar (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    IsOpen ((kChar a).ker : Set (deltaTilde D)) := by
  have : ((kChar a).ker : Set (deltaTilde D)) =
      (fun s : deltaTilde D => ((s : D.H) : Ω ≃ₐ[K₀ k t] Ω)) ⁻¹'
        (MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) (kRoot a) : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
      MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact kChar_eq_one_iff a (kRep n a) (kRoot_pow a) s
  rw [this]
  exact (stabilizer_isOpen_of_isIntegral (kRoot a)).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

lemma isClosed_kerAll : IsClosed (kerAll (D := D) n : Set (deltaTilde D)) := by
  rw [kerAll, Subgroup.coe_iInf]
  exact isClosed_iInter fun a => Subgroup.isClosed_of_isOpen _ (isOpen_ker_kChar a)

lemma conjDT_conjDT_inv (h : D.H) (s : deltaTilde D) : conjDT h⁻¹ (conjDT h s) = s := by
  apply Subtype.ext
  simp only [coe_conjDT]
  group

/-- `⋂ ker χ_a` is normalised by `H`. -/
lemma conjDT_mem_kerAll (h : D.H) {s : deltaTilde D} (hs : s ∈ kerAll n) :
    conjDT h s ∈ kerAll n := by
  rw [mem_kerAll] at hs ⊢
  intro a
  have h1 := kVal_conj h⁻¹ a (conjDT h s)
  rw [conjDT_conjDT_inv] at h1
  have h0 : kVal ⟨picAct D h⁻¹ a, picAct_mem_picTorsion D h⁻¹ a.2⟩ s = 1 :=
    (kChar_eq_one_iff_kVal _ _).1 (hs _)
  rw [h0] at h1
  rw [kChar_eq_one_iff_kVal]
  have h3 := congrArg (h : Ω ≃ₐ[K₀ k t] Ω) h1
  simp only [Subgroup.coe_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply, map_one] at h3
  exact h3.symm

/-- **`χ_a` kills the kernel of `H → Π_X`**. -/
lemma mem_kerAll_of_mem_kernel (s : deltaTilde D)
    (hs : (s : D.H) ∈ GaloisPi1.kernel D.H (SAll D)) : s ∈ kerAll n := by
  let L : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := ((kerAll n).map (deltaTilde D).subtype).map D.H.subtype
  have hL : IsClosed (L : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    have h1 := ((isClosed_deltaTilde (D := D)).isClosedEmbedding_subtypeVal
      ).isClosed_iff_image_isClosed.1 (isClosed_kerAll (D := D) (n := n))
    have h2 := (D.isClosed_H.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.1 h1
    simp only [L, Subgroup.coe_map]
    exact h2
  have hconj : GaloisPi1.conjSet D.H (SAll D) ⊆ L := by
    rintro _ ⟨h, hh, x, ⟨hxH, W, hk, hW⟩, rfl⟩
    have hx' : (⟨x, hxH⟩ : D.H) ∈ deltaTilde D :=
      (hToGk_eq_one_iff D ⟨x, hxH⟩).2 fun y hy =>
        inertia_fix_algebraic hk hW (mem_algebraicClosure_iff.mp hy)
    have h1 : (⟨⟨x, hxH⟩, hx'⟩ : deltaTilde D) ∈ kerAll n :=
      mem_kerAll.2 fun a => kChar_eq_one_of_mem_SAll a _ ⟨hxH, W, hk, hW⟩
    exact ⟨_, ⟨_, conjDT_mem_kerAll ⟨h, hh⟩ h1, rfl⟩, rfl⟩
  have hle : GaloisPi1.ambientKernel D.H (SAll D) ≤ L :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le L).2 hconj) hL
  obtain ⟨_, ⟨s', hs', rfl⟩, he⟩ := hle (Subgroup.mem_subgroupOf.1 hs)
  have : s' = s := Subtype.ext (Subtype.ext he)
  exact this ▸ hs'

set_option synthInstance.maxHeartbeats 400000 in
-- `T2Space (PiX D)` and the group structure on `PiX D` take long to synthesize
/-- **`χ_a` kills `\overline{[Δ_X, Δ_X]}`**: an element of `Δ̃` with trivial image in `Δ_X^{ab}`
lies in every `ker χ_a`. -/
lemma ker_deltaTildeToAb_le : (deltaTildeToAb (D := D)).ker ≤ kerAll n := by
  haveI : IsClosed (GaloisPi1.kernel D.H (SAll D) : Set D.H) := GaloisPi1.isClosed_kernel _ _
  intro s hs
  have hs' : ((s : D.H) : PiX D) ∈ commClosure D := (deltaAbMk_eq_one_iff D _).1 hs
  let f : deltaTilde D →* PiX D := (QuotientGroup.mk' _).comp (deltaTilde D).subtype
  let M : Subgroup (PiX D) := (kerAll n).map f
  have hM : IsClosed (M : Set (PiX D)) := by
    simp only [M, Subgroup.coe_map]
    exact ((isClosed_kerAll (D := D) (n := n)).isCompact.image
      (QuotientGroup.continuous_mk.comp continuous_subtype_val)).isClosed
  have hcomm : ⁅DeltaX D, DeltaX D⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨(⟨x, hp⟩ : deltaTilde D) * ⟨y, hq⟩ * (⟨x, hp⟩ : deltaTilde D)⁻¹ *
      (⟨y, hq⟩ : deltaTilde D)⁻¹, mem_kerAll.2 fun a => ?_, ?_⟩
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (kChar a ⟨x, hp⟩),
        mul_inv_cancel_right, mul_inv_cancel]
    · rw [commutatorElement_def]
      rfl
  have hle : commClosure D ≤ M := Subgroup.topologicalClosure_minimal _ hcomm hM
  obtain ⟨l, hl, hle'⟩ := hle hs'
  have hk : ((l⁻¹ * s : deltaTilde D) : D.H) ∈ GaloisPi1.kernel D.H (SAll D) :=
    QuotientGroup.eq.1 hle'
  simpa using (kerAll n).mul_mem hl (mem_kerAll_of_mem_kernel _ hk)

/-- **The Kummer character on `Δ_X^{ab}`** (`kCharAb_deltaTildeToAb`). -/
noncomputable def kCharAb (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    DeltaAb D →* (kbar k Ω)ˣ :=
  (deltaTildeToAb (D := D)).liftOfSurjective deltaTildeToAb_surjective
    ⟨kChar a, fun _ hs => mem_kerAll.1 (ker_deltaTildeToAb_le hs) a⟩

@[simp]
lemma kCharAb_deltaTildeToAb (a : picTorsion (kbar k Ω) (F (baseChange D)) n)
    (s : deltaTilde D) : kCharAb a (deltaTildeToAb s) = kChar a s :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ s

lemma kCharAb_add (a b : picTorsion (kbar k Ω) (F (baseChange D)) n) (δ : DeltaAb D) :
    kCharAb (a + b) δ = kCharAb a δ * kCharAb b δ := by
  obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
  simp only [kCharAb_deltaTildeToAb, kChar_add]

lemma kCharAb_zero (δ : DeltaAb D) :
    kCharAb (0 : picTorsion (kbar k Ω) (F (baseChange D)) n) δ = 1 := by
  have h := kCharAb_add (0 : picTorsion (kbar k Ω) (F (baseChange D)) n) 0 δ
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

variable (n) in
/-- `⋂_{a ∈ J[n]} ker χ_a ⊆ Δ_X^{ab}`. -/
noncomputable def kerAb : Subgroup (DeltaAb D) := (kerAll (D := D) n).map deltaTildeToAb

lemma mem_kerAb {δ : DeltaAb D} : δ ∈ kerAb n ↔ ∀ a, kCharAb (n := n) a δ = 1 := by
  constructor
  · rintro ⟨s, hs, rfl⟩ a
    rw [kCharAb_deltaTildeToAb]
    exact mem_kerAll.1 hs a
  · intro h
    obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
    exact ⟨s, mem_kerAll.2 fun a => by rw [← kCharAb_deltaTildeToAb]; exact h a, rfl⟩

lemma continuous_deltaTildeToAb : Continuous (deltaTildeToAb (D := D)) :=
  QuotientGroup.continuous_mk.comp
    ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _)

lemma isClosed_kerAb [Fact (Function.Surjective (piJ1ToGk D))] :
    IsClosed (kerAb (D := D) n : Set (DeltaAb D)) := by
  rw [kerAb, Subgroup.coe_map]
  exact ((isClosed_kerAll (D := D) (n := n)).isCompact.image continuous_deltaTildeToAb).isClosed

end Factor

end CurvesJacobian.Kummer
