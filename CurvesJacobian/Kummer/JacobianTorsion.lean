/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.MiddleExact
import CurvesJacobian.Galois.PiCharacters

/-!
# Galois-equivariant Kummer duality for `J(k̄)[n]`

Setting of `Kummer/MiddleExact.lean`: `D : GaloisData k t`, `char k = 0`, `Ω` algebraically
closed and Galois over `k(t)`; `F k̄ = F (baseChange D)` is the function field of `X_{k̄}` and
`Δ = Gal(Ω/F k̄)` (`galToH`, image `ker(H → G_k)`). By `picTorsionEquivUnramified` for the base
change model, `Pic(X_{k̄})[n] = J(k̄)[n]` is the group of characters `Δ → μ_n` which are unramified
at every place, i.e. the characters of `Δ_X^{ab}/n` (Milne, *Abelian Varieties*, III.9.2):

  `J(k̄)[n] ≃ Hom(Δ_X^{ab}, μ_n)`,  `[E] ↦ (τ ↦ τ(α)/α)`, `αⁿ = f`, `div f = n E`.

This file proves that this isomorphism is compatible with the two structures that the comparison
of the Tate module of `J` with `Π_X^{ab}` needs ([AbsTopIII] Prop. 1.6, T3 l.1985: "`Π_X ↠ Π_{J¹}`
… whose kernel is equal to the commutator subgroup of `Δ_X`"):

* **Galois equivariance** (`torsionChar_picAct`): for `h ∈ H` (acting
  on `J(k̄)` through `G_k`, `picAct`), `χ_{h x}(τ) = h(χ_x(h⁻¹ τ h))`, where `h⁻¹ τ h` is
  `conjGal D h τ`; i.e. `J(k̄)[n] ≃ Hom(Δ_X^{ab}, μ_n)` is `H`-equivariant for the conjugation
  action on `Δ_X` and the cyclotomic action on `μ_n`.
* **Compatibility in `n`** (`torsionChar_nsmul`, for any model, in particular `baseChange D`): for
  `x ∈ J(k̄)[nm]`, `χ^{(n)}_{m x} = (χ^{(nm)}_x)^m`. With the inclusions `J[n] ⊆ J[nm]` this
  identifies the inverse system `(J[nm] → J[n], x ↦ m x)` (the Tate module `T(J)`) with the dual
  of the system `Hom(Δ_X^{ab}, μ_n)`, i.e. `T(J) ≅ Hom(Δ_X^{ab}, Ẑ(1))` levelwise.

Both are first proved for an arbitrary Galois model over an algebraically closed field and a
semilinear automorphism (`torsionChar_picMap`, `torsionChar_nsmul`; `torsionChar D hn x σ` is the
value `χ_x(σ) ∈ μ_n ⊆ Ω`), resp. for Kummer classes over any field
(`val_evalTriv_kummer_map`), and then specialised to the base change model.

No Jacobian scheme is used: `J(k̄)` is the divisor class group of `F k̄` (weil-curves); its
comparison with the `k̄`-points of the Picard scheme `Pic⁰_{C/k̄,σ}` is recorded in the MR5 plan
(continuous-kummer-theory `Plans/MR5Plan.md`, §10) as an input of J1.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

namespace CurvesJacobian.Kummer

universe u

section KummerGeneric

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Conjugation `τ ↦ φ⁻¹ τ φ` of `Gal(Ω/K)` by a ring automorphism `φ` of `Ω` with
`φ(K) ⊆ K`. -/
def conjAut (φ : Ω ≃+* Ω) (hφ : ∀ x : K, φ (algebraMap K Ω x) ∈ (algebraMap K Ω).range) :
    (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[K] Ω) where
  toFun τ := AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun x => by
    obtain ⟨y, hy⟩ := hφ x
    change φ.symm (τ (φ (algebraMap K Ω x))) = algebraMap K Ω x
    rw [← hy, τ.commutes, hy, RingEquiv.symm_apply_apply]
  map_one' := by
    ext x
    change φ.symm (φ x) = x
    exact φ.symm_apply_apply x
  map_mul' τ σ := by
    ext x
    change φ.symm (τ (σ (φ x))) = φ.symm (τ (φ (φ.symm (σ (φ x)))))
    rw [RingEquiv.apply_symm_apply]

@[simp]
lemma conjAut_apply (φ : Ω ≃+* Ω) (hφ : ∀ x : K, φ (algebraMap K Ω x) ∈ (algebraMap K Ω).range)
    (τ : Ω ≃ₐ[K] Ω) (x : Ω) : conjAut φ hφ τ x = φ.symm (τ (φ x)) :=
  rfl

variable {n : ℕ} [HasKummerRoots n K Ω] [Algebra.IsIntegral K Ω]

/-- The value of a Kummer class at an element `τ` acting trivially on `μ_n` is `τ(α)/α` for
any `n`-th root `α`. -/
lemma val_evalTriv_kummer_mul (v : Kˣ) (α : Ωˣ)
    (hα : α ^ n = Units.map (algebraMap K Ω : K →* Ω) v) (τ : Ω ≃ₐ[K] Ω)
    (hτ : ∀ ζ : Mu n Ω, τ • ζ = ζ) :
    ((Mu.val (ContH1.evalTriv τ hτ (kummer n K Ω v)) : Ωˣ) : Ω) * α = τ α := by
  rw [kummer_eq v α hα, ContH1.evalTriv_mk, kummerCocycle_apply, val_kummerFun,
    Units.val_div_eq_div_val, div_mul_cancel₀ _ α.ne_zero]
  rfl

/-- **Semilinear transport of Kummer classes**: if `φ` is a ring automorphism of `Ω` with
`φ(K) ⊆ K` and `w = φ(v)`, then `κ(w)(τ) = φ(κ(v)(φ⁻¹ τ φ))`. -/
theorem val_evalTriv_kummer_map (φ : Ω ≃+* Ω)
    (hφ : ∀ x : K, φ (algebraMap K Ω x) ∈ (algebraMap K Ω).range) (v w : Kˣ)
    (hw : algebraMap K Ω (w : K) = φ (algebraMap K Ω (v : K))) (τ : Ω ≃ₐ[K] Ω)
    (hτ : ∀ ζ : Mu n Ω, τ • ζ = ζ) (hτ' : ∀ ζ : Mu n Ω, conjAut φ hφ τ • ζ = ζ) :
    ((Mu.val (ContH1.evalTriv τ hτ (kummer n K Ω w)) : Ωˣ) : Ω) =
      φ ((Mu.val (ContH1.evalTriv (conjAut φ hφ τ) hτ' (kummer n K Ω v)) : Ωˣ) : Ω) := by
  obtain ⟨α, hα⟩ := HasKummerRoots.exists_pow_eq (n := n) (Ω := Ω) v
  have hβ : (Units.map (φ : Ω →* Ω) α) ^ n = Units.map (algebraMap K Ω : K →* Ω) w := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, ← map_pow,
      ← Units.val_pow_eq_pow_val, hα, Units.coe_map]
    exact hw.symm
  apply mul_right_cancel₀ (Units.map (φ : Ω →* Ω) α).ne_zero
  rw [val_evalTriv_kummer_mul w _ hβ τ hτ]
  change τ (φ α) = _ * φ α
  rw [← map_mul, val_evalTriv_kummer_mul v α hα _ hτ', conjAut_apply, RingEquiv.apply_symm_apply]

end KummerGeneric

section Semilinear

variable {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [PerfectField κ] [IsFunctionField κ K]
  {n : ℕ}

/-- The unit `τ(v)`, for `τ ∈ constAut κ K`. -/
def constAutUnit (τ : constAut κ K) : Kˣ →* Kˣ :=
  Units.map ((τ : K ≃+* K) : K →* K)

omit [PerfectField κ] [IsFunctionField κ K] in
@[simp]
lemma coe_constAutUnit (τ : constAut κ K) (v : Kˣ) :
    ((constAutUnit τ v : Kˣ) : K) = (τ : K ≃+* K) v :=
  rfl

/-- `τ` maps Kummer classes (`div v ∈ n · Div`) to Kummer classes. -/
lemma constAutUnit_mem_kummerClasses (τ : constAut κ K) {v : Kˣ}
    (hv : Additive.ofMul v ∈ kummerClasses κ K n) :
    Additive.ofMul (constAutUnit τ v) ∈ kummerClasses κ K n := by
  obtain ⟨E, hE⟩ := hv
  refine ⟨divMap τ E, ?_⟩
  rw [nsmulAddMonoidHom_apply, ← map_nsmul]
  rw [nsmulAddMonoidHom_apply] at hE
  change divMap τ (n • E) = Divisor.div κ ((τ : K ≃+* K) v)
  rw [hE]
  exact divMap_div τ _

/-- `τ ∈ constAut κ K` on Kummer classes. -/
noncomputable def kummerClassMap (τ : constAut κ K) (f : kummerClasses κ K n) :
    kummerClasses κ K n :=
  ⟨Additive.ofMul (constAutUnit τ (Additive.toMul f.1)), constAutUnit_mem_kummerClasses τ f.2⟩

/-- **`f ↦ [E]` is `τ`-equivariant**: `[E_{τ f}] = τ [E_f]`. -/
lemma kummerToPic_kummerClassMap (hn : 0 < n) (τ : constAut κ K) (f : kummerClasses κ K n) :
    (kummerToPic hn (kummerClassMap τ f) : Pic κ K) = picMap τ (kummerToPic hn f) := by
  rw [kummerToPic_apply, kummerToPic_apply, picMap_mk]
  congr 1
  refine kummerDivisor_eq hn _ ?_
  rw [← map_nsmul, nsmul_kummerDivisor]
  exact divMap_div τ _

/-- A Kummer class at level `nm` is one at level `n`. -/
lemma mem_kummerClasses_of_mul {m : ℕ} (f : kummerClasses κ K (n * m)) :
    f.1 ∈ kummerClasses κ K n :=
  ⟨m • kummerDivisor f, by
    rw [nsmulAddMonoidHom_apply, ← mul_nsmul', nsmul_kummerDivisor]⟩

/-- `[E_f^{(n)}] = m [E_f^{(nm)}]`. -/
lemma kummerToPic_of_mul {m : ℕ} (hn : 0 < n) (hnm : 0 < n * m) (f : kummerClasses κ K (n * m)) :
    (kummerToPic hn ⟨f.1, mem_kummerClasses_of_mul f⟩ : Pic κ K) =
      m • (kummerToPic hnm f : Pic κ K) := by
  rw [kummerToPic_apply, kummerToPic_apply, ← QuotientAddGroup.mk_nsmul]
  congr 1
  refine kummerDivisor_eq hn _ ?_
  rw [← mul_nsmul', nsmul_kummerDivisor]

end Semilinear

section Model

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  [IsAlgClosed k]

attribute [local instance] isFunctionField_F

/-- The isomorphism `Pic(F)[n] ≃ unramifiedChars` on the class of a Kummer function. -/
lemma picTorsionEquivUnramified_kummerToPic {n : ℕ} [NeZero n] (hn : 0 < n)
    (f : kummerClasses k (F D) n) :
    picTorsionEquivUnramified D hn (kummerToPic hn f) = kummerToUnramified D f := by
  have h : (picTorsionEquiv hn).symm (kummerToPic hn f) = QuotientAddGroup.mk f :=
    (picTorsionEquiv hn).symm_apply_eq.2 rfl
  simp only [picTorsionEquivUnramified, AddEquiv.trans_apply, h]
  rfl

omit [IsAlgClosed k] in
@[simp]
lemma coe_kummerToUnramified {n : ℕ} [NeZero n] (f : kummerClasses k (F D) n) :
    ((Additive.toMul (kummerToUnramified D f) : unramifiedChars D n) :
      ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω)) = kummer n (F D) Ω (Additive.toMul f.1) :=
  rfl

omit [IsSepClosed Ω] [IsAlgClosed k] in
/-- `n`-torsion is preserved by `τ ∈ constAut`. -/
lemma picMap_mem_picTorsion {n : ℕ} (τ : constAut k (F D)) {x : Pic k (F D)}
    (hx : x ∈ picTorsion k (F D) n) : picMap τ x ∈ picTorsion k (F D) n := by
  change n • picMap τ x = 0
  rw [← map_nsmul, show n • x = 0 from hx, map_zero]

/-- The character `χ_x : Gal(Ω/F) → μ_n ⊆ Ω` of `x ∈ Pic(F)[n]` (`picTorsionEquivUnramified`),
evaluated at `σ`: `χ_x(σ) = σ(α)/α` with `αⁿ = f`, `div f = n E`, `x = [E]`. -/
noncomputable def torsionChar {n : ℕ} [NeZero n] (hn : 0 < n) (x : picTorsion k (F D) n)
    (σ : Ω ≃ₐ[F D] Ω) : Ω :=
  ((Mu.val (ContH1.evalTriv σ (galF_smul_mu D n σ)
    ((Additive.toMul (picTorsionEquivUnramified D hn x) : unramifiedChars D n) :
      ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω))) : Ωˣ) : Ω)

/-- **Semilinear equivariance of `Pic(F)[n] ≃ Hom(Π_X, μ_n)`**: if `τ ∈ constAut k (F D)` is
induced by a ring automorphism `φ` of `Ω` (`τ x = φ x`), then
`χ_{τ x}(σ) = φ(χ_x(φ⁻¹ σ φ))`. -/
theorem torsionChar_picMap {n : ℕ} [NeZero n] (hn : 0 < n)
    (φ : Ω ≃+* Ω) (hφ : ∀ x : F D, φ (algebraMap (F D) Ω x) ∈ (algebraMap (F D) Ω).range)
    (τ : constAut k (F D)) (hτφ : ∀ x : F D, (((τ : F D ≃+* F D) x : F D) : Ω) = φ x)
    (x : picTorsion k (F D) n) (σ : Ω ≃ₐ[F D] Ω) :
    torsionChar D hn ⟨picMap τ x, picMap_mem_picTorsion D τ x.2⟩ σ =
      φ (torsionChar D hn x (conjAut φ hφ σ)) := by
  obtain ⟨f, rfl⟩ := kummerToPic_surjective hn x
  have hE : (⟨picMap τ (kummerToPic hn f), picMap_mem_picTorsion D τ (kummerToPic hn f).2⟩ :
      picTorsion k (F D) n) = kummerToPic hn (kummerClassMap τ f) :=
    Subtype.ext (kummerToPic_kummerClassMap hn τ f).symm
  rw [torsionChar, torsionChar, hE, picTorsionEquivUnramified_kummerToPic,
    picTorsionEquivUnramified_kummerToPic, coe_kummerToUnramified, coe_kummerToUnramified]
  exact val_evalTriv_kummer_map φ hφ (Additive.toMul f.1)
    (constAutUnit τ (Additive.toMul f.1)) (hτφ _) σ _ _

/-- **Compatibility of `Pic(F)[n] ≃ Hom(Π_X, μ_n)` in `n`**: for `x ∈ Pic[nm]`,
`χ^{(n)}_{m x}(σ) = χ^{(nm)}_x(σ)^m`. -/
theorem torsionChar_nsmul {n m : ℕ} [NeZero n] [NeZero (n * m)]
    (hn : 0 < n) (hnm : 0 < n * m) (x : picTorsion k (F D) (n * m))
    (hx : m • (x : Pic k (F D)) ∈ picTorsion k (F D) n) (σ : Ω ≃ₐ[F D] Ω) :
    torsionChar D hn ⟨_, hx⟩ σ = torsionChar D hnm x σ ^ m := by
  obtain ⟨f, rfl⟩ := kummerToPic_surjective hnm x
  have hE : (⟨_, hx⟩ : picTorsion k (F D) n) = kummerToPic hn ⟨f.1, mem_kummerClasses_of_mul f⟩ :=
    Subtype.ext (kummerToPic_of_mul hn hnm f).symm
  rw [torsionChar, torsionChar, hE, picTorsionEquivUnramified_kummerToPic,
    picTorsionEquivUnramified_kummerToPic, coe_kummerToUnramified, coe_kummerToUnramified]
  obtain ⟨α, hα⟩ := HasKummerRoots.exists_pow_eq (n := n * m) (Ω := Ω) (Additive.toMul f.1)
  have hαm : (α ^ m) ^ n = Units.map (algebraMap (F D) Ω : F D →* Ω) (Additive.toMul f.1) := by
    rw [← pow_mul, mul_comm, hα]
  apply mul_right_cancel₀ (α ^ m).ne_zero
  rw [val_evalTriv_kummer_mul _ (α ^ m) hαm σ, Units.val_pow_eq_pow_val, ← mul_pow,
    val_evalTriv_kummer_mul _ α hα σ, map_pow]

end Model

section BaseChange

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]

lemma apply_mem_range_F_baseChange (h : D.H) (x : F (baseChange D)) :
    ((h : Ω ≃ₐ[K₀ k t] Ω) : Ω ≃+* Ω) (algebraMap (F (baseChange D)) Ω x) ∈
      (algebraMap (F (baseChange D)) Ω).range :=
  ⟨⟨_, smul_mem_F_baseChange D h.2 x.2⟩, rfl⟩

/-- `τ ↦ h⁻¹ τ h` on `Δ = Gal(Ω/F k̄)`, for `h ∈ H` (which stabilises `F k̄`). -/
noncomputable def conjGal (h : D.H) :
    (Ω ≃ₐ[F (baseChange D)] Ω) →* (Ω ≃ₐ[F (baseChange D)] Ω) :=
  conjAut ((h : Ω ≃ₐ[K₀ k t] Ω) : Ω ≃+* Ω) (apply_mem_range_F_baseChange D h)

@[simp]
lemma conjGal_apply (h : D.H) (τ : Ω ≃ₐ[F (baseChange D)] Ω) (x : Ω) :
    conjGal D h τ x = (h : Ω ≃ₐ[K₀ k t] Ω).symm (τ ((h : Ω ≃ₐ[K₀ k t] Ω) x)) :=
  rfl

variable [CharZero k] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

omit [IsAlgClosed Ω] in
/-- `picAct` maps `J(k̄)[n]` to itself. -/
lemma picAct_mem_picTorsion {n : ℕ} (h : D.H) {x : Pic (kbar k Ω) (F (baseChange D))}
    (hx : x ∈ picTorsion (kbar k Ω) (F (baseChange D)) n) :
    picAct D h x ∈ picTorsion (kbar k Ω) (F (baseChange D)) n :=
  picMap_mem_picTorsion (baseChange D) (autF D h) hx

/-- **Galois equivariance of `J(k̄)[n] ≃ Hom(Δ_X^{ab}, μ_n)`**: for `h ∈ H`, `x ∈ J(k̄)[n]` and
`τ ∈ Δ`, `χ_{h x}(τ) = h(χ_x(h⁻¹ τ h))`. -/
theorem torsionChar_picAct {n : ℕ} [NeZero n] (hn : 0 < n) (h : D.H)
    (x : picTorsion (kbar k Ω) (F (baseChange D)) n) (τ : Ω ≃ₐ[F (baseChange D)] Ω) :
    torsionChar (baseChange D) hn ⟨picAct D h x, picAct_mem_picTorsion D h x.2⟩ τ =
      (h : Ω ≃ₐ[K₀ k t] Ω) (torsionChar (baseChange D) hn x (conjGal D h τ)) :=
  torsionChar_picMap (baseChange D) hn _ (apply_mem_range_F_baseChange D h) (autF D h)
    (fun _ => rfl) x τ

end BaseChange

end CurvesJacobian.Kummer
