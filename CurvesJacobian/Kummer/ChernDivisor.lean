/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspChern
import CurvesJacobian.Galois.UnramifiedKummer
import CurvesJacobian.Galois.AbelianPi1
import CurvesJacobian.Cusp.SingleCusp
import CurvesJacobian.Cusp.PlaceTransitivity

/-!
# The first Chern class modulo `n` of divisors

[Mzk7] = *Topics surrounding the anabelian geometry of hyperbolic curves*, Def. 4.1
(`Topics Surrounding the Anabelian Geometry of Hyperbolic Curves.txt` l.1488–1510): the first
Chern class modulo `N` of a line bundle `L` is the image of `L ∈ H¹(X, 𝔾ₘ)` under the boundary
`H¹(X, 𝔾ₘ) → H²(X, μ_N)` of the Kummer sequence `1 → μ_N → 𝔾ₘ → 𝔾ₘ → 1`.

We work in the Galois model of `CuspChern` (`k = k̄` of characteristic `0`, `H = Gal(Ω/K(X))`,
`ρ : H ↠ Δ_X = π₁ᵉᵗ(X)`, `F = Ω^H ≅ K(X)`, and `Ω^{ker ρ}` the function field of the profinite
universal cover `X̃`), and compute the boundary on `X̃`: for a divisor `E` of `F`, choose a
function `f` on `X̃` with `div f ≡ E (mod n)`; then `γ f = f g_γⁿ` for `γ ∈ Δ_X`, and
`c₁(𝒪_X(E)) mod n` is the class of `g_γ γ(g_δ) / g_{γδ} ∈ μ_n` (`ChernClass.chernClass`).

**The Kummer form of `div f ≡ E (mod n)`.** `X̃` is not of finite type, so instead of orders we
use inertia: at a place `W` of `Ω` over the place `P` of `F` (with inertia group `I_W`), if
`u ∈ F` has `ord_P u = E(P)` then `f/u` has order divisible by `n` at `W`, i.e. the Kummer
characters of `f` and `u` agree on `I_W`: `σ(β)/β = σ(γ)/γ` for `βⁿ = f`, `γⁿ = u`, `σ ∈ I_W`
(`IsChernRepDiv`).

* `IsChernRepDiv D eL hH n E f`: `f` represents `𝒪_X(E)` modulo `n`;
* `IsChernRepDiv.exists_eq_mul_pow`: two representatives differ by `bⁿ`, `b ∈ Ω^{ker ρ}`
  (`Ω^{ker ρ}` has no unramified Kummer extensions); `chernClassDiv`, `chernClassDiv_eq`;
* `IsChernRepDiv.mul`, `IsChernRepDiv.inv`, `IsChernRepDiv.zpow`, `isChernRepDiv_div`
  (`h ∈ Fˣ` represents `div h`), `isChernRepDiv_one_nsmul` (`1` represents `n • E`), with the
  classes `chernClassDiv_mul`, `chernClassDiv_div`, `chernClassDiv_one_nsmul`;
* `IsChernRep.isChernRepDiv`: a representative of `𝒪_X(x)` in the sense of `CuspChern`
  represents the divisor `P₀` (the place under `W₀`), and `chernClassDiv_isChernRepDiv`: its class
  is `chernClassX`;
* `exists_isChernRepDiv` (genus `≥ 1`): every divisor has a representative;
* `c1Div : Div(F) →+ H²(Δ_X, μ_n)` with `c1Div_div`, `c1Div_nsmul`,
  `c1Div_single_eq_chernClassX`, and `c1Pic : Pic(F) →+ H²(Δ_X, μ_n)`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField

namespace CurvesJacobian.ChernClass

universe u

/-! ### Products and trivial classes (group theory) -/

section Generic

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  {ρ : G →* Q} {n : ℕ}

lemma isFix_one : IsFix ρ (1 : Ω) := fun σ _ ↦ smul_one σ

lemma IsFix.inv {x : Ω} (hx : IsFix ρ x) : IsFix ρ x⁻¹ := fun σ hσ ↦ by
  rw [smul_inv'', hx σ hσ]

/-- Products of functions invariant modulo `n`-th powers are invariant modulo `n`-th powers. -/
lemma KummerInv.mul {f f' : Ω} (hf : KummerInv ρ n f) (hf' : KummerInv ρ n f') :
    KummerInv ρ n (f * f') where
  ne := mul_ne_zero hf.ne hf'.ne
  fix := hf.fix.mul hf'.fix
  inv σ := by
    obtain ⟨g, hg, h⟩ := hf.inv σ
    obtain ⟨g', hg', h'⟩ := hf'.inv σ
    exact ⟨g * g', hg.mul hg', by rw [smul_mul', h, h', mul_pow]; ring⟩

/-- Inverses of functions invariant modulo `n`-th powers are invariant modulo `n`-th powers. -/
lemma KummerInv.inverse {f : Ω} (hf : KummerInv ρ n f) : KummerInv ρ n f⁻¹ where
  ne := inv_ne_zero hf.ne
  fix := hf.fix.inv
  inv σ := by
    obtain ⟨g, hg, h⟩ := hf.inv σ
    exact ⟨g⁻¹, hg.inv, by rw [smul_inv'', h, mul_inv, inv_pow]⟩

variable {s : Q → G}

lemma IsAdm.mul {f f' : Ω} {g g' : Q → Ω} (hg : IsAdm ρ n s f g) (hg' : IsAdm ρ n s f' g') :
    IsAdm ρ n s (f * f') (g * g') where
  fix γ := (hg.fix γ).mul (hg'.fix γ)
  ne γ := mul_ne_zero (hg.ne γ) (hg'.ne γ)
  eq γ := by
    rw [Pi.mul_apply, smul_mul', hg.eq, hg'.eq, mul_pow]
    ring

lemma chernVal_mul (g g' : Q → Ω) (x : Q × Q) :
    chernVal s (g * g') x = chernVal s g x * chernVal s g' x := by
  simp only [chernVal, Pi.mul_apply, smul_mul']
  ring

lemma chernVal_one (x : Q × Q) : chernVal s (fun _ ↦ (1 : Ω)) x = 1 := by
  simp [chernVal]

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hs : ∀ γ, ρ (s γ) = γ) (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

/-- The trivial action of `Q` on `μ_n` (as in `ChernClass`). -/
local instance : MulDistribMulAction Q (Mu n Ω) := Pi1.SurfaceGroup.trivialAction Q (Mu n Ω)

/-- **The class of a product is the product of the classes** (for the product choice `g g'`). -/
theorem chernClassOf_mul {f f' : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) (hf' : f' ≠ 0)
    (hfix' : IsFix ρ f') {g g' : Q → Ω} (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g)
    (hg' : IsAdm ρ n s f' g') (hglc' : IsLocallyConstant g') :
    chernClassOf hs hμ hstab hq (mul_ne_zero hf hf') (hfix.mul hfix') (hg.mul hg')
        (hglc.mul hglc') =
      chernClassOf hs hμ hstab hq hf hfix hg hglc *
        chernClassOf hs hμ hstab hq hf' hfix' hg' hglc' := by
  have h : chernCocycles hs hμ hstab hq (mul_ne_zero hf hf') (hfix.mul hfix') (hg.mul hg')
      (hglc.mul hglc') = chernCocycles hs hμ hstab hq hf hfix hg hglc *
        chernCocycles hs hμ hstab hq hf' hfix' hg' hglc' :=
    Subtype.ext (funext fun x ↦ Mu.ext (Units.ext (chernVal_mul g g' x)))
  unfold chernClassOf
  rw [h]
  rfl

/-- **The class of a product is the product of the classes.** -/
theorem chernClass_mul [NeZero n] {f f' : Ω} (hf : KummerInv ρ n f) (hf' : KummerInv ρ n f') :
    chernClass hs hμ hstab hq (hf.mul hf') =
      chernClass hs hμ hstab hq hf * chernClass hs hμ hstab hq hf' := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf
  obtain ⟨g', hg', hglc'⟩ := exists_isAdm hs hstab hq hf'
  rw [← chernClassOf_eq_chernClass hs hμ hstab hq hf hg hglc,
    ← chernClassOf_eq_chernClass hs hμ hstab hq hf' hg' hglc',
    ← chernClassOf_eq_chernClass hs hμ hstab hq (hf.mul hf') (hg.mul hg') (hglc.mul hglc')]
  exact chernClassOf_mul hs hμ hstab hq hf.ne hf.fix hf'.ne hf'.fix hg hglc hg' hglc'

/-- **A function fixed by `G` has trivial class** (choice `g ≡ 1`). -/
theorem chernClass_eq_one [NeZero n] {f : Ω} (hf : KummerInv ρ n f) (h : ∀ σ : G, σ • f = f) :
    chernClass hs hμ hstab hq hf = 1 := by
  have hg : IsAdm ρ n s f (fun _ ↦ 1) :=
    ⟨fun _ ↦ isFix_one, fun _ ↦ one_ne_zero, fun γ ↦ by rw [one_pow, mul_one, h]⟩
  rw [← chernClassOf_eq_chernClass hs hμ hstab hq hf hg (IsLocallyConstant.const 1)]
  have h1 : chernCocycles hs hμ hstab hq hf.ne hf.fix hg (IsLocallyConstant.const 1) = 1 :=
    Subtype.ext (funext fun x ↦ Mu.ext (Units.ext (chernVal_one x)))
  unfold chernClassOf
  rw [h1]
  rfl

/-- **Replacing `f` by `f bⁿ`** (`b ∈ (Ω^{ker ρ})ˣ`) does not change the class. -/
theorem chernClass_mul_pow [NeZero n] {f b : Ω} (hf : KummerInv ρ n f) (hb : IsFix ρ b)
    (hb0 : b ≠ 0) (hf' : KummerInv ρ n (f * b ^ n)) :
    chernClass hs hμ hstab hq hf' = chernClass hs hμ hstab hq hf := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf
  rw [← chernClassOf_eq_chernClass hs hμ hstab hq hf hg hglc,
    ← chernClassOf_eq_chernClass hs hμ hstab hq hf' (isAdm_mul_pow hg hb hb0)
      ((hglc.comp₂ (isLocallyConstant_smul hs hstab hq hb) (· * ·)).comp₂
        (IsLocallyConstant.const b) (· / ·))]
  exact chernClassOf_mul_pow hs hμ hstab hq hf.ne hf.fix hg hglc hb hb0

end Topology

end Generic

/-! ### Representatives of divisors -/

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n : ℕ} [NeZero n]

attribute [local instance] isFunctionField_F instTrivMu

variable (D eL hH n) in
/-- **`f` represents `𝒪_X(E)` modulo `n`** (`E` a divisor of `F ≅ K(X)`): `f` is a function on the
profinite universal cover `X̃` (fixed by `ker(H → Δ_X)`), invariant modulo `n`-th powers, with
`div f ≡ E (mod n)` on `X̃` in Kummer form: for every place `P` of `F`, every place `W` of `Ω`
over `P`, every `u ∈ Fˣ` with `ord_P u = E(P)` and every `σ` in the inertia group of `W`, the
Kummer characters of `f` and `u` agree at `σ` (`σ(β)/β = σ(γ)/γ` for `βⁿ = f`, `γⁿ = u`).
The places `W ⊇ k` of `Ω` which are trivial on `F` are not quantified over: their inertia groups
are trivial (`smul_eq_of_forall_mem`). -/
structure IsChernRepDiv (E : Divisor k (F D)) (f : Ω) : Prop
    extends KummerInv (rhoX D eL hH) n f where
  loc : ∀ (P : Place k (F D)) (W : ValuationSubring Ω),
    (∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) → ∀ u : F D, u ≠ 0 → P.ord u = E P →
    ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W →
    ∀ β γ : Ω, β ^ n = f → γ ^ n = (u : Ω) → σ • β / β = σ • γ / γ

/-! #### Local lemmas -/

omit [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
/-- `σ(β)/β` does not depend on the choice of the `n`-th root `β`. -/
lemma smul_div_eq_of_pow_eq (σ : D.H) {a β β' : Ω} (ha : a ≠ 0) (hβ : β ^ n = a)
    (hβ' : β' ^ n = a) : σ • β / β = σ • β' / β' := by
  have hβ0 := ne_zero_of_pow_eq ha hβ
  have hβ'0 := ne_zero_of_pow_eq ha hβ'
  have hζ : (β' / β) ^ n = 1 := by rw [div_pow, hβ, hβ', div_self ha]
  have h1 := smul_eq_of_pow_eq_one D n σ hζ
  have hσβ0 : σ • β ≠ 0 := (smul_ne_zero_iff_ne σ).2 hβ0
  rw [smul_div₀', div_eq_div_iff hσβ0 hβ0] at h1
  rw [div_eq_div_iff hβ0 hβ'0]
  linear_combination -h1

omit [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
lemma smul_mul_div_mul (σ : D.H) (a b : Ω) : σ • (a * b) / (a * b) = σ • a / a * (σ • b / b) := by
  rw [smul_mul', mul_div_mul_comm]

omit [IsAlgClosed k] [IsSepClosed Ω] in
/-- **Inertia fixes the `n`-th roots of functions whose order is divisible by `n`.** -/
lemma smul_eq_of_ord_eq {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {u : F D} (hu : u ≠ 0) {m : ℤ}
    (hord : P.ord u = n * m) {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    {γ : Ω} (hγ : γ ^ n = (u : Ω)) : σ • γ = γ := by
  have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  set w : F D := π ^ m
  have hw0 : w ≠ 0 := zpow_ne_zero _ hπ0
  set v : F D := u / w ^ n
  have hv0 : v ≠ 0 := div_ne_zero hu (pow_ne_zero _ hw0)
  have hvord : P.ord v = 0 := by
    rw [P.ord_div hu (pow_ne_zero _ hw0), P.ord_pow, P.ord_zpow, hπ1, hord]
    ring
  obtain ⟨hv1, hv2⟩ := (P.ord_eq_zero_iff hv0).1 hvord
  have hwΩ : ((w : F D) : Ω) ≠ 0 := fun h ↦ hw0 (Subtype.ext h)
  have hvΩ : ((v : F D) : Ω) ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  set z : Ω := γ / (w : Ω)
  have hz : z ^ n = (v : Ω) := by
    simp only [z, v, div_pow, hγ, IntermediateField.coe_div, IntermediateField.coe_pow]
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq hvΩ hz
  have hzW : z ∈ W := mem_of_pow_mem hn (by rw [hz]; exact (hW v).2 hv1)
  have hzW' : z⁻¹ ∈ W := mem_of_pow_mem hn (by
    rw [inv_pow, hz, ← IntermediateField.coe_inv]; exact (hW _).2 hv2)
  have hpow : ((σ : Ω ≃ₐ[K₀ k t] Ω) z / z) ^ n = 1 := by
    rw [div_pow, ← map_pow, hz, fixes_of_mem_F σ.2, div_self hvΩ]
  have hσz : (σ : Ω ≃ₐ[K₀ k t] Ω) z = z :=
    eq_of_mem_inertia (k := k) hkW hσ hzW (valuation_eq_one_of_mem hzW hzW' hz0) hn hpow
      (by field_simp)
  have hσw : (σ : Ω ≃ₐ[K₀ k t] Ω) (w : Ω) = w := fixes_of_mem_F σ.2 w
  have hγz : γ = z * w := by simp only [z]; field_simp
  change (σ : Ω ≃ₐ[K₀ k t] Ω) γ = γ
  rw [hγz, map_mul, hσz, hσw]

omit [IsAlgClosed k] [IsSepClosed Ω] in
/-- Inertia fixes the `n`-th roots of the units at `W`. -/
lemma smul_eq_of_ord_eq_zero {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {u : F D} (hu : u ≠ 0)
    (hord : P.ord u = 0) {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    {γ : Ω} (hγ : γ ^ n = (u : Ω)) : σ • γ = γ :=
  smul_eq_of_ord_eq hW hu (m := 0) (by rw [hord, mul_zero]) hσ hγ

omit [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] in
/-- **The places of `Ω` trivial on `F` have trivial inertia**: such a `W` is all of `Ω` (`Ω/F`
is algebraic and `W` is integrally closed). -/
lemma smul_eq_of_forall_mem {W : ValuationSubring Ω} (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W)
    {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (y : Ω) : σ • y = y := by
  haveI : Algebra.IsAlgebraic (F D) Ω := Algebra.IsAlgebraic.tower_top (K := K₀ k t) (F D)
  have hall : ∀ z : Ω, z ∈ W := fun z ↦ by
    obtain ⟨p, hpm, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := F D) z).isIntegral
    let φ : F D →+* W := (algebraMap (F D) Ω).codRestrict W.toSubring hW
    have hφ : (algebraMap W Ω).comp φ = algebraMap (F D) Ω := RingHom.ext fun _ ↦ rfl
    have hint : IsIntegral W z := ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hw]
    exact w.2
  by_contra hne
  have h0 : (σ : Ω ≃ₐ[K₀ k t] Ω) y - y ≠ 0 := sub_ne_zero.2 hne
  have h1 := hσ y (hall y)
  rw [valuation_eq_one_of_mem (hall _) (hall _) h0] at h1
  exact lt_irrefl _ h1

omit [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
/-- `F ⊆ L`. -/
lemma mem_L_of_mem_F (z : F D) : ((z : F D) : Ω) ∈ D.L := by
  rw [GaloisData.L, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact (IntermediateField.mem_fixedField_iff _ _).1 z.2 σ (D.le hσ)

omit [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
variable (hH) in
include hH in
/-- `L ⊆ F` (as `H ≤ H_L`). -/
lemma mem_F_of_mem_L (z : D.L) : (z : Ω) ∈ F D :=
  (IntermediateField.mem_fixedField_iff _ _).2 fun _ hσ ↦ Cusp.apply_eq_of_mem_HL D (hH hσ) z

omit [IsAlgClosed k] [IsSepClosed Ω] in
/-- A uniformiser at `P`, with the valuation properties used in `CuspChern`. -/
lemma exists_uniformiser {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) :
    ∃ π : (F D)ˣ, P.ord (π : F D) = 1 ∧ W.valuation ((π : F D) : Ω) < 1 ∧
      ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω) := by
  obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  have hπmem : π ∈ P.1 ∧ π⁻¹ ∉ P.1 := by
    refine ⟨P.mem_of_ord_nonneg (by rw [hπ1]; norm_num), fun h ↦ ?_⟩
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ1] at this
    norm_num at this
  have hπW : W.valuation ((π : F D) : Ω) < 1 := (valuation_lt_one_iff hW hπ0).2 hπmem
  refine ⟨Units.mk0 π hπ0, hπ1, hπW, ?_⟩
  intro f hf hlt
  set x : F D := ⟨f, hf⟩
  rcases eq_or_ne x 0 with hx0 | hx0
  · have : f = 0 := congrArg Subtype.val hx0
    rw [this, map_zero]; exact zero_le
  obtain ⟨hxP, hxP'⟩ := (valuation_lt_one_iff hW hx0).1 hlt
  have hord : 1 ≤ P.ord x := by
    have h0 := P.ord_nonneg_of_mem hxP
    rcases (show P.ord x = 0 ∨ 1 ≤ P.ord x by omega) with h | h
    · exact absurd ((P.ord_eq_zero_iff hx0).1 h).2 hxP'
    · exact h
  have hdiv : x / π ∈ P.1 := P.mem_of_ord_nonneg (by rw [P.ord_div hx0 hπ0, hπ1]; omega)
  have hdivW := (W.valuation_le_one_iff _).2 ((hW _).2 hdiv)
  rw [IntermediateField.coe_div, map_div₀] at hdivW
  have hπΩ : W.valuation ((π : F D) : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h ↦ hπ0 (Subtype.ext h)
  exact (div_le_one₀ (zero_lt_iff.2 hπΩ)).1 hdivW

omit [IsAlgClosed k] [IsSepClosed Ω] in
/-- A uniformiser in the sense of `CuspChern` (`v_W(π) < 1` maximal) has order `1`. -/
lemma ord_eq_one_of_valuation {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {π : (F D)ˣ}
    (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) :
    P.ord (π : F D) = 1 := by
  have hπ0 : (π : F D) ≠ 0 := π.ne_zero
  obtain ⟨hπP, hπP'⟩ := (valuation_lt_one_iff hW hπ0).1 hπW
  have h1 : 1 ≤ P.ord (π : F D) := by
    have h0 := P.ord_nonneg_of_mem hπP
    rcases (show P.ord (π : F D) = 0 ∨ 1 ≤ P.ord (π : F D) by omega) with h | h
    · exact absurd ((P.ord_eq_zero_iff hπ0).1 h).2 hπP'
    · exact h
  obtain ⟨π', hπ'1, hπ'W, -⟩ := exists_uniformiser hW
  have hle := hπ _ (π' : F D).2 hπ'W
  have hπΩ : W.valuation ((π : F D) : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h ↦ hπ0 (Subtype.ext h)
  have hdiv : (((π' : F D) / π : F D) : Ω) ∈ W := by
    rw [← W.valuation_le_one_iff, IntermediateField.coe_div, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 hπΩ)).2 hle
  have := P.ord_nonneg_of_mem ((hW _).1 hdiv)
  rw [P.ord_div π'.ne_zero hπ0, hπ'1] at this
  omega

/-! #### Uniqueness and the class -/

omit [IsAlgClosed k] in
include hk hτ in
/-- **Two representatives of the same divisor differ by an `n`-th power on `X̃`**:
`f' = f bⁿ` with `b ∈ Ω^{ker ρ}` (`Ω^{ker ρ}` has no unramified Kummer extensions,
`exists_eq_pow_of_unram`). -/
theorem IsChernRepDiv.exists_eq_mul_pow {E : Divisor k (F D)} {f f' : Ω}
    (hf : IsChernRepDiv D eL hH n E f) (hf' : IsChernRepDiv D eL hH n E f') :
    ∃ b, IsFix (rhoX D eL hH) b ∧ b ≠ 0 ∧ f' = f * b ^ n := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨b, hb, hb0, hbu⟩ := exists_eq_pow_of_unram hk hτ (n := n) (u := f' / f)
    (div_ne_zero hf'.ne hf.ne) fun W hW σ hσ γ hγ ↦ by
      by_cases hA : W.comap (algebraMap (F D) Ω) = ⊤
      · refine smul_eq_of_forall_mem (fun x ↦ ?_) hσ γ
        have : x ∈ W.comap (algebraMap (F D) Ω) := hA ▸ ValuationSubring.mem_top _
        exact this
      let P : Place k (F D) := ⟨W.comap (algebraMap (F D) Ω), hA, fun c ↦ by
        change algebraMap (F D) Ω (algebraMap k (F D) c) ∈ W
        rw [← IsScalarTower.algebraMap_apply k (F D) Ω]
        exact hW.1 c⟩
      have hWP : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1 := fun _ ↦ Iff.rfl
      obtain ⟨π, hπ1, -⟩ := exists_uniformiser hWP
      set u : F D := (π : F D) ^ (E P)
      have hu : u ≠ 0 := zpow_ne_zero _ π.ne_zero
      have hord : P.ord u = E P := by rw [P.ord_zpow, hπ1, mul_one]
      obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq f n
      obtain ⟨δ, hδ⟩ := IsSepClosed.exists_pow_nat_eq ((u : F D) : Ω) n
      have hβ0 := ne_zero_of_pow_eq hf.ne hβ
      have hγ0 : γ ≠ 0 := ne_zero_of_pow_eq (div_ne_zero hf'.ne hf.ne) hγ
      have hβ' : (γ * β) ^ n = f' := by rw [mul_pow, hγ, hβ, div_mul_cancel₀ _ hf.ne]
      have e1 := hf.loc P W hWP u hu hord σ hσ β δ hβ hδ
      have e2 := hf'.loc P W hWP u hu hord σ hσ (γ * β) δ hβ' hδ
      rw [← e1, smul_mul_div_mul] at e2
      have hσβ : σ • β / β ≠ 0 := div_ne_zero ((smul_ne_zero_iff_ne σ).2 hβ0) hβ0
      have h1 : σ • γ / γ = 1 := mul_right_cancel₀ hσβ (e2.trans (one_mul _).symm)
      exact (div_eq_one_iff_eq hγ0).1 h1
  exact ⟨b, hb, hb0, by rw [← hbu, mul_div_cancel₀ _ hf.ne]⟩

/-- **The first Chern class modulo `n` of `𝒪_X(E)`**, computed from a representative `f`
(`div f ≡ E mod n` on `X̃`, `IsChernRepDiv`): the class in `H²(Δ_X, μ_n)` of
`a(γ, δ) = g_γ γ(g_δ) / g_{γδ}`, `γ f = f g_γⁿ` (the boundary of the Kummer sequence on `X̃`,
[Mzk7] Def. 4.1). It does not depend on `f` (`chernClassDiv_eq`). -/
noncomputable def chernClassDiv {E : Divisor k (F D)} {f : Ω}
    (hf : IsChernRepDiv D eL hH n E f) :
    H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω) :=
  chernClass (rhoX_sX hH hk hτ) (fun σ _ hζ ↦ smul_eq_of_pow_eq_one D n σ hζ)
    (isOpen_stabilizer D) (isOpen_of_rhoX hk hτ) hf.toKummerInv

include hk hτ in
/-- **The Chern class does not depend on the representative.** -/
theorem chernClassDiv_eq {E : Divisor k (F D)} {f f' : Ω} (hf : IsChernRepDiv D eL hH n E f)
    (hf' : IsChernRepDiv D eL hH n E f') : chernClassDiv hk hτ hf = chernClassDiv hk hτ hf' := by
  obtain ⟨b, hb, hb0, rfl⟩ := hf.exists_eq_mul_pow hk hτ hf'
  exact (chernClass_mul_pow _ _ _ _ hf.toKummerInv hb hb0 hf'.toKummerInv).symm

/-! #### Algebra of representatives -/

omit [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- **The product of representatives of `E` and `E'` represents `E + E'`.** -/
theorem IsChernRepDiv.mul {E E' : Divisor k (F D)} {f f' : Ω} (hf : IsChernRepDiv D eL hH n E f)
    (hf' : IsChernRepDiv D eL hH n E' f') : IsChernRepDiv D eL hH n (E + E') (f * f') where
  toKummerInv := hf.toKummerInv.mul hf'.toKummerInv
  loc P W hW u hu hord σ hσ β γ hβ hγ := by
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    rw [Finsupp.add_apply] at hord
    obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
    set u₁ : F D := π ^ (E P)
    have hu₁ : u₁ ≠ 0 := zpow_ne_zero _ hπ0
    have hord₁ : P.ord u₁ = E P := by rw [P.ord_zpow, hπ1, mul_one]
    have hord₂ : P.ord (u / u₁) = E' P := by rw [P.ord_div hu hu₁, hord, hord₁]; ring
    obtain ⟨β₁, hβ₁⟩ := IsSepClosed.exists_pow_nat_eq f n
    obtain ⟨β₂, hβ₂⟩ := IsSepClosed.exists_pow_nat_eq f' n
    obtain ⟨γ₁, hγ₁⟩ := IsSepClosed.exists_pow_nat_eq ((u₁ : F D) : Ω) n
    obtain ⟨γ₂, hγ₂⟩ := IsSepClosed.exists_pow_nat_eq ((u / u₁ : F D) : Ω) n
    have e₁ := hf.loc P W hW u₁ hu₁ hord₁ σ hσ β₁ γ₁ hβ₁ hγ₁
    have e₂ := hf'.loc P W hW _ (div_ne_zero hu hu₁) hord₂ σ hσ β₂ γ₂ hβ₂ hγ₂
    have huΩ : ((u : F D) : Ω) ≠ 0 := fun h ↦ hu (Subtype.ext h)
    have hu₁Ω : ((u₁ : F D) : Ω) ≠ 0 := fun h ↦ hu₁ (Subtype.ext h)
    rw [smul_div_eq_of_pow_eq σ (β' := β₁ * β₂) (mul_ne_zero hf.ne hf'.ne) hβ
        (by rw [mul_pow, hβ₁, hβ₂]),
      smul_div_eq_of_pow_eq σ (β' := γ₁ * γ₂) huΩ hγ (show (γ₁ * γ₂) ^ n = (u : Ω) by
        rw [mul_pow, hγ₁, hγ₂, IntermediateField.coe_div]; field_simp),
      smul_mul_div_mul, smul_mul_div_mul, e₁, e₂]

omit [IsAlgClosed k] [X.Over (Spec (.of k))] [IsCurveOver k X] [NeZero n] in
/-- **The inverse of a representative of `E` represents `-E`.** -/
theorem IsChernRepDiv.neg {E : Divisor k (F D)} {f : Ω} (hf : IsChernRepDiv D eL hH n E f) :
    IsChernRepDiv D eL hH n (-E) f⁻¹ where
  toKummerInv := hf.toKummerInv.inverse
  loc P W hW u hu hord σ hσ β γ hβ hγ := by
    have h := hf.loc P W hW u⁻¹ (inv_ne_zero hu)
      (by rw [P.ord_inv, hord, Finsupp.neg_apply, neg_neg]) σ hσ β⁻¹ γ⁻¹
      (by rw [inv_pow, hβ, inv_inv]) (by rw [inv_pow, hγ, IntermediateField.coe_inv])
    rw [smul_inv'', smul_inv'', inv_div_inv, inv_div_inv] at h
    rw [← inv_div β, ← inv_div γ, h]

omit [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- **`1` represents `n • E`.** -/
theorem isChernRepDiv_one_nsmul (E : Divisor k (F D)) : IsChernRepDiv D eL hH n (n • E) 1 where
  ne := one_ne_zero
  fix := isFix_one
  inv σ := ⟨1, isFix_one, by rw [smul_one, one_pow, mul_one]⟩
  loc P W hW u hu hord σ hσ β γ hβ hγ := by
    rw [Finsupp.smul_apply, nsmul_eq_mul] at hord
    have hγ0 : γ ≠ 0 := ne_zero_of_pow_eq (fun h ↦ hu (Subtype.ext h)) hγ
    have hβ0 : β ≠ 0 := ne_zero_of_pow_eq one_ne_zero hβ
    rw [smul_eq_of_ord_eq hW hu hord hσ hγ, smul_eq_of_pow_eq_one D n σ hβ, div_self hβ0,
      div_self hγ0]

omit [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- `1` represents the zero divisor. -/
theorem isChernRepDiv_one : IsChernRepDiv D eL hH n 0 1 := by
  have := isChernRepDiv_one_nsmul (D := D) (eL := eL) (hH := hH) (n := n) 0
  rwa [smul_zero] at this

omit [IsAlgClosed k] [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- **`h ∈ Fˣ` represents its divisor `div h`.** -/
theorem isChernRepDiv_div (h : F D) (h0 : h ≠ 0) :
    IsChernRepDiv D eL hH n (Divisor.div k h) (h : Ω) where
  ne := fun e ↦ h0 (Subtype.ext e)
  fix := fun σ _ ↦ fixes_of_mem_F σ.2 h
  inv σ := ⟨1, isFix_one, by rw [one_pow, mul_one]; exact fixes_of_mem_F σ.2 h⟩
  loc P W hW u hu hord σ hσ β γ hβ hγ := by
    rw [Divisor.div_apply] at hord
    have hβ0 : β ≠ 0 := ne_zero_of_pow_eq (fun e ↦ h0 (Subtype.ext e)) hβ
    have hγ0 : γ ≠ 0 := ne_zero_of_pow_eq (fun e ↦ hu (Subtype.ext e)) hγ
    have hz : (γ / β) ^ n = ((u / h : F D) : Ω) := by
      rw [div_pow, hγ, hβ, IntermediateField.coe_div]
    have e := smul_eq_of_ord_eq_zero hW (div_ne_zero hu h0)
      (by rw [P.ord_div hu h0, hord, sub_self]) hσ hz
    have hσβ0 : σ • β ≠ 0 := (smul_ne_zero_iff_ne σ).2 hβ0
    rw [smul_div₀', div_eq_div_iff hσβ0 hβ0] at e
    rw [div_eq_div_iff hβ0 hγ0]
    linear_combination -e

omit [X.Over (Spec (.of k))] [IsCurveOver k X] in
/-- **Integral powers**: `f^m` represents `m • E`. -/
theorem IsChernRepDiv.zpow {E : Divisor k (F D)} {f : Ω} (hf : IsChernRepDiv D eL hH n E f)
    (m : ℤ) : IsChernRepDiv D eL hH n (m • E) (f ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, zpow_zero]
    exact isChernRepDiv_one
  | succ i ih =>
    rw [add_smul, one_smul, zpow_add_one₀ hf.ne]
    exact ih.mul hf
  | pred i ih =>
    rw [sub_smul, one_smul, zpow_sub_one₀ hf.ne, sub_eq_add_neg]
    exact ih.mul hf.neg

/-! #### The classes of products, of principal divisors and of `n • E` -/

/-- **The class of a product is the product of the classes.** -/
theorem chernClassDiv_mul {E E' : Divisor k (F D)} {f f' : Ω} (hf : IsChernRepDiv D eL hH n E f)
    (hf' : IsChernRepDiv D eL hH n E' f') :
    chernClassDiv hk hτ (hf.mul hf') = chernClassDiv hk hτ hf * chernClassDiv hk hτ hf' :=
  chernClass_mul _ _ _ _ hf.toKummerInv hf'.toKummerInv

/-- **Principal divisors have trivial class.** -/
theorem chernClassDiv_div (h : F D) (h0 : h ≠ 0) :
    chernClassDiv hk hτ (isChernRepDiv_div (D := D) (eL := eL) (hH := hH) (n := n) h h0) = 1 :=
  chernClass_eq_one _ _ _ _ _ fun σ ↦ fixes_of_mem_F σ.2 h

/-- **`n • E` has trivial class.** -/
theorem chernClassDiv_one_nsmul (E : Divisor k (F D)) :
    chernClassDiv hk hτ (isChernRepDiv_one_nsmul (D := D) (eL := eL) (hH := hH) (n := n) E) = 1 :=
  chernClass_eq_one _ _ _ _ _ fun σ ↦ smul_one σ

/-- The zero divisor has trivial class. -/
theorem chernClassDiv_one :
    chernClassDiv hk hτ (isChernRepDiv_one (D := D) (eL := eL) (hH := hH) (n := n)) = 1 :=
  chernClass_eq_one _ _ _ _ _ fun σ ↦ smul_one σ

/-! #### Comparison with `IsChernRep` -/

variable {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X}

include hk hτ in
/-- **A representative of `𝒪_X(x)` in the sense of `CuspChern` represents the divisor `P₀`**,
the place of `F` under `W₀`: at the places `W` over `P₀` (the `H`-conjugates of `W₀`) the
inertia acts on the roots of `f` as on those of a uniformiser (`IsChernRep.conj`), and the other
places are centred on `U = X ∖ {x}`, where the roots of `f` are unramified. -/
theorem IsChernRep.isChernRepDiv (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) {π : (F D)ˣ} (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {P₀ : Place k (F D)} (hW₀P : ∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P₀.1) {f : Ω}
    (hf : IsChernRep D eL hH n U W₀ ((π : F D) : Ω) f) :
    IsChernRepDiv D eL hH n (Finsupp.single P₀ 1) f where
  toKummerInv := hf.toKummerInv
  loc P W hW u hu hord σ hσ β γ hβ hγ := by
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.algebraMap_mem c)
    have hβ0 := ne_zero_of_pow_eq hf.ne hβ
    have hγ0 : γ ≠ 0 := ne_zero_of_pow_eq (fun e ↦ hu (Subtype.ext e)) hγ
    by_cases hP : P = P₀
    · subst hP
      have hπ1 := ord_eq_one_of_valuation hW₀P hπW hπ
      -- `W` and `W₀` lie over the same place of `L = F`
      have hL : W₀.comap (algebraMap D.L Ω) = W.comap (algebraMap D.L Ω) := by
        ext z
        change (z : Ω) ∈ W₀ ↔ (z : Ω) ∈ W
        rw [show (z : Ω) = ((⟨z, mem_F_of_mem_L hH z⟩ : F D) : Ω) from rfl, hW₀P, hW]
      haveI : IsGalois D.L Ω := IsGalois.tower_top_of_isGalois (K₀ k t) D.L Ω
      obtain ⟨ρ, hρ⟩ := exists_algEquiv_comap_eq W₀ W hL
      set h' : Ω ≃ₐ[K₀ k t] Ω := ρ.restrictScalars (K₀ k t)
      have hhL : h' ∈ D.HL := by
        have hcl : IsClosed (D.HL : Set (Ω ≃ₐ[K₀ k t] Ω)) := D.isClosed_HL
        have h := InfiniteGalois.fixingSubgroup_fixedField (⟨D.HL, hcl⟩ : ClosedSubgroup _)
        change h' ∈ (⟨D.HL, hcl⟩ : ClosedSubgroup _).toSubgroup
        rw [← h, IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        exact ρ.commutes ⟨y, hy⟩
      set h : D.H := ⟨h', D.le hhL⟩
      have hσ' : ((h⁻¹ * σ * h : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W₀ := by
        have := (GaloisPi1.mem_inertia_comap_iff h' (σ : Ω ≃ₐ[K₀ k t] Ω)).1 (by
          rw [show W₀.comap (h'.symm : Ω →+* Ω) = W from hρ.symm]; exact hσ)
        simpa using this
      obtain ⟨β₀, hβ₀⟩ := IsSepClosed.exists_pow_nat_eq ((π : F D) : Ω) n
      have hπ0 : ((π : F D) : Ω) ≠ 0 := by simp
      have hβ₀0 : β₀ ≠ 0 := ne_zero_of_pow_eq hπ0 hβ₀
      have e1 := hf.conj hk hτ hW₀ hπ0 (smul_uniformiser π) h hσ' hβ hβ₀
      rw [show h * (h⁻¹ * σ * h) * h⁻¹ = σ by group] at e1
      -- `h(β₀)` is an `n`-th root of `π`, and its Kummer value at `σ` is that of `β₀`
      have hβ₁ : (h • β₀) ^ n = ((π : F D) : Ω) := by
        rw [← smul_pow', hβ₀, smul_uniformiser]
      have e2 : σ • (h • β₀) / (h • β₀) = (h⁻¹ * σ * h) • β₀ / β₀ := by
        have hζ : ((h⁻¹ * σ * h) • β₀ / β₀) ^ n = 1 := by
          rw [div_pow, ← smul_pow', hβ₀, smul_uniformiser, div_self hπ0]
        have hr := smul_eq_of_pow_eq_one D n h hζ
        rw [smul_div₀', smul_smul, show h * (h⁻¹ * σ * h) = σ * h by group, mul_smul] at hr
        exact hr
      -- `u / π` is a unit at `P₀`
      have hπF : (π : F D) ≠ 0 := π.ne_zero
      have hord' : P.ord (u / π) = 0 := by
        rw [P.ord_div hu hπF, hord, hπ1, Finsupp.single_eq_same, sub_self]
      have hγ' : (γ / h • β₀) ^ n = ((u / π : F D) : Ω) := by
        rw [div_pow, hγ, hβ₁, IntermediateField.coe_div]
      have e3 := smul_eq_of_ord_eq_zero hW (div_ne_zero hu hπF) hord' hσ hγ'
      have hhβ₀ : h • β₀ ≠ 0 := (smul_ne_zero_iff_ne h).2 hβ₀0
      have hσhβ₀ : σ • h • β₀ ≠ 0 := (smul_ne_zero_iff_ne σ).2 hhβ₀
      rw [smul_div₀', div_eq_div_iff hσhβ₀ hhβ₀] at e3
      rw [e1, ← e2, div_eq_div_iff hhβ₀ hγ0]
      linear_combination -e3
    · have hWU : IsCentredOn D X eL U W := by
        by_contra hWU
        apply hP
        apply Place.ext
        ext y
        rw [← hW y, ← hW₀P y]
        exact eq_of_not_isCentredOn D X eL hk U (by rw [hUx]; exact Set.subsingleton_singleton)
          hkW hW₀.1 hWU hW₀U y
      have hord0 : P.ord u = 0 := by rw [hord, Finsupp.single_eq_of_ne hP]
      rw [hf.unram W hWU σ hσ β hβ, smul_eq_of_ord_eq_zero hW hu hord0 hσ hγ, div_self hβ0,
        div_self hγ0]

/-- The class of `IsChernRep.isChernRepDiv` is `chernClassX`. -/
theorem chernClassDiv_isChernRepDiv (hUx : (U : Set X)ᶜ = {x})
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀) {π : (F D)ˣ}
    (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {P₀ : Place k (F D)} (hW₀P : ∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P₀.1) {f : Ω}
    (hf : IsChernRep D eL hH n U W₀ ((π : F D) : Ω) f) :
    chernClassDiv hk hτ (hf.isChernRepDiv hk hτ hUx hW₀ hW₀U hπW hπ hW₀P) =
      chernClassX hk hτ hf :=
  rfl

/-! #### Existence -/

omit [IsAlgClosed k] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
include hk in
/-- Every place `W ⊇ k` of `Ω` is centred on the proper curve `X`. -/
lemma isCentredOn_top_of {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W) :
    IsCentredOn D X eL ⊤ W := by
  by_contra h
  obtain ⟨z, hz, -⟩ := exists_notMem_of_not_isCentredOn D X eL hk ⊤ hkW h
  exact hz trivial

include hk hτ in
/-- **Every place of `F` (a point of `X`) has a representative** (`X` of genus `≥ 1`): the
representative of `𝒪_X(x)` of `exists_isChernRep`, for `x` the point under a place `W₀` over
`P` and `U = X ∖ {x}`. -/
theorem exists_isChernRepDiv_single (hgen : 0 < (curveGenus k X).toNat) (P : Place k (F D)) :
    ∃ f, IsChernRepDiv D eL hH n (Finsupp.single P 1) f := by
  obtain ⟨W₀, hW₀P⟩ := exists_valuationSubring_liesOver D P
  have hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW₀P _).2 (P.algebraMap_mem c)
  -- the point `y` of `X` under `W₀`
  haveI := isSeparated_of_over k X
  have hkO : ∀ c : k, algebraMap k X.functionField c ∈ comapK D X eL hk W₀ := fun c ↦ by
    change ((eL (algebraMap k X.functionField c) : D.L) : Ω) ∈ W₀
    rw [hk]
    exact hkW₀ c
  obtain ⟨y, hy⟩ : ∃ y : X, stalkVS k y = comapK D X eL hk W₀ := by
    refine ⟨(pointEquivValuationSubringOver k (valuationRing_stalk_of_isCurveOver k X)).symm
      ⟨_, hkO⟩, ?_⟩
    have := congrArg Subtype.val ((pointEquivValuationSubringOver k
      (valuationRing_stalk_of_isCurveOver k X)).apply_symm_apply ⟨_, hkO⟩)
    rw [pointEquivValuationSubringOver_apply] at this
    exact this
  have hyη : y ≠ genericPoint X := by
    intro hyη
    apply P.ne_top
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h1 : eL.symm ⟨_, mem_L_of_mem_F z⟩ ∈ comapK D X eL hk W₀ := by
      have htop : stalkVS k (genericPoint X) = ⊤ := stalkValuationSubring_genericPoint _
      rw [← hy, hyη, htop]
      trivial
    have h2 : ((z : F D) : Ω) ∈ W₀ := by
      change ((eL (eL.symm ⟨_, mem_L_of_mem_F z⟩) : D.L) : Ω) ∈ W₀ at h1
      simpa using h1
    exact (hW₀P z).1 h2
  -- `U = X ∖ {y}`
  let U : X.Opens := ⟨{y}ᶜ, (isClosed_closedPoint k X ⟨y, hyη⟩).isOpen_compl⟩
  have hUx : (U : Set X)ᶜ = {y} := compl_compl _
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ hyη h.symm⟩⟩
  have hUfin : (U : Set X)ᶜ.Finite := hUx ▸ Set.finite_singleton y
  have hW₀ : IsCentredOn D X eL ⊤ W₀ := isCentredOn_top_of hk hkW₀
  have hW₀U : ¬ IsCentredOn D X eL U W₀ := fun h ↦
    (mem_of_isCentredOn D X eL hk U hUfin h hy) rfl
  obtain ⟨π, -, hπW, hπ⟩ := exists_uniformiser hW₀P
  obtain ⟨f, hf⟩ := exists_isChernRep hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  exact ⟨f, hf.isChernRepDiv hk hτ hUx hW₀ hW₀U hπW hπ hW₀P⟩

include hk hτ in
/-- **Every divisor has a representative** (`X` of genus `≥ 1`). -/
theorem exists_isChernRepDiv (hgen : 0 < (curveGenus k X).toNat) (E : Divisor k (F D)) :
    ∃ f, IsChernRepDiv D eL hH n E f := by
  induction E using Finsupp.induction_linear with
  | zero => exact ⟨1, isChernRepDiv_one⟩
  | add E E' hE hE' =>
    obtain ⟨f, hf⟩ := hE
    obtain ⟨f', hf'⟩ := hE'
    exact ⟨_, hf.mul hf'⟩
  | single P m =>
    obtain ⟨f, hf⟩ := exists_isChernRepDiv_single hk hτ (n := n) (hH := hH) hgen P
    refine ⟨f ^ m, ?_⟩
    have := hf.zpow m
    rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at this

/-! ### The homomorphisms `Div(F) → H²(Δ_X, μ_n)` and `Pic(F) → H²(Δ_X, μ_n)` -/

variable (hH n) in
/-- **The first Chern class modulo `n`** `c₁ : Div(F) → H²(Δ_X, μ_n)`, `E ↦ c₁(𝒪_X(E)) mod n`
(`X` of genus `≥ 1`). -/
noncomputable def c1Div (hgen : 0 < (curveGenus k X).toNat) :
    Divisor k (F D) →+ Additive (H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)) where
  toFun E := Additive.ofMul
    (chernClassDiv hk hτ (exists_isChernRepDiv hk hτ (n := n) (hH := hH) hgen E).choose_spec)
  map_zero' := by
    rw [chernClassDiv_eq hk hτ _ isChernRepDiv_one, chernClassDiv_one]
    rfl
  map_add' E E' := by
    rw [← ofMul_mul, chernClassDiv_eq hk hτ _
      ((exists_isChernRepDiv hk hτ (n := n) (hH := hH) hgen E).choose_spec.mul
        (exists_isChernRepDiv hk hτ (n := n) (hH := hH) hgen E').choose_spec),
      chernClassDiv_mul]

/-- `c1Div` is computed by any representative. -/
theorem c1Div_eq (hgen : 0 < (curveGenus k X).toNat) {E : Divisor k (F D)} {f : Ω}
    (hf : IsChernRepDiv D eL hH n E f) :
    c1Div hH hk hτ n hgen E = Additive.ofMul (chernClassDiv hk hτ hf) :=
  congrArg Additive.ofMul (chernClassDiv_eq hk hτ _ hf)

/-- **Principal divisors have trivial Chern class.** -/
theorem c1Div_div (hgen : 0 < (curveGenus k X).toNat) (h : F D) (h0 : h ≠ 0) :
    c1Div hH hk hτ n hgen (Divisor.div k h) = 0 := by
  rw [c1Div_eq hk hτ hgen (isChernRepDiv_div h h0), chernClassDiv_div hk hτ h h0]
  rfl

/-- **`c₁(𝒪_X(n E)) ≡ 0 mod n`.** -/
theorem c1Div_nsmul (hgen : 0 < (curveGenus k X).toNat) (E : Divisor k (F D)) :
    c1Div hH hk hτ n hgen (n • E) = 0 := by
  rw [c1Div_eq hk hτ hgen (isChernRepDiv_one_nsmul E), chernClassDiv_one_nsmul hk hτ E]
  rfl

/-- **Comparison with `CuspChern`**: on the divisor `P₀` of a point, `c1Div` is
`chernClassX` (`c₁(𝒪_X(x)) mod n`). -/
theorem c1Div_single_eq_chernClassX (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) {π : (F D)ˣ} (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {P₀ : Place k (F D)} (hW₀P : ∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P₀.1) {f : Ω}
    (hf : IsChernRep D eL hH n U W₀ ((π : F D) : Ω) f) :
    c1Div hH hk hτ n hgen (Finsupp.single P₀ 1) = Additive.ofMul (chernClassX hk hτ hf) :=
  c1Div_eq hk hτ hgen (hf.isChernRepDiv hk hτ hUx hW₀ hW₀U hπW hπ hW₀P)

variable (hH n) in
/-- **The first Chern class modulo `n` on the Picard group** `Pic(F) → H²(Δ_X, μ_n)`
(`c1Div` kills the principal divisors). -/
noncomputable def c1Pic (hgen : 0 < (curveGenus k X).toNat) :
    Pic k (F D) →+ Additive (H2lc π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)) :=
  QuotientAddGroup.lift (principal k (F D)) (c1Div hH hk hτ n hgen) fun E hE ↦ by
    obtain ⟨h, h0, rfl⟩ := mem_principal.1 hE
    exact c1Div_div hk hτ hgen h h0

/-- `c1Pic` on the class of a divisor. -/
theorem c1Pic_mk (hgen : 0 < (curveGenus k X).toNat) (E : Divisor k (F D)) :
    c1Pic hH hk hτ n hgen (QuotientAddGroup.mk E) = c1Div hH hk hτ n hgen E :=
  rfl

end Curve

end CurvesJacobian.ChernClass
