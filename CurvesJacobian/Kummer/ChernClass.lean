/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Surface.H2
import ContinuousKummerTheory.Kummer.Basic

/-!
# The Kummer cocycle of a function invariant modulo `n`-th powers (Chern classes, group theory)

Let `G` act on a field `Ω` by ring automorphisms, `ρ : G →* Q` surjective with kernel `N`, and
`Ω^N` the fixed elements of `N` (in the application `G = H = Gal(Ω/K(X))`, `Q = Δ_X`, and `Ω^N`
is the function field of the profinite universal cover `X̃` of `X`). Let `f ∈ (Ω^N)ˣ` be
**invariant modulo `n`-th powers**: `σ f = f g_σⁿ` with `g_σ ∈ Ω^N` for all `σ ∈ G`
(`KummerInv`). This is the image of `f ∈ H⁰(Q, Ω^{N×}/n)` in `H¹(Q, Ω^{N×n})`, and

  `a(γ, δ) = g_γ · γ(g_δ) / g_{γδ} ∈ μ_n`

is the image of that class under the boundary of `1 → μ_n → Ω^{N×} → Ω^{N×}/μ_n → 1`
(`chernVal`, `chernCocycle`). For `f` with `div f ≡ D (mod n)` on `X̃` this is the
group-theoretic first Chern class of `𝒪_X(D)` modulo `n` (the boundary of the Kummer sequence
computed on the universal cover: [Mzk7] = *Topics surrounding the anabelian geometry of
hyperbolic curves*, Def. 4.1 and the proof of Lemma 4.4, txt l.1490–1625: on a finite étale
cover `Y` with `L|_Y ≅ P^{⊗n}`, i.e. `D_Y = n E + div f`).

Here (pure group theory, no curves):

* `chernVal_pow` (`a(γ, δ)ⁿ = 1`), `chernVal_cond` (the cocycle identity), `chernCocycle`;
* `chernCocycle_mul_dx` (another choice `g'` changes `a` by the coboundary of `g'/g`),
  `chernCocycle_mul_pow` (replacing `f` by `f bⁿ` with `b ∈ Ω^N` does not change `a` for the
  choice `g_γ γ(b)/b`);
* `kummerTwist`: for a root `βⁿ = f`, the homomorphism `G →* μ_n ×_a Q`,
  `σ ↦ (σ(β) / (g_{ρσ} β), ρ σ)` — the Kummer extension `Gal(Ω^N(β)/Ω^G)` as the twisted product;
* topology: if the stabilisers of the action are open and `ρ` is a quotient map, admissible
  locally constant `g` exist (`exists_isAdm`) and `a` is locally constant
  (`isLocallyConstant_chernCocycle`), so `a` defines a class in `H²_lc(Q, μ_n)`
  (`chernClassOf`), independent of `g` (`chernClassOf_eq`) and unchanged under `f ↦ f bⁿ`
  (`chernClassOf_mul_pow`).
-/

open Pi1.Profinite KummerTheory

namespace CurvesJacobian.ChernClass

section Generic

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  (ρ : G →* Q) (n : ℕ)

/-- `x` is fixed by `ker ρ`. -/
def IsFix (x : Ω) : Prop := ∀ σ ∈ ρ.ker, σ • x = x

/-- **`f` is invariant modulo `n`-th powers**: a nonzero element of `Ω^{ker ρ}` with
`σ f = f gⁿ`, `g ∈ Ω^{ker ρ}`, for every `σ ∈ G`. -/
structure KummerInv (f : Ω) : Prop where
  ne : f ≠ 0
  fix : IsFix ρ f
  inv : ∀ σ : G, ∃ g, IsFix ρ g ∧ σ • f = f * g ^ n

variable {ρ}

lemma IsFix.smul_eq {x : Ω} (hx : IsFix ρ x) {σ τ : G} (h : ρ σ = ρ τ) : σ • x = τ • x := by
  have hk : τ⁻¹ * σ ∈ ρ.ker := by simp [MonoidHom.mem_ker, h]
  calc σ • x = τ • ((τ⁻¹ * σ) • x) := by rw [smul_smul, mul_inv_cancel_left]
    _ = τ • x := by rw [hx _ hk]

lemma IsFix.smul {x : Ω} (hx : IsFix ρ x) (τ : G) : IsFix ρ (τ • x) := fun σ hσ ↦ by
  have : τ⁻¹ * σ * τ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [hσ]
  calc σ • τ • x = τ • ((τ⁻¹ * σ * τ) • x) := by
        rw [smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = τ • x := by rw [hx _ this]

lemma IsFix.mul {x y : Ω} (hx : IsFix ρ x) (hy : IsFix ρ y) : IsFix ρ (x * y) := fun σ hσ ↦ by
  rw [smul_mul', hx σ hσ, hy σ hσ]

lemma IsFix.div {x y : Ω} (hx : IsFix ρ x) (hy : IsFix ρ y) : IsFix ρ (x / y) := fun σ hσ ↦ by
  rw [smul_div₀', hx σ hσ, hy σ hσ]

variable (s : Q → G) (hs : ∀ γ, ρ (s γ) = γ)

variable (ρ) in
/-- **Admissible choices** `g : Q → Ω^{ker ρ}` for `f`: `s(γ) f = f g(γ)ⁿ`. -/
structure IsAdm (f : Ω) (g : Q → Ω) : Prop where
  fix : ∀ γ, IsFix ρ (g γ)
  ne : ∀ γ, g γ ≠ 0
  eq : ∀ γ, s γ • f = f * g γ ^ n

/-- The value `g(γ) · γ(g(δ)) / g(γδ)` of the Chern cocycle. -/
def chernVal (g : Q → Ω) (x : Q × Q) : Ω := g x.1 * (s x.1 • g x.2) / g (x.1 * x.2)

variable {s n}

lemma chernVal_ne {f : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g) (x : Q × Q) : chernVal s g x ≠ 0 := by
  simp only [chernVal, ne_eq, div_eq_zero_iff, mul_eq_zero, smul_eq_zero_iff_eq, not_or]
  exact ⟨⟨hg.ne _, hg.ne _⟩, hg.ne _⟩

include hs

lemma chernVal_pow {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g)
    (x : Q × Q) : chernVal s g x ^ n = 1 := by
  obtain ⟨γ, δ⟩ := x
  have h1 := hg.eq γ
  have h2 := hg.eq δ
  have h3 := hg.eq (γ * δ)
  have h4 : s (γ * δ) • f = (s γ * s δ) • f := hfix.smul_eq (by simp [hs])
  rw [mul_smul, h2, smul_mul', h1, smul_pow'] at h4
  simp only [chernVal, div_pow, mul_pow]
  have hgd : g (γ * δ) ^ n ≠ 0 := pow_ne_zero _ (hg.ne _)
  rw [div_eq_one_iff_eq hgd]
  apply mul_left_cancel₀ hf
  rw [← h3, h4]
  ring

variable (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
include hμ

lemma chernVal_cond {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g)
    (γ δ ε : Q) :
    chernVal s g (γ * δ, ε) * chernVal s g (γ, δ) =
      chernVal s g (δ, ε) * chernVal s g (γ, δ * ε) := by
  have hμ' := hμ (s γ) _ (chernVal_pow hs hf hfix hg (δ, ε))
  have hfixe : s (γ * δ) • g ε = s γ • s δ • g ε := by
    rw [smul_smul]; exact (hg.fix ε).smul_eq (by simp [hs])
  conv_rhs => rw [← hμ']
  simp only [chernVal, smul_div₀', smul_mul', hfixe]
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  have := hg.ne (δ * ε)
  have := hg.ne (γ * δ * ε)
  have : s γ • g (δ * ε) ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hg.ne _
  rw [mul_assoc γ δ ε]
  field_simp

/-- **The Chern cocycle** `a(γ, δ) = g(γ) γ(g(δ)) / g(γδ)`, with values in `μ_n`. -/
def chernMu {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g) :
    Q × Q → Mu n Ω := fun x ↦
  Mu.mk (Units.mk0 _ (chernVal_ne hg x)) (Units.ext (by simp [chernVal_pow hs hf hfix hg x]))

omit hμ in
@[simp] lemma val_chernMu {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (x : Q × Q) :
    ((Mu.val (chernMu hs hf hfix hg x) : Ωˣ) : Ω) = chernVal s g x := rfl

/-- The Chern cocycle is a (trivial-action) 2-cocycle. -/
theorem chernMu_mem {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g) :
    chernMu hs hf hfix hg ∈ TrivCocycle Q (Mu n Ω) := fun γ δ ε ↦ by
  ext
  exact chernVal_cond hs hμ hf hfix hg γ δ ε

/-- The Chern cocycle as an element of `TrivCocycle`. -/
def chernCocycle {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g) :
    TrivCocycle Q (Mu n Ω) :=
  ⟨chernMu hs hf hfix hg, chernMu_mem hs hμ hf hfix hg⟩

/-! ### Changing the choices -/

omit hs hμ in
lemma ratio_pow {f : Ω} (hf : f ≠ 0) {g g' : Q → Ω} (hg : IsAdm ρ n s f g)
    (hg' : IsAdm ρ n s f g') (γ : Q) : (g' γ / g γ) ^ n = 1 := by
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ (hg.ne γ))]
  apply mul_left_cancel₀ hf
  rw [← hg.eq, ← hg'.eq]

omit hs in
lemma chernVal_mul_ratio {f : Ω} (hf : f ≠ 0) {g g' : Q → Ω} (hg : IsAdm ρ n s f g)
    (hg' : IsAdm ρ n s f g') (γ δ : Q) :
    chernVal s g' (γ, δ) = chernVal s g (γ, δ) *
      ((g' δ / g δ) / (g' (γ * δ) / g (γ * δ)) * (g' γ / g γ)) := by
  have h1 : s γ • g' δ = s γ • g δ * (g' δ / g δ) := by
    rw [← hμ (s γ) _ (ratio_pow hf hg hg' δ), ← smul_mul', mul_div_cancel₀ _ (hg.ne δ)]
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  have := hg'.ne (γ * δ)
  simp only [chernVal]
  rw [h1]
  field_simp

omit hs hμ in
/-- **Changing `f` to `f bⁿ`** (`b ∈ Ω^{ker ρ}`): `g'(γ) = g(γ) γ(b) / b` is admissible. -/
lemma isAdm_mul_pow {f b : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g) (hb : IsFix ρ b)
    (hb0 : b ≠ 0) : IsAdm ρ n s (f * b ^ n) (fun γ ↦ g γ * (s γ • b) / b) where
  fix γ := ((hg.fix γ).mul (hb.smul _)).div hb
  ne γ := by
    have : s γ • b ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hb0
    have := hg.ne γ
    positivity
  eq γ := by
    rw [smul_mul', smul_pow', hg.eq γ, div_pow, mul_pow]
    field_simp

omit hμ in
lemma chernVal_mul_pow {f b : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g) (hb : IsFix ρ b)
    (hb0 : b ≠ 0) (x : Q × Q) :
    chernVal s (fun γ ↦ g γ * (s γ • b) / b) x = chernVal s g x := by
  obtain ⟨γ, δ⟩ := x
  have h : s γ • s δ • b = s (γ * δ) • b := by
    rw [smul_smul]; exact hb.smul_eq (by simp [hs])
  have : s γ • b ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hb0
  have : s (γ * δ) • b ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hb0
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  simp only [chernVal, smul_div₀', smul_mul', h]
  field_simp

/-! ### The Kummer extension as a twisted product -/

omit hμ in
/-- `σ(β) / (g(ρσ) β) ∈ μ_n` for a root `βⁿ = f`. -/
lemma kummerVal_pow {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g)
    {β : Ω} (hβ : β ^ n = f) (σ : G) : (σ • β / (g (ρ σ) * β)) ^ n = 1 := by
  have h1 : σ • f = s (ρ σ) • f := hfix.smul_eq (hs _).symm
  rw [div_pow, mul_pow, ← smul_pow', hβ, h1, hg.eq,
    div_eq_one_iff_eq (mul_ne_zero (pow_ne_zero _ (hg.ne _)) hf)]
  ring

omit hs hμ in
lemma ne_zero_of_pow_eq [NeZero n] {f β : Ω} (hf : f ≠ 0) (hβ : β ^ n = f) : β ≠ 0 :=
  fun h ↦ hf (by rw [← hβ, h, zero_pow (NeZero.ne n)])

/-- **The Kummer extension `Ω^{ker ρ}(β) / Ω^G` as a twisted product**: for `βⁿ = f`,
`σ ↦ (σ(β) / (g(ρσ) β), ρσ)` is a homomorphism `G →* μ_n ×_a Q`. -/
def kummerTwist [NeZero n] {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) {β : Ω} (hβ : β ^ n = f) :
    G →* Twist (chernCocycle hs hμ hf hfix hg) where
  toFun σ := ⟨Mu.mk (Units.mk0 (σ • β / (g (ρ σ) * β))
      (div_ne_zero (by rw [ne_eq, smul_eq_zero_iff_eq]; exact ne_zero_of_pow_eq hf hβ)
        (mul_ne_zero (hg.ne _) (ne_zero_of_pow_eq hf hβ))))
      (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        exact kummerVal_pow hs hf hfix hg hβ σ)), ρ σ⟩
  map_one' := by
    have hβ0 := ne_zero_of_pow_eq hf hβ
    have h1 : s 1 • g 1 = g 1 := hg.fix 1 (s 1) (by rw [MonoidHom.mem_ker, hs])
    have := hg.ne 1
    refine Twist.ext (Mu.ext (Units.ext ?_)) (map_one ρ)
    change (1 : G) • β / (g (ρ 1) * β) = ((chernVal s g (1, 1))⁻¹ : Ω)
    simp only [chernVal, one_smul, map_one, mul_one, h1]
    field_simp
  map_mul' σ τ := by
    have hβ0 := ne_zero_of_pow_eq hf hβ
    have hτ := kummerVal_pow hs hf hfix hg hβ τ
    set mτ := τ • β / (g (ρ τ) * β) with hmτ
    have hτβ : τ • β = mτ * g (ρ τ) * β := by
      rw [hmτ]; have := hg.ne (ρ τ); field_simp
    have hσm : σ • mτ = mτ := hμ σ mτ hτ
    have hσg : σ • g (ρ τ) = s (ρ σ) • g (ρ τ) := (hg.fix _).smul_eq (hs _).symm
    refine Twist.ext (Mu.ext (Units.ext ?_)) (map_mul ρ σ τ)
    change (σ * τ) • β / (g (ρ (σ * τ)) * β) =
      σ • β / (g (ρ σ) * β) * (τ • β / (g (ρ τ) * β)) * chernVal s g (ρ σ, ρ τ)
    rw [← hmτ, mul_smul, hτβ, smul_mul', smul_mul', hσm, hσg, map_mul]
    have := hg.ne (ρ σ)
    have := hg.ne (ρ τ)
    have := hg.ne (ρ σ * ρ τ)
    simp only [chernVal]
    field_simp

@[simp] lemma kummerTwist_g [NeZero n] {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) {β : Ω} (hβ : β ^ n = f) (σ : G) :
    (kummerTwist hs hμ hf hfix hg hβ σ).g = ρ σ := rfl

/-- On `ker ρ`, `kummerTwist` is the Kummer character `σ ↦ σ(β)/β`. -/
lemma kummerTwist_of_mem_ker [NeZero n] {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) {β : Ω} (hβ : β ^ n = f) {σ : G} (hσ : σ ∈ ρ.ker) (ζ : Mu n Ω)
    (hζ : σ • β = ((Mu.val ζ : Ωˣ) : Ω) * β) :
    kummerTwist hs hμ hf hfix hg hβ σ = Twist.incl ζ := by
  have hβ0 := ne_zero_of_pow_eq hf hβ
  have hσ1 : ρ σ = 1 := hσ
  have h1 : s 1 • g 1 = g 1 := hg.fix 1 (s 1) (by rw [MonoidHom.mem_ker, hs])
  have := hg.ne 1
  refine Twist.ext (Mu.ext (Units.ext ?_)) hσ1
  change σ • β / (g (ρ σ) * β) = ((Mu.val ζ : Ωˣ) : Ω) * (chernVal s g (1, 1))⁻¹
  simp only [chernVal, hσ1, hζ, mul_one, h1]
  field_simp

/-! ### Locally constant choices and the class in `H²_lc(Q, μ_n)` -/

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

omit [IsTopologicalGroup Q] hs hμ in
include hstab in
lemma isOpen_setOf_smul_eq (x y : Ω) : IsOpen {σ : G | σ • x = y} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ₀ h0
  refine ⟨(fun σ ↦ σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer G x), fun σ hσ ↦ ?_,
    (hstab x).preimage (continuous_const.mul continuous_id), by simp⟩
  have hσ' : (σ₀⁻¹ * σ) • x = x := hσ
  change σ • x = y
  calc σ • x = σ₀ • ((σ₀⁻¹ * σ) • x) := by rw [smul_smul, mul_inv_cancel_left]
    _ = y := by rw [hσ']; exact h0

omit [IsTopologicalGroup Q] hμ in
include hstab hq in
/-- `γ ↦ γ(x)` is locally constant on `Q` for `x ∈ Ω^{ker ρ}`. -/
lemma isLocallyConstant_smul {x : Ω} (hx : IsFix ρ x) : IsLocallyConstant fun γ ↦ s γ • x := by
  intro S
  apply hq
  have h1 : ρ ⁻¹' ((fun γ ↦ s γ • x) ⁻¹' S) = ⋃ y ∈ S, {σ : G | σ • x = y} := by
    ext σ
    simp [hx.smul_eq (hs (ρ σ))]
  rw [h1]
  exact isOpen_biUnion fun y _ ↦ isOpen_setOf_smul_eq hstab x y

omit [IsTopologicalGroup Q] hμ in
include hstab hq in
lemma isLocallyConstant_smul_comp {g : Q → Ω} (hfix : ∀ γ, IsFix ρ (g γ))
    (hg : IsLocallyConstant g) : IsLocallyConstant fun x : Q × Q ↦ s x.1 • g x.2 := by
  intro S
  have h1 : (fun x : Q × Q ↦ s x.1 • g x.2) ⁻¹' S =
      ⋃ δ : Q, ((fun γ ↦ s γ • g δ) ⁻¹' S) ×ˢ (g ⁻¹' {g δ}) := by
    ext ⟨γ, δ⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    exact ⟨fun h ↦ ⟨δ, h, rfl⟩, fun ⟨δ', h, h'⟩ ↦ by rwa [h']⟩
  rw [h1]
  exact isOpen_iUnion fun δ ↦ (isLocallyConstant_smul hs hstab hq (hfix δ) _).prod (hg _)

omit [IsTopologicalGroup G] hμ in
include hstab hq in
/-- **Locally constant admissible choices exist.** -/
theorem exists_isAdm [NeZero n] {f : Ω} (hf : KummerInv ρ n f) :
    ∃ g, IsAdm ρ n s f g ∧ IsLocallyConstant g := by
  classical
  set Q₀ : Subgroup Q := (MulAction.stabilizer G f).map ρ
  have hQ₀ : ∀ σ : G, ρ σ ∈ Q₀ → σ • f = f := by
    rintro σ ⟨τ, hτ, hτσ⟩
    rw [← hf.fix.smul_eq hτσ]
    exact hτ
  have hQ₀o : IsOpen (Q₀ : Set Q) := hq _ (by
    have : ρ ⁻¹' Q₀ = MulAction.stabilizer G f := by
      ext σ
      exact ⟨hQ₀ σ, fun h ↦ ⟨σ, h, rfl⟩⟩
    rw [this]
    exact hstab f)
  choose g₀ hg₀ using fun γ : Q ↦ hf.inv (s γ)
  let r : Q → Q := fun γ ↦ (QuotientGroup.mk γ : Q ⧸ Q₀).out
  have hr : ∀ γ, s γ • f = s (r γ) • f := fun γ ↦ by
    have h : (r γ)⁻¹ * γ ∈ Q₀ := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have h2 : ((s (r γ))⁻¹ * s γ) • f = f := hQ₀ _ (by simpa [hs] using h)
    calc s γ • f = s (r γ) • (((s (r γ))⁻¹ * s γ) • f) := by
          rw [smul_smul, mul_inv_cancel_left]
      _ = s (r γ) • f := by rw [h2]
  have hmk : IsLocallyConstant (QuotientGroup.mk : Q → Q ⧸ Q₀) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro c
    induction c using QuotientGroup.induction_on with | H a => ?_
    have : (QuotientGroup.mk : Q → Q ⧸ Q₀) ⁻¹' {(a : Q ⧸ Q₀)} =
        (fun b ↦ a⁻¹ * b) ⁻¹' (Q₀ : Set Q) := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientGroup.eq]
    rw [this]
    exact hQ₀o.preimage (continuous_const.mul continuous_id)
  refine ⟨fun γ ↦ g₀ (r γ), ⟨fun γ ↦ (hg₀ _).1, fun γ h0 ↦ ?_, fun γ ↦ ?_⟩, ?_⟩
  · have h := (hg₀ (r γ)).2
    rw [h0, zero_pow (NeZero.ne n), mul_zero, smul_eq_zero_iff_eq] at h
    exact hf.ne h
  · rw [hr]
    exact (hg₀ _).2
  · exact hmk.comp (fun c ↦ g₀ c.out)

omit hμ in
include hstab hq in
lemma isLocallyConstant_chernVal {f : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g)
    (hglc : IsLocallyConstant g) : IsLocallyConstant (chernVal s g) := by
  have h1 : IsLocallyConstant fun x : Q × Q ↦ g x.1 := hglc.comp_continuous continuous_fst
  have h3 : IsLocallyConstant fun x : Q × Q ↦ g (x.1 * x.2) :=
    hglc.comp_continuous continuous_mul
  have h2 := isLocallyConstant_smul_comp hs hstab hq hg.fix hglc
  exact (h1.comp₂ h2 (· * ·)).comp₂ h3 (· / ·)

/-- The trivial action of `Q` on `μ_n` (the geometric fundamental group acts trivially on the
roots of unity of an algebraically closed constant field). -/
local instance : MulDistribMulAction Q (Mu n Ω) := Pi1.SurfaceGroup.trivialAction Q (Mu n Ω)

/-- The Chern cocycle as a locally constant `2`-cocycle. -/
def chernCocycles {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) : H2lc.cocycles Q (Mu n Ω) :=
  ⟨chernMu hs hf hfix hg, IsLocallyConstant.desc _ (fun ζ : Mu n Ω ↦ ((Mu.val ζ : Ωˣ) : Ω))
    (isLocallyConstant_chernVal hs hstab hq hg hglc)
    (fun _ _ h ↦ Mu.ext (Units.ext h)), fun a b c ↦ chernMu_mem hs hμ hf hfix hg a b c⟩

/-- **The class of `f` in `H²_lc(Q, μ_n)`** for a locally constant admissible choice `g`. -/
def chernClassOf {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) : H2lc Q (Mu n Ω) :=
  QuotientGroup.mk (chernCocycles hs hμ hstab hq hf hfix hg hglc)

/-- **The class does not depend on `g`.** -/
theorem chernClassOf_eq {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g g' : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) (hg' : IsAdm ρ n s f g')
    (hglc' : IsLocallyConstant g') :
    chernClassOf hs hμ hstab hq hf hfix hg hglc =
      chernClassOf hs hμ hstab hq hf hfix hg' hglc' := by
  let ζ : Q → Mu n Ω := fun γ ↦ Mu.mk (Units.mk0 (g' γ / g γ) (div_ne_zero (hg'.ne γ) (hg.ne γ)))
    (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact ratio_pow hf hg hg' γ))
  have hζ : IsLocallyConstant ζ := IsLocallyConstant.desc _
    (fun ζ : Mu n Ω ↦ ((Mu.val ζ : Ωˣ) : Ω)) (hglc'.comp₂ hglc (· / ·))
    (fun _ _ h ↦ Mu.ext (Units.ext h))
  apply QuotientGroup.eq.2
  refine ⟨ζ, hζ, ?_⟩
  ext ⟨γ, δ⟩
  change ((Mu.val (ζ δ / ζ (γ * δ) * ζ γ) : Ωˣ) : Ω) =
    ((Mu.val ((chernMu hs hf hfix hg (γ, δ))⁻¹ * chernMu hs hf hfix hg' (γ, δ)) : Ωˣ) : Ω)
  simp only [map_mul, map_div, map_inv, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val,
    val_chernMu, ζ, Mu.val_mk, Units.val_mk0]
  rw [chernVal_mul_ratio hμ hf hg hg']
  have := chernVal_ne hg (γ, δ)
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  have := hg'.ne (γ * δ)
  field_simp

/-- **Replacing `f` by `f bⁿ`** (`b ∈ (Ω^{ker ρ})ˣ`) does not change the class. -/
theorem chernClassOf_mul_pow {f b : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) (hb : IsFix ρ b) (hb0 : b ≠ 0) :
    chernClassOf hs hμ hstab hq (mul_ne_zero hf (pow_ne_zero n hb0))
      (hfix.mul fun σ hσ ↦ by rw [smul_pow', hb σ hσ]) (isAdm_mul_pow hg hb hb0)
      ((hglc.comp₂ (isLocallyConstant_smul hs hstab hq hb) (· * ·)).comp₂
        (IsLocallyConstant.const b) (· / ·)) =
    chernClassOf hs hμ hstab hq hf hfix hg hglc := by
  unfold chernClassOf
  congr 1
  refine Subtype.ext (funext fun x ↦ ?_)
  exact Mu.ext (Units.ext (chernVal_mul_pow hs hg hb hb0 x))

/-- **The Chern class modulo `n`** of `f`, invariant modulo `n`-th powers. -/
noncomputable def chernClass [NeZero n] {f : Ω} (hf : KummerInv ρ n f) : H2lc Q (Mu n Ω) :=
  chernClassOf hs hμ hstab hq hf.ne hf.fix (exists_isAdm hs hstab hq hf).choose_spec.1
    (exists_isAdm hs hstab hq hf).choose_spec.2

theorem chernClassOf_eq_chernClass [NeZero n] {f : Ω} (hf : KummerInv ρ n f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) :
    chernClassOf hs hμ hstab hq hf.ne hf.fix hg hglc = chernClass hs hμ hstab hq hf :=
  chernClassOf_eq hs hμ hstab hq _ _ _ _ _ _

end Topology

end Generic

end CurvesJacobian.ChernClass
