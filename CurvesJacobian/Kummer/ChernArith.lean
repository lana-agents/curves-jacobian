/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernClass
import LocalClassFieldTheory.Brauer.ContH2

/-!
# The Kummer–Chern class with a non-trivial action on `μ_n` (arithmetic Chern classes, group theory)

`Kummer/ChernClass.lean` computes the first Chern class modulo `n` as the boundary of the Kummer
sequence on the profinite universal cover, for the **geometric** fundamental group (`k = k̄`, the
group `Q` acts trivially on `μ_n`; class in pi1's `H2lc`). For a curve over a non-closed field
(`Q = Π_X`, acting on `μ_n` through `Π_X ↠ G_k` and the cyclotomic character) the same cochain

  `a(γ, δ) = g_γ · s_γ(g_δ) / g_{γδ}`   (`s_γ f = f g_γⁿ`)

is a 2-cocycle for the **non-trivial** action (`chernVal_cond_act`: the identity
`a(γδ, ε) a(γ, δ) = s_γ(a(δ, ε)) a(γ, δε)` holds in `Ω` without any hypothesis on `μ_n`). This file
gives the class in `ContH2 Q μ_n` (locally constant cochains, the cohomology used by MR7's
`EigenH2` / `ThetaClass`), for any action of `Q` on `μ_n` compatible with the action of `G` on `Ω`
(`hμQ : (ρ σ) • ζ = σ • ζ` in `Ω`):

* `chernMuA`, `isMulCocycle₂_chernMuA`, `chernCocyclesA`, `chernClassOfA`;
* `chernClassOfA_eq` (independent of the admissible `g`), `chernClassOfA_mul_pow`
  (`f ↦ f bⁿ`, `b ∈ Ω^{ker ρ}`), **`chernClassA`** for `f` invariant modulo `n`-th powers;
* `chernClassA_mul`: `c(f f') = c(f) c(f')`;
* **`map_chernClassA`**: restriction along a continuous `ι : Q' →* Q` with a compatible
  `ρ' : G' →* Q'` (e.g. `Δ_X ⊆ Π_X`) is the class of the same `f` for `(G', ρ')` — this is the
  comparison of the arithmetic class with MR5's geometric `chernClass` on `Δ_X`
  (JAC D-d milestone C1; `JAC-plan.md`).
-/

open Pi1.Profinite KummerTheory groupCohomology

namespace CurvesJacobian.ChernClass

set_option linter.unusedSectionVars false

section Arith

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  {ρ : G →* Q} {n : ℕ} {s : Q → G} (hs : ∀ γ, ρ (s γ) = γ)

include hs in
/-- **The cocycle identity of the Chern cochain for the actual action** (no hypothesis on the
action on `μ_n`). -/
lemma chernVal_cond_act {f : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g) (γ δ ε : Q) :
    chernVal s g (γ * δ, ε) * chernVal s g (γ, δ) =
      s γ • chernVal s g (δ, ε) * chernVal s g (γ, δ * ε) := by
  have hfixe : s (γ * δ) • g ε = s γ • s δ • g ε := by
    rw [smul_smul]; exact (hg.fix ε).smul_eq (by simp [hs])
  simp only [chernVal, smul_div₀', smul_mul', hfixe]
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  have := hg.ne (δ * ε)
  have := hg.ne (γ * δ * ε)
  have : s γ • g (δ * ε) ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hg.ne _
  rw [mul_assoc γ δ ε]
  field_simp

variable [MulDistribMulAction Q (Mu n Ω)]
  (hμQ : ∀ (σ : G) (ζ : Mu n Ω), ((Mu.val (ρ σ • ζ) : Ωˣ) : Ω) = σ • ((Mu.val ζ : Ωˣ) : Ω))

include hs hμQ in
lemma val_smul_mu (γ : Q) (ζ : Mu n Ω) :
    ((Mu.val (γ • ζ) : Ωˣ) : Ω) = s γ • ((Mu.val ζ : Ωˣ) : Ω) := by
  rw [← hμQ, hs]

include hs hμQ in
/-- **The Chern cocycle is a 2-cocycle for the action of `Q` on `μ_n`.** -/
theorem isMulCocycle₂_chernMu {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) : IsMulCocycle₂ (chernMu hs hf hfix hg) := fun γ δ ε ↦ by
  refine Mu.ext (Units.ext ?_)
  simp only [Units.val_mul, val_chernMu, map_mul]
  rw [val_smul_mu hs hμQ, val_chernMu]
  exact chernVal_cond_act hs hg γ δ ε

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

/-- The Chern cocycle as a locally constant 2-cocycle for the action of `Q` on `μ_n`. -/
def chernCocyclesA {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) : ContH2.cocycles Q (Mu n Ω) :=
  ⟨chernMu hs hf hfix hg, IsLocallyConstant.desc _ (fun ζ : Mu n Ω ↦ ((Mu.val ζ : Ωˣ) : Ω))
    (isLocallyConstant_chernVal hs hstab hq hg hglc)
    (fun _ _ h ↦ Mu.ext (Units.ext h)), isMulCocycle₂_chernMu hs hμQ hf hfix hg⟩

/-- **The class of `f` in `H²(Q, μ_n)`** (`ContH2`) for a locally constant admissible `g`. -/
def chernClassOfA {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) : ContH2 Q (Mu n Ω) :=
  ContH2.mk (chernCocyclesA hs hμQ hstab hq hf hfix hg hglc)

/-- **The class does not depend on `g`.** -/
theorem chernClassOfA_eq {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g g' : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) (hg' : IsAdm ρ n s f g')
    (hglc' : IsLocallyConstant g') :
    chernClassOfA hs hμQ hstab hq hf hfix hg hglc =
      chernClassOfA hs hμQ hstab hq hf hfix hg' hglc' := by
  let ζ : Q → Mu n Ω := fun γ ↦ Mu.mk (Units.mk0 (g' γ / g γ) (div_ne_zero (hg'.ne γ) (hg.ne γ)))
    (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact ratio_pow hf hg hg' γ))
  have hζ : IsLocallyConstant ζ := IsLocallyConstant.desc _
    (fun ζ : Mu n Ω ↦ ((Mu.val ζ : Ωˣ) : Ω)) (hglc'.comp₂ hglc (· / ·))
    (fun _ _ h ↦ Mu.ext (Units.ext h))
  refine (ContH2.mk_eq_mk_iff _ _).2 ⟨ζ⁻¹, hζ.inv, ?_⟩
  funext ⟨γ, δ⟩
  refine Mu.ext (Units.ext ?_)
  rw [ContH2.dx_apply]
  simp only [Pi.inv_apply, Pi.div_apply, smul_inv', map_mul, map_div, map_inv, Units.val_mul,
    Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  rw [val_smul_mu hs hμQ]
  change (s γ • (g' δ / g δ))⁻¹ / (g' (γ * δ) / g (γ * δ))⁻¹ * (g' γ / g γ)⁻¹ =
    chernVal s g (γ, δ) / chernVal s g' (γ, δ)
  have := hg.ne γ
  have := hg.ne δ
  have := hg.ne (γ * δ)
  have := hg'.ne γ
  have := hg'.ne δ
  have := hg'.ne (γ * δ)
  have : s γ • g δ ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hg.ne _
  have : s γ • g' δ ≠ 0 := by rw [ne_eq, smul_eq_zero_iff_eq]; exact hg'.ne _
  simp only [chernVal, smul_div₀']
  field_simp

/-- **Replacing `f` by `f bⁿ`** (`b ∈ (Ω^{ker ρ})ˣ`) does not change the class. -/
theorem chernClassOfA_mul_pow {f b : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) (hb : IsFix ρ b) (hb0 : b ≠ 0) :
    chernClassOfA hs hμQ hstab hq (mul_ne_zero hf (pow_ne_zero n hb0))
      (hfix.mul fun σ hσ ↦ by rw [smul_pow', hb σ hσ]) (isAdm_mul_pow hg hb hb0)
      ((hglc.comp₂ (isLocallyConstant_smul hs hstab hq hb) (· * ·)).comp₂
        (IsLocallyConstant.const b) (· / ·)) =
    chernClassOfA hs hμQ hstab hq hf hfix hg hglc := by
  unfold chernClassOfA
  congr 1
  refine Subtype.ext (funext fun x ↦ ?_)
  exact Mu.ext (Units.ext (chernVal_mul_pow hs hg hb hb0 x))

/-- **The arithmetic Chern class modulo `n`** of `f`, invariant modulo `n`-th powers. -/
noncomputable def chernClassA [NeZero n] {f : Ω} (hf : KummerInv ρ n f) : ContH2 Q (Mu n Ω) :=
  chernClassOfA hs hμQ hstab hq hf.ne hf.fix (exists_isAdm hs hstab hq hf).choose_spec.1
    (exists_isAdm hs hstab hq hf).choose_spec.2

theorem chernClassOfA_eq_chernClassA [NeZero n] {f : Ω} (hf : KummerInv ρ n f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) :
    chernClassOfA hs hμQ hstab hq hf.ne hf.fix hg hglc = chernClassA hs hμQ hstab hq hf :=
  chernClassOfA_eq hs hμQ hstab hq _ _ _ _ _ _

/-- The admissible choices for `f` and `f'` multiply to one for `f f'`. -/
lemma IsAdm.mulA {f f' : Ω} {g g' : Q → Ω} (hg : IsAdm ρ n s f g) (hg' : IsAdm ρ n s f' g') :
    IsAdm ρ n s (f * f') (g * g') where
  fix γ := (hg.fix γ).mul (hg'.fix γ)
  ne γ := mul_ne_zero (hg.ne γ) (hg'.ne γ)
  eq γ := by rw [smul_mul', hg.eq γ, hg'.eq γ, Pi.mul_apply, mul_pow]; ring

/-- **Multiplicativity**: `c(f f') = c(f) c(f')`. -/
theorem chernClassA_mul [NeZero n] {f f' : Ω} (hf : KummerInv ρ n f) (hf' : KummerInv ρ n f')
    (hff' : KummerInv ρ n (f * f')) :
    chernClassA hs hμQ hstab hq hff' =
      chernClassA hs hμQ hstab hq hf * chernClassA hs hμQ hstab hq hf' := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf
  obtain ⟨g', hg', hglc'⟩ := exists_isAdm hs hstab hq hf'
  rw [← chernClassOfA_eq_chernClassA hs hμQ hstab hq hf hg hglc,
    ← chernClassOfA_eq_chernClassA hs hμQ hstab hq hf' hg' hglc',
    ← chernClassOfA_eq_chernClassA hs hμQ hstab hq hff' (hg.mulA hg') (hglc.mul hglc')]
  rw [chernClassOfA, chernClassOfA, chernClassOfA, ← map_mul]
  congr 1
  refine Subtype.ext (funext fun x ↦ Mu.ext (Units.ext ?_))
  change chernVal s (g * g') x = chernVal s g x * chernVal s g' x
  obtain ⟨γ, δ⟩ := x
  have := hg.ne (γ * δ)
  have := hg'.ne (γ * δ)
  simp only [chernVal, Pi.mul_apply, smul_mul']
  field_simp

end Topology

/-! ### Restriction (comparison with the geometric class) -/

section Restriction

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)
  {G' Q' : Type*} [Group G'] [Group Q'] [MulSemiringAction G' Ω] [TopologicalSpace G']
  [IsTopologicalGroup G'] [TopologicalSpace Q'] [IsTopologicalGroup Q']
  [MulDistribMulAction Q' (Mu n Ω)] {ρ' : G' →* Q'} {s' : Q' → G'} (hs' : ∀ γ, ρ' (s' γ) = γ)
  (hμQ' : ∀ (σ : G') (ζ : Mu n Ω), ((Mu.val (ρ' σ • ζ) : Ωˣ) : Ω) = σ • ((Mu.val ζ : Ωˣ) : Ω))
  (hstab' : ∀ x : Ω, IsOpen (MulAction.stabilizer G' x : Set G'))
  (hq' : ∀ S : Set Q', IsOpen (ρ' ⁻¹' S) → IsOpen S)

/-- **Restriction of the arithmetic Chern class.** Let `κ : G' →* G` and `ι : Q' →* Q` be
compatible (`ρ ∘ κ = ι ∘ ρ'`, `κ` compatible with the actions on `Ω` and `ι` with those on `μ_n`,
`ι` continuous) and `ker ρ' = κ⁻¹(ker ρ)` (the same universal cover). If `f` is invariant modulo
`n`-th powers for both, then `ι^* c_{ρ}(f) = c_{ρ'}(f)`. (Example: `G' = Gal(Ω/F k̄) ⊆ G`,
`Q' = Δ_X ⊆ Π_X = Q`.) -/
theorem map_chernClassA [NeZero n] (κ : G' →* G) (hκ : ∀ (σ : G') (x : Ω), κ σ • x = σ • x)
    (ι : Q' →* Q) (hι : Continuous ι) (hρ : ∀ σ, ρ (κ σ) = ι (ρ' σ))
    (hker : ∀ σ, ρ' σ = 1 ↔ ρ (κ σ) = 1)
    (hιμ : ∀ (γ : Q') (ζ : Mu n Ω), ι γ • ζ = γ • ζ) {f : Ω} (hf : KummerInv ρ n f)
    (hf' : KummerInv ρ' n f) :
    ContH2.map ι hι (MonoidHom.id (Mu n Ω)) (fun γ ζ ↦ hιμ γ ζ)
      (chernClassA hs hμQ hstab hq hf) = chernClassA hs' hμQ' hstab' hq' hf' := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf
  rw [← chernClassOfA_eq_chernClassA hs hμQ hstab hq hf hg hglc]
  -- the pulled-back choice `g ∘ ι` is admissible for `(ρ', s')`
  have hfixT : ∀ x : Ω, IsFix ρ x → IsFix ρ' x := fun x hx σ hσ ↦ by
    rw [← hκ]
    exact hx _ ((hker σ).1 hσ)
  have hsmul : ∀ (γ : Q') (x : Ω), IsFix ρ x → s' γ • x = s (ι γ) • x := fun γ x hx ↦ by
    rw [← hκ]
    exact hx.smul_eq (by rw [hρ, hs', hs])
  have hg' : IsAdm ρ' n s' f (g ∘ ι) :=
    { fix := fun γ ↦ hfixT _ (hg.fix (ι γ))
      ne := fun γ ↦ hg.ne (ι γ)
      eq := fun γ ↦ by rw [hsmul γ f hf.fix]; exact hg.eq (ι γ) }
  rw [← chernClassOfA_eq_chernClassA hs' hμQ' hstab' hq' hf' hg' (hglc.comp_continuous hι)]
  rw [chernClassOfA, chernClassOfA, ContH2.map_mk]
  congr 1
  refine Subtype.ext (funext fun ⟨γ, δ⟩ ↦ Mu.ext (Units.ext ?_))
  change chernVal s g (ι γ, ι δ) = chernVal s' (g ∘ ι) (γ, δ)
  simp only [chernVal, Function.comp_apply, map_mul, hsmul γ _ (hg.fix (ι δ))]

end Restriction

end Arith

/-! ### `H2lc` (pi1) and `ContH2` (local-class-field-theory) -/

section Compare

variable {A M : Type*} [Group A] [TopologicalSpace A] [CommGroup M] [MulDistribMulAction A M]

/-- The two models of `H²` with locally constant cochains agree: the identity on cocycles
induces `H2lc A M →* ContH2 A M` (pi1's `H2lc` vs `local-class-field-theory`'s `ContH2`). -/
def h2lcToContH2 : H2lc A M →* ContH2 A M :=
  QuotientGroup.map _ _
    { toFun := fun c ↦ ⟨c.1, c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
    (by
      rintro c ⟨x, hx, hxc⟩
      exact ⟨x, hx, hxc⟩)

@[simp] theorem h2lcToContH2_mk (c : H2lc.cocycles A M) :
    h2lcToContH2 (QuotientGroup.mk c : H2lc A M) = ContH2.mk ⟨c.1, c.2⟩ := rfl

end Compare

section Trivial

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  {ρ : G →* Q} {n : ℕ} {s : Q → G} (hs : ∀ γ, ρ (s γ) = γ)
  (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

attribute [local instance] Pi1.SurfaceGroup.trivialAction in
/-- **Comparison with the geometric class of `ChernClass.lean`**: for the trivial action on
`μ_n` (the geometric case `k = k̄`), the class of `f` in `ContH2` is the image of MR5's
`chernClass` (in pi1's `H2lc`). -/
theorem h2lcToContH2_chernClass [NeZero n] {f : Ω} (hf : KummerInv ρ n f) :
    h2lcToContH2 (chernClass hs hμ hstab hq hf) =
      chernClassA hs (fun σ ζ ↦ (hμ σ _ (by
        rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one])).symm) hstab hq hf := rfl

end Trivial

end CurvesJacobian.ChernClass
