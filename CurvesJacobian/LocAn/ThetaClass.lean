/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.EigenH2

/-!
# The Heisenberg (theta) class of a bilinear form on `T ⋊ G` (MR7 Route T′, model for `c(L)`)

Route T′ of the MR7 plan (`MR7-plan.md` §3.3, research note R-D3, review 2026-10-18) uses the
class `c(L) ∈ H²(T ⋊ Γ_K, μ_{pⁿ})` of a symmetric ample line bundle `L` on the Jacobian
(`T = T_p J`): `[-1]^* c(L) = c(L)`, `ε^* c(L) = 0`, and `c(L)|_T` is the commutator form
`e^{φ_L}` (theta group, [EvdGM] (11.20)). This file gives the **explicit group-theoretic model**
of such a class, so that the geometric input of T′ can be stated as an identity with an explicit
class (JAC D-d, `JAC-plan.md`).

Setting (as in `EigenH2`): `π : E →* G` split by `ε`, `T = ker π` abelian, `E` acting on `M`
through `π`, `ι : E →* E` with `ι ∘ ε = ε` and `ι = (·)⁻¹` on `T`. A map `b : E → E → M` is
**bilinear on `T`** (`IsBilin`) and **equivariant** (`IsEquivar`:
`e • b(t, s) = b(e t e⁻¹, e s e⁻¹)`).
For `e = t ε(g)` write `t_e = t` (`tpart`) and `cnj e x = ε(π e) x ε(π e)⁻¹`. Then

  `θ_b(e, e') = b(t_e, cnj e t_{e'})`   (for `T ⋊ G`: `θ_b((t, g), (t', g')) = b(t, g t')`)

is a 2-cocycle (`isMulCocycle₂_thetaFun`): the class of the Heisenberg extension
`M ×_{θ_b} E`, whose commutator pairing on `T` is `b(t, s) / b(s, t)`.

## Main results

* `thetaCocycle`, **`thetaClass b ∈ ContH2 E M`** (locally constant cochains);
* `thetaFun_ker`: on `T × T` it is `b` itself; `thetaFun_ε`: it vanishes on `ε(G) × ε(G)`, so
  **`map_ε_thetaClass`**: `ε^* θ_b = 1`; **`map_ι_thetaClass`**: `ι^* θ_b = θ_b` (cocycle level);
* `thetaFun_mapHom` / **`map_thetaClass`**: functoriality along a morphism `Φ : E' →* E` of split
  extensions over the same `G` (e.g. `Φ = α_T ⋊ id` in step 4 of T′), and along coefficient maps
  (`thetaFun_pow`: `θ_{b^λ} = θ_b^λ`, which absorbs the scalar `λ ∈ ℤ_p^×` of T′);
* `res_thetaClass_eq_of_comm`: if squaring on `M` is bijective (e.g. `M = μ_{pⁿ}`, `p` odd), two
  bilinear forms with the same commutator pairing give the same class on `T`;
* **`eq_thetaClass`**: if `M` has odd exponent, a class `x ∈ H²(E, M)` with `ι^* x = x`,
  `ε^* x = 1` and `res_T x = res_T θ_b` **is** `θ_b` (from the eigenspace lemma
  `EigenH2.sq_eq_one`);
* `IsAlt`, `halfForm`: for an alternating equivariant `e` and odd exponent `2k + 1`, the bilinear
  form `b = e^{k+1}` has commutator pairing `e` (`halfForm_comm`).

So for `p` odd, a class `c(L)` with the three properties and `res_T c(L) = res_T θ_{b}` with
`b(t, s)/b(s, t) = e^{φ_L}(t, s)^{±2}` is `θ_{halfForm (e^{±2})}`, an explicit class depending only
on
`(T ⋊ Γ, e^{φ_L})`.
-/

open groupCohomology ContH2

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.ThetaClass

open EigenH2

variable {E G M : Type*} [Group E] [Group G] [CommGroup M] [MulDistribMulAction E M]

/-! ### Bilinear forms on `T = ker π` -/

section Algebra

variable (π : E →* G) (ε : G →* E)

/-- `b : E → E → M` is **bilinear on `T = ker π`**. -/
structure IsBilin (b : E → E → M) : Prop where
  mul_left : ∀ t t' s, π t = 1 → π t' = 1 → π s = 1 → b (t * t') s = b t s * b t' s
  mul_right : ∀ t s s', π t = 1 → π s = 1 → π s' = 1 → b t (s * s') = b t s * b t s'

/-- `b` is **equivariant**: `e • b(t, s) = b(e t e⁻¹, e s e⁻¹)` for `t, s ∈ T`. -/
def IsEquivar (b : E → E → M) : Prop :=
  ∀ e t s, π t = 1 → π s = 1 → e • b t s = b (e * t * e⁻¹) (e * s * e⁻¹)

/-- Conjugation by the `G`-part `ε(π e)` of `e`. -/
def cnj (e x : E) : E := ε (π e) * x * (ε (π e))⁻¹

/-- **The theta (Heisenberg) cochain** `θ_b(e, e') = b(t_e, cnj e t_{e'})`. -/
def thetaFun (b : E → E → M) : E × E → M :=
  fun p => b (tpart π ε p.1) (cnj π ε p.1 (tpart π ε p.2))

variable {π ε}

namespace IsBilin

variable {b : E → E → M} (hb : IsBilin π b)
include hb

theorem one_left {s : E} (hs : π s = 1) : b 1 s = 1 := by
  have h := hb.mul_left 1 1 s (map_one π) (map_one π) hs
  rw [mul_one] at h
  exact (mul_eq_left.1 h.symm)

theorem one_right {t : E} (ht : π t = 1) : b t 1 = 1 := by
  have h := hb.mul_right t 1 1 ht (map_one π) (map_one π)
  rw [mul_one] at h
  exact (mul_eq_left.1 h.symm)

theorem inv_left {t s : E} (ht : π t = 1) (hs : π s = 1) : b t⁻¹ s = (b t s)⁻¹ := by
  have h := hb.mul_left t⁻¹ t s (by rw [map_inv, ht, inv_one]) ht hs
  rw [inv_mul_cancel, hb.one_left hs] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem inv_right {t s : E} (ht : π t = 1) (hs : π s = 1) : b t s⁻¹ = (b t s)⁻¹ := by
  have h := hb.mul_right t s⁻¹ s ht (by rw [map_inv, hs, inv_one]) hs
  rw [inv_mul_cancel, hb.one_right ht] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem inv_inv {t s : E} (ht : π t = 1) (hs : π s = 1) : b t⁻¹ s⁻¹ = b t s := by
  rw [hb.inv_left ht (by rw [map_inv, hs, inv_one]), hb.inv_right ht hs, _root_.inv_inv]

end IsBilin

theorem π_cnj (hπε : ∀ g, π (ε g) = g) (e x : E) : π (cnj π ε e x) = π e * π x * (π e)⁻¹ := by
  simp [cnj, hπε]

theorem π_cnj_of_ker (hπε : ∀ g, π (ε g) = g) (e : E) {x : E} (hx : π x = 1) :
    π (cnj π ε e x) = 1 := by
  rw [π_cnj hπε, hx, mul_one, mul_inv_cancel]

theorem cnj_mul (e x y : E) : cnj π ε e (x * y) = cnj π ε e x * cnj π ε e y := by
  simp only [cnj]
  group

theorem cnj_mul_left (e e' x : E) : cnj π ε (e * e') x = cnj π ε e (cnj π ε e' x) := by
  simp only [cnj, map_mul]
  group

theorem cnj_inv (e x : E) : cnj π ε e x⁻¹ = (cnj π ε e x)⁻¹ := by
  simp only [cnj]
  group

/-- On an abelian `T`, conjugation by `e` is conjugation by its `G`-part. -/
theorem conj_eq_cnj (hπε : ∀ g, π (ε g) = g) (hab : ∀ a b : E, π a = 1 → π b = 1 → a * b = b * a)
    (e : E) {x : E} (hx : π x = 1) : e * x * e⁻¹ = cnj π ε e x := by
  have h1 := π_tpart hπε e
  have h2 := π_cnj_of_ker hπε e hx
  conv_lhs => rw [← tpart_mul_ε (π := π) (ε := ε) e]
  have : tpart π ε e * ε (π e) * x * (tpart π ε e * ε (π e))⁻¹ =
      tpart π ε e * cnj π ε e x * (tpart π ε e)⁻¹ := by
    simp only [cnj]
    group
  rw [this, hab _ _ h1 h2]
  group

/-- **`θ_b` is a 2-cocycle.** -/
theorem isMulCocycle₂_thetaFun (hπε : ∀ g, π (ε g) = g)
    (hab : ∀ a b : E, π a = 1 → π b = 1 → a * b = b * a) {b : E → E → M} (hb : IsBilin π b)
    (hequiv : IsEquivar π b) : IsMulCocycle₂ (thetaFun π ε b) := by
  intro e e' e''
  simp only [thetaFun]
  have ht := π_tpart hπε e
  have ht' := π_tpart hπε e'
  have ht'' := π_tpart hπε e''
  have hc := π_cnj_of_ker hπε e ht'
  have hc' := π_cnj_of_ker hπε e' ht''
  have hcc := π_cnj_of_ker hπε e hc'
  rw [tpart_mul (π := π) (ε := ε) e e', tpart_mul (π := π) (ε := ε) e' e'',
    hequiv e _ _ ht' hc', conj_eq_cnj hπε hab e ht', conj_eq_cnj hπε hab e hc',
    cnj_mul_left]
  change b (tpart π ε e * cnj π ε e (tpart π ε e')) _ * _ =
    _ * b (tpart π ε e) (cnj π ε e (tpart π ε e' * cnj π ε e' (tpart π ε e'')))
  rw [hb.mul_left _ _ _ ht hc hcc, cnj_mul, hb.mul_right _ _ _ ht hc hcc]
  mul_abel

/-- On `T × T`, `θ_b = b`. -/
theorem thetaFun_ker (b : E → E → M) {t s : E} (ht : π t = 1)
    (hs : π s = 1) : thetaFun π ε b (t, s) = b t s := by
  simp [thetaFun, cnj, tpart_of_ker ht, tpart_of_ker hs, ht]

/-- On `ε(G) × ε(G)`, `θ_b = 1`. -/
theorem thetaFun_ε (hπε : ∀ g, π (ε g) = g) {b : E → E → M} (hb : IsBilin π b) (g g' : G) :
    thetaFun π ε b (ε g, ε g') = 1 := by
  simp only [thetaFun]
  rw [tpart_ε hπε g]
  exact hb.one_left (π_cnj_of_ker hπε _ (π_tpart hπε _))

/-- `π ∘ ι = π` for an endomorphism `ι` over `G` which inverts `T`. -/
theorem π_ι (hπε : ∀ g, π (ε g) = g) (ι : E →* E) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (e : E) : π (ι e) = π e := by
  conv_lhs => rw [← tpart_mul_ε (π := π) (ε := ε) e]
  rw [map_mul, hιε, hιT _ (π_tpart hπε e), map_mul, map_inv, π_tpart hπε e, hπε, inv_one,
    one_mul]

theorem tpart_ι (hπε : ∀ g, π (ε g) = g) (ι : E →* E) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (e : E) : tpart π ε (ι e) = (tpart π ε e)⁻¹ := by
  have h := π_ι hπε ι hιε hιT e
  conv_lhs => rw [← tpart_mul_ε (π := π) (ε := ε) e]
  rw [map_mul, hιε, hιT _ (π_tpart hπε e), tpart, map_mul, hπε, map_inv, π_tpart hπε e, inv_one,
    one_mul]
  group

/-- `ι^* θ_b = θ_b` on cochains. -/
theorem thetaFun_ι (hπε : ∀ g, π (ε g) = g) {b : E → E → M} (hb : IsBilin π b) (ι : E →* E)
    (hιε : ∀ g, ι (ε g) = ε g) (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (e e' : E) :
    thetaFun π ε b (ι e, ι e') = thetaFun π ε b (e, e') := by
  simp only [thetaFun]
  rw [tpart_ι hπε ι hιε hιT, tpart_ι hπε ι hιε hιT, cnj, π_ι hπε ι hιε hιT, ← cnj, cnj_inv,
    hb.inv_inv (π_tpart hπε e) (π_cnj_of_ker hπε e (π_tpart hπε e'))]

/-- Functoriality of `θ_b` along a morphism `Φ` of split extensions over the same `G`. -/
theorem thetaFun_mapHom {E' : Type*} [Group E'] {π' : E' →* G} {ε' : G →* E'} (Φ : E' →* E)
    (hπ : ∀ e, π (Φ e) = π' e) (hε : ∀ g, Φ (ε' g) = ε g) (b : E → E → M) (e e' : E') :
    thetaFun π ε b (Φ e, Φ e') =
      thetaFun π' ε' (fun t s => b (Φ t) (Φ s)) (e, e') := by
  have htp : ∀ x, tpart π ε (Φ x) = Φ (tpart π' ε' x) := fun x => by
    simp [tpart, hπ, hε]
  simp only [thetaFun, htp, cnj, hπ, map_mul, map_inv, hε]

/-- `θ_{ψ ∘ b} = ψ ∘ θ_b`. -/
theorem thetaFun_comp {M' : Type*} [CommGroup M'] (ψ : M →* M') (b : E → E → M) (p : E × E) :
    thetaFun π ε (fun t s => ψ (b t s)) p = ψ (thetaFun π ε b p) := rfl

/-- `θ_{b^λ} = θ_b^λ`. -/
theorem thetaFun_pow (b : E → E → M) (m : ℕ) (p : E × E) :
    thetaFun π ε (fun t s => b t s ^ m) p = thetaFun π ε b p ^ m := rfl

theorem IsBilin.pow {b : E → E → M} (hb : IsBilin π b) (m : ℕ) :
    IsBilin π (fun t s => b t s ^ m) :=
  ⟨fun t t' s ht ht' hs => by simp only [hb.mul_left t t' s ht ht' hs, mul_pow],
    fun t s s' ht hs hs' => by simp only [hb.mul_right t s s' ht hs hs', mul_pow]⟩

theorem IsEquivar.pow {b : E → E → M} (hb : IsEquivar π b) (m : ℕ) :
    IsEquivar π (fun t s => b t s ^ m) :=
  fun e t s ht hs => by simp only [smul_pow', hb e t s ht hs]

end Algebra

/-! ### Alternating forms and halves -/

section Half

variable {π : E →* G}

/-- `e` is **alternating** on `T`: `e(t, t) = 1`. -/
def IsAlt (π : E →* G) (e : E → E → M) : Prop := ∀ t, π t = 1 → e t t = 1

theorem IsAlt.swap {e : E → E → M} (he : IsBilin π e) (ha : IsAlt π e) {t s : E} (ht : π t = 1)
    (hs : π s = 1) : e s t = (e t s)⁻¹ := by
  have h := ha (t * s) (by rw [map_mul, ht, hs, one_mul])
  rw [he.mul_left _ _ _ ht hs (by rw [map_mul, ht, hs, one_mul]), he.mul_right _ _ _ ht ht hs,
    he.mul_right _ _ _ hs ht hs, ha t ht, ha s hs, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **Half of an alternating form**: for exponent `2k + 1`, `b = e^{k+1}`. -/
def halfForm (e : E → E → M) (k : ℕ) : E → E → M := fun t s => e t s ^ (k + 1)

/-- The commutator pairing of `halfForm e k` is `e`. -/
theorem halfForm_comm {e : E → E → M} (he : IsBilin π e) (ha : IsAlt π e) {k : ℕ}
    (hexp : ∀ m : M, m ^ (2 * k + 1) = 1) {t s : E} (ht : π t = 1) (hs : π s = 1) :
    halfForm e k t s / halfForm e k s t = e t s := by
  simp only [halfForm]
  rw [IsAlt.swap he ha ht hs, inv_pow, div_inv_eq_mul, ← pow_add]
  rw [show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hexp, one_mul]

end Half

/-! ### The class in `ContH2` -/

theorem mk_eq_one_of_eq_one {A : Type*} [Group A] [TopologicalSpace A] [MulDistribMulAction A M]
    {c : cocycles A M} (h : ∀ p, c p = 1) : mk c = 1 :=
  (mk_eq_one_iff c).2 ⟨1, IsLocallyConstant.const 1, by
    funext p
    rw [h p, ContH2.dx_one]
    rfl⟩

section Class

variable [TopologicalSpace E] [IsTopologicalGroup E] [TopologicalSpace G]
  {π : E →* G} {ε : G →* E}

theorem continuous_cnj (hπ : Continuous π) (hε : Continuous ε) :
    Continuous fun p : E × E => cnj π ε p.1 p.2 := by
  simp only [cnj]
  have h : Continuous fun p : E × E => ε (π p.1) :=
    hε.comp (hπ.comp (continuous_fst : Continuous (Prod.fst : E × E → E)))
  exact (h.mul (continuous_snd : Continuous (Prod.snd : E × E → E))).mul h.inv

theorem isLocallyConstant_thetaFun (hπ : Continuous π) (hε : Continuous ε) {b : E → E → M}
    (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) :
    IsLocallyConstant (thetaFun π ε b) := by
  have h1 : Continuous fun p : E × E => tpart π ε p.1 :=
    (continuous_tpart hπ hε).comp continuous_fst
  have h2 : Continuous fun p : E × E => cnj π ε p.1 (tpart π ε p.2) :=
    (continuous_cnj hπ hε).comp
      (continuous_fst.prodMk ((continuous_tpart hπ hε).comp continuous_snd))
  exact hlc.comp_continuous (h1.prodMk h2)

/-- **The theta cocycle** of a bilinear equivariant locally constant `b`. -/
def thetaCocycle (hπ : Continuous π) (hε : Continuous ε) (hπε : ∀ g, π (ε g) = g)
    (hab : ∀ a b : E, π a = 1 → π b = 1 → a * b = b * a) {b : E → E → M} (hb : IsBilin π b)
    (hequiv : IsEquivar π b) (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) :
    cocycles E M :=
  ⟨thetaFun π ε b, isLocallyConstant_thetaFun hπ hε hlc,
    isMulCocycle₂_thetaFun hπε hab hb hequiv⟩

/-- **The theta class** `θ_b ∈ H²(E, M)`. -/
def thetaClass (hπ : Continuous π) (hε : Continuous ε) (hπε : ∀ g, π (ε g) = g)
    (hab : ∀ a b : E, π a = 1 → π b = 1 → a * b = b * a) {b : E → E → M} (hb : IsBilin π b)
    (hequiv : IsEquivar π b) (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) :
    ContH2 E M :=
  mk (thetaCocycle hπ hε hπε hab hb hequiv hlc)

variable (hπ : Continuous π) (hε : Continuous ε) (hπε : ∀ g, π (ε g) = g)
  (hab : ∀ a b : E, π a = 1 → π b = 1 → a * b = b * a)

/-- **`ε^* θ_b = 1`.** -/
theorem map_ε_thetaClass [MulDistribMulAction G M] (hact : ∀ (e : E) (m : M), e • m = π e • m)
    {b : E → E → M} (hb : IsBilin π b) (hequiv : IsEquivar π b)
    (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) :
    ContH2.map ε hε (MonoidHom.id M)
      (fun g m => by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact, hπε])
      (thetaClass hπ hε hπε hab hb hequiv hlc) = 1 := by
  rw [thetaClass, map_mk]
  exact mk_eq_one_of_eq_one fun ⟨g, g'⟩ => thetaFun_ε hπε hb g g'

/-- **`ι^* θ_b = θ_b`.** -/
theorem map_ι_thetaClass [MulDistribMulAction G M] (hact : ∀ (e : E) (m : M), e • m = π e • m)
    (ι : E →* E) (hι : Continuous ι) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹) {b : E → E → M} (hb : IsBilin π b)
    (hequiv : IsEquivar π b) (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) :
    ContH2.map ι hι (MonoidHom.id M)
      (fun e m => smul_ι hπε (fun e he m => by rw [hact, he, one_smul]) ι hιε hιT e m)
      (thetaClass hπ hε hπε hab hb hequiv hlc) = thetaClass hπ hε hπε hab hb hequiv hlc := by
  rw [thetaClass, map_mk]
  congr 1
  ext p
  exact thetaFun_ι hπε hb ι hιε hιT p.1 p.2

/-- The restriction of `θ_b` to `T` is the class of `b` itself. -/
theorem res_thetaClass {b : E → E → M} (hb : IsBilin π b) (hequiv : IsEquivar π b)
    (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) (t s : π.ker) :
    (cocyclesMap π.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl)
      (thetaCocycle hπ hε hπε hab hb hequiv hlc)) (t, s) = b t s :=
  thetaFun_ker b t.2 s.2

/-- **Functoriality**: for a morphism `Φ : E' →* E` of split extensions over the same `G`
(`π ∘ Φ = π'`, `Φ ∘ ε' = ε`), `Φ^* θ_b = θ_{b ∘ (Φ × Φ)}`. -/
theorem map_thetaClass {E' : Type*} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E']
    [MulDistribMulAction E' M] {π' : E' →* G} {ε' : G →* E'} (hπ' : Continuous π')
    (hε' : Continuous ε') (hπε' : ∀ g, π' (ε' g) = g)
    (hab' : ∀ a b : E', π' a = 1 → π' b = 1 → a * b = b * a) (Φ : E' →* E) (hΦ : Continuous Φ)
    (hΦπ : ∀ e, π (Φ e) = π' e) (hΦε : ∀ g, Φ (ε' g) = ε g)
    (hsmul : ∀ (e : E') (m : M), Φ e • m = e • m)
    {b : E → E → M} (hb : IsBilin π b) (hequiv : IsEquivar π b)
    (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2)
    (hb' : IsBilin π' fun t s => b (Φ t) (Φ s)) (hequiv' : IsEquivar π' fun t s => b (Φ t) (Φ s))
    (hlc' : IsLocallyConstant fun p : E' × E' => b (Φ p.1) (Φ p.2)) :
    ContH2.map Φ hΦ (MonoidHom.id M) (fun e m => hsmul e m)
      (thetaClass hπ hε hπε hab hb hequiv hlc) =
      thetaClass hπ' hε' hπε' hab' hb' hequiv' hlc' := by
  rw [thetaClass, map_mk]
  congr 1
  ext p
  exact thetaFun_mapHom Φ hΦπ hΦε b p.1 p.2

/-- **Bilinear forms with the same commutator pairing give the same class on `T`** if squaring
on `M` is bijective: the quotient `β = b / b'` is symmetric bilinear and
`β = d(t ↦ √β(t, t)⁻¹)` on `T`. -/
theorem res_thetaClass_eq_of_comm [MulDistribMulAction G M]
    (hact : ∀ (e : E) (m : M), e • m = π e • m) (hsq : Function.Bijective fun m : M => m ^ 2)
    {b b' : E → E → M} (hb : IsBilin π b) (hequiv : IsEquivar π b)
    (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2) (hb' : IsBilin π b')
    (hequiv' : IsEquivar π b') (hlc' : IsLocallyConstant fun p : E × E => b' p.1 p.2)
    (hcomm : ∀ t s, π t = 1 → π s = 1 → b t s / b s t = b' t s / b' s t) :
    ContH2.map π.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl)
      (thetaClass hπ hε hπε hab hb hequiv hlc) =
    ContH2.map π.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl)
      (thetaClass hπ hε hπε hab hb' hequiv' hlc') := by
  have htriv : ∀ (t : π.ker) (m : M), t • m = m := fun t m => by
    change (t : E) • m = m
    rw [hact, t.2, one_smul]
  set β : E → E → M := fun t s => b t s / b' t s with hβ
  have hβsymm : ∀ t s, π t = 1 → π s = 1 → β t s = β s t := fun t s ht hs => by
    have h := hcomm t s ht hs
    simp only [hβ]
    calc b t s / b' t s = (b t s / b s t) * b s t / b' t s := by mul_abel
      _ = (b' t s / b' s t) * b s t / b' t s := by rw [h]
      _ = b s t / b' s t := by mul_abel
  have hβdiag : ∀ t s, π t = 1 → π s = 1 → β (t * s) (t * s) = β t t * β s s * β t s ^ 2 :=
    fun t s ht hs => by
      have hts : π (t * s) = 1 := by rw [map_mul, ht, hs, one_mul]
      simp only [hβ]
      rw [hb.mul_left _ _ _ ht hs hts, hb.mul_right _ _ _ ht ht hs, hb.mul_right _ _ _ hs ht hs,
        hb'.mul_left _ _ _ ht hs hts, hb'.mul_right _ _ _ ht ht hs, hb'.mul_right _ _ _ hs ht hs]
      have h := hβsymm s t hs ht
      simp only [hβ] at h
      rw [sq]
      calc b t t * b t s * (b s t * b s s) / (b' t t * b' t s * (b' s t * b' s s))
          = b t t / b' t t * (b s s / b' s s) * (b t s / b' t s) * (b s t / b' s t) := by
            mul_abel
        _ = _ := by rw [← h]; exact mul_assoc _ _ _
  let r : M → M := Function.surjInv hsq.2
  have hr : ∀ m, r m ^ 2 = m := Function.surjInv_eq hsq.2
  have hrmul : ∀ t s, π t = 1 → π s = 1 → r (β (t * s) (t * s)) = r (β t t) * r (β s s) * β t s :=
    fun t s ht hs => hsq.1 (by
      change r (β (t * s) (t * s)) ^ 2 = (r (β t t) * r (β s s) * β t s) ^ 2
      rw [hr, mul_pow, mul_pow, hr, hr, hβdiag t s ht hs])
  have hdiag : IsLocallyConstant fun t : E => β t t := by
    have h1 : IsLocallyConstant fun t : E => b t t :=
      hlc.comp_continuous (continuous_id.prodMk continuous_id)
    have h2 : IsLocallyConstant fun t : E => b' t t :=
      hlc'.comp_continuous (continuous_id.prodMk continuous_id)
    exact h1.div h2
  rw [thetaClass, thetaClass, map_mk, map_mk, mk_eq_mk_iff]
  refine ⟨fun t : π.ker => (r (β t t))⁻¹,
    ((hdiag.comp_continuous continuous_subtype_val).comp r).inv, ?_⟩
  funext ⟨t, s⟩
  rw [dx_apply, htriv, Pi.div_apply, res_thetaClass, res_thetaClass]
  change (r (β s s))⁻¹ / (r (β (t * s : E) (t * s)))⁻¹ * (r (β t t))⁻¹ = β t s
  rw [hrmul t s t.2 s.2]
  mul_abel

/-- **Uniqueness of the theta class** (odd exponent): a class `x ∈ H²(E, M)` with `ι^* x = x`,
`ε^* x = 1` and the same restriction to `T` as `θ_b` is `θ_b`. With
`res_thetaClass_eq_of_comm`, `θ_b` is determined by `ι`, `ε` and the commutator pairing of `b`.
(The eigenspace lemma `EigenH2.sq_eq_one` gives `(x / θ_b)² = 1`.) -/
theorem eq_thetaClass [MulDistribMulAction G M] (hact : ∀ (e : E) (m : M), e • m = π e • m)
    {k : ℕ} (hexp : ∀ m : M, m ^ (2 * k + 1) = 1)
    (ι : E →* E) (hι : Continuous ι) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹) {b : E → E → M} (hb : IsBilin π b)
    (hequiv : IsEquivar π b) (hlc : IsLocallyConstant fun p : E × E => b p.1 p.2)
    (x : ContH2 E M)
    (hT : ContH2.map π.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl) x =
      ContH2.map π.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl)
        (thetaClass hπ hε hπε hab hb hequiv hlc))
    (hG : ContH2.map ε hε (MonoidHom.id M)
      (fun g m => by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact, hπε]) x = 1)
    (hI : ContH2.map ι hι (MonoidHom.id M)
      (fun e m => smul_ι hπε (fun e he m => by rw [hact, he, one_smul]) ι hιε hιT e m) x = x) :
    x = thetaClass hπ hε hπε hab hb hequiv hlc := by
  set θ := thetaClass hπ hε hπε hab hb hequiv hlc
  have hsq := sq_eq_one hπ hε hπε hact ι hι hιε hιT (x / θ)
    (by rw [map_div, hT, div_self'])
    (by rw [map_div, hG, map_ε_thetaClass hπ hε hπε hab hact hb hequiv hlc, div_one])
    (by rw [map_div, hI, map_ι_thetaClass hπ hε hπε hab hact ι hι hιε hιT hb hequiv hlc])
  have hN : (x / θ) ^ (2 * k + 1) = 1 := by
    induction (x / θ) using ContH2.induction_on with
    | h c =>
      rw [← map_pow]
      exact mk_eq_one_of_eq_one fun p => by
        change (c : E × E → M) p ^ (2 * k + 1) = 1
        exact hexp _
  have h1 : x / θ = 1 := by
    rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at hN
    exact hN
  exact div_eq_one.1 h1

end Class

end CurvesJacobian.LocAn.ThetaClass
