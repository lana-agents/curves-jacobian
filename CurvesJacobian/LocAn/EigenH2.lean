/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ContH2

/-!
# The eigenspace lemma for `T ⋊ G` with the inversion (MR7 Route T′, step 3)

Route T′ of the MR7 plan (`MR7-plan.md` §3.3, research note R-D3 step 3, reviewed 2026-10-18)
replaces [TopSurr] Cor. 4.10 (moduli of abelian varieties, `Sp(2g, ℤ)`, congruence subgroups,
étale Leray–Serre) by the following purely group-cohomological statement.

> **Eigenspace lemma.** Let `E = T ⋊ G` (`T` normal, `π : E → G` split by `ε`), let `M` be an
> `E`-module on which `T` acts trivially, and let `ι : E → E` be an automorphism over `G` with
> `ι ∘ ε = ε` and `ι(t) = t⁻¹` on `T`. If `c ∈ H²(E, M)` satisfies `res_T c = 0`, `ε^* c = 0` and
> `ι^* c = c`, then `2c = 0`.

The plan's proof uses the Hochschild–Serre filtration (`H²₁ = ker res_T → E₂^{1,1}`, on which `ι`
acts by `−1`). Here the argument is carried out directly on cochains, which needs neither the
spectral sequence nor finiteness of `H¹`, and works for any topological group `E` and any
`E`-module `M` (locally constant cochains, `ContH2` of `local-class-field-theory`):

1. (*normalisation*) `c` is cohomologous to a cocycle `c₀` with `c₀ = 1` on `T × T` and on
   `ε(G) × ε(G)` (`exists_isNorm`);
2. for a normalised cocycle, `X(c₀)(g, t) = c₀(u, t) / c₀(u t u⁻¹, u)` (`u = ε g`) is a
   homomorphism in `t ∈ T` (`X_mul`); it is the image of `c₀` in `E₂^{1,1} = H¹(G, Hom(T, M))`;
3. if `X(c₀)(g, t) = u • h(t) / h(u t u⁻¹)` for a homomorphism `h` on `T` (a coboundary in
   `H¹(G, Hom(T, M))`), then `c₀` is a coboundary (`exists_dx_eq_of_X_eq_coboundary`); the
   section `t u ↦ (c₀(t, u), t u)` of the extension is then a homomorphism;
4. `X(ι^* c₀)(g, t) = X(c₀)(g, t⁻¹) = X(c₀)(g, t)⁻¹`, and `ι^* c₀ = c₀ · dγ` gives
   `X(c₀)² = ` a coboundary, so `c₀²` is a coboundary.

## Main results

* `CurvesJacobian.LocAn.EigenH2.exists_dx_eq_sq`: the cochain version;
* **`CurvesJacobian.LocAn.EigenH2.sq_eq_one`**: the eigenspace lemma in `ContH2 E M`.

For `E = T_pJ ⋊ Γ_K` and `M = μ_{pⁿ}` this is step 3 of Route T′ at finite level `n`: a class
`c = Φ^* c(L₂) − λ c(L₁)` with `c|_T = 0`, `ε^* c = 0`, `[−1]^* c = c` is `2`-torsion; for `p` odd
it vanishes.
-/

open groupCohomology ContH2

namespace CurvesJacobian.LocAn.EigenH2

variable {E G M : Type*} [Group E] [Group G] [CommGroup M] [MulDistribMulAction E M]

/-! ### The decomposition `e = t u` -/

section Decomposition

variable (π : E →* G) (ε : G →* E)

/-- The `T`-part `e ε(π e)⁻¹` of `e = t · ε(π e)`. -/
def tpart (e : E) : E := e * (ε (π e))⁻¹

variable {π ε}

theorem π_tpart (hπε : ∀ g, π (ε g) = g) (e : E) : π (tpart π ε e) = 1 := by
  simp [tpart, hπε]

theorem tpart_mul_ε (e : E) : tpart π ε e * ε (π e) = e := by
  simp [tpart]

theorem tpart_of_ker {e : E} (he : π e = 1) : tpart π ε e = e := by
  simp [tpart, he]

theorem tpart_ε (hπε : ∀ g, π (ε g) = g) (g : G) : tpart π ε (ε g) = 1 := by
  simp [tpart, hπε]

theorem tpart_mul (e e' : E) :
    tpart π ε (e * e') = tpart π ε e * (ε (π e) * tpart π ε e' * (ε (π e))⁻¹) := by
  simp only [tpart, map_mul, mul_inv_rev]
  group

theorem continuous_tpart [TopologicalSpace E] [IsTopologicalGroup E] [TopologicalSpace G]
    (hπ : Continuous π) (hε : Continuous ε) : Continuous (tpart π ε) :=
  continuous_id.mul (hε.comp hπ).inv

end Decomposition

/-! ### Normalised cocycles and the map to `H¹(G, Hom(T, M))` -/

section Normalised

variable (π : E →* G) (ε : G →* E)

/-- A 2-cochain is **normalised** if it is `1` on `T × T` and on `ε(G) × ε(G)`. -/
def IsNorm (c : E × E → M) : Prop :=
  (∀ a b, π a = 1 → π b = 1 → c (a, b) = 1) ∧ ∀ g g', c (ε g, ε g') = 1

/-- `X(c)(g, t) = c(u, t) / c(u t u⁻¹, u)` for `u = ε g`: in the extension defined by `c`,
`s(u) s(t) s(u)⁻¹ = X(c)(g, t) · s(u t u⁻¹)`. -/
def X (c : E × E → M) (g : G) (t : E) : M := c (ε g, t) / c (ε g * t * (ε g)⁻¹, ε g)

variable {π ε}

omit [MulDistribMulAction E M] in
theorem X_mul_fun (c c' : E × E → M) (g : G) (t : E) :
    X ε (c * c') g t = X ε c g t * X ε c' g t := by
  simp only [X, Pi.mul_apply]
  mul_abel

omit [MulDistribMulAction E M] in
theorem X_div_fun (c c' : E × E → M) (g : G) (t : E) :
    X ε (c / c') g t = X ε c g t / X ε c' g t := by
  simp only [X, Pi.div_apply]
  mul_abel

omit [MulDistribMulAction E M] in
theorem X_pow_two (c : E × E → M) (g : G) (t : E) :
    X ε (fun p => c p ^ 2) g t = X ε c g t ^ 2 := by
  simp only [X, div_pow]

theorem conj_mem_ker (hπε : ∀ g, π (ε g) = g) (g : G) {t : E} (ht : π t = 1) :
    π (ε g * t * (ε g)⁻¹) = 1 := by
  simp [ht, hπε]

/-- **`X` of a coboundary** only sees the cochain on `T`: `X(dγ)(g, t) = u • γ(t) / γ(u t u⁻¹)`. -/
theorem X_dx (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m) (γ : E → M)
    (g : G) {t : E} (ht : π t = 1) :
    X ε (dx E M γ) g t = ε g • γ t / γ (ε g * t * (ε g)⁻¹) := by
  simp only [X, dx_apply]
  rw [htriv _ (conj_mem_ker hπε g ht), show ε g * t * (ε g)⁻¹ * ε g = ε g * t by group]
  mul_abel

variable {c : E × E → M}

omit [MulDistribMulAction E M] in
theorem IsNorm.one_one (hN : IsNorm π ε c) : c (1, 1) = 1 :=
  hN.1 1 1 (map_one π) (map_one π)

theorem IsNorm.one_left (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (e : E) : c (1, e) = 1 := by
  rw [map_one_fst_of_isMulCocycle₂ hc, hN.one_one]

theorem IsNorm.one_right (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (e : E) : c (e, 1) = 1 := by
  rw [map_one_snd_of_isMulCocycle₂ hc, hN.one_one, smul_one]

/-- **`X(c)(g, ·)` is a homomorphism on `T`** for a normalised cocycle. -/
theorem X_mul (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (g : G) {t t' : E} (ht : π t = 1)
    (ht' : π t' = 1) : X ε c g (t * t') = X ε c g t * X ε c g t' := by
  simp only [X]
  set u := ε g
  set w := u * t * u⁻¹
  set w' := u * t' * u⁻¹
  have hw : π w = 1 := conj_mem_ker hπε g ht
  have hw' : π w' = 1 := conj_mem_ker hπε g ht'
  have h1 := hc u t t'
  rw [hN.1 t t' ht ht', smul_one, one_mul] at h1
  have h2 := hc w u t'
  rw [htriv w hw, show w * u = u * t by simp only [w]; group] at h2
  have h3 := hc w w' u
  rw [hN.1 w w' hw hw', mul_one, htriv w hw, show w' * u = u * t' by simp only [w']; group,
    show w * w' = u * (t * t') * u⁻¹ by simp only [w, w']; group] at h3
  rw [← h1, h3]
  calc c (u * t, t') * c (u, t) / (c (w', u) * c (w, u * t'))
      = (c (u * t, t') * c (w, u)) * c (u, t) / (c (w', u) * c (w, u * t') * c (w, u)) := by
        mul_abel
    _ = (c (u, t') * c (w, u * t')) * c (u, t) / (c (w', u) * c (w, u * t') * c (w, u)) := by
        rw [h2]
    _ = c (u, t) / c (w, u) * (c (u, t') / c (w', u)) := by mul_abel

theorem X_one (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (g : G) : X ε c g 1 = 1 := by
  simp only [X, mul_one, mul_inv_cancel, hN.one_right hc, hN.one_left hc, div_one]

theorem X_inv (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (g : G) {t : E} (ht : π t = 1) :
    X ε c g t⁻¹ = (X ε c g t)⁻¹ := by
  have h := X_mul hπε htriv hc hN g ht (by rw [map_inv, ht, inv_one])
  rw [mul_inv_cancel, X_one hc hN] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **Splitting**: a normalised cocycle with `X = 1` is a coboundary; explicitly
`c = d(β⁻¹)` with `β(e) = c(t_e, ε(π e))` (the section `t u ↦ (β(t u), t u)` of the extension
defined by `c` is a homomorphism). -/
theorem dx_eq_of_X_eq_one (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (hc : IsMulCocycle₂ c) (hN : IsNorm π ε c) (hX : ∀ g t, π t = 1 → X ε c g t = 1)
    (e e' : E) :
    dx E M (fun e => (c (tpart π ε e, ε (π e)))⁻¹) (e, e') = c (e, e') := by
  set t := tpart π ε e
  set u := ε (π e)
  set t' := tpart π ε e'
  set u' := ε (π e')
  set w := u * t' * u⁻¹
  have ht : π t = 1 := π_tpart hπε e
  have ht' : π t' = 1 := π_tpart hπε e'
  have hw : π w = 1 := conj_mem_ker hπε _ ht'
  have he : t * u = e := tpart_mul_ε e
  have he' : t' * u' = e' := tpart_mul_ε e'
  have hee : tpart π ε (e * e') = t * w := tpart_mul e e'
  have huu : ε (π (e * e')) = u * u' := by rw [map_mul, map_mul]
  -- the four cocycle identities and `X = 1`
  have hA := hc t u (t' * u')
  rw [htriv t ht] at hA
  have hB := hc u t' u'
  have hC := hc t w (u * u')
  rw [hN.1 t w ht hw, mul_one, htriv t ht, show w * (u * u') = u * (t' * u') by
    simp only [w]; group] at hC
  have hD := hc w u u'
  rw [hN.2 _ _, smul_one, one_mul, show w * u = u * t' by simp only [w]; group] at hD
  have hXe : c (u, t') = c (w, u) := by
    have := hX (π e) t' ht'
    rwa [X, div_eq_one] at this
  have key : c (t * u, t' * u') * c (t, u) * u • c (t', u') = c (t * w, u * u') :=
    calc c (t * u, t' * u') * c (t, u) * u • c (t', u')
        = c (u, t' * u') * c (t, u * (t' * u')) * u • c (t', u') := by rw [hA]
      _ = (u • c (t', u') * c (u, t' * u')) * c (t, u * (t' * u')) := by mul_abel
      _ = (c (u * t', u') * c (u, t')) * c (t, u * (t' * u')) := by rw [hB]
      _ = (c (u * t', u') * c (w, u)) * c (t, u * (t' * u')) := by rw [hXe]
      _ = c (w, u * u') * c (t, u * (t' * u')) := by rw [hD]
      _ = c (t * w, u * u') := by rw [hC]
  rw [dx_apply, hee, huu, ← he, ← he', mul_smul, htriv t ht]
  rw [he, he'] at key ⊢
  calc u • (c (t', u'))⁻¹ / (c (t * w, u * u'))⁻¹ * (c (t, u))⁻¹
      = c (t * w, u * u') / (c (t, u) * u • c (t', u')) := by
        rw [smul_inv']
        mul_abel
    _ = c (e, e') := by
        rw [← key]
        mul_abel

end Normalised

/-! ### Normalisation and the main computation -/

section Algebra

variable {f f' : E × E → M}

theorem isMulCocycle₂_mul (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (f * f') := by
  intro a b c
  simp only [Pi.mul_apply, smul_mul']
  calc f (a * b, c) * f' (a * b, c) * (f (a, b) * f' (a, b))
      = (f (a * b, c) * f (a, b)) * (f' (a * b, c) * f' (a, b)) := by mul_abel
    _ = (a • f (b, c) * f (a, b * c)) * (a • f' (b, c) * f' (a, b * c)) := by rw [hf, hf']
    _ = _ := by mul_abel

theorem isMulCocycle₂_div (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (f / f') := by
  intro a b c
  simp only [Pi.div_apply, smul_div']
  calc f (a * b, c) / f' (a * b, c) * (f (a, b) / f' (a, b))
      = (f (a * b, c) * f (a, b)) / (f' (a * b, c) * f' (a, b)) := by mul_abel
    _ = (a • f (b, c) * f (a, b * c)) / (a • f' (b, c) * f' (a, b * c)) := by rw [hf, hf']
    _ = _ := by mul_abel

theorem dx_div' (x y : E → M) : dx E M (x / y) = dx E M x / dx E M y := by
  rw [div_eq_mul_inv, dx_mul, dx_inv, div_eq_mul_inv]

variable {π : E →* G} {ε : G →* E}

omit [MulDistribMulAction E M] in
theorem IsNorm.mul (h : IsNorm π ε f) (h' : IsNorm π ε f') : IsNorm π ε (f * f') :=
  ⟨fun a b ha hb => by simp [h.1 a b ha hb, h'.1 a b ha hb],
    fun g g' => by simp [h.2 g g', h'.2 g g']⟩

omit [MulDistribMulAction E M] in
theorem IsNorm.div (h : IsNorm π ε f) (h' : IsNorm π ε f') : IsNorm π ε (f / f') :=
  ⟨fun a b ha hb => by simp [h.1 a b ha hb, h'.1 a b ha hb],
    fun g g' => by simp [h.2 g g', h'.2 g g']⟩

/-- On `T`, the action is trivial, so `dβ(t, y) = β(y) / β(t y) · β(t)`. -/
theorem dx_apply_of_ker (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m) (β : E → M) {t : E}
    (ht : π t = 1) (y : E) : dx E M β (t, y) = β y / β (t * y) * β t := by
  rw [dx_apply, htriv t ht]

/-- An endomorphism `ι` over `G` with `ι(t) = t⁻¹` on `T` preserves the action on `M`. -/
theorem smul_ι (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (ι : E →* E) (hιε : ∀ g, ι (ε g) = ε g) (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (e : E) (m : M) :
    ι e • m = e • m := by
  have ht := π_tpart hπε e
  conv_lhs => rw [← tpart_mul_ε (π := π) (ε := ε) e]
  conv_rhs => rw [← tpart_mul_ε (π := π) (ε := ε) e]
  rw [map_mul, hιε, hιT _ ht, mul_smul, mul_smul, htriv _ (by rw [map_inv, ht, inv_one]),
    htriv _ ht]

theorem dx_comp_ι (hπε : ∀ g, π (ε g) = g) (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (ι : E →* E) (hιε : ∀ g, ι (ε g) = ε g) (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (β : E → M)
    (e e' : E) : dx E M β (ι e, ι e') = dx E M (β ∘ ι) (e, e') := by
  rw [dx_apply, dx_apply, smul_ι hπε htriv ι hιε hιT, ← map_mul]
  rfl

end Algebra

section Main

variable [TopologicalSpace E] [IsTopologicalGroup E] [TopologicalSpace G]
  {π : E →* G} {ε : G →* E}

/-- **Normalisation.** If `c` is a coboundary on `T × T` and on `ε(G) × ε(G)`, then `c / dβ` is
normalised for the locally constant `β(t u) = b(t) b'(π u) / c(1, 1)`. -/
theorem exists_isNorm (hπ : Continuous π) (hε : Continuous ε) (hπε : ∀ g, π (ε g) = g)
    {c : E × E → M} {b : E → M} (hb : IsLocallyConstant b)
    (hres : ∀ a a', π a = 1 → π a' = 1 → c (a, a') = dx E M b (a, a'))
    {b' : G → M} (hb' : IsLocallyConstant b')
    (hsec : ∀ g g', c (ε g, ε g') = ε g • b' g' / b' (g * g') * b' g) :
    ∃ β : E → M, IsLocallyConstant β ∧ IsNorm π ε (c / dx E M β) := by
  have hb1 : c (1, 1) = b 1 := by
    rw [hres 1 1 (map_one π) (map_one π), dx_apply, one_smul, mul_one]
    mul_abel
  have hb'1 : c (1, 1) = b' 1 := by
    have := hsec 1 1
    rw [map_one, one_smul, mul_one] at this
    rw [this]
    mul_abel
  set β : E → M := fun e => b (tpart π ε e) * b' (π e) / c (1, 1) with hβdef
  have hβT : ∀ a, π a = 1 → β a = b a := by
    intro a ha
    simp only [hβdef, tpart_of_ker ha, ha, ← hb'1]
    mul_abel
  have hβG : ∀ g, β (ε g) = b' g := by
    intro g
    simp only [hβdef, tpart_ε hπε, hπε, ← hb1]
    mul_abel
  refine ⟨β, ?_, ?_, ?_⟩
  · exact ((hb.comp_continuous (continuous_tpart hπ hε)).mul
      (hb'.comp_continuous hπ)).div (IsLocallyConstant.const _)
  · intro a a' ha ha'
    have haa : π (a * a') = 1 := by rw [map_mul, ha, ha', one_mul]
    rw [Pi.div_apply, dx_apply, hβT a ha, hβT a' ha', hβT _ haa, hres a a' ha ha', dx_apply,
      div_self']
  · intro g g'
    rw [Pi.div_apply, dx_apply, ← map_mul, hβG, hβG, hβG, hsec, div_self']

/-- **The eigenspace lemma, cochain version.** Let `π : E → G` be split by `ε`, let
`T = ker π` act trivially on `M`, and let `ι : E → E` be an endomorphism with `ι ∘ ε = ε` and
`ι(t) = t⁻¹` on `T`. If the locally constant `2`-cocycle `c` is a coboundary on `T × T`
(`hres`) and on `ε(G) × ε(G)` (`hsec`), and `ι^* c = c · d b''` (`hinv`), then `c²` is the
coboundary of a locally constant cochain. -/
theorem exists_dx_eq_sq (hπ : Continuous π) (hε : Continuous ε) (hπε : ∀ g, π (ε g) = g)
    (htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m)
    (ι : E →* E) (hι : Continuous ι) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹)
    {c : E × E → M} (hc : IsMulCocycle₂ c) (hcl : IsLocallyConstant c)
    {b : E → M} (hb : IsLocallyConstant b)
    (hres : ∀ a a', π a = 1 → π a' = 1 → c (a, a') = dx E M b (a, a'))
    {b' : G → M} (hb' : IsLocallyConstant b')
    (hsec : ∀ g g', c (ε g, ε g') = ε g • b' g' / b' (g * g') * b' g)
    {b'' : E → M} (hb'' : IsLocallyConstant b'')
    (hinv : ∀ e e', c (ι e, ι e') = c (e, e') * dx E M b'' (e, e')) :
    ∃ x : E → M, IsLocallyConstant x ∧ dx E M x = fun p => c p ^ 2 := by
  obtain ⟨β, hβ, hN⟩ := exists_isNorm hπ hε hπε hb hres hb' hsec
  set c₀ := c / dx E M β with hc₀def
  have hc₀ : IsMulCocycle₂ c₀ := isMulCocycle₂_div hc (isMulCocycle₂_dx β)
  -- `ι^* c₀ = c₀ · dγ`
  set γ : E → M := β * b'' / (β ∘ ι) with hγdef
  have hιc₀ : ∀ e e', c₀ (ι e, ι e') = c₀ (e, e') * dx E M γ (e, e') := by
    intro e e'
    simp only [hc₀def, hγdef, dx_div', dx_mul, Pi.div_apply, Pi.mul_apply, hinv,
      dx_comp_ι hπε htriv ι hιε hιT]
    mul_abel
  -- `γ` is a homomorphism on `T`
  have hγT : ∀ a a', π a = 1 → π a' = 1 → γ (a * a') = γ a * γ a' := by
    intro a a' ha ha'
    have h := hιc₀ a a'
    rw [hιT a ha, hιT a' ha', hN.1 _ _ (by rw [map_inv, ha, inv_one])
      (by rw [map_inv, ha', inv_one]), hN.1 a a' ha ha', one_mul,
      dx_apply_of_ker htriv γ ha] at h
    have h' := congrArg (· * γ (a * a')) h
    simp only [one_mul] at h'
    rw [h']
    mul_abel
  -- `X(c₀)² = u • γ(t)⁻¹ / γ(u t u⁻¹)⁻¹`
  have hX2 : ∀ g t, π t = 1 →
      X ε (c₀ * c₀) g t = ε g • (γ t)⁻¹ / (γ (ε g * t * (ε g)⁻¹))⁻¹ := by
    intro g t ht
    have h1 : X ε (fun p => c₀ (ι p.1, ι p.2)) g t = X ε c₀ g t⁻¹ := by
      simp only [X, map_mul, map_inv, hιε, hιT t ht]
    have h2 : X ε (fun p => c₀ (ι p.1, ι p.2)) g t = X ε c₀ g t * X ε (dx E M γ) g t := by
      rw [← X_mul_fun]
      simp only [X, Pi.mul_apply, hιc₀]
    rw [h1, X_inv hπε htriv hc₀ hN g ht, X_dx hπε htriv γ g ht] at h2
    rw [X_mul_fun]
    have h3 := congrArg (· * X ε c₀ g t) h2
    simp only [inv_mul_cancel] at h3
    set Y := ε g • γ t / γ (ε g * t * (ε g)⁻¹)
    set Z := X ε c₀ g t
    have key : Z * Z * Y = 1 :=
      calc Z * Z * Y = Z * Y * Z := by mul_abel
        _ = 1 := h3.symm
    rw [smul_inv']
    calc Z * Z = Z * Z * Y * Y⁻¹ := by mul_abel
      _ = Y⁻¹ := by rw [key, one_mul]
      _ = _ := by simp only [Y]; mul_abel
  -- `h = γ⁻¹` is a homomorphism on `T` with `h 1 = 1`
  set h : E → M := γ⁻¹ with hhdef
  have hhT : ∀ a a', π a = 1 → π a' = 1 → h (a * a') = h a * h a' := by
    intro a a' ha ha'
    simp only [hhdef, Pi.inv_apply, hγT a a' ha ha', mul_inv]
  have hh1 : h 1 = 1 := by
    have := hhT 1 1 (map_one π) (map_one π)
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  -- `c₁ = c₀² / d(h ∘ tpart)` is normalised with `X(c₁) = 1`
  set δ : E → M := h ∘ tpart π ε with hδdef
  have hNδ : IsNorm π ε (dx E M δ) := by
    refine ⟨fun a a' ha ha' => ?_, fun g g' => ?_⟩
    · have haa : π (a * a') = 1 := by rw [map_mul, ha, ha', one_mul]
      rw [dx_apply_of_ker htriv δ ha]
      simp only [hδdef, Function.comp_apply, tpart_of_ker ha, tpart_of_ker ha',
        tpart_of_ker haa, hhT a a' ha ha']
      mul_abel
    · rw [dx_apply, ← map_mul]
      simp only [hδdef, Function.comp_apply, tpart_ε hπε, hh1, smul_one]
      mul_abel
  set c₁ := c₀ * c₀ / dx E M δ with hc₁def
  have hc₁ : IsMulCocycle₂ c₁ :=
    isMulCocycle₂_div (isMulCocycle₂_mul hc₀ hc₀) (isMulCocycle₂_dx δ)
  have hN₁ : IsNorm π ε c₁ := (hN.mul hN).div hNδ
  have hX₁ : ∀ g t, π t = 1 → X ε c₁ g t = 1 := by
    intro g t ht
    rw [hc₁def, X_div_fun, hX2 g t ht, X_dx hπε htriv δ g ht]
    simp only [hδdef, Function.comp_apply, tpart_of_ker ht,
      tpart_of_ker (conj_mem_ker hπε g ht), hhdef, Pi.inv_apply]
    exact div_self' _
  have hdx₁ := dx_eq_of_X_eq_one hπε htriv hc₁ hN₁ hX₁
  -- assemble
  set s : E → E × E := fun e => (tpart π ε e, ε (π e)) with hsdef
  have hs : Continuous s := (continuous_tpart hπ hε).prodMk (hε.comp hπ)
  have hlocdx : ∀ y : E → M, IsLocallyConstant y → IsLocallyConstant (fun e => dx E M y (s e)) := by
    intro y hy
    have : (fun e => dx E M y (s e)) =
        fun e => y (ε (π e)) / y (tpart π ε e * ε (π e)) * y (tpart π ε e) :=
      funext fun e => dx_apply_of_ker htriv y (π_tpart hπε e) _
    rw [this]
    exact ((hy.comp_continuous (hε.comp hπ)).div (hy.comp_continuous
      ((continuous_tpart hπ hε).mul (hε.comp hπ)))).mul
      (hy.comp_continuous (continuous_tpart hπ hε))
  have hcs : IsLocallyConstant (fun e => c (s e)) := hcl.comp_continuous hs
  have hγl : IsLocallyConstant γ :=
    (hβ.mul hb'').div (hβ.comp_continuous hι)
  have hδl : IsLocallyConstant δ := hγl.inv.comp_continuous (continuous_tpart hπ hε)
  have hx₁ : IsLocallyConstant (fun e => (c₁ (s e))⁻¹) := by
    have hc₀s : IsLocallyConstant (fun e => c₀ (s e)) := hcs.div (hlocdx β hβ)
    exact ((hc₀s.mul hc₀s).div (hlocdx δ hδl)).inv
  refine ⟨(fun e => (c₁ (s e))⁻¹) * δ * β * β, ((hx₁.mul hδl).mul hβ).mul hβ, ?_⟩
  funext p
  obtain ⟨e, e'⟩ := p
  rw [dx_mul, dx_mul, dx_mul]
  simp only [Pi.mul_apply]
  rw [hdx₁ e e']
  simp only [hc₁def, hc₀def, Pi.div_apply, Pi.mul_apply, sq]
  mul_abel

/-- **The eigenspace lemma** (MR7 Route T′, step 3) in `H²(E, M)` (`ContH2`, locally constant
cochains): let `π : E → G` be split by `ε`, let `E` act on `M` through `π`, and let `ι : E → E` be
an endomorphism with `ι ∘ ε = ε` and `ι(t) = t⁻¹` on `T = ker π`. If `x ∈ H²(E, M)` restricts to
`0` on `T` and along `ε`, and `ι^* x = x`, then `x² = 1` (i.e. `2x = 0`). -/
theorem sq_eq_one [MulDistribMulAction G M] (hπ : Continuous π) (hε : Continuous ε)
    (hπε : ∀ g, π (ε g) = g) (hact : ∀ (e : E) (m : M), e • m = π e • m)
    (ι : E →* E) (hι : Continuous ι) (hιε : ∀ g, ι (ε g) = ε g)
    (hιT : ∀ t, π t = 1 → ι t = t⁻¹) (x : ContH2 E M)
    (hT : ContH2.map π.ker.subtype continuous_subtype_val (MonoidHom.id M)
      (fun _ _ => rfl) x = 1)
    (hG : ContH2.map ε hε (MonoidHom.id M)
      (fun g m => by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact, hπε]) x = 1)
    (hI : ContH2.map ι hι (MonoidHom.id M)
      (fun e m => smul_ι hπε (fun e he m => by rw [hact, he, one_smul]) ι hιε hιT e m) x = x) :
    x ^ 2 = 1 := by
  have htriv : ∀ e, π e = 1 → ∀ m : M, e • m = m := fun e he m => by rw [hact, he, one_smul]
  induction x using ContH2.induction_on with
  | h c =>
  rw [ContH2.map_mk, ContH2.mk_eq_one_iff] at hT hG
  rw [ContH2.map_mk, ContH2.mk_eq_mk_iff] at hI
  obtain ⟨bT, hbT, hbTc⟩ := hT
  obtain ⟨b', hb', hb'c⟩ := hG
  obtain ⟨b'', hb'', hb''c⟩ := hI
  have hsub : Continuous (fun e : E => (⟨tpart π ε e, π_tpart hπε e⟩ : π.ker)) :=
    (continuous_tpart hπ hε).subtype_mk _
  have hres : ∀ a a', π a = 1 → π a' = 1 →
      c (a, a') = dx E M (fun e => bT ⟨tpart π ε e, π_tpart hπε e⟩) (a, a') := by
    intro a a' ha ha'
    have h := congrFun hbTc (⟨a, ha⟩, ⟨a', ha'⟩)
    rw [ContH2.cocyclesMap_apply, dx_apply] at h
    have haa : π (a * a') = 1 := by rw [map_mul, ha, ha', one_mul]
    rw [dx_apply]
    simp only [tpart_of_ker ha, tpart_of_ker ha', tpart_of_ker haa]
    exact h.symm
  have hsec : ∀ g g', c (ε g, ε g') = ε g • b' g' / b' (g * g') * b' g := by
    intro g g'
    have h := congrFun hb'c (g, g')
    rw [ContH2.cocyclesMap_apply, dx_apply, MonoidHom.id_apply] at h
    rw [hact, hπε]
    exact h.symm
  have hinv : ∀ e e', c (ι e, ι e') = c (e, e') * dx E M b'' (e, e') := by
    intro e e'
    have h := congrFun hb''c (e, e')
    rw [Pi.div_apply, ContH2.cocyclesMap_apply] at h
    rw [h, MonoidHom.id_apply]
    mul_abel
  obtain ⟨x₀, hx₀, hdx⟩ := exists_dx_eq_sq hπ hε hπε htriv ι hι hιε hιT
    (ContH2.isMulCocycle₂ c) (ContH2.isLocallyConstant c) (hbT.comp_continuous hsub) hres hb'
    hsec hb'' hinv
  rw [← map_pow, ContH2.mk_eq_one_iff]
  exact ⟨x₀, hx₀, by rw [hdx]; rfl⟩

end Main

end CurvesJacobian.LocAn.EigenH2
