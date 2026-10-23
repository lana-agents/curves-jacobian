/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NatIsoCompat
import CurvesJacobian.Kummer.PicAction

/-!
# Equivariance of the first Chern class and of `M_X/n ≅ μ_n` (S1f, generic part)

[AbsTopIII] Prop. 1.4(ii) (`Topics in Absolute Anabelian Geometry III.txt` l.1771–1802) and
[Mzk19] Prop. 1.2(ii) (`Absolute Anabelian Cuspidalizations.txt` l.363–371): the natural
isomorphism `M_X ≅ Ẑ(1)` is an isomorphism of `Π_X`-modules, `Π_X` acting on
`M_X = Hom(H²(Δ_X, Ẑ), Ẑ)` through its conjugation action on `Δ_X` and on `Ẑ(1)` through the
cyclotomic character. Both actions come from automorphisms of the Galois model, so we prove the
equivariance for an arbitrary "semilinear automorphism" of the model:

* `α : Ω ≃+* Ω` a field automorphism, `θ : G ≃* G` with `α(σ x) = θ(σ) α(x)` (conjugation by
  `α`), and `θ̄ : Q ≃ₜ* Q` with `ρ ∘ θ = θ̄ ∘ ρ`.

Results:

* `ChernClass.muMap α : μ_n ≃* μ_n` (the action of `α` on roots of unity);
* **`ChernClass.chernClass_map`** (pure group theory): `c(α f) = α_* (θ̄⁻¹)^* c(f)` for the
  Kummer-boundary class of `ChernClass.lean`;
* `TopClass.precompMX θ̄ : M_X/n ≃* M_X/n`, `φ ↦ φ ∘ θ̄^*` (the induced action on
  `M_X/n = Hom(H²(Δ_X, ℤ/n), ℤ/n)`), and **`TopClass.h2Map_precompMX_of_isTaut`**: it maps the
  tautological class to `θ̄^* t` (for `G ≃ₜ* Π̂_{g,0}`);
* curve level (`k = k̄`, Galois model `(D, eL)` as in `ChernDivisor`): `IsChernRepDiv.map`
  (`α f` represents `τ E`, `τ = α|_F` acting on divisors by `divMap`), **`c1Div_divMap`**,
  **`c1One_map`** (`(θ̄)^* c₁(pt) = α_* c₁(pt)`), and
  **`natIso_precompMX`**: `natIso (φ ∘ θ̄^*) = α · natIso φ` (from the uniqueness of `natIso`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup WeilCurves.FunctionField

noncomputable section

namespace CurvesJacobian.ChernClass

/-! ### The action of a field automorphism on `μ_n` -/

section Mu

variable {Ω : Type*} [Field Ω] (n : ℕ)

/-- **`α : Ω ≃+* Ω` acting on `μ_n(Ω)`.** -/
def muMap (α : Ω ≃+* Ω) : Mu n Ω ≃* Mu n Ω where
  toFun ζ := Mu.mk (Units.map (α : Ω →* Ω) (Mu.val ζ)) (by
    rw [← map_pow, Mu.val_pow_n, map_one])
  invFun ζ := Mu.mk (Units.map (α.symm : Ω →* Ω) (Mu.val ζ)) (by
    rw [← map_pow, Mu.val_pow_n, map_one])
  left_inv ζ := Mu.ext (Units.ext (by simp))
  right_inv ζ := Mu.ext (Units.ext (by simp))
  map_mul' ζ η := Mu.ext (Units.ext (by simp))

@[simp] lemma val_muMap (α : Ω ≃+* Ω) (ζ : Mu n Ω) :
    ((Mu.val (muMap n α ζ) : Ωˣ) : Ω) = α ((Mu.val ζ : Ωˣ) : Ω) := rfl

lemma muMap_mul (α β : Ω ≃+* Ω) (ζ : Mu n Ω) :
    muMap n (β.trans α) ζ = muMap n α (muMap n β ζ) := rfl

/-- For a Galois automorphism, `muMap` is the Galois action. -/
lemma muMap_galois {K : Type*} [Field K] [Algebra K Ω] (σ : Gal(Ω/K)) (ζ : Mu n Ω) :
    muMap n (σ : Ω ≃+* Ω) ζ = σ • ζ := rfl

end Mu

/-! ### The Chern class of `α f` (group theory) -/

section Generic

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  {ρ : G →* Q} {n : ℕ}
  (α : Ω ≃+* Ω) (θ : G ≃* G) (hθ : ∀ (σ : G) (x : Ω), α (σ • x) = θ σ • α x)

include hθ in
lemma smul_symm_apply (σ : G) (x : Ω) : θ.symm σ • x = α.symm (σ • α x) := by
  apply α.injective
  rw [hθ, MulEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

section Bar

variable {θb : Q ≃* Q} (hρθ : ∀ σ : G, ρ (θ σ) = θb (ρ σ))

include hρθ in
lemma rho_symm (σ : G) : ρ (θ.symm σ) = θb.symm (ρ σ) := by
  apply θb.injective
  rw [← hρθ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

include hθ hρθ in
lemma IsFix.map {x : Ω} (hx : IsFix ρ x) : IsFix ρ (α x) := fun σ hσ ↦ by
  have h1 : θ.symm σ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, rho_symm θ hρθ, hσ, map_one]
  have h2 := hθ (θ.symm σ) x
  rw [hx _ h1, MulEquiv.apply_symm_apply] at h2
  exact h2.symm

include hθ hρθ in
/-- **`α f` is invariant modulo `n`-th powers if `f` is.** -/
lemma KummerInv.map {f : Ω} (hf : KummerInv ρ n f) : KummerInv ρ n (α f) where
  ne := (map_ne_zero α).2 hf.ne
  fix := hf.fix.map α θ hθ hρθ
  inv σ := by
    obtain ⟨g, hg, hfg⟩ := hf.inv (θ.symm σ)
    refine ⟨α g, hg.map α θ hθ hρθ, ?_⟩
    have h2 := hθ (θ.symm σ) f
    rw [MulEquiv.apply_symm_apply, hfg, map_mul, map_pow] at h2
    exact h2.symm

variable {s : Q → G} (hs : ∀ γ, ρ (s γ) = γ)

include hθ hρθ hs in
/-- **Admissible choices for `α f`**: `γ ↦ α(g(θ̄⁻¹ γ))`. -/
lemma IsAdm.map {f : Ω} (hfix : IsFix ρ f) {g : Q → Ω} (hg : IsAdm ρ n s f g) :
    IsAdm ρ n s (α f) (fun γ ↦ α (g (θb.symm γ))) where
  fix γ := (hg.fix _).map α θ hθ hρθ
  ne γ := (map_ne_zero α).2 (hg.ne _)
  eq γ := by
    have h1 : θ.symm (s γ) • f = s (θb.symm γ) • f :=
      hfix.smul_eq (by rw [rho_symm θ hρθ, hs, hs])
    have h2 := hθ (θ.symm (s γ)) f
    rw [MulEquiv.apply_symm_apply, h1, hg.eq, map_mul, map_pow] at h2
    exact h2.symm

include hθ hρθ hs in
lemma chernVal_map {f : Ω} {g : Q → Ω} (hg : IsAdm ρ n s f g) (γ δ : Q) :
    chernVal s (fun γ ↦ α (g (θb.symm γ))) (γ, δ) =
      α (chernVal s g (θb.symm γ, θb.symm δ)) := by
  have h1 : s γ • α (g (θb.symm δ)) = α (s (θb.symm γ) • g (θb.symm δ)) := by
    have h2 := hθ (θ.symm (s γ)) (g (θb.symm δ))
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2, (hg.fix _).smul_eq (σ := θ.symm (s γ)) (τ := s (θb.symm γ))
      (by rw [rho_symm θ hρθ, hs, hs])]
  simp only [chernVal, map_mul, map_div₀, h1]

end Bar

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  {s : Q → G} (hs : ∀ γ, ρ (s γ) = γ) (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)
  (θb : Q ≃ₜ* Q) (hρθ : ∀ σ : G, ρ (θ σ) = θb (ρ σ))

/-- The trivial action of `Q` on `μ_n` (as in `ChernClass`). -/
local instance : MulDistribMulAction Q (Mu n Ω) := Pi1.SurfaceGroup.trivialAction Q (Mu n Ω)

/-- `θ̄^*` on `H²(Q, μ_n)` (trivial action). -/
abbrev comapQ (e : Q ≃ₜ* Q) : H2lc Q (Mu n Ω) →* H2lc Q (Mu n Ω) :=
  H2lc.comap e.toMulEquiv.toMonoidHom e.continuous fun _ _ ↦ rfl

/-- **The Chern class of `α f`** ([Mzk7] Def. 4.1 is functorial): `c(α f) = α_* (θ̄⁻¹)^* c(f)`. -/
theorem chernClass_map [NeZero n] {f : Ω} (hf : KummerInv ρ n f) :
    chernClass hs hμ hstab hq (hf.map α θ hθ (θb := θb.toMulEquiv) hρθ) =
      TopClass.h2Map (muMap n α).toMonoidHom (fun _ _ ↦ rfl)
        (comapQ (n := n) (Ω := Ω) θb.symm (chernClass hs hμ hstab hq hf)) := by
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf
  have hg' := hg.map α θ (θb := θb.toMulEquiv) hθ hρθ hs hf.fix
  have hglc' : IsLocallyConstant (fun γ ↦ α (g (θb.symm γ))) :=
    (hglc.comp_continuous θb.symm.continuous).comp α
  rw [← chernClassOf_eq_chernClass hs hμ hstab hq hf hg hglc,
    ← chernClassOf_eq_chernClass hs hμ hstab hq _ hg' hglc']
  change QuotientGroup.mk _ = QuotientGroup.mk _
  congr 1
  refine Subtype.ext (funext fun x ↦ Mu.ext (Units.ext ?_))
  obtain ⟨γ, δ⟩ := x
  exact chernVal_map α θ hθ (θb := θb.toMulEquiv) hρθ hs hg γ δ

end Topology

end Generic

end CurvesJacobian.ChernClass

/-! ### `M_X/n` and automorphisms of `Δ_X` -/

namespace CurvesJacobian.TopClass

section Comap

variable {G M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup M']
  [MulDistribMulAction G M] [MulDistribMulAction G M']

lemma h2Map_comap (φ : G →* G) (hφ : Continuous φ) (hact : ∀ (g : G) (m : M), φ g • m = g • m)
    (hact' : ∀ (g : G) (m : M'), φ g • m = g • m) (ρ : M →* M')
    (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m) (c : H2lc G M) :
    h2Map ρ hρ (H2lc.comap φ hφ hact c) = H2lc.comap φ hφ hact' (h2Map ρ hρ c) := by
  induction c using QuotientGroup.induction_on with
  | H f => rfl

lemma comap_comap (φ ψ : G →* G) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hact : ∀ (g : G) (m : M), φ g • m = g • m) (hact' : ∀ (g : G) (m : M), ψ g • m = g • m)
    (c : H2lc G M) :
    H2lc.comap φ hφ hact (H2lc.comap ψ hψ hact' c) =
      H2lc.comap (ψ.comp φ) (hψ.comp hφ) (fun g m ↦ by
        rw [MonoidHom.comp_apply, hact', hact]) c := by
  induction c using QuotientGroup.induction_on with
  | H f => rfl

lemma comap_eq_self (φ : G →* G) (hφ : Continuous φ) (hact : ∀ (g : G) (m : M), φ g • m = g • m)
    (h : ∀ g, φ g = g) (c : H2lc G M) : H2lc.comap φ hφ hact c = c := by
  induction c using QuotientGroup.induction_on with
  | H f =>
    change QuotientGroup.mk _ = QuotientGroup.mk f
    congr 1
    ext ⟨a, b⟩
    change f.1 (φ a, φ b) = f.1 (a, b)
    rw [h, h]

end Comap

section Precomp

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- `θ̄^*` on `H²(G, M)` for a trivial action. -/
abbrev comapE {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (e : G ≃ₜ* G) : H2lc G M →* H2lc G M :=
  H2lc.comap e.toMulEquiv.toMonoidHom e.continuous fun g m ↦ by rw [htriv, htriv]

lemma comapE_symm_comapE {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (e : G ≃ₜ* G) (c : H2lc G M) :
    comapE htriv e.symm (comapE htriv e c) = c := by
  rw [comap_comap]
  exact comap_eq_self _ _ _ (fun g ↦ e.apply_symm_apply g) c

lemma comapE_comapE_symm {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (e : G ≃ₜ* G) (c : H2lc G M) :
    comapE htriv e (comapE htriv e.symm c) = c := by
  rw [comap_comap]
  exact comap_eq_self _ _ _ (fun g ↦ e.symm_apply_apply g) c

/-- **The action of an automorphism `θ̄` of `G` on `M_X/n = Hom(H²(G, ℤ/n), ℤ/n)`**:
`φ ↦ φ ∘ θ̄^*`. For the conjugation `θ̄_σ` by `σ ∈ Π_X` on `Δ_X` this is the natural action of
`Π_X` on `M_X/n` (`(στ) · φ = σ · (τ · φ)`, `precompMX_trans`). -/
def precompMX (e : G ≃ₜ* G) : MXmod G n ≃* MXmod G n where
  toFun φ := (MXmod.toHom G n).symm
    ((MXmod.toHom G n φ).comp (comapE (fun _ _ ↦ rfl) e))
  invFun φ := (MXmod.toHom G n).symm
    ((MXmod.toHom G n φ).comp (comapE (fun _ _ ↦ rfl) e.symm))
  left_inv φ := by
    apply (MXmod.toHom G n).injective
    refine MonoidHom.ext fun u ↦ ?_
    change MXmod.toHom G n φ (comapE _ e (comapE _ e.symm u)) = _
    rw [comapE_comapE_symm]
  right_inv φ := by
    apply (MXmod.toHom G n).injective
    refine MonoidHom.ext fun u ↦ ?_
    change MXmod.toHom G n φ (comapE _ e.symm (comapE _ e u)) = _
    rw [comapE_symm_comapE]
  map_mul' _ _ := rfl

@[simp] lemma evAt_precompMX (e : G ≃ₜ* G) (u : H2lc G (TrivZ G n)) (φ : MXmod G n) :
    evAt u (precompMX e φ) = evAt (comapE (fun _ _ ↦ rfl) e u) φ := rfl

lemma precompMX_symm_apply (e : G ≃ₜ* G) (φ : MXmod G n) :
    (precompMX e).symm φ = precompMX e.symm φ := rfl

/-- `precompMX` is a left action: `(θ̄₁ θ̄₂)^*`-precomposition is the composite. -/
lemma precompMX_trans (e₁ e₂ : G ≃ₜ* G) (φ : MXmod G n) :
    precompMX (e₂.trans e₁) φ = precompMX e₁ (precompMX e₂ φ) := by
  apply (MXmod.toHom G n).injective
  refine MonoidHom.ext fun u ↦ ?_
  change MXmod.toHom G n φ (comapE _ (e₂.trans e₁) u) =
    MXmod.toHom G n φ (comapE _ e₂ (comapE _ e₁ u))
  rw [comap_comap]
  rfl

variable {g : ℕ} [NeZero n]

/-- **The tautological class under `θ̄`**: `(φ ↦ φ ∘ θ̄^*)_* t = θ̄^* t` (uniqueness of `t`). -/
theorem h2Map_precompMX_of_isTaut (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0))
    (e : G ≃ₜ* G) {t : H2lc G (MXmod G n)} (ht : IsTaut G n t) :
    h2Map (precompMX e).toMonoidHom (fun _ _ ↦ rfl) t = comapE (fun _ _ ↦ rfl) e t := by
  set t' := h2Map (precompMX e).symm.toMonoidHom (fun _ _ ↦ rfl)
    (comapE (fun _ _ ↦ rfl) e t) with ht'
  have htaut : IsTaut G n t' := fun u ↦ by
    rw [ht', h2Map_comp]
    have hc : (evAt u).comp (precompMX e).symm.toMonoidHom =
        evAt (comapE (fun _ _ ↦ rfl) e.symm u) := MonoidHom.ext fun φ ↦ rfl
    rw [h2Map_congr hc _ (fun _ _ ↦ rfl),
      h2Map_comap _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl), ht, comapE_comapE_symm]
  have h1 : t' = t := (exists_unique_isTaut hg he).unique htaut ht
  conv_lhs => rw [← h1, ht', h2Map_comp]
  have hc : (precompMX (n := n) e).toMonoidHom.comp (precompMX e).symm.toMonoidHom =
      MonoidHom.id _ :=
    MonoidHom.ext fun φ ↦ (precompMX e).apply_symm_apply φ
  conv_lhs => rw [h2Map_congr hc _ (fun _ _ ↦ rfl), h2Map_id]

end Precomp

end CurvesJacobian.TopClass

/-! ### Curves: transport of representatives and of `c₁` -/

namespace CurvesJacobian.ChernClass

universe u

section Inertia

variable {Ω : Type u} [Field Ω]

lemma valuation_lt_one_iff_mem (A : ValuationSubring Ω) (x : Ω) :
    A.valuation x < 1 ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_inv₀]
  simp only [hx, false_or, not_le]
  constructor
  · intro h
    exact ⟨h.le, one_lt_inv₀ ((Valuation.pos_iff _).2 hx) |>.2 h⟩
  · rintro ⟨-, h⟩
    exact (one_lt_inv₀ ((Valuation.pos_iff _).2 hx)).1 h

/-- **Conjugating inertia**: if `σ = α⁻¹ σ' α` and `σ'` is in the inertia group of `W'`, then
`σ` is in the inertia group of `α⁻¹(W')`. -/
lemma mem_inertia_comap {P : Type u} [Field P] [Algebra P Ω] (α : Ω ≃+* Ω)
    {σ σ' : Ω ≃ₐ[P] Ω} (h : ∀ x, α (σ x) = σ' (α x)) {W' : ValuationSubring Ω}
    (hσ' : σ' ∈ GaloisPi1.inertia W') :
    σ ∈ GaloisPi1.inertia (W'.comap (α : Ω →+* Ω)) := by
  intro a ha
  have ha' : α a ∈ W' := ValuationSubring.mem_comap.1 ha
  have h1 := hσ' (α a) ha'
  rw [valuation_lt_one_iff_mem] at h1 ⊢
  have he : α (σ a - a) = σ' (α a) - α a := by rw [map_sub, h]
  simp only [ValuationSubring.mem_comap, RingHom.coe_coe, map_inv₀, he]
  rcases h1 with ⟨h1, h2 | h2⟩
  · refine ⟨h1, Or.inl ?_⟩
    rw [← he] at h2
    exact (map_eq_zero α).1 h2
  · exact ⟨h1, Or.inr h2⟩

end Inertia

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n : ℕ} [NeZero n]
  (α : Ω ≃+* Ω) (θ : D.H ≃* D.H) (hθ : ∀ (σ : D.H) (x : Ω), α (σ • x) = θ σ • α x)
  (θb : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤))
  (hρθ : ∀ σ : D.H, rhoX D eL hH (θ σ) = θb (rhoX D eL hH σ))
  (ε : Kummer.constAut k (F D)) (hε : ∀ x : F D, (((ε : F D ≃+* F D) x : F D) : Ω) = α x)

attribute [local instance] isFunctionField_F instTrivMu

omit [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] in
include hε in
lemma coe_constAut_inv_apply (x : F D) :
    ((((ε⁻¹ : Kummer.constAut k (F D)) : F D ≃+* F D) x : F D) : Ω) = α.symm x := by
  apply α.injective
  rw [← hε, RingEquiv.apply_symm_apply]
  change (((ε : F D ≃+* F D) ((ε : F D ≃+* F D).symm x) : F D) : Ω) = x
  rw [RingEquiv.apply_symm_apply]

omit [IsAlgClosed k] [X.Over (Spec (.of k))] [IsCurveOver k X] [NeZero n] in
include hθ hρθ hε in
/-- **`α f` represents `ε E`** if `f` represents `E` (`ε = α|_F` acting on divisors). -/
theorem IsChernRepDiv.map {E : Divisor k (F D)} {f : Ω} (hf : IsChernRepDiv D eL hH n E f) :
    IsChernRepDiv D eL hH n (Kummer.divMap ε E) (α f) where
  toKummerInv := hf.toKummerInv.map α θ hθ (θb := θb.toMulEquiv) hρθ
  loc := by
    intro P' W' hP'W' u' hu' hord σ' hσ' β' γ' hβ' hγ'
    set σ := θ.symm σ'
    have hσα : ∀ x, α ((σ : Ω ≃ₐ[K₀ k t] Ω) x) = (σ' : Ω ≃ₐ[K₀ k t] Ω) (α x) := fun x ↦ by
      have := hθ σ x
      rwa [MulEquiv.apply_symm_apply] at this
    have hin := mem_inertia_comap α hσα hσ'
    set ε' : Kummer.constAut k (F D) := ε⁻¹
    set P := Kummer.placeMap ε' P'
    have hPW : ∀ x : F D, ((x : F D) : Ω) ∈ W'.comap (α : Ω →+* Ω) ↔ x ∈ P.1 := fun x ↦ by
      rw [ValuationSubring.mem_comap, Kummer.mem_placeMap, RingHom.coe_coe, ← hε]
      exact hP'W' _
    set u : F D := (ε' : F D ≃+* F D) u'
    have hu0 : u ≠ 0 := (map_ne_zero _).2 hu'
    have hordu : P.ord u = E P := by
      rw [Kummer.ord_placeMap_apply, hord, Kummer.divMap_apply]
    have hβ : (α.symm β') ^ n = f := by
      apply α.injective
      rw [map_pow, RingEquiv.apply_symm_apply, hβ']
    have hγ : (α.symm γ') ^ n = ((u : F D) : Ω) := by
      rw [coe_constAut_inv_apply α ε hε, ← map_pow, hγ']
    have key := hf.loc P _ hPW u hu0 hordu σ hin _ _ hβ hγ
    have h2 := congrArg α key
    simp only [map_div₀, RingEquiv.apply_symm_apply] at h2
    change α ((σ : Ω ≃ₐ[K₀ k t] Ω) (α.symm β')) / β' =
      α ((σ : Ω ≃ₐ[K₀ k t] Ω) (α.symm γ')) / γ' at h2
    rw [hσα, hσα, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h2
    exact h2

include hk hτ hθ hρθ hε in
/-- **`c₁(ε E) = α_* (θ̄⁻¹)^* c₁(E)`.** -/
theorem c1Div_divMap (hgen : 0 < (curveGenus k X).toNat) (E : Divisor k (F D)) :
    Additive.toMul (c1Div hH hk hτ n hgen (Kummer.divMap ε E)) =
      TopClass.h2Map (muMap n α).toMonoidHom (fun _ _ ↦ rfl)
        (TopClass.comapE (fun _ _ ↦ rfl) θb.symm
          (Additive.toMul (c1Div hH hk hτ n hgen E))) := by
  obtain ⟨f, hf⟩ := exists_isChernRepDiv hk hτ (n := n) (hH := hH) hgen E
  rw [c1Div_eq hk hτ hgen hf, c1Div_eq hk hτ hgen (IsChernRepDiv.map α θ hθ θb hρθ ε hε hf)]
  exact chernClass_map α θ hθ (rhoX_sX hH hk hτ) (fun σ _ hζ ↦ smul_eq_of_pow_eq_one D n σ hζ)
    (isOpen_stabilizer D) (isOpen_of_rhoX hk hτ) θb hρθ hf.toKummerInv

include hk hτ hθ hρθ hε in
/-- **`θ̄^* c₁(pt) = α_* c₁(pt)`**: the first Chern class of a degree-`1` line bundle is
equivariant (`ε` permutes the points, and `c₁(pt)` does not depend on the point). -/
theorem c1One_map (hgen : 0 < (curveGenus k X).toNat) :
    TopClass.comapE (fun _ _ ↦ rfl) θb (c1One hH hk hτ n hgen) =
      TopClass.h2Map (muMap n α).toMonoidHom (fun _ _ ↦ rfl) (c1One hH hk hτ n hgen) := by
  set P := Classical.arbitrary (Place k (F D))
  have h1 := c1Div_divMap hk hτ α θ hθ θb hρθ ε hε hgen (n := n) (Finsupp.single P 1)
  have hs : Kummer.divMap ε (Finsupp.single P 1) = Finsupp.single (Kummer.placeMap ε P) 1 := by
    ext Q
    have hiff : P = Kummer.placeMap ε⁻¹ Q ↔ Kummer.placeMap ε P = Q := by
      constructor
      · intro h
        rw [h, ← Kummer.placeMap_mul, mul_inv_cancel, Kummer.placeMap_one]
      · intro h
        rw [← h, ← Kummer.placeMap_mul, inv_mul_cancel, Kummer.placeMap_one]
    rw [Kummer.divMap_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp only [hiff]
  rw [hs, ← c1One_eq hk hτ hgen, ← c1One_eq hk hτ hgen] at h1
  conv_lhs => rw [h1, TopClass.h2Map_comap _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl),
    TopClass.comapE_comapE_symm]

include hk hτ hθ hρθ hε in
/-- **S1f, modulo `n`: equivariance of the natural `M_X/n ≅ μ_n`** ([Mzk19] Prop. 1.2(ii) is
natural): for a semilinear automorphism `(α, θ, θ̄)` of the Galois model,
`natIso (φ ∘ θ̄^*) = α · natIso φ`. -/
theorem natIso_precompMX (hgen : 0 < (curveGenus k X).toNat)
    (φ : TopClass.MXmod π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) n) :
    natIso hH hk hτ n hgen (TopClass.precompMX θb φ) = muMap n α (natIso hH hk hτ n hgen φ) := by
  set ι := natIso hH hk hτ n hgen
  let ι' := ((TopClass.precompMX θb).trans ι).trans (muMap n α).symm
  have hι' : ι' = ι := by
    apply natIso_unique hk hτ hgen
    have e2 : TopClass.h2Map ι'.toMonoidHom (fun _ _ ↦ rfl) (tautX hH hk hτ n hgen) =
        TopClass.h2Map (muMap n α).symm.toMonoidHom (fun _ _ ↦ rfl)
          (TopClass.h2Map ι.toMonoidHom (fun _ _ ↦ rfl)
            (TopClass.h2Map (TopClass.precompMX θb).toMonoidHom (fun _ _ ↦ rfl)
              (tautX hH hk hτ n hgen))) := by
      rw [TopClass.h2Map_comp, TopClass.h2Map_comp]
      rfl
    rw [e2, TopClass.h2Map_precompMX_of_isTaut hgen (nonempty_orientation hH hk hτ) θb
        (isTaut_tautX hk hτ hgen),
      TopClass.h2Map_comap _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl), natIso_spec,
      c1One_map hk hτ α θ hθ θb hρθ ε hε hgen, TopClass.h2Map_comp]
    have hc : (muMap n α).symm.toMonoidHom.comp (muMap n α).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun ζ ↦ (muMap n α).symm_apply_apply ζ
    rw [TopClass.h2Map_congr hc _ (fun _ _ ↦ rfl), TopClass.h2Map_id]
  have := congrArg (fun j : _ ≃* _ ↦ muMap n α (j φ)) hι'
  simp only [ι', MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at this
  exact this

end Curve

end CurvesJacobian.ChernClass
