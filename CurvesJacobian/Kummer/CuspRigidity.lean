/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.SyncZHat

/-!
# Rigidity of cuspidal geometric decomposition groups ([GalSect] Thm. 4.3)

[GalSect] = *Galois sections in absolute anabelian geometry* (`Galois Sections.txt`).
Theorem 4.3 (l.841–882): in the notation of Thm. 2.3 (`α : Π_{X_K} ≅ Π_{Y_L}` for hyperbolic
curves over `p`-adic local fields), if `α` induces isomorphisms `I_x ≅ I_y` and
`μ_Ẑ(K̄) ≅ μ_Ẑ(L̄)` (`x`, `y` cusps), then these are compatible with the natural isomorphisms
`μ_Ẑ(K̄) ≅ I_x`, `μ_Ẑ(L̄) ≅ I_y` (roots of local coordinates, l.837). The proof (l.861–882)
reduces to `X̄`, `Ȳ` of genus `≥ 2` with exactly one cusp ("filling in" the others), and then
compares two facts about `H²(Δ_X, -) ≅ Ẑ`:
* by Lemma 4.2 (cj: [AbsTopIII] Prop. 1.4(ii), `ChernClass.IsCuspPushout.mk_eq_natIso`) the class
  of `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` is, under `I_x ≅ Ẑ(1)`, the first Chern class of the
  degree-one line bundle `𝒪(x)`; `α` maps this extension to the one of `y`;
* by [AbsAnab] Lemma 2.5(ii) (`Absolute Anabelian Geometry.txt` l.1736–1779) the map
  `H²(Δ_X, μ_Ẑ(K̄)) ≅ H²(Δ_Y, μ_Ẑ(L̄))` induced by `α` (and the cyclotome isomorphism)
  preserves the first Chern classes of line bundles of degree `1`.

This file proves, for one-point complements `U = X ∖ {x}`, `V = Y ∖ {y}` of proper curves of genus
`≥ 1` over algebraically closed fields of characteristic `0` (the geometric fundamental groups;
Galois models of `Kummer/CuspChern.lean`), and abstract isomorphisms
`α_U : Δ_U ≃ₜ* Δ_V`, `α_X : Δ_X ≃ₜ* Δ_Y` compatible with filling, with `α_U(I_x) = I_y`:

* `IsPushoutAlong`, `IsPushoutAlong.transport` (pure group theory): transport of a pushout of
  `1 → I → G_U → G_X → 1` along `(α_U, α_X)` and a coefficient isomorphism; `h2Transport`;
* `cuspPushout_chi_eq`: two cusp pushouts along continuous characters `I_x → μ_n` with
  the same class have the same character (relator value, `IsCuspPushout.h2EquivAny_mk`);
* **`chiN_map_iff`**: for `β_n : μ_n(Ω_X) ≃* μ_n(Ω_Y)`, `χ_n^Y ∘ α_U = β_n ∘ χ_n^X` on `I_x` **iff**
  `(α_X, β_n)_*` sends `c₁(deg 1)` to `c₁(deg 1)` in `H²(-, μ_n)` (unconditional);
* **`cuspInertiaZHatEquiv_map_iff`**: the same at the `Ẑ(1)`-level: for `β : Ẑ(1)_X ≃* Ẑ(1)_Y`
  with levels `β_n`, the natural `I_x ≅ Ẑ(1)` (`cuspInertiaZHatEquiv`) are compatible with
  `α_U`, `β` iff `(α_X, β_n)` preserve `c₁(deg 1)` for every `n`;
* **`rigidity_cuspInertia`** ([GalSect] Thm. 4.3, one-cusp case): the compatibility, with the
  degree-one statement of [AbsAnab] Lemma 2.5(ii) as the explicit hypothesis
  `DegOneChernPreserved` (a recorded debt, `MR13-plan.md`: its proof needs the `p`-adic
  `Q_{>0}`-structure on `H²` from Faltings–Chai degenerations, l.1736–1779).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup Pi1.SurfaceGen WeilCurves.FunctionField

namespace CurvesJacobian.CuspRigidity

/-! ### Transport of pushouts (pure group theory) -/

section Generic

variable {G G' M M' : Type*} [Group G] [Group G'] [CommGroup M] [CommGroup M']

/-- Transport of a trivial-action cocycle along `α : G ≃* G'` and `β : M →* M'`:
`(a, b) ↦ β (Φ (α⁻¹ a, α⁻¹ b))`. -/
def cocycleTransport (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M) : TrivCocycle G' M' :=
  ⟨fun p ↦ β (Φ.1 (α.symm p.1, α.symm p.2)), fun a b c ↦ by
    have := congrArg β (Φ.2 (α.symm a) (α.symm b) (α.symm c))
    simpa only [map_mul] using this⟩

@[simp] lemma cocycleTransport_apply (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M)
    (a b : G') : (cocycleTransport α β Φ).1 (a, b) = β (Φ.1 (α.symm a, α.symm b)) := rfl

/-- The induced homomorphism of twisted products `M ×_Φ G → M' ×_{Φ'} G'`. -/
def twistTransport (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M) :
    Twist Φ →* Twist (cocycleTransport α β Φ) where
  toFun x := ⟨β x.m, α x.g⟩
  map_one' := by
    ext
    · simp [map_inv]
    · simp
  map_mul' x y := by
    ext
    · simp [map_mul]
    · simp

@[simp] lemma twistTransport_m (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M) (x : Twist Φ) :
    (twistTransport α β Φ x).m = β x.m := rfl

@[simp] lemma twistTransport_g (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M) (x : Twist Φ) :
    (twistTransport α β Φ x).g = α x.g := rfl

lemma twistTransport_incl (α : G ≃* G') (β : M →* M') (Φ : TrivCocycle G M) (c : M) :
    twistTransport α β Φ (Twist.incl c) = Twist.incl (β c) := by
  ext
  · simp [map_mul, map_inv]
  · simp

variable {GU GV : Type*} [Group GU] [Group GV]

/-- **`(Φ, Ψ)` represents the pushout of `1 → I → G_U → G_X` along `χ`**: `Ψ : G_U →* M ×_Φ G_X`
lies over `p` and is `χ` on `I` (the generic form of `ChernClass.IsCuspPushout`, which is this
for `p` the filling map and `I = I_x`). -/
def IsPushoutAlong (p : GU →* G) (I : Subgroup GU) (χ : I → M) (Φ : TrivCocycle G M)
    (Ψ : GU →* Twist Φ) : Prop :=
  (∀ γ, (Ψ γ).g = p γ) ∧ ∀ i : I, Ψ i = Twist.incl (χ i)

/-- **Transport of a pushout** along `α_U : G_U ≃* G_V`, `α_X : G ≃* G'` compatible with the
projections, an isomorphism `e : I ≃* J` induced by `α_U`, and `β : M →* M'`. -/
theorem IsPushoutAlong.transport {p : GU →* G} {q : GV →* G'} (αU : GU ≃* GV) (αX : G ≃* G')
    (hpq : ∀ γ, q (αU γ) = αX (p γ)) {I : Subgroup GU} {J : Subgroup GV} (e : I ≃* J)
    (he : ∀ i, (e i : GV) = αU i) (β : M →* M') {χ : I → M} {Φ : TrivCocycle G M}
    {Ψ : GU →* Twist Φ} (h : IsPushoutAlong p I χ Φ Ψ) :
    IsPushoutAlong q J (fun j ↦ β (χ (e.symm j))) (cocycleTransport αX β Φ)
      ((twistTransport αX β Φ).comp (Ψ.comp αU.symm.toMonoidHom)) := by
  refine ⟨fun γ ↦ ?_, fun j ↦ ?_⟩
  · simp only [MonoidHom.comp_apply, twistTransport_g, MulEquiv.coe_toMonoidHom, h.1]
    rw [← hpq, MulEquiv.apply_symm_apply]
  · have hj : αU.symm (j : GV) = (e.symm j : GU) := by
      rw [MulEquiv.symm_apply_eq, ← he, MulEquiv.apply_symm_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hj, h.2, twistTransport_incl]

/-- The isomorphism `I ≃* J` induced by `α_U` when `α_U(I) = J`. -/
def inertiaEquiv {A B : Type*} [Group A] [Group B] (αU : A ≃* B) {I : Subgroup A}
    {J : Subgroup B} (hIJ : I.map αU.toMonoidHom = J) : I ≃* J :=
  (αU.subgroupMap I).trans (MulEquiv.subgroupCongr hIJ)

@[simp] lemma coe_inertiaEquiv {A B : Type*} [Group A] [Group B] (αU : A ≃* B)
    {I : Subgroup A} {J : Subgroup B} (hIJ : I.map αU.toMonoidHom = J) (i : I) :
    (inertiaEquiv αU hIJ i : B) = αU i := rfl

lemma coe_inertiaEquiv_symm {A B : Type*} [Group A] [Group B] (αU : A ≃* B)
    {I : Subgroup A} {J : Subgroup B} (hIJ : I.map αU.toMonoidHom = J) (j : J) :
    ((inertiaEquiv αU hIJ).symm j : A) = αU.symm j := by
  rw [MulEquiv.eq_symm_apply, ← coe_inertiaEquiv αU hIJ, MulEquiv.apply_symm_apply]

lemma continuous_inertiaEquiv_symm {A B : Type*} [Group A] [Group B] [TopologicalSpace A]
    [TopologicalSpace B] (αU : A ≃ₜ* B) {I : Subgroup A} {J : Subgroup B}
    (hIJ : I.map αU.toMulEquiv.toMonoidHom = J) :
    Continuous (inertiaEquiv αU.toMulEquiv hIJ).symm := by
  refine continuous_induced_rng.2 ?_
  have : (Subtype.val ∘ (inertiaEquiv αU.toMulEquiv hIJ).symm : J → A) =
      αU.symm ∘ Subtype.val := funext (coe_inertiaEquiv_symm αU.toMulEquiv hIJ)
  rw [this]
  exact αU.symm.continuous.comp continuous_subtype_val

lemma isClosed_map_of_contEquiv {A B : Type*} [Group A] [Group B] [TopologicalSpace A]
    [TopologicalSpace B] (Θ : A ≃ₜ* B) {K : Subgroup A} (hK : IsClosed (K : Set A)) :
    IsClosed ((K.map Θ.toMulEquiv.toMonoidHom : Subgroup B) : Set B) := by
  rw [Subgroup.coe_map]
  exact Θ.toHomeomorph.isClosedMap _ hK

/-- Elements of `Ẑ(1)` (characteristic `0`) are determined by their projections to `μ_n`. -/
lemma zHatOne_ext {K Ω : Type*} [Field K] [CharZero K] [Field Ω] {z z' : ZHatOne K Ω}
    (h : ∀ (n : ℕ) [NeZero n],
      ZHatOne.proj (⟨n, Nat.cast_ne_zero.2 (NeZero.ne n)⟩ : KummerIndex K) z =
        ZHatOne.proj (⟨n, Nat.cast_ne_zero.2 (NeZero.ne n)⟩ : KummerIndex K) z') :
    z = z' := by
  refine Subtype.ext (funext fun i ↦ ?_)
  obtain ⟨m, hm⟩ := i
  haveI : NeZero m := ⟨fun h0 ↦ hm (by simp [h0])⟩
  exact h m

end Generic

section Induced

variable {A A' B B' : Type*} [Group A] [Group A'] [Group B] [Group B']

/-- The isomorphism `B ≃* B'` induced by `α : A ≃* A'` on surjections `p : A ↠ B`, `q : A' ↠ B'`
with `α(ker p) = ker q`. -/
noncomputable def inducedMulEquiv (α : A ≃* A') {p : A →* B} {q : A' →* B'}
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : p.ker.map α.toMonoidHom = q.ker) : B ≃* B' :=
  ((QuotientGroup.quotientKerEquivOfSurjective p hp).symm.trans
    (QuotientGroup.congr p.ker q.ker α hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)

lemma inducedMulEquiv_apply (α : A ≃* A') {p : A →* B} {q : A' →* B'}
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : p.ker.map α.toMonoidHom = q.ker) (a : A) :
    inducedMulEquiv α hp hq hker (p a) = q (α a) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective p hp).symm (p a) =
      (QuotientGroup.mk a : A ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [inducedMulEquiv, MulEquiv.trans_apply, h1]
  rfl

variable [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
  [CompactSpace A] [T2Space B] [T2Space B']

/-- The continuous version of `inducedMulEquiv` (compact sources, Hausdorff targets). -/
noncomputable def inducedContEquiv (α : A ≃ₜ* A') {p : A →* B} {q : A' →* B'}
    (hpc : Continuous p) (hqc : Continuous q)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : p.ker.map α.toMulEquiv.toMonoidHom = q.ker) : B ≃ₜ* B' :=
  have hcont : Continuous (inducedMulEquiv α.toMulEquiv hp hq hker) := by
    rw [(IsClosedMap.isQuotientMap hpc.isClosedMap hpc hp).continuous_iff]
    have : (inducedMulEquiv α.toMulEquiv hp hq hker ∘ p) = q ∘ α :=
      funext (inducedMulEquiv_apply α.toMulEquiv hp hq hker)
    rw [this]
    exact hqc.comp α.continuous
  haveI : CompactSpace B := hp.compactSpace hpc
  { inducedMulEquiv α.toMulEquiv hp hq hker with
    continuous_toFun := hcont
    continuous_invFun :=
      (hcont.homeoOfEquivCompactToT2
        (f := (inducedMulEquiv α.toMulEquiv hp hq hker).toEquiv)).symm.continuous }

lemma inducedContEquiv_apply (α : A ≃ₜ* A') {p : A →* B} {q : A' →* B'}
    (hpc : Continuous p) (hqc : Continuous q)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : p.ker.map α.toMulEquiv.toMonoidHom = q.ker) (a : A) :
    inducedContEquiv α hpc hqc hp hq hker (p a) = q (α a) :=
  inducedMulEquiv_apply α.toMulEquiv hp hq hker a

end Induced

section H2

variable {G G' M M' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [CommGroup M] [CommGroup M'] [MulDistribMulAction G M] [MulDistribMulAction G M']
  [MulDistribMulAction G' M']

/-- **Transport of `H²` with trivial actions** along `α : G ≃ₜ* G'` and `β : M →* M'`. -/
noncomputable def h2Transport (hM : ∀ (g : G) (m : M), g • m = m)
    (hM' : ∀ (g : G) (m : M'), g • m = m) (hM'' : ∀ (g : G') (m : M'), g • m = m)
    (α : G ≃ₜ* G') (β : M →* M') : H2lc G M →* H2lc G' M' :=
  (H2lc.congr α fun g m ↦ by rw [hM', hM'']).toMonoidHom.comp
    (TopClass.h2Map β fun g m ↦ by rw [hM, hM'])

/-- A locally constant trivial-action cocycle as an element of `Z²_lc` (generic `toCocyclesX`). -/
def toCocycles (htriv : ∀ (g : G) (m : M), g • m = m) {Φ : TrivCocycle G M}
    (hΦ : IsLocallyConstant Φ.1) : H2lc.cocycles G M :=
  ⟨Φ.1, hΦ, fun a b c ↦ by rw [htriv]; exact TrivCocycle.cond Φ.2 a b c⟩

omit [MulDistribMulAction G M] [MulDistribMulAction G M'] [MulDistribMulAction G' M'] in
lemma isLocallyConstant_cocycleTransport (α : G ≃ₜ* G') (β : M →* M') {Φ : TrivCocycle G M}
    (hΦ : IsLocallyConstant Φ.1) :
    IsLocallyConstant (cocycleTransport α.toMulEquiv β Φ).1 :=
  (hΦ.comp_continuous (α.symm.continuous.prodMap α.symm.continuous)).comp β

lemma h2Transport_mk (hM : ∀ (g : G) (m : M), g • m = m)
    (hM' : ∀ (g : G) (m : M'), g • m = m) (hM'' : ∀ (g : G') (m : M'), g • m = m)
    (α : G ≃ₜ* G') (β : M →* M') {Φ : TrivCocycle G M} (hΦ : IsLocallyConstant Φ.1) :
    h2Transport hM hM' hM'' α β (QuotientGroup.mk (toCocycles hM hΦ)) =
      QuotientGroup.mk (toCocycles hM'' (isLocallyConstant_cocycleTransport α β hΦ)) :=
  rfl

end H2

/-! ### Cusp pushouts: existence and uniqueness of the character -/

open ChernClass

universe u v

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n : ℕ} [NeZero n]
  {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X} {π : (F D)ˣ}

attribute [local instance] instTrivMu

include hk hτ in
/-- **A cusp pushout along `χ_n` exists** (the Kummer extension of a representative of `𝒪_X(x)`
modulo `n`, `kummerPushout_isCuspPushout`). -/
theorem exists_isCuspPushout_chiN (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    ∃ (Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω))
      (Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ),
      IsLocallyConstant Φ.1 ∧
        IsCuspPushout hH U (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ) Φ Ψ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hs := rhoX_sX hH hk hτ
  have hμ : ∀ (σ : D.H) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ :=
    fun σ _ hζ ↦ smul_eq_of_pow_eq_one D n σ hζ
  have hstab := isOpen_stabilizer D
  have hq := isOpen_of_rhoX (hH := hH) hk hτ
  obtain ⟨f, hf⟩ := exists_isChernRep hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  obtain ⟨g, hg, hglc⟩ := exists_isAdm hs hstab hq hf.toKummerInv
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq f n
  exact ⟨_, _, (chernCocycles hs hμ hstab hq hf.ne hf.fix hg hglc).2.1,
    kummerPushout_isCuspPushout hk hτ hgen hUx hW₀ hW₀U hπW hπ hf hg hβ⟩

include hk hτ in
/-- The class of a cusp pushout along `χ_n` is `c₁(deg 1)` (`mk_eq_natIso`, `natIso_spec`). -/
theorem cuspPushout_mk_eq_c1One (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    {Φ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout hH U (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) = c1One hH hk hτ n hgen := by
  rw [h.mk_eq_natIso hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ, natIso_spec]

include hk hτ in
/-- **The character of a cusp pushout is determined by its class**: two cusp pushouts of
`1 → I_x → Δ^{c-cn}_U → Δ_X → 1` along continuous characters `χ₁, χ₂ : I_x → μ_n` with the same
class in `H²(Δ_X, μ_n)` have `χ₁ = χ₂` (under the relator value both classes go to the value at
the cusp generator `c`, `IsCuspPushout.h2EquivAny_mk`, and `c` topologically generates `I_x`). -/
theorem cuspPushout_chi_eq (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀)
    {χ₁ χ₂ : cuspInertia D X eL hH U W₀ →* Mu n Ω} (hχ₁ : Continuous χ₁) (hχ₂ : Continuous χ₂)
    {Φ₁ Φ₂ : TrivCocycle π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω)}
    {Ψ₁ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ₁}
    {Ψ₂ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Twist Φ₂}
    (hΦ₁ : IsLocallyConstant Φ₁.1) (hΦ₂ : IsLocallyConstant Φ₂.1)
    (h₁ : IsCuspPushout hH U χ₁ Φ₁ Ψ₁) (h₂ : IsCuspPushout hH U χ₂ Φ₂ Ψ₂)
    (hmk : (QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ₁) : H2lc _ (Mu n Ω)) =
      QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ₂)) :
    χ₁ = χ₂ := by
  obtain ⟨Θ, Θ₀, hI, hfill, -, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  have hc := cuspHat_mem Θ hI
  have e₁ := h₁.h2EquivAny_mk hgen Θ Θ₀ hfill hc hΦ₁
  have e₂ := h₂.h2EquivAny_mk hgen Θ Θ₀ hfill hc hΦ₂
  rw [hmk, e₂] at e₁
  have hc₀ : χ₁ ⟨_, hc⟩ = χ₂ ⟨_, hc⟩ := (inv_injective e₁).symm
  -- the equaliser of `χ₁, χ₂` is a closed subgroup containing `c`, hence all of `I_x`
  let K : Subgroup (cuspInertia D X eL hH U W₀) := MonoidHom.eqLocus χ₁ χ₂
  have hIc : IsCompact (cuspInertia D X eL hH U W₀ :
      Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := by
    rw [CuspCentral.cuspInertia_eq_map D eL hH U W₀, Subgroup.coe_map]
    exact (isClosed_inertiaH D W₀).isCompact.image (D.continuous_chartHom hH _)
  haveI : CompactSpace (cuspInertia D X eL hH U W₀) := isCompact_iff_compactSpace.1 hIc
  have hKc : IsCompact (K : Set (cuspInertia D X eL hH U W₀)) :=
    (isClosed_eq hχ₁ hχ₂).isCompact
  let T : Subgroup (ProfiniteSurfaceGroup (curveGenus k X).toNat 1) :=
    (K.map (cuspInertia D X eL hH U W₀).subtype).map Θ.toMulEquiv.toMonoidHom
  have hTc : IsClosed (T : Set (ProfiniteSurfaceGroup (curveGenus k X).toNat 1)) := by
    rw [Subgroup.coe_map, Subgroup.coe_map, Set.image_image]
    exact (hKc.image (Θ.continuous.comp continuous_subtype_val)).isClosed
  have hcT : CuspCentral.cuspHat (curveGenus k X).toNat ∈ T :=
    ⟨_, ⟨⟨_, hc⟩, hc₀, rfl⟩, Θ.apply_symm_apply _⟩
  have hIT : inertia (g := (curveGenus k X).toNat) (r := 1) 0 ≤ T :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hcT) hTc
  refine MonoidHom.ext fun i ↦ ?_
  have h1 : Θ.toMulEquiv.toMonoidHom (i : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) ∈ T :=
    hIT (by rw [← hI]; exact Subgroup.mem_map_of_mem _ i.2)
  obtain ⟨y, ⟨j, hj, rfl⟩, hy⟩ := h1
  have : j = i := Subtype.ext (Θ.injective hy)
  subst this
  exact hj

/-- `χ_n` (as a homomorphism) is continuous. -/
lemma continuous_chiNHom (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) :
    Continuous (chiNHom (hH := hH) hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ) :=
  (ZHatOne.continuous_proj _).comp (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U
    hπW hπ).continuous

end Curve

/-! ### The filling map: kernel and induced isomorphisms -/

section Fill

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X}

omit [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X] [IsSepClosed Ω]
  [IsGalois (K₀ k t) Ω] in
lemma continuous_fillX : Continuous (fillX D eL U) :=
  (fundamentalGroupMap (X.homOfLE (le_top : U ≤ ⊤))
    (specPoint_genericL_homOfLE D X eL le_top)).continuous

omit [IsAlgClosed k] [CharZero k] [X.Over (Spec (.of k))] [IsCurveOver k X] [IsSepClosed Ω]
  [IsGalois (K₀ k t) Ω] in
lemma isClosed_ker_fillX :
    IsClosed (((fillX D eL U).ker : Subgroup _) : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :=
  isClosed_singleton.preimage continuous_fillX

include hk hτ hH in
/-- `Δ_U ↠ Δ_X` is surjective (`U = X ∖ {x}`). -/
theorem fillX_surjective (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) : Function.Surjective (fillX D eL U) := by
  obtain ⟨Θ, Θ₀, -, hfill, -, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  intro b
  obtain ⟨y, hy⟩ := CuspCentral.fillHat_surjective _ (Θ₀ b)
  refine ⟨Θ.symm y, Θ₀.injective ?_⟩
  rw [← hy, ← ContinuousMulEquiv.apply_symm_apply Θ y]
  exact (hfill _).trans (by rw [ContinuousMulEquiv.apply_symm_apply])

include hk hτ in
/-- **`ker(Δ_U ↠ Δ_X)` is the closed normal subgroup generated by `I_x`**: it contains `I_x`, and
it is contained in every closed normal subgroup containing `I_x`. -/
theorem cuspInertia_le_ker_fillX (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) :
    cuspInertia D X eL hH U W₀ ≤ (fillX D eL U).ker := by
  obtain ⟨Θ, -, hI, -, hker, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  rw [← Subgroup.map_le_map_iff_of_injective (f := Θ.toMulEquiv.toMonoidHom) Θ.injective]
  rw [hI, hker]
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 ?_) inferInstance
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_singleton _))

include hk hτ in
theorem ker_fillX_le (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (K : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U))
    [K.Normal] (hK : IsClosed (K : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)))
    (hIK : cuspInertia D X eL hH U W₀ ≤ K) : (fillX D eL U).ker ≤ K := by
  obtain ⟨Θ, -, hI, -, hker, -⟩ :=
    CuspCentral.exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  rw [← Subgroup.map_le_map_iff_of_injective (f := Θ.toMulEquiv.toMonoidHom) Θ.injective]
  rw [hker]
  have hKc := isClosed_map_of_contEquiv Θ hK
  haveI : (K.map Θ.toMulEquiv.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ Θ.surjective
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hKc
  rw [Set.singleton_subset_iff]
  have : CuspCentral.cuspHat (curveGenus k X).toNat ∈
      (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom := by
    rw [hI]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  exact Subgroup.map_mono hIK this

end Fill

/-! ### [GalSect] Thm. 4.3 for one-point complements -/

section TwoCurves

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] {W₀ : ValuationSubring Ω} {x : X} {π : (F D)ˣ}
  {k' Ω' : Type v} [Field k'] [IsAlgClosed k'] [CharZero k']
  [Field Ω'] [Algebra k' Ω'] [IsSepClosed Ω'] {t' : Ω'} [IsGalois (K₀ k' t') Ω']
  {D' : GaloisData k' t'}
  {Y : Scheme.{v}} [Y.Over (Spec (.of k'))] [IsCurveOver k' Y] [IsIntegral Y]
  {eL' : Y.functionField ≃+* D'.L} {hH' : D'.H ≤ D'.HL}
  [Nonempty (⊤ : Y.Opens)]
  (hk' : ∀ c : k', ((eL' (algebraMap k' Y.functionField c) : D'.L) : Ω') = algebraMap k' Ω' c)
  {τ' : Y.functionField} (hτ' : ((eL' τ' : D'.L) : Ω') = t')
  {V : Y.Opens} [Nonempty V] {W₁ : ValuationSubring Ω'} {y : Y} {π' : (F D')ˣ}

attribute [local instance] instTrivMu

/-- `Δ_X` acts trivially on `μ_n(Ω')` (for transporting classes to `Δ_Y`). -/
noncomputable local instance instTrivMuXY (n : ℕ) :
    MulDistribMulAction π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) (Mu n Ω') :=
  Pi1.SurfaceGroup.trivialAction _ _

include hk hτ hk' hτ' in
/-- `α_U(ker(Δ_U ↠ Δ_X)) = ker(Δ_V ↠ Δ_Y)` if `α_U(I_x) = I_y` (both kernels are the closed normal
subgroups generated by the cuspidal inertia groups). -/
theorem map_ker_fillX (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁) :
    (fillX D eL U).ker.map αU.toMulEquiv.toMonoidHom = (fillX D' eL' V).ker := by
  set KX := (fillX D eL U).ker
  set KY := (fillX D' eL' V).ker
  have hKX : IsClosed (KX : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := isClosed_ker_fillX
  have hKY : IsClosed (KY : Set π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V)) :=
    isClosed_ker_fillX
  have hIX : cuspInertia D X eL hH U W₀ ≤ KX := cuspInertia_le_ker_fillX hk hτ hUx hW₀ hW₀U
  have hIY : cuspInertia D' Y eL' hH' V W₁ ≤ KY := cuspInertia_le_ker_fillX hk' hτ' hVy hW₁ hW₁V
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    let K := KY.comap αU.toMulEquiv.toMonoidHom
    haveI : K.Normal := Subgroup.Normal.comap inferInstance _
    have hK : IsClosed (K : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :=
      hKY.preimage αU.continuous
    have hIK : cuspInertia D X eL hH U W₀ ≤ K := by
      rw [← Subgroup.map_le_iff_le_comap, hI]
      exact hIY
    exact ker_fillX_le hk hτ hUx hW₀ hW₀U K hK hIK
  · let K := KX.map αU.toMulEquiv.toMonoidHom
    haveI : K.Normal := Subgroup.Normal.map inferInstance _ αU.surjective
    have hK : IsClosed (K : Set π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V)) :=
      isClosed_map_of_contEquiv αU hKX
    have hIK : cuspInertia D' Y eL' hH' V W₁ ≤ K := by
      rw [← hI]
      exact Subgroup.map_mono hIX
    exact ker_fillX_le hk' hτ' hVy hW₁ hW₁V K hK hIK

/-- **The isomorphism `Δ_X ≃ₜ* Δ_Y` induced by `α_U`** (filling in `x`, `y`) when
`α_U(I_x) = I_y`. -/
noncomputable def fillEquiv (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁) :
    π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' ⊤) :=
  inducedContEquiv αU continuous_fillX continuous_fillX
    (fillX_surjective (hH := hH) hk hτ hUx hW₀ hW₀U)
    (fillX_surjective (hH := hH') hk' hτ' hVy hW₁ hW₁V)
    (map_ker_fillX hk hτ hk' hτ' hUx hW₀ hW₀U hVy hW₁ hW₁V αU hI)

lemma fillEquiv_fillX (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁)
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁) (γ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :
    fillEquiv hk hτ hk' hτ' hUx hW₀ hW₀U hVy hW₁ hW₁V αU hI (fillX D eL U γ) =
      fillX D' eL' V (αU γ) :=
  inducedContEquiv_apply _ _ _ _ _ _ γ

include hk hτ hk' hτ' in
/-- **[GalSect] Thm. 4.3 modulo `n`, as an equivalence** (one-point complements, genus `≥ 1`):
for `α_U : Δ_U ≃ₜ* Δ_V`, `α_X : Δ_X ≃ₜ* Δ_Y` compatible with filling, `α_U(I_x) = I_y`, and
`β : μ_n(Ω) ≃* μ_n(Ω')`, the natural characters `χ_n : I_x ≅ Ẑ(1) ↠ μ_n` (roots of a local
coordinate, [GalSect] l.837) satisfy `χ_n^Y ∘ α_U = β ∘ χ_n^X` **iff** `(α_X, β)_*` sends the
first Chern class of a degree-one line bundle of `X` to that of `Y` in `H²(-, μ_n)`.
Proof ([GalSect] l.866–882): `α` transports the cusp pushout of `X` along `χ_n^X` to a cusp
pushout of `Y` along `β ∘ χ_n^X ∘ α_U⁻¹`; its class is `(α_X, β)_* c₁^X` (Lemma 4.2 =
`cuspPushout_mk_eq_c1One`), and the character of a cusp pushout is determined by its class
(`cuspPushout_chi_eq`). -/
theorem chiN_map_iff (n : ℕ) [NeZero n] (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (hgen' : 0 < (curveGenus k' Y).toNat)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁) (hπW' : W₁.valuation ((π' : F D') : Ω') < 1)
    (hπ' : ∀ f ∈ F D', W₁.valuation f < 1 → W₁.valuation f ≤ W₁.valuation ((π' : F D') : Ω'))
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (αX : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' ⊤))
    (hfill : ∀ γ, fillX D' eL' V (αU γ) = αX (fillX D eL U γ))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁)
    (β : Mu n Ω ≃* Mu n Ω') :
    (∀ i, chiN hH' hk' hτ' n V hgen' hVy hW₁ hW₁V hπW' hπ'
        (inertiaEquiv αU.toMulEquiv hI i) = β (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ i)) ↔
      h2Transport (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) αX β.toMonoidHom
        (c1One hH hk hτ n hgen) = c1One hH' hk' hτ' n hgen' := by
  set e := inertiaEquiv αU.toMulEquiv hI
  obtain ⟨Φ, Ψ, hΦ, hP⟩ := exists_isCuspPushout_chiN hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ
  have hT := IsPushoutAlong.transport (p := fillX D eL U) (q := fillX D' eL' V)
    αU.toMulEquiv αX.toMulEquiv hfill e (fun _ ↦ rfl) β.toMonoidHom hP
  have hΦT := isLocallyConstant_cocycleTransport αX β.toMonoidHom hΦ
  have hclass : h2Transport (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) αX β.toMonoidHom
      (c1One hH hk hτ n hgen) = QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦT) := by
    rw [← cuspPushout_mk_eq_c1One hk hτ hgen hUx hW₀ hW₀U hπW hπ hΦ hP]
    rfl
  rw [hclass]
  constructor
  · intro h
    have hχ : (fun j ↦ β.toMonoidHom (chiN hH hk hτ n U hgen hUx hW₀ hW₀U hπW hπ (e.symm j))) =
        chiN hH' hk' hτ' n V hgen' hVy hW₁ hW₁V hπW' hπ' := by
      funext j
      have := h (e.symm j)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [hχ] at hT
    exact cuspPushout_mk_eq_c1One hk' hτ' hgen' hVy hW₁ hW₁V hπW' hπ' hΦT hT
  · intro h i
    obtain ⟨Φ', Ψ', hΦ', hP'⟩ :=
      exists_isCuspPushout_chiN hk' hτ' (n := n) hgen' hVy hW₁ hW₁V hπW' hπ'
    let χ₁ : cuspInertia D' Y eL' hH' V W₁ →* Mu n Ω' := β.toMonoidHom.comp
      ((chiNHom (hH := hH) hk hτ (n := n) hgen hUx hW₀ hW₀U hπW hπ).comp e.symm.toMonoidHom)
    have hχ₁ : Continuous χ₁ :=
      (continuous_of_discreteTopology (α := Mu n Ω) (f := ⇑β.toMonoidHom)).comp
        ((continuous_chiNHom hk hτ hgen hUx hW₀ hW₀U hπW hπ).comp
        (continuous_inertiaEquiv_symm αU hI))
    have key := cuspPushout_chi_eq hk' hτ' hgen' hVy hW₁ hW₁V (χ₁ := χ₁)
      (χ₂ := chiNHom (hH := hH') hk' hτ' (n := n) hgen' hVy hW₁ hW₁V hπW' hπ') hχ₁
      (continuous_chiNHom hk' hτ' hgen' hVy hW₁ hW₁V hπW' hπ') hΦT hΦ' hT hP'
      (h.trans (cuspPushout_mk_eq_c1One hk' hτ' hgen' hVy hW₁ hW₁V hπW' hπ' hΦ' hP').symm)
    have := DFunLike.congr_fun key (e i)
    simp only [χ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      at this
    exact this.symm

include hk hτ hk' hτ' in
/-- **[GalSect] Thm. 4.3 at the `Ẑ(1)`-level, as an equivalence** (one-point complements, genus
`≥ 1`): for `β : Ẑ(1)_X ≃* Ẑ(1)_Y` with level components `β_n`, the natural isomorphisms
`I_x ≅ Ẑ(1)` (`cuspInertiaZHatEquiv`: roots of a local coordinate, [GalSect] l.837) are
compatible with `α_U` and `β` iff `(α_X, β_n)_*` preserves the first Chern class of a degree-one
line bundle for every `n`. -/
theorem cuspInertiaZHatEquiv_map_iff (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (hgen' : 0 < (curveGenus k' Y).toNat)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁) (hπW' : W₁.valuation ((π' : F D') : Ω') < 1)
    (hπ' : ∀ f ∈ F D', W₁.valuation f < 1 → W₁.valuation f ≤ W₁.valuation ((π' : F D') : Ω'))
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (αX : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' ⊤))
    (hfill : ∀ γ, fillX D' eL' V (αU γ) = αX (fillX D eL U γ))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁)
    (β : ZHatOne (F D) Ω ≃* ZHatOne (F D') Ω') (βn : ∀ (n : ℕ) [NeZero n], Mu n Ω ≃* Mu n Ω')
    (hβ : ∀ (n : ℕ) [NeZero n] (z : ZHatOne (F D) Ω),
      ZHatOne.proj (kIdx D' n) (β z) = βn n (ZHatOne.proj (kIdx D n) z)) :
    (∀ i, CuspCentral.cuspInertiaZHatEquiv hk' hτ' hgen' V hVy hW₁ hW₁V hπW' hπ'
        (inertiaEquiv αU.toMulEquiv hI i) =
          β (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U hπW hπ i)) ↔
      ∀ (n : ℕ) [NeZero n], h2Transport (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) αX
        (βn n).toMonoidHom (c1One hH hk hτ n hgen) = c1One hH' hk' hτ' n hgen' := by
  constructor
  · intro h n _
    refine (chiN_map_iff hk hτ hk' hτ' n hgen hUx hW₀ hW₀U hπW hπ hgen' hVy hW₁ hW₁V hπW' hπ'
      αU αX hfill hI (βn n)).1 fun i ↦ ?_
    simp only [chiN, h i, hβ]
  · intro h i
    refine zHatOne_ext fun n _ ↦ ?_
    change ZHatOne.proj (kIdx D' n) _ = ZHatOne.proj (kIdx D' n) _
    have := (chiN_map_iff hk hτ hk' hτ' n hgen hUx hW₀ hW₀U hπW hπ hgen' hVy hW₁ hW₁V hπW' hπ'
      αU αX hfill hI (βn n)).2 (h n) i
    simp only [chiN] at this
    rw [this, ← hβ]

variable (hH hH') in
/-- **[AbsAnab] Lemma 2.5(ii), degree-one form — a named hypothesis (debt, `MR13-plan.md`).**
`(α_X, β_n)_* : H²(Δ_X, μ_n(Ω)) ≅ H²(Δ_Y, μ_n(Ω'))` sends the first Chern class of a degree-one
line bundle on `X` to that on `Y`, for every `n`. [AbsAnab] (`Absolute Anabelian Geometry.txt`
l.1736–1779) proves this for the isomorphism induced by an isomorphism `α : Π_{X_K} ≅ Π_{Y_L}`
of arithmetic fundamental groups over `p`-adic fields, `β` the induced isomorphism of the
cyclotomes; the proof uses the `Q_{>0}`-structure on `H²` coming from Faltings–Chai
degenerations (Lemma 2.5(i)), not available here. -/
def DegOneChernPreserved (hgen : 0 < (curveGenus k X).toNat) (hgen' : 0 < (curveGenus k' Y).toNat)
    (αX : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' ⊤))
    (βn : ∀ (n : ℕ) [NeZero n], Mu n Ω ≃* Mu n Ω') : Prop :=
  ∀ (n : ℕ) [NeZero n], h2Transport (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) αX
    (βn n).toMonoidHom (c1One hH hk hτ n hgen) = c1One hH' hk' hτ' n hgen'

include hk hτ hk' hτ' in
/-- **[GalSect] Thm. 4.3 (Rigidity of cuspidal geometric decomposition groups)**, for
one-point complements of proper curves of genus `≥ 1` (`Galois Sections.txt` l.841–882): if `α`
induces `I_x ≅ I_y` (via `α_U`, compatible with filling by `α_X`) and `μ_Ẑ ≅ μ_Ẑ` (`β`, with
levels `β_n`), then these are compatible with the natural isomorphisms `I_x ≅ Ẑ(1)`,
`I_y ≅ Ẑ(1)`, given [AbsAnab] Lemma 2.5(ii) in the form `DegOneChernPreserved` (debt). -/
theorem rigidity_cuspInertia (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (hgen' : 0 < (curveGenus k' Y).toNat)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁) (hπW' : W₁.valuation ((π' : F D') : Ω') < 1)
    (hπ' : ∀ f ∈ F D', W₁.valuation f < 1 → W₁.valuation f ≤ W₁.valuation ((π' : F D') : Ω'))
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (αX : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' ⊤))
    (hfill : ∀ γ, fillX D' eL' V (αU γ) = αX (fillX D eL U γ))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁)
    (β : ZHatOne (F D) Ω ≃* ZHatOne (F D') Ω') (βn : ∀ (n : ℕ) [NeZero n], Mu n Ω ≃* Mu n Ω')
    (hβ : ∀ (n : ℕ) [NeZero n] (z : ZHatOne (F D) Ω),
      ZHatOne.proj (kIdx D' n) (β z) = βn n (ZHatOne.proj (kIdx D n) z))
    (hdeg : DegOneChernPreserved hH hk hτ hH' hk' hτ' hgen hgen' αX βn)
    (i : cuspInertia D X eL hH U W₀) :
    CuspCentral.cuspInertiaZHatEquiv hk' hτ' hgen' V hVy hW₁ hW₁V hπW' hπ'
        (inertiaEquiv αU.toMulEquiv hI i) =
      β (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U hπW hπ i) :=
  (cuspInertiaZHatEquiv_map_iff hk hτ hk' hτ' hgen hUx hW₀ hW₀U hπW hπ hgen' hVy hW₁ hW₁V hπW'
    hπ' αU αX hfill hI β βn hβ).2 hdeg i

include hk hτ hk' hτ' in
/-- **[GalSect] Thm. 4.3 (Rigidity of cuspidal geometric decomposition groups)**, one-point
complements, with only `α_U : Δ_U ≃ₜ* Δ_V`, `α_U(I_x) = I_y` and `β : μ_Ẑ ≅ μ_Ẑ` given: the
filled isomorphism `α_X = fillEquiv` is induced, and [AbsAnab] Lemma 2.5(ii) enters as
`DegOneChernPreserved` for it (debt). -/
theorem rigidity_cuspInertia_of_map (hgen : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set X)ᶜ = {x}) (hW₀ : IsCentredOn D X eL ⊤ W₀)
    (hW₀U : ¬ IsCentredOn D X eL U W₀) (hπW : W₀.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω))
    (hgen' : 0 < (curveGenus k' Y).toNat)
    (hVy : (V : Set Y)ᶜ = {y}) (hW₁ : IsCentredOn D' Y eL' ⊤ W₁)
    (hW₁V : ¬ IsCentredOn D' Y eL' V W₁) (hπW' : W₁.valuation ((π' : F D') : Ω') < 1)
    (hπ' : ∀ f ∈ F D', W₁.valuation f < 1 → W₁.valuation f ≤ W₁.valuation ((π' : F D') : Ω'))
    (αU : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
      π₁ᵉᵗ(specPoint D'.L Ω' ≫ genericL D' Y eL' V))
    (hI : (cuspInertia D X eL hH U W₀).map αU.toMulEquiv.toMonoidHom =
      cuspInertia D' Y eL' hH' V W₁)
    (β : ZHatOne (F D) Ω ≃* ZHatOne (F D') Ω') (βn : ∀ (n : ℕ) [NeZero n], Mu n Ω ≃* Mu n Ω')
    (hβ : ∀ (n : ℕ) [NeZero n] (z : ZHatOne (F D) Ω),
      ZHatOne.proj (kIdx D' n) (β z) = βn n (ZHatOne.proj (kIdx D n) z))
    (hdeg : DegOneChernPreserved hH hk hτ hH' hk' hτ' hgen hgen'
      (fillEquiv hk hτ hk' hτ' hUx hW₀ hW₀U hVy hW₁ hW₁V αU hI) βn)
    (i : cuspInertia D X eL hH U W₀) :
    CuspCentral.cuspInertiaZHatEquiv hk' hτ' hgen' V hVy hW₁ hW₁V hπW' hπ'
        (inertiaEquiv αU.toMulEquiv hI i) =
      β (CuspCentral.cuspInertiaZHatEquiv hk hτ hgen U hUx hW₀ hW₀U hπW hπ i) :=
  rigidity_cuspInertia hk hτ hk' hτ' hgen hUx hW₀ hW₀U hπW hπ hgen' hVy hW₁ hW₁V hπW' hπ' αU _
    (fun γ ↦ (fillEquiv_fillX hk hτ hk' hτ' hUx hW₀ hW₀U hVy hW₁ hW₁V αU hI γ).symm) hI β βn hβ
    hdeg i

end TwoCurves

end CurvesJacobian.CuspRigidity
