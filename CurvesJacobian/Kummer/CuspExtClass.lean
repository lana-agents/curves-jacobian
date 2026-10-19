/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspFill
import Pi1.Surface.H2

/-!
# The class of `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` ([AbsTopIII] Prop. 1.4(ii), second part)

[AbsTopIII] Prop. 1.4(ii) (T3 l.1785–1795): the `E₂`-differential of the Leray spectral sequence
of the central extension `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` sends `1 ∈ Hom(I_x, I_x)` to the
extension class in `H²(Δ_X, I_x) = Hom(M_X, I_x)`, and this class is an isomorphism
`M_X ≅ I_x`. In the group-theoretic model (`Δ_{U_x} = Π̂_{g,1}`, `Δ_X = Π̂_{g,0}`, `g ≥ 1`,
`I_x = ℤ̂` via `k ↦ cᵏ`) we compute the class with finite coefficients: for a finite commutative
group `M` and a continuous `χ : ℤ̂ →* M` (e.g. `ℤ̂ ↠ ℤ/n`), the **pushout** `χ_* Δ^{c-cn}` of the
extension along `χ` is represented by a locally constant cocycle `f` together with a morphism of
extensions `Ψ : Δ^{c-cn} →* M ×_f Π̂_{g,0}` restricting to `χ` on `I_x` (`IsCcnPushout χ f Ψ`).

* `exists_isCcnPushout`: such `(f, Ψ)` exist, with `f` locally constant. The section of
  `Π̂_{g,1} ↠ Π̂_{g,0}` used to define `f` is chosen on a finite level: an open normal subgroup
  `W` with `χ` trivial on the part of `I_x` that `W` meets maps isomorphically (modulo
  `ker χ`) onto the open subgroup `fillHat(W)`, and the section is `W`-equivariant
  (`secCocycle_mul_right`), so `f` is invariant under `fillHat(W) × fillHat(W)`.
* **`relVal_of_isCcnPushout`**: for every such `(f, Ψ)`, the relator value is
  `relVal f = χ(c)⁻¹` (`∏ᵢ [âᵢ, b̂ᵢ] = c⁻¹` in `Δ^{c-cn}`, `commProd_eq_incl_relVal`).
* **`h2Equiv_ccnClass`**: hence under `SurfaceGroup.h2Equiv : H²(Π̂_{g,0}, M) ≃* M` the class
  `ccnClass χ` of the pushout is `χ(c)⁻¹`; it does not depend on the choices
  (`mk_eq_ccnClass`). For `M = ℤ/n` and `χ` the projection the class is a generator, i.e. the
  induced `M_X/n → I_x/n` is an isomorphism; the classes are compatible with change of
  coefficients (`ccnClass_map`), which gives the `ℤ̂`-statement as their limit.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology
open Pi1 Pi1.Profinite Pi1.SurfaceGen Pi1.SurfaceGroup

namespace CurvesJacobian.CuspCentral

/-! ### Cocycles of sections (pure group theory) -/

section SecCocycle

variable {E G M : Type*} [Group E] [Group G] [CommGroup M] {p : E →* G} {ψ : E → M}

/-- The cocycle `(γ, δ) ↦ ψ(s(γ) s(δ) s(γδ)⁻¹)` of a set-theoretic section `s` of `p`. -/
def secCocycle (ψ : E → M) (s : G → E) : G × G → M :=
  fun x ↦ ψ (s x.1 * s x.2 * (s (x.1 * x.2))⁻¹)

variable (hψ : ∀ a ∈ p.ker, ∀ b ∈ p.ker, ψ (a * b) = ψ a * ψ b)
  (hψc : ∀ e, ∀ a ∈ p.ker, ψ (e * a * e⁻¹) = ψ a)
include hψ

lemma psi_one : ψ 1 = 1 := by
  have := hψ 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at this
  exact left_eq_mul.1 this |>.symm ▸ rfl

lemma psi_inv {a : E} (ha : a ∈ p.ker) : ψ a⁻¹ = (ψ a)⁻¹ := by
  have := hψ a ha a⁻¹ (inv_mem ha)
  rw [mul_inv_cancel, psi_one hψ] at this
  exact eq_inv_of_mul_eq_one_right this.symm

variable {s : G → E} (hs : ∀ γ, p (s γ) = γ)
include hs

omit hψ in
lemma sec_mem_ker (γ δ : G) : s γ * s δ * (s (γ * δ))⁻¹ ∈ p.ker := by
  simp [hs]

include hψc in
theorem secCocycle_mem : secCocycle ψ s ∈ TrivCocycle G M := fun a b c ↦ by
  simp only [secCocycle]
  have hk := sec_mem_ker hs
  rw [mul_comm, ← hψ _ (hk a b) _ (hk _ c), ← hψc (s a) _ (hk b c),
    ← hψ _ (p.normal_ker.conj_mem _ (hk b c) _) _ (hk a _)]
  congr 1
  simp only [mul_assoc]
  group

include hψc in
/-- The morphism of extensions `E →* M ×_f G`, `e ↦ (ψ(e s(p e)⁻¹), p e)`. -/
def secTwist : E →* Twist (⟨secCocycle ψ s, secCocycle_mem hψ hψc hs⟩ : TrivCocycle G M) where
  toFun e := ⟨ψ (e * (s (p e))⁻¹), p e⟩
  map_one' := by
    ext
    · change ψ (1 * (s (p 1))⁻¹) = (ψ (s 1 * s 1 * (s (1 * 1))⁻¹))⁻¹
      have h1 : s 1 ∈ p.ker := by simp [hs]
      rw [map_one, one_mul, mul_one, mul_inv_cancel_right, psi_inv hψ h1]
    · exact map_one p
  map_mul' e e' := by
    ext
    · change ψ (e * e' * (s (p (e * e')))⁻¹) =
        ψ (e * (s (p e))⁻¹) * ψ (e' * (s (p e'))⁻¹) *
          ψ (s (p e) * s (p e') * (s (p e * p e'))⁻¹)
      have ha : e * (s (p e))⁻¹ ∈ p.ker := by simp [hs]
      have ha' : e' * (s (p e'))⁻¹ ∈ p.ker := by simp [hs]
      rw [← hψc (s (p e)) _ ha', ← hψ _ ha _ (p.normal_ker.conj_mem _ ha' _),
        ← hψ _ (p.ker.mul_mem ha (p.normal_ker.conj_mem _ ha' _)) _ (sec_mem_ker hs _ _), map_mul]
      congr 1
      group
    · exact map_mul p e e'

include hψc in
@[simp] lemma secTwist_g (e : E) : (secTwist hψ hψc hs e).g = p e := rfl

include hψc in
lemma secTwist_of_mem_ker {a : E} (ha : a ∈ p.ker) :
    secTwist hψ hψc hs a = Twist.incl (ψ a) := by
  have h1 : s 1 ∈ p.ker := by simp [hs]
  ext
  · change ψ (a * (s (p a))⁻¹) = ψ a * (ψ (s 1 * s 1 * (s (1 * 1))⁻¹))⁻¹
    rw [ha, mul_one, mul_inv_cancel_right, hψ _ ha _ (inv_mem h1), psi_inv hψ h1]
  · exact ha

/-- **Equivariant sections give invariant cocycles.** If `s (γ p(v)) ∈ s(γ) v (V ∩ ker p)` for
`v ∈ V` (a normal subgroup on whose intersection with `ker p` the map `ψ` is trivial), then the
cocycle is invariant under right multiplication by `p(V) × p(V)`. -/
theorem secCocycle_mul_right {V : Subgroup E} [V.Normal] (hV : ∀ a ∈ V ⊓ p.ker, ψ a = 1)
    (hsV : ∀ γ, ∀ v ∈ V, ∃ k ∈ V ⊓ p.ker, s (γ * p v) = s γ * v * k)
    (γ δ : G) {v v' : E} (hv : v ∈ V) (hv' : v' ∈ V) :
    secCocycle ψ s (γ * p v, δ * p v') = secCocycle ψ s (γ, δ) := by
  simp only [secCocycle]
  set w := (s δ)⁻¹ * v * s δ * v'
  have hw : w ∈ V := V.mul_mem (by simpa using ‹V.Normal›.conj_mem v hv (s δ)⁻¹) hv'
  have hpw : γ * p v * (δ * p v') = γ * δ * p w := by simp [w, hs, mul_assoc]
  obtain ⟨k₁, hk₁, h₁⟩ := hsV γ v hv
  obtain ⟨k₂, hk₂, h₂⟩ := hsV δ v' hv'
  obtain ⟨k₃, hk₃, h₃⟩ := hsV (γ * δ) w hw
  set R := s γ * s δ * (s (γ * δ))⁻¹
  set L := s (γ * p v) * s (δ * p v') * (s (γ * p v * (δ * p v')))⁻¹
  have hR : R ∈ p.ker := sec_mem_ker hs _ _
  have hκ : R⁻¹ * L ∈ V ⊓ p.ker := by
    rw [← QuotientGroup.eq_one_iff (N := V ⊓ p.ker)]
    have e₁ : ((k₁ : E) : E ⧸ (V ⊓ p.ker)) = 1 := (QuotientGroup.eq_one_iff _).2 hk₁
    have e₂ : ((k₂ : E) : E ⧸ (V ⊓ p.ker)) = 1 := (QuotientGroup.eq_one_iff _).2 hk₂
    have e₃ : ((k₃ : E) : E ⧸ (V ⊓ p.ker)) = 1 := (QuotientGroup.eq_one_iff _).2 hk₃
    simp only [L, R, hpw, h₁, h₂, h₃, w, QuotientGroup.mk_mul, QuotientGroup.mk_inv, e₁, e₂, e₃,
      mul_one]
    group
  have hL : L = R * (R⁻¹ * L) := by group
  rw [hL, hψ _ hR _ hκ.2, hV _ hκ, mul_one]

/-- **Invariant cocycles are locally constant.** -/
theorem isLocallyConstant_secCocycle [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Subgroup E} [V.Normal] (hV : ∀ a ∈ V ⊓ p.ker, ψ a = 1)
    (hsV : ∀ γ, ∀ v ∈ V, ∃ k ∈ V ⊓ p.ker, s (γ * p v) = s γ * v * k)
    (hVo : IsOpen ((V.map p : Subgroup G) : Set G)) :
    IsLocallyConstant (secCocycle ψ s) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨γ, δ⟩
  refine ⟨{x | γ⁻¹ * x.1 ∈ V.map p ∧ δ⁻¹ * x.2 ∈ V.map p}, ?_, ?_, ?_⟩
  · exact (hVo.preimage (continuous_const.mul continuous_fst)).inter
      (hVo.preimage (continuous_const.mul continuous_snd))
  · simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  · rintro ⟨γ', δ'⟩ ⟨⟨v, hv, hv1⟩, ⟨v', hv', hv2⟩⟩
    have e1 : γ' = γ * p v := by rw [hv1]; group
    have e2 : δ' = δ * p v' := by rw [hv2]; group
    rw [e1, e2]
    exact secCocycle_mul_right hψ hs hV hsV γ δ hv hv'

end SecCocycle

/-- **Equivariant sections exist**: for a surjection `p` and a normal subgroup `V`, there is a
section `s` of `p` with `s (γ p(v)) ∈ s(γ) v (V ∩ ker p)` for `v ∈ V`. -/
theorem exists_sec {E G : Type*} [Group E] [Group G] {p : E →* G} (hp : Function.Surjective p)
    (V : Subgroup E) :
    ∃ s : G → E, (∀ γ, p (s γ) = γ) ∧ ∀ γ, ∀ v ∈ V, ∃ k ∈ V ⊓ p.ker, s (γ * p v) = s γ * v * k := by
  classical
  -- representatives of the cosets of `p(V)`
  let r : G → G := fun γ ↦ Quotient.out (QuotientGroup.mk γ : G ⧸ V.map p)
  have hr (γ : G) : (r γ)⁻¹ * γ ∈ V.map p := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have hrv (γ : G) {v : E} (hv : v ∈ V) : r (γ * p v) = r γ := by
    simp only [r]
    congr 1
    exact (QuotientGroup.eq.2 (by simpa using Subgroup.mem_map_of_mem p hv)).symm
  choose w hwV hw using fun γ ↦ Subgroup.mem_map.1 (hr γ)
  let e := Function.surjInv hp
  refine ⟨fun γ ↦ e (r γ) * w γ, fun γ ↦ ?_, fun γ v hv ↦ ?_⟩
  · simp [e, Function.surjInv_eq hp, hw]
  · refine ⟨v⁻¹ * (w γ)⁻¹ * w (γ * p v), Subgroup.mem_inf.2 ⟨V.mul_mem (V.mul_mem (V.inv_mem hv)
      (V.inv_mem (hwV γ))) (hwV _), ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hw, hw, hrv γ hv]
      group
    · change e (r (γ * p v)) * w (γ * p v) =
        e (r γ) * w γ * v * (v⁻¹ * (w γ)⁻¹ * w (γ * p v))
      rw [hrv γ hv]
      group

/-! ### The pushout of `Δ^{c-cn}_{U_x}` along `χ : ℤ̂ → M` -/

section Pushout

variable {g : ℕ} {M : Type} [CommGroup M]

/-- The topological generator `1 ∈ ℤ̂`; `ccnInertia` sends it to `c`. -/
noncomputable abbrev zhatOne : ZHat :=
  etaFn (GrpCat.of (Multiplicative ℤ)) (Multiplicative.ofAdd (1 : ℤ))

lemma ccnInertia_zhatOne : ccnInertia g zhatOne = (cuspHat g : CcnQuot g) := by
  simp only [ccnInertia, MonoidHom.comp_apply, cuspInertia, completionMap_eta, zpowersHom_apply]
  change ((etaFn (GrpCat.of (SurfaceGroup g 1)) (cusp 0 ^ (1 : ℤ)) : CcnQuot g)) = _
  rw [zpow_one]

/-- `(f, Ψ)` **represents the pushout** of `1 → ℤ̂ → Δ^{c-cn} → Π̂_{g,0} → 1` along `χ`: `Ψ` is a
morphism of extensions `Δ^{c-cn} →* M ×_f Π̂_{g,0}` over `Π̂_{g,0}` restricting to `χ` on `I_x`. -/
def IsCcnPushout (χ : ZHat →* M) (f : TrivCocycle (ProfiniteSurfaceGroup g 0) M)
    (Ψ : CcnQuot g →* Twist f) : Prop :=
  (∀ k, Ψ (ccnInertia g k) = Twist.incl (χ k)) ∧ ∀ e, (Ψ e).g = ccnFill g e

/-- **The relator value of the pushout class is `χ(c)⁻¹`**: the lifts `Ψ(âᵢ), Ψ(b̂ᵢ)` of the
generators of `Π̂_{g,0}` satisfy `∏ᵢ [Ψ(âᵢ), Ψ(b̂ᵢ)] = Ψ(c⁻¹) = χ(c)⁻¹`. -/
theorem relVal_of_isCcnPushout {χ : ZHat →* M} {f : TrivCocycle (ProfiniteSurfaceGroup g 0) M}
    {Ψ : CcnQuot g →* Twist f} (h : IsCcnPushout χ f Ψ) :
    relVal genAhat genBhat f = (χ zhatOne)⁻¹ := by
  apply Twist.incl_injective (f := f)
  let φ : SurfaceGroup g 1 →* CcnQuot g :=
    (QuotientGroup.mk' (ccnKernel g)).comp (eta (GrpCat.of (SurfaceGroup g 1))).hom
  have hc : commProd (fun i ↦ φ (genA i)) (fun i ↦ φ (genB i)) = (ccnInertia g zhatOne)⁻¹ := by
    rw [ccnInertia_zhatOne, ← map_commProd, commProd_genA_genB_one, map_inv]
    rfl
  have hg (x : SurfaceGroup g 1) : (Ψ (φ x)).g = etaFn _ (fillHom g x) := by
    rw [h.2]
    exact fillHat_eta x
  rw [← commProd_eq_incl_relVal commProd_genAhat f (fun i ↦ Ψ (φ (genA i)))
    (fun i ↦ Ψ (φ (genB i))) (fun i ↦ by rw [hg, fillHom_genA])
    (fun i ↦ by rw [hg, fillHom_genB]), ← map_commProd, hc, map_inv, h.1, map_inv]

/-- **The pushout exists**, with a locally constant cocycle (`g ≥ 1`, `M` finite, `χ`
continuous). -/
theorem exists_isCcnPushout [Finite M] (χ : ZHat →* M) (hχ : ∀ m, IsOpen (χ ⁻¹' {m})) :
    ∃ (f : TrivCocycle (ProfiniteSurfaceGroup (g + 1) 0) M) (Ψ : CcnQuot (g + 1) →* Twist f),
      IsLocallyConstant f.1 ∧ IsCcnPushout χ f Ψ := by
  set ι := ccnInertia (g + 1)
  have hι : Function.Injective ι := ccnInertia_injective
  set mk := QuotientGroup.mk' (ccnKernel (g + 1))
  set p := fillHat (g + 1)
  let ψ : ProfiniteSurfaceGroup (g + 1) 1 → M := fun x ↦ χ (Function.invFun ι (mk x))
  have hinv {a} (ha : a ∈ p.ker) : ι (Function.invFun ι (mk a)) = mk a := by
    have : mk a ∈ ι.range := by
      rw [← map_cuspKernel_eq_range_ccnInertia]
      exact ⟨a, (ker_fillHat _) ▸ ha, rfl⟩
    exact Function.invFun_eq this
  have hψ : ∀ a ∈ p.ker, ∀ b ∈ p.ker, ψ (a * b) = ψ a * ψ b := fun a ha b hb ↦ by
    change χ (Function.invFun ι (mk (a * b))) =
      χ (Function.invFun ι (mk a)) * χ (Function.invFun ι (mk b))
    rw [← map_mul χ]
    congr 1
    apply hι
    rw [map_mul ι, hinv ha, hinv hb, hinv (p.ker.mul_mem ha hb), map_mul]
  have hψc : ∀ e, ∀ a ∈ p.ker, ψ (e * a * e⁻¹) = ψ a := fun e a ha ↦ by
    have hm : mk (e * a * e⁻¹) = mk a := by
      simp only [mk, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← mk_mul_comm_of_mem ((ker_fillHat _) ▸ ha) e, mul_inv_cancel_right]
    simp only [ψ, hm]
  -- an open normal subgroup on which `ψ` is trivial
  have hCc : IsClosed (mk ⁻¹' (ι '' (χ ⁻¹' {1})ᶜ)) :=
    (((hχ 1).isClosed_compl.isCompact.image (continuous_ccnInertia _)).isClosed).preimage
      continuous_quotient_mk'
  have h1 : (1 : ProfiniteSurfaceGroup (g + 1) 1) ∈ (mk ⁻¹' (ι '' (χ ⁻¹' {1})ᶜ))ᶜ := by
    rintro ⟨k, hk, hk1⟩
    rw [map_one, ← map_one ι] at hk1
    exact hk (by simp [hι hk1])
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hCc.isOpen_compl h1
  set V := W.toSubgroup
  have hV : ∀ a ∈ V ⊓ p.ker, ψ a = 1 := fun a ha ↦ by
    by_contra hne
    exact hW ha.1 ⟨_, hne, hinv ha.2⟩
  have hVo : IsOpen ((V.map p : Subgroup _) : Set (ProfiniteSurfaceGroup (g + 1) 0)) := by
    haveI : Finite (ProfiniteSurfaceGroup (g + 1) 1 ⧸ V) :=
      Subgroup.quotient_finite_of_isOpen _ W.isOpen'
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : (V.map p).FiniteIndex := ⟨fun h0 ↦ Subgroup.FiniteIndex.index_ne_zero (H := V)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_map_dvd V (fillHat_surjective _)))⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map]
    exact ((OpenSubgroup.isClosed W.toOpenSubgroup).isCompact.image
      (continuous_fillHat _)).isClosed
  obtain ⟨s, hs, hsV⟩ := exists_sec (fillHat_surjective (g + 1)) V
  let Ψ₀ := secTwist hψ hψc hs
  have hψ1 : ∀ a ∈ ccnKernel (g + 1), ψ a = 1 := fun a ha ↦ by
    have hmk : mk a = 1 := (QuotientGroup.eq_one_iff _).2 ha
    have : Function.invFun ι (mk a) = 1 := hι (by
      rw [hinv ((ker_fillHat _).symm ▸ ccnKernel_le_cuspKernel ha), hmk, map_one])
    simp only [ψ, this, map_one]
  have hle : ccnKernel (g + 1) ≤ Ψ₀.ker := fun a ha ↦ by
    have ha' : a ∈ p.ker := (ker_fillHat _).symm ▸ ccnKernel_le_cuspKernel ha
    rw [MonoidHom.mem_ker, secTwist_of_mem_ker hψ hψc hs ha', hψ1 a ha, map_one]
  refine ⟨_, QuotientGroup.lift _ Ψ₀ hle,
    isLocallyConstant_secCocycle hψ hs hV hsV hVo, fun k ↦ ?_, fun e ↦ ?_⟩
  · have hk : cuspInertia 0 k ∈ p.ker := by
      rw [ker_fillHat]
      exact inertia_le_cuspKernel _ (by rw [← range_cuspInertia]; exact ⟨k, rfl⟩)
    change Ψ₀ (cuspInertia 0 k) = _
    rw [secTwist_of_mem_ker hψ hψc hs hk]
    exact congrArg (fun x ↦ Twist.incl (χ x)) (Function.leftInverse_invFun hι k)
  · induction e using QuotientGroup.induction_on with
    | H x => rfl

/-! ### The class in `H²(Π̂_{g,0}, M) ≅ M` -/

variable [Finite M]

/-- The trivial action of `Π̂_{g,0}` on `M` (the action of `Δ_X` on `I_x ⊗ M`). -/
noncomputable local instance : MulDistribMulAction (ProfiniteSurfaceGroup g 0) M :=
  trivialAction _ _

/-- A locally constant trivial-action cocycle as an element of `Z²_lc`. -/
def toCocycles {f : TrivCocycle (ProfiniteSurfaceGroup g 0) M} (hf : IsLocallyConstant f.1) :
    H2lc.cocycles (ProfiniteSurfaceGroup g 0) M :=
  ⟨f.1, hf, fun a b d ↦ TrivCocycle.cond f.2 a b d⟩

/-- **The class of the pushout `χ_* Δ^{c-cn}_{U_x}`** in `H²(Π̂_{g,0}, M)`. -/
noncomputable def ccnClass (χ : ZHat →* M) (hχ : ∀ m, IsOpen (χ ⁻¹' {m})) :
    H2lc (ProfiniteSurfaceGroup (g + 1) 0) M :=
  QuotientGroup.mk (toCocycles (exists_isCcnPushout χ hχ).choose_spec.choose_spec.1)

/-- **[AbsTopIII] Prop. 1.4(ii), the class of the extension**: under
`H²(Π̂_{g,0}, M) ≃* M` (relator value) the class of the pushout of
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` along `χ` is `χ(c)⁻¹`. -/
theorem h2Equiv_ccnClass (χ : ZHat →* M) (hχ : ∀ m, IsOpen (χ ⁻¹' {m})) :
    h2Equiv g.succ_pos (fun _ _ ↦ rfl) (ccnClass χ hχ) = (χ zhatOne)⁻¹ := by
  rw [ccnClass, h2Equiv_mk]
  exact relVal_of_isCcnPushout (exists_isCcnPushout χ hχ).choose_spec.choose_spec.2

/-- The class does not depend on the choice of the representing cocycle. -/
theorem mk_eq_ccnClass {χ : ZHat →* M} (hχ : ∀ m, IsOpen (χ ⁻¹' {m}))
    {f : TrivCocycle (ProfiniteSurfaceGroup (g + 1) 0) M} {Ψ : CcnQuot (g + 1) →* Twist f}
    (hf : IsLocallyConstant f.1) (h : IsCcnPushout χ f Ψ) :
    (QuotientGroup.mk (toCocycles hf) : H2lc (ProfiniteSurfaceGroup (g + 1) 0) M) =
      ccnClass χ hχ :=
  (h2Equiv g.succ_pos fun _ _ ↦ rfl).injective (by
    rw [h2Equiv_mk, h2Equiv_ccnClass]
    exact relVal_of_isCcnPushout h)

/-- **Compatibility with change of coefficients** (so the classes for `M = ℤ/n` form a compatible
system, the `ℤ̂`-coefficient statement). -/
theorem h2Equiv_ccnClass_comp {M' : Type} [CommGroup M'] [Finite M'] (ρ : M →* M')
    (χ : ZHat →* M) (hχ : ∀ m, IsOpen (χ ⁻¹' {m})) (hρχ : ∀ m, IsOpen ((ρ.comp χ) ⁻¹' {m})) :
    h2Equiv g.succ_pos (fun _ _ ↦ rfl) (ccnClass (ρ.comp χ) hρχ) =
      ρ (h2Equiv g.succ_pos (fun _ _ ↦ rfl) (ccnClass χ hχ)) := by
  rw [h2Equiv_ccnClass, h2Equiv_ccnClass, map_inv, MonoidHom.comp_apply]

/-- `ℤ̂ ↠ ℤ/n`, `1 ↦ 1`. -/
noncomputable def zmodChar (n : ℕ) [NeZero n] : ZHat →* Multiplicative (ZMod n) :=
  liftFinite (zpowersHom _ (Multiplicative.ofAdd 1))

lemma zmodChar_zhatOne (n : ℕ) [NeZero n] : zmodChar n zhatOne = Multiplicative.ofAdd 1 := by
  rw [zmodChar, liftFinite_eta, zpowersHom_apply]
  change Multiplicative.ofAdd (1 : ZMod n) ^ (1 : ℤ) = _
  rw [zpow_one]

lemma isOpen_zmodChar_fiber (n : ℕ) [NeZero n] (m : Multiplicative (ZMod n)) :
    IsOpen (zmodChar n ⁻¹' {m}) :=
  isOpen_liftFinite_fiber _ m

/-- **The class mod `n` is a generator**: `H²(Π̂_{g,0}, ℤ/n) ≃ ℤ/n` sends the class of
`Δ^{c-cn}_{U_x} / n I_x` to `-1`; i.e. the induced map `M_X / n → I_x / n` is an isomorphism. -/
theorem h2Equiv_ccnClass_zmod (n : ℕ) [NeZero n] :
    h2Equiv g.succ_pos (fun _ _ ↦ rfl) (ccnClass (zmodChar n) (isOpen_zmodChar_fiber n)) =
      Multiplicative.ofAdd (-1) := by
  rw [h2Equiv_ccnClass, zmodChar_zhatOne]
  rfl

end Pushout

end CurvesJacobian.CuspCentral
