/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.DeltaAbDuality
import CurvesJacobian.Kummer.TSectionPlace
import CurvesJacobian.Kummer.KummerFaithful

/-!
# `D` is principal iff `η_D = 0` ([AbsTopIII] Prop. 1.6(ii), [Cusp] Prop. 2.3(i))

Galois model `D : GaloisData k t` of a proper curve `X/k` (`char k = 0`), `F k̄ = F (baseChange D)`
the function field of `X_{k̄}`, `J(k̄) = Pic⁰(F k̄)`, `Δ_X^{ab} = DeltaAb D`.

* `placeOf x`: the place of `F k̄` below the place `A` of a rational point `x : RatPoint D`
  (`RatPoint.comap_ne_top`), and `omegaPlace x : OmegaPlace (placeOf x)` (`A` itself, residue
  field `k̄` by `kbarEquiv`);
* **`kCharAb_diffFun`**: the Kummer–Weil identity at rational points: there is `z` with
  `n z = [x − y]` such that `χ_a([t_x − t_y](g)) = e_n(a, g z − z)` for all `g ∈ G_k`
  (`exists_kummer_weil` with `τ_x ∈ D_{A_x}`, `τ_y ∈ D_{A_y}` lifting `g`, `tSection_hToGk`);
* `ratDiv f`: the divisor `∑ nᵢ xᵢ` of `F k̄`; **`eta_eq_one_iff`**: for `deg f = 0`,
  `η_D = 0 ⟺ [D] = 0` in `Pic(F k̄)`, given `IsKummerFaithfulJac D`, divisibility of `Pic⁰(F k̄)`
  and perfectness of the Weil pairing;
* **`eta_eq_one_iff_curve`**: the same for the Galois model `curveGaloisData k hτ` of a curve with
  a `k`-point over a Kummer-faithful field `k` (all hypotheses discharged:
  `isKummerFaithfulJac_of_isKummerFaithful`, `exists_nsmul_eq_jacPsi`,
  `weilDual_bijective_baseChange`) — [AbsTopIII] Prop. 1.6(ii) (T3 l.1993–2000) in the form of
  [Cusp] Prop. 2.3(i) (txt l.2077–2104).

Proof ([Cusp] l.2084–2102, "general nonsense"): `η_D mod N` corresponds under
`Δ_X^{ab}/N ≅ Hom(J[N], μ_N) ≅ J[N]` (`kDual_surjective`, `weilDual_bijective_baseChange`) to
the Kummer cocycle `g ↦ g z − z` of `[D] = N z`. If `η_D = 0`, this cocycle is a coboundary for
every `N`, so `[D] ∈ ⋂_N N · J(k̄)^{G_k} = 0` (`IsKummerFaithfulJac`). If `[D] = 0`, the cocycle
of `η_D` is a coboundary modulo `⋂_a ker χ_a` for every `N`, hence a coboundary
(`ContH1.mk_eq_one_of_forall_mem`, `iInf_kerAb_eq_bot`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Kummer

universe u

section Generic

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

lemma nsmul_eq_zero_of_mem_picTorsion {n : ℕ} {a : Pic κ K} (ha : a ∈ picTorsion κ K n) :
    n • a = 0 :=
  ha

lemma deg_mk_single_sub_single (P Q : Place κ K) :
    Pic.deg κ K (QuotientAddGroup.mk (Finsupp.single P 1 - Finsupp.single Q 1)) = 0 := by
  rw [Pic.deg_mk, Divisor.deg_sub, Divisor.deg_single, Divisor.deg_single, Place.deg_eq_one,
    Place.deg_eq_one, sub_self]

end Generic

section General

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

/-! ### The action of `H` on `J(k̄)` -/

lemma autF_inv (h : D.H) : autF D h⁻¹ = (autF D h)⁻¹ :=
  Subtype.ext (RingEquiv.ext fun _ => rfl)

lemma picMap_picMap_inv {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [PerfectField κ]
    [IsFunctionField κ K] (τ : constAut κ K) (x : Pic κ K) : picMap τ (picMap τ⁻¹ x) = x := by
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [picMap_mk, picMap_mk]
  congr 1
  ext P
  rw [divMap_apply, divMap_apply, ← placeMap_mul, inv_inv, mul_inv_cancel, placeMap_one]

lemma picAct_picAct_inv (h : D.H) (x : Pic (kbar k Ω) (F (baseChange D))) :
    picAct D h (picAct D h⁻¹ x) = x := by
  change picMap (autF D h) (picMap (autF D h⁻¹) x) = x
  rw [autF_inv]
  exact picMap_picMap_inv _ x

/-- `h ∈ H` acts on `F k̄` only through its image in `G_k`. -/
lemma autF_eq_of_hToGk_eq {h h' : D.H} (hh : hToGk D h = hToGk D h') : autF D h = autF D h' := by
  refine Subtype.ext (RingEquiv.ext fun x => Subtype.ext ?_)
  change (h : Ω ≃ₐ[K₀ k t] Ω) x = (h' : Ω ≃ₐ[K₀ k t] Ω) x
  have h1 : hToGk D (h'⁻¹ * h) = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  have h2 := fixes_F_baseChange D (h'⁻¹ * h).2 ((hToGk_eq_one_iff D _).1 h1) x.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h2
  have h3 := congrArg (h' : Ω ≃ₐ[K₀ k t] Ω) h2
  rwa [AlgEquiv.apply_symm_apply] at h3

lemma picAct_eq_of_hToGk_eq {h h' : D.H} (hh : hToGk D h = hToGk D h') :
    picAct D h = picAct D h' := by
  change picMap (autF D h) = picMap (autF D h')
  rw [autF_eq_of_hToGk_eq hh]

/-! ### Places of `F k̄` from rational points -/

/-- The place of `Ω` of a rational point does not contain `F k̄`. -/
lemma RatPoint.comap_ne_top (x : RatPoint D) :
    x.A.comap (algebraMap (F (baseChange D)) Ω) ≠ ⊤ := by
  intro htop
  have hall : ∀ y : F (baseChange D), (y : Ω) ∈ x.A := fun y => by
    have : y ∈ x.A.comap (algebraMap (F (baseChange D)) Ω) := by rw [htop]; trivial
    exact this
  have htF : t ∈ F D := (F D).algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
  have ht : t ∈ x.A := hall ⟨t, le_F_baseChange D htF⟩
  obtain ⟨c, hc⟩ := x.hrat ⟨t, htF⟩ ht
  set u := t - algebraMap k Ω c with hu
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hu, sub_eq_zero] at h0
    exact D.transcendental (h0 ▸ isAlgebraic_algebraMap c)
  have huA : u ∈ x.A := sub_mem ht (x.hk c)
  have hum : (⟨u, huA⟩ : x.A) ∈ maximalIdeal x.A := by
    rw [← residue_eq_zero_iff]
    have : residue x.A ⟨u, huA⟩ =
        residue x.A ⟨t, ht⟩ - residue x.A ⟨algebraMap k Ω c, x.hk c⟩ := by
      rw [← map_sub]; rfl
    rw [this, hc, RatPoint.hkres, sub_self]
  have huF : u ∈ F (baseChange D) :=
    sub_mem (le_F_baseChange D htF)
      (kbar_le_F_baseChange D (algebraMap k (kbar k Ω) c).2)
  have hui : u⁻¹ ∈ x.A := hall ⟨u⁻¹, inv_mem huF⟩
  have hunit : IsUnit (⟨u, huA⟩ : x.A) :=
    isUnit_iff_exists_inv.2 ⟨⟨u⁻¹, hui⟩, Subtype.ext (mul_inv_cancel₀ hu0)⟩
  exact (mem_maximalIdeal _).1 hum hunit

/-- **The place `x_{k̄}` of `F k̄` below the place of a rational point.** -/
noncomputable def placeOf (x : RatPoint D) : Place (kbar k Ω) (F (baseChange D)) :=
  ⟨x.A.comap (algebraMap (F (baseChange D)) Ω), x.comap_ne_top, fun c => kbar_mem x.A x.hk c⟩

lemma mem_placeOf {x : RatPoint D} {g : F (baseChange D)} :
    g ∈ (placeOf x).1 ↔ (g : Ω) ∈ x.A := Iff.rfl

/-- **The place `A` of a rational point as a place of `Ω` over `x_{k̄}` with residue field
`k̄`.** -/
noncomputable def omegaPlace (x : RatPoint D) : OmegaPlace (Ω := Ω) (placeOf x) where
  W := x.A
  liesOver _ := Iff.rfl
  bijective := (kbarEquiv x.A x.hk x.hkres).bijective

/-- Elements of the decomposition group stabilise `A`. -/
lemma decomp_apply_mem_iff {A : ValuationSubring Ω} {σ : Ω ≃ₐ[F D] Ω} (hσ : σ • A = A) (β : Ω) :
    σ β ∈ A ↔ β ∈ A := by
  calc σ β ∈ A ↔ σ β ∈ σ • A := by rw [hσ]
    _ ↔ β ∈ A := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change σ⁻¹ (σ β) ∈ A ↔ _
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- `τ ∈ D_A` fixes the place `x_{k̄}` of `F k̄`. -/
lemma placeMap_autF_placeOf (x : RatPoint D) (τ : x.A.decompositionSubgroup (F D)) :
    placeMap (autF D (ofGalF D τ.1)) (placeOf x) = placeOf x := by
  ext g
  rw [mem_placeMap, mem_placeOf, mem_placeOf]
  change ((ofGalF D τ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).symm g ∈ x.A ↔ _
  rw [← decomp_apply_mem_iff τ.2, ← ofGalF_apply, AlgEquiv.apply_symm_apply]

/-! ### The Kummer–Weil identity at rational points -/

variable [Fact (Function.Surjective (piJ1ToGk D))]

/-- `[t_x − t_y](g) = [τ_x τ_y⁻¹]` for `τ_x ∈ D_{A_x}`, `τ_y ∈ D_{A_y}` over `g`. -/
lemma diffFun_tSection (x y : RatPoint D) (τx : x.A.decompositionSubgroup (F D))
    (τy : y.A.decompositionSubgroup (F D)) (hxy : hToGk D (ofGalF D τx.1) = hToGk D (ofGalF D τy.1))
    (hmem : ofGalF D τx.1 * (ofGalF D τy.1)⁻¹ ∈ deltaTilde D) :
    diffFun (tSection x) (tSection y) (hToGk D (ofGalF D τx.1)) =
      deltaTildeToAb ⟨_, hmem⟩ := by
  apply deltaAbToPiJ1_injective D
  have e1 := tSection_hToGk x τx
  have e2 := tSection_hToGk y τy
  rw [← hxy] at e2
  rw [deltaAbToPiJ1_diffFun, e1, e2, decompToPiX_apply, decompToPiX_apply]
  change _ = deltaAbToPiJ1 D (deltaAbMk D _)
  rw [deltaAbToPiJ1_deltaAbMk, ← map_inv, ← map_mul]
  rfl

set_option maxHeartbeats 400000 in
-- the semilinear actions on `F k̄`, `Pic(F k̄)` and `Ω` are unfolded in several defeq checks
/-- **The Kummer–Weil identity at rational points** ([Cusp] Prop. 2.3(i), `η_{x − y} mod n`):
there is `z ∈ J(k̄)` with `n z = [x − y]` such that for every `h ∈ H` (over `g ∈ G_k`) and every
`a ∈ J(k̄)[n]`, `χ_a([t_x − t_y](g)) = e_n(a, h z − z)`. -/
theorem kCharAb_diffFun {n : ℕ} [NeZero n] (x y : RatPoint D)
    (hdiv : ∃ z : Pic (kbar k Ω) (F (baseChange D)),
      n • z = QuotientAddGroup.mk (Finsupp.single (placeOf x) 1 - Finsupp.single (placeOf y) 1))
    (hperf : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := n))) :
    ∃ z : Pic (kbar k Ω) (F (baseChange D)),
      n • z = QuotientAddGroup.mk (Finsupp.single (placeOf x) 1 - Finsupp.single (placeOf y) 1) ∧
      ∀ h : D.H, ∃ hz : picAct D h z - z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n,
        ∀ a, ((kCharAb a (diffFun (tSection x) (tSection y) (hToGk D h)) : (kbar k Ω)ˣ) :
          kbar k Ω) = weilPairing n a ⟨_, hz⟩ := by
  obtain ⟨z, hz, H⟩ := exists_kummer_weil (omegaPlace x) (omegaPlace y) hdiv hperf
  refine ⟨z, hz, fun h => ?_⟩
  obtain ⟨τx, hτx⟩ := exists_hToGk_eq x (hToGk D h)
  obtain ⟨τy, hτy⟩ := exists_hToGk_eq y (hToGk D h)
  have hxy : autF D (ofGalF D τy.1) = autF D (ofGalF D τx.1) :=
    autF_eq_of_hToGk_eq (hτy.trans hτx.symm)
  have hσx := placeMap_autF_placeOf x τx
  have hσy : placeMap (autF D (ofGalF D τx.1)) (placeOf y) = placeOf y := by
    rw [← hxy]; exact placeMap_autF_placeOf y τy
  have hact : picAct D h = picMap (autF D (ofGalF D τx.1)) := picAct_eq_of_hToGk_eq hτx.symm
  have key := fun a => H (autF D (ofGalF D τx.1)) hσx hσy
    ((ofGalF D τx.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv
    ((ofGalF D τy.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (fun g => rfl)
    (fun g => by rw [← hxy]; rfl)
    (fun β => by
      change (ofGalF D τx.1 : Ω ≃ₐ[K₀ k t] Ω) β ∈ x.A ↔ _
      rw [ofGalF_apply]; exact decomp_apply_mem_iff τx.2 β)
    (fun β => by
      change (ofGalF D τy.1 : Ω ≃ₐ[K₀ k t] Ω) β ∈ y.A ↔ _
      rw [ofGalF_apply]; exact decomp_apply_mem_iff τy.2 β)
    a (kRep n a) (kRoot a) (kRoot_pow a)
  obtain ⟨hz0, -⟩ := key 0
  have hz1 : picAct D h z - z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n := by
    rw [hact]; exact hz0
  refine ⟨hz1, fun a => ?_⟩
  obtain ⟨hz2, hval⟩ := key a
  have hmem : ofGalF D τx.1 * (ofGalF D τy.1)⁻¹ ∈ deltaTilde D := by
    change hToGk D _ = 1
    rw [map_mul, map_inv, hτx, hτy, mul_inv_cancel]
  have hdiff := diffFun_tSection x y τx τy (hτx.trans hτy.symm) hmem
  rw [hτx] at hdiff
  rw [hdiff, kCharAb_deltaTildeToAb]
  apply Subtype.ext
  rw [coe_kChar]
  change ((ofGalF D τx.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω)
    (((ofGalF D τy.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).symm (kRoot a)) / kRoot a = _
  rw [show ((ofGalF D τx.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω)
    (((ofGalF D τy.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).symm (kRoot a)) =
      ((ofGalF D τx.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv
        (((ofGalF D τy.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv.symm (kRoot a)) from rfl, hval]
  have e : (⟨picMap (autF D (ofGalF D τx.1)) z - z, hz2⟩ :
      picTorsion (kbar k Ω) (F (baseChange D)) n) = ⟨picAct D h z - z, hz1⟩ :=
    Subtype.ext (show picMap _ z - z = picAct D h z - z by rw [hact])
  rw [e]
  rfl

/-! ### `η_D` and the Kummer cocycle of `[D]` -/

/-- **The divisor `∑ nᵢ xᵢ` of `X_{k̄}`** for `f = ∑ nᵢ [xᵢ]` supported on rational points. -/
noncomputable def ratDiv (f : RatPoint D →₀ ℤ) : Divisor (kbar k Ω) (F (baseChange D)) :=
  Finsupp.mapDomain placeOf f

/-- The cocycle `σ ↦ ∏ [t_{xᵢ} − t_{x₀}](σ)^{nᵢ}` representing `η_D` (`etaDiv_eq_mk`). -/
noncomputable def etaCocycle (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D) :
    ContH1.cocycles (Gk k Ω) (DeltaAb D) :=
  f.prod fun x m => diffCocycle (tSection x) (tSection x₀) ^ m

lemma etaDiv_eq_mk (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D) :
    etaDiv f x₀ = ContH1.mk (etaCocycle f x₀) := by
  rw [etaDiv, etaWith, etaCocycle, map_finsuppProd]
  simp only [map_zpow]
  rfl

lemma etaCocycle_apply (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D) (g : Gk k Ω) :
    (etaCocycle f x₀ : Gk k Ω → DeltaAb D) g =
      f.prod fun x m => diffFun (tSection x) (tSection x₀) g ^ m := by
  let ev : ContH1.cocycles (Gk k Ω) (DeltaAb D) →* DeltaAb D :=
    (Pi.evalMonoidHom (fun _ => DeltaAb D) g).comp (ContH1.cocycles _ _).subtype
  change ev (etaCocycle f x₀) = _
  rw [etaCocycle, map_finsuppProd]
  simp only [map_zpow]
  rfl

variable {n : ℕ} [NeZero n]

/-- `b ↦ e_n(a, b)` as a homomorphism `J[n] → k̄ˣ`. -/
noncomputable def weilR (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    picTorsion (kbar k Ω) (F (baseChange D)) n →+ Additive (kbar k Ω)ˣ where
  toFun b := Additive.ofMul (Units.mk0 (weilPairing n a b) (weilPairing_ne_zero a b))
  map_zero' := by
    apply Additive.toMul.injective
    exact Units.ext (weilPairing_zero_right a)
  map_add' b b' := by
    apply Additive.toMul.injective
    exact Units.ext (weilPairing_add_right a b b')

@[simp]
lemma coe_toMul_weilR (a b : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    ((Additive.toMul (weilR a b) : (kbar k Ω)ˣ) : kbar k Ω) = weilPairing n a b := rfl

lemma weilDual_apply_ofAdd (a b : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    weilDual b (Multiplicative.ofAdd a) = Additive.toMul (weilR a b) := rfl

/-- If `χ_a(m) = e_n(a, w)` for all `a`, then `χ_a(g m) = e_n(a, h w)` for `h` over `g`. -/
lemma kCharAb_smul_eq {m : DeltaAb D} {w : picTorsion (kbar k Ω) (F (baseChange D)) n}
    (hw : ∀ a, kCharAb a m = Additive.toMul (weilR a w)) (h : D.H)
    (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    kCharAb a (hToGk D h • m) =
      Additive.toMul (weilR a ⟨picAct D h w, picAct_mem_picTorsion D h w.2⟩) := by
  obtain ⟨a', rfl⟩ : ∃ a' : picTorsion (kbar k Ω) (F (baseChange D)) n,
      (⟨picAct D h a', picAct_mem_picTorsion D h a'.2⟩ :
        picTorsion (kbar k Ω) (F (baseChange D)) n) = a :=
    ⟨⟨picAct D h⁻¹ a, picAct_mem_picTorsion D h⁻¹ a.2⟩, Subtype.ext (picAct_picAct_inv h a)⟩
  apply Units.ext
  apply Subtype.ext
  rw [kCharAb_smul h a' m, hw a', coe_toMul_weilR, coe_toMul_weilR]
  exact (weilPairing_picAct D h a' w).symm

/-- `∑ mₓ (P(x) − P₀) = ∑ mₓ P(x)` for `∑ mₓ = 0`. -/
lemma _root_.Finsupp.sum_zsmul_single_sub {ι α : Type*} (f : ι →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (P : ι → α) (a₀ : α) :
    (f.sum fun x m => m • (Finsupp.single (P x) (1 : ℤ) - Finsupp.single a₀ 1)) =
      Finsupp.mapDomain P f := by
  simp only [smul_sub, Finsupp.smul_single_one]
  rw [Finsupp.sum_sub]
  have h2 : (f.sum fun _ m => Finsupp.single a₀ m) = Finsupp.single a₀ (f.sum fun _ m => m) := by
    rw [Finsupp.sum, Finsupp.sum, Finsupp.single_finsetSum]
  rw [h2, hf, Finsupp.single_zero, sub_zero]
  rfl

/-- `↑(∑ mₓ ⟨φ zₓ − zₓ⟩) = φ(∑ mₓ zₓ) − ∑ mₓ zₓ` in a subgroup. -/
lemma _root_.AddSubgroup.coe_finsuppSum_sub {M ι : Type*} [AddCommGroup M] (S : AddSubgroup M)
    (φ : M →+ M) (f : ι →₀ ℤ) (z : ι → M) (hz : ∀ i, φ (z i) - z i ∈ S) :
    (f.sum fun i m => m • (⟨φ (z i) - z i, hz i⟩ : S)).1 =
      φ (f.sum fun i m => m • z i) - f.sum fun i m => m • z i := by
  simp only [Finsupp.sum, AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul, map_sum, map_zsmul,
    smul_sub, Finset.sum_sub_distrib]

/-- `n (∑ mₓ zₓ) = [D]` when `n zₓ = [x − x₀]`. -/
lemma nsmul_sum_eq_ratDiv (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint D) (zx : RatPoint D → Pic (kbar k Ω) (F (baseChange D)))
    (hzx : ∀ x, n • zx x =
      QuotientAddGroup.mk (Finsupp.single (placeOf x) 1 - Finsupp.single (placeOf x₀) 1)) :
    n • (f.sum fun x m => m • zx x) = QuotientAddGroup.mk (ratDiv f) := by
  rw [Finsupp.smul_sum]
  simp only [smul_comm n, hzx]
  rw [ratDiv, ← Finsupp.sum_zsmul_single_sub f hf placeOf (placeOf x₀), Finsupp.sum, Finsupp.sum,
    QuotientAddGroup.mk_sum]
  simp only [QuotientAddGroup.mk_zsmul]

/-- The Kummer characters of the cocycle of `η_D`, given the Kummer–Weil data at each point. -/
lemma kCharAb_etaCocycle (f : RatPoint D →₀ ℤ) (x₀ : RatPoint D) (h : D.H)
    (zx : RatPoint D → Pic (kbar k Ω) (F (baseChange D)))
    (hzmem : ∀ x, picAct D h (zx x) - zx x ∈ picTorsion (kbar k Ω) (F (baseChange D)) n)
    (hval : ∀ x a, ((kCharAb a (diffFun (tSection x) (tSection x₀) (hToGk D h)) :
      (kbar k Ω)ˣ) : kbar k Ω) = weilPairing n a ⟨_, hzmem x⟩)
    (a : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    kCharAb a ((etaCocycle f x₀ : Gk k Ω → DeltaAb D) (hToGk D h)) =
      Additive.toMul (weilR a (f.sum fun x m => m •
        (⟨picAct D h (zx x) - zx x, hzmem x⟩ : picTorsion (kbar k Ω) (F (baseChange D)) n))) := by
  rw [etaCocycle_apply, map_finsuppProd, Finsupp.prod, map_finsuppSum, Finsupp.sum, toMul_sum]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_zpow, map_zsmul, toMul_zsmul]
  congr 1
  exact Units.ext (Subtype.ext (by rw [hval x a]; rfl))

/-- **`η_D mod n` is the Kummer cocycle of `[D]`**: for `deg D = 0` there is `z` with
`n z = [D]` such that `χ_a(η_D(g)) = e_n(a, h z − z)` for all `h` over `g` and `a ∈ J[n]`. -/
theorem exists_eta_kummer (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint D)
    (hdiv : ∀ x : RatPoint D, ∃ z : Pic (kbar k Ω) (F (baseChange D)),
      n • z = QuotientAddGroup.mk (Finsupp.single (placeOf x) 1 - Finsupp.single (placeOf x₀) 1))
    (hperf : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := n))) :
    ∃ z : Pic (kbar k Ω) (F (baseChange D)), n • z = QuotientAddGroup.mk (ratDiv f) ∧
      ∀ h : D.H, ∃ hz : picAct D h z - z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n,
        ∀ a, kCharAb a ((etaCocycle f x₀ : Gk k Ω → DeltaAb D) (hToGk D h)) =
          Additive.toMul (weilR a ⟨_, hz⟩) := by
  choose zx hzx hzx' using fun x => kCharAb_diffFun (n := n) x x₀ (hdiv x) hperf
  refine ⟨f.sum fun x m => m • zx x, nsmul_sum_eq_ratDiv f hf x₀ zx hzx, fun h => ?_⟩
  choose hzmem hval using fun x => hzx' x h
  have hw := (picTorsion (kbar k Ω) (F (baseChange D)) n).coe_finsuppSum_sub (picAct D h) f zx
    hzmem
  refine ⟨hw ▸ (f.sum fun x m => m • (⟨picAct D h (zx x) - zx x, hzmem x⟩ :
    picTorsion (kbar k Ω) (F (baseChange D)) n)).2, fun a => ?_⟩
  rw [kCharAb_etaCocycle f x₀ h zx hzmem hval a]
  congr 3
  exact Subtype.ext hw

/-! ### The theorem -/

lemma hToGk_surjective_of_fact (g : Gk k Ω) : ∃ h : D.H, hToGk D h = g := by
  obtain ⟨p, hp⟩ := (Fact.out : Function.Surjective (piJ1ToGk D)) g
  obtain ⟨y, rfl⟩ := piXToPiJ1_surjective D p
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨h, hp⟩

lemma deg_eq_zero_of_mem_picTorsion {a : Pic (kbar k Ω) (F (baseChange D))}
    (ha : a ∈ picTorsion (kbar k Ω) (F (baseChange D)) n) : Pic.deg _ _ a = 0 := by
  have h := congrArg (Pic.deg _ _) (show n • a = 0 from ha)
  rw [map_nsmul, map_zero, nsmul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast NeZero.ne n)

/-- `χ^{(n)}_{m a} = (χ^{(nm)}_a)^m` on `Δ_X^{ab}`. -/
lemma kCharAb_ofMul {m : ℕ} [NeZero (n * m)]
    (a : picTorsion (kbar k Ω) (F (baseChange D)) (n * m))
    (ha : m • (a : Pic (kbar k Ω) (F (baseChange D))) ∈ picTorsion (kbar k Ω) (F (baseChange D)) n)
    (δ : DeltaAb D) : kCharAb ⟨_, ha⟩ δ = kCharAb a δ ^ m := by
  obtain ⟨s, rfl⟩ := deltaTildeToAb_surjective δ
  rw [kCharAb_deltaTildeToAb, kCharAb_deltaTildeToAb]
  exact kChar_ofMul a s

/-- **The subgroups `⋂_{a ∈ J[n]} ker χ_a` are directed** (divisibility of `J(k̄)`). -/
lemma kerAb_mul_le
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y) {m : ℕ} (hm : 0 < m) [NeZero (n * m)] :
    kerAb (D := D) (n * m) ≤ kerAb n := by
  intro δ hδ
  rw [mem_kerAb] at hδ ⊢
  intro a
  obtain ⟨a', ha'⟩ := hdivJ m hm a (deg_eq_zero_of_mem_picTorsion a.2)
  have hmem : a' ∈ picTorsion (kbar k Ω) (F (baseChange D)) (n * m) := by
    change (n * m) • a' = 0
    rw [mul_comm, mul_nsmul, ha']
    exact a.2
  have hma : m • ((⟨a', hmem⟩ : picTorsion (kbar k Ω) (F (baseChange D)) (n * m)) :
      Pic (kbar k Ω) (F (baseChange D))) ∈ picTorsion (kbar k Ω) (F (baseChange D)) n := by
    change m • a' ∈ _
    rw [ha']
    exact a.2
  have h1 := kCharAb_ofMul ⟨a', hmem⟩ hma δ
  have h2 : (⟨_, hma⟩ : picTorsion (kbar k Ω) (F (baseChange D)) n) = a := Subtype.ext ha'
  rw [h2, hδ, one_pow] at h1
  exact h1

lemma kerAb_le_of_dvd
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y) {L : ℕ} [NeZero L] (hnL : n ∣ L) :
    kerAb (D := D) L ≤ kerAb n := by
  obtain ⟨m, rfl⟩ := hnL
  exact kerAb_mul_le hdivJ (Nat.pos_of_ne_zero (right_ne_zero_of_mul (NeZero.ne (n * m))))

set_option maxHeartbeats 400000 in
-- the `G_k`-action on `Δ_X^{ab}` and the semilinear action on `J(k̄)` are unfolded in defeq checks
/-- **If the cocycle `c` is a coboundary, `x = n z` is `n` times an invariant class**, where the
Kummer characters of `c` are `e_n(·, h z − z)` (the "only if" direction modulo `n`). -/
lemma exists_mem_picInv_of_coboundary {c : ContH1.cocycles (Gk k Ω) (DeltaAb D)} {m : DeltaAb D}
    (hm : ∀ g, g • m / m = (c : Gk k Ω → DeltaAb D) g) {x z : Pic (kbar k Ω) (F (baseChange D))}
    (hz : n • z = x)
    (hzk : ∀ h : D.H, ∃ hz : picAct D h z - z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n,
      ∀ a, kCharAb a ((c : Gk k Ω → DeltaAb D) (hToGk D h)) = Additive.toMul (weilR a ⟨_, hz⟩))
    (hperf : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := n))) :
    ∃ y ∈ picInv D, n • y = x := by
  obtain ⟨w, hw⟩ := hperf.2 (kDual D n m)
  have hwa : ∀ a, kCharAb a m = Additive.toMul (weilR a w) := fun a => by
    have := DFunLike.congr_fun hw (Multiplicative.ofAdd a)
    rw [kDual_apply, weilDual_apply_ofAdd] at this
    exact this.symm
  refine ⟨z - w, fun h => ?_, ?_⟩
  · obtain ⟨hzh, hzv⟩ := hzk h
    have heq : (⟨picAct D h z - z, hzh⟩ : picTorsion (kbar k Ω) (F (baseChange D)) n) =
        ⟨picAct D h w, picAct_mem_picTorsion D h w.2⟩ - w := by
      apply hperf.1
      refine MonoidHom.ext fun a' => ?_
      obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = a' := ⟨Multiplicative.toAdd a', rfl⟩
      rw [weilDual_apply_ofAdd, weilDual_apply_ofAdd, map_sub, toMul_sub, ← hzv a,
        ← kCharAb_smul_eq hwa h a, ← hwa a, ← hm, map_div]
    have h2 := congrArg Subtype.val heq
    simp only [AddSubgroup.coe_sub] at h2
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 h2
  · have hw0 := nsmul_eq_zero_of_mem_picTorsion w.2
    rw [smul_sub, hz, hw0, sub_zero]

set_option maxHeartbeats 400000 in
-- the `G_k`-action on `Δ_X^{ab}` and the semilinear action on `J(k̄)` are unfolded in defeq checks
/-- **If `n z = 0`, the cocycle `c` is a coboundary modulo `⋂_{a ∈ J[n]} ker χ_a`**, where the
Kummer characters of `c` are `e_n(·, h z − z)` (the "if" direction modulo `n`). -/
lemma exists_coboundary_mod_kerAb [Finite (picTorsion (kbar k Ω) (F (baseChange D)) n)]
    {c : ContH1.cocycles (Gk k Ω) (DeltaAb D)} {z : Pic (kbar k Ω) (F (baseChange D))}
    (hzt : z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n)
    (hzk : ∀ h : D.H, ∃ hz : picAct D h z - z ∈ picTorsion (kbar k Ω) (F (baseChange D)) n,
      ∀ a, kCharAb a ((c : Gk k Ω → DeltaAb D) (hToGk D h)) = Additive.toMul (weilR a ⟨_, hz⟩)) :
    ∃ m : DeltaAb D, ∀ g : Gk k Ω, (c : Gk k Ω → DeltaAb D) g / (g • m / m) ∈ kerAb n := by
  obtain ⟨m, hm⟩ := kDual_surjective (D := D) (n := n) (weilDual ⟨z, hzt⟩)
  have hma : ∀ a, kCharAb a m = Additive.toMul (weilR a ⟨z, hzt⟩) := fun a => by
    have := DFunLike.congr_fun hm (Multiplicative.ofAdd a)
    rw [kDual_apply, weilDual_apply_ofAdd] at this
    exact this
  refine ⟨m, fun g => ?_⟩
  obtain ⟨h, rfl⟩ := hToGk_surjective_of_fact (D := D) g
  obtain ⟨hzh, hzv⟩ := hzk h
  rw [mem_kerAb]
  intro a
  rw [map_div, map_div, hzv a, kCharAb_smul_eq hma h a, hma a, ← toMul_sub, ← toMul_sub,
    ← map_sub, ← map_sub]
  have : (⟨picAct D h z - z, hzh⟩ : picTorsion (kbar k Ω) (F (baseChange D)) n) -
      (⟨picAct D h z, picAct_mem_picTorsion D h hzt⟩ - ⟨z, hzt⟩) = 0 :=
    Subtype.ext (by simp)
  rw [this, map_zero, toMul_zero]

omit [NeZero n] in
lemma directed_kerAb
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y) :
    Directed (· ≥ ·) (fun N : {N : ℕ // 0 < N} =>
      (haveI : NeZero N.1 := ⟨N.2.ne'⟩; kerAb (D := D) N.1)) := by
  intro N M
  haveI : NeZero (N.1 * M.1) := ⟨(Nat.mul_pos N.2 M.2).ne'⟩
  haveI : NeZero N.1 := ⟨N.2.ne'⟩
  haveI : NeZero M.1 := ⟨M.2.ne'⟩
  exact ⟨⟨N.1 * M.1, Nat.mul_pos N.2 M.2⟩, kerAb_le_of_dvd hdivJ (dvd_mul_right _ _),
    kerAb_le_of_dvd hdivJ (dvd_mul_left _ _)⟩

omit [NeZero n] in
/-- **[AbsTopIII] Prop. 1.6(ii) / [Cusp] Prop. 2.3(i) in the Galois model**: a divisor
`D = ∑ nᵢ xᵢ` of degree `0` supported on `k`-rational points is principal (on `X_{k̄}`) iff
`η_D = 0` in `H¹(G_k, Δ_X^{ab})`, given Kummer-faithfulness for the Jacobian
(`IsKummerFaithfulJac D`, J1), divisibility of `Pic⁰(F k̄)` and perfectness of the Weil pairing.
For curves these hypotheses are theorems: `eta_eq_one_iff_curve`. -/
theorem eta_eq_one_iff (hKF : IsKummerFaithfulJac D)
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y)
    (hperf : ∀ (N : ℕ) [NeZero N],
      Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := N)))
    (hfin : ∀ (N : ℕ) [NeZero N], Finite (picTorsion (kbar k Ω) (F (baseChange D)) N))
    (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    eta f = 1 ↔ (QuotientAddGroup.mk (ratDiv f) : Pic (kbar k Ω) (F (baseChange D))) = 0 := by
  by_cases hf0 : f = 0
  · subst hf0
    simp [eta, ratDiv]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hf0
  rw [eta_eq_etaDiv f hf x₀, etaDiv_eq_mk]
  have hdivx : ∀ N : ℕ, 0 < N → ∀ x : RatPoint D, ∃ z : Pic (kbar k Ω) (F (baseChange D)),
      N • z = QuotientAddGroup.mk (Finsupp.single (placeOf x) 1 -
        Finsupp.single (placeOf x₀) 1) := fun N hN x =>
    hdivJ N hN _ (deg_mk_single_sub_single _ _)
  constructor
  · intro h1
    obtain ⟨m, hm⟩ := (ContH1.mk_eq_one_iff _).1 h1
    refine hKF _ fun N hN => ?_
    haveI : NeZero N := ⟨hN.ne'⟩
    obtain ⟨z, hz, hzk⟩ := exists_eta_kummer f hf x₀ (hdivx N hN) (hperf N)
    exact exists_mem_picInv_of_coboundary hm hz hzk (hperf N)
  · intro h1
    refine ContH1.mk_eq_one_of_forall_mem _ (fun N => by
        haveI : NeZero N.1 := ⟨N.2.ne'⟩
        exact isClosed_kerAb) (directed_kerAb hdivJ) iInf_kerAb_eq_bot _ (fun N => ?_)
    obtain ⟨N, hN⟩ := N
    haveI : NeZero N := ⟨hN.ne'⟩
    haveI := hfin N
    obtain ⟨z, hz, hzk⟩ := exists_eta_kummer f hf x₀ (hdivx N hN) (hperf N)
    exact exists_coboundary_mod_kerAb (show N • z = 0 by rw [hz, h1]) hzk

end General

/-! ### Curves over Kummer-faithful fields -/

section Curve

open AlgebraicGeometry Belyi CurvesJacobian.Cusp CategoryTheory

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **[AbsTopIII] Prop. 1.6(ii)** ([Cusp] Prop. 2.3(i)) for a curve `X` with a `k`-point over a
Kummer-faithful field `k` of characteristic `0` (Galois model `curveGaloisData k hτ`): a divisor
`D = ∑ nᵢ xᵢ` of degree `0` supported on `k`-rational points is principal on `X_{k̄}`
(`[D] = 0` in `Pic(F k̄) = Pic(X_{k̄})`) iff `η_D = 0` in `H¹(G_k, Δ_X^{ab})`, i.e. iff the section
`t_D` is `Δ_X`-conjugate to the identity section. -/
theorem eta_eq_one_iff_curve (hk : IsKummerFaithful k) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ (QuotientAddGroup.mk (ratDiv f) :
      Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) = 0 :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  eta_eq_one_iff (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ)
    (fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_baseChange k hτ)
    (fun N _ => finite_picTorsion_baseChange k hτ) f hf

end Curve

end CurvesJacobian.Kummer
