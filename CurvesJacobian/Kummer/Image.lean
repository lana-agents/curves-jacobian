/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.MiddleExact

/-!
# [AbsTopIII] Prop. 1.6(iii): the exact sequence and the image of `Γ(U, 𝒪^×)`; the group `P_U`

Setting of `Kummer/MiddleExact.lean` (`D : GaloisData k t`, `Π_U = Pi D`, `M_X = Ẑ(1)`).

The second map of the exact sequence of [AbsTopIII] Prop. 1.6(iii) (T3 l.2001–2012) is the
restriction of a class `η ∈ H¹(Π_U, Ẑ(1))` to the inertia groups: we record it as the family of
evaluations `η(σ)`, `σ ∈ I_W ∩ H`, over all places `W ⊇ k` of `Ω` (`res_W`, the "residues"; for
`σ` with tame character a fixed generator this is the element of `Hom(I_x, M_X) ≅ Ẑ`; for places of
`U` it is trivial). For a unit `u` of `U` the residues of `κ_U(u)` are the orders of `u`
(continuous-kummer-theory `evalTriv_kummerMapZHat`, `exists_inertia_evalTriv_kummerMap_eq`), so

* `CurvesJacobian.Kummer.res D`: the residues, as a homomorphism to `∏_{(W, σ)} Ẑ(1)`;
* `CurvesJacobian.Kummer.PU D`: the classes whose residues are those of some `κ_U(u)`,
  `u ∈ Γ(U, 𝒪^×)`, i.e. the inverse image of the principal divisors supported on the cusps
  ([AbsTopIII] Prop. 1.8, l.2065–2077, `P_U`);
* `CurvesJacobian.Kummer.ker_res`: **exactness in the middle**: `ker(res) = (kˣ)^∧` (with
  `constMapZHat_injective`: exactness on the left);
* `CurvesJacobian.Kummer.PU_eq`, `mem_PU_iff`: **the image statement**:
  `P_U = κ_U(Γ(U, 𝒪^×)) · (kˣ)^∧`.

All under `IsKummerFaithfulJac D` (Kummer-faithfulness for the Jacobian, `Kummer/PicAction.lean`)
and `k` algebraically closed in `F` (`X` geometrically connected).
-/

open KummerTheory Curve AffOrbicurve

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- The places `W ⊇ k` of `Ω` together with an element of `I_W ∩ H`. -/
def InertiaIndex : Type u :=
  {p : ValuationSubring Ω × D.H //
    (∀ x : k, algebraMap k Ω x ∈ p.1) ∧ ((p.2 : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia p.1}

/-- **The residues** `η ↦ (η(σ))_{σ ∈ I_W ∩ H, W ⊇ k}`: restriction to the inertia groups (the
second map of [AbsTopIII] Prop. 1.6(iii)). -/
noncomputable def res : ContH1 (Pi D) (ZHatOne (F D) Ω) →* (InertiaIndex D → ZHatOne (F D) Ω) :=
  MonoidHom.pi fun p => ContH1.evalTriv ((p.1.2 : D.H) : Pi D)
    (pi_inertia_smul_zHatOne p.2.1 p.2.2 (F D))

omit [IsAlgClosed Ω] in
lemma res_apply (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (p : InertiaIndex D) :
    res D η p = ContH1.evalTriv ((p.1.2 : D.H) : Pi D)
      (pi_inertia_smul_zHatOne p.2.1 p.2.2 (F D)) η := rfl

/-- **`P_U`** ([AbsTopIII] Prop. 1.8, l.2065–2077): the classes whose residues are those of the
Kummer class of a unit of `U`, i.e. the inverse image of the principal divisors supported on the
cusps. -/
noncomputable def PU : Subgroup (ContH1 (Pi D) (ZHatOne (F D) Ω)) :=
  ((res D).comp (kummerMapZHat D)).range.comap (res D)

variable {D}

/-- **[AbsTopIII] Prop. 1.6(iii), exactness in the middle**: a class lies in the image of
`(kˣ)^∧` iff all its residues vanish. -/
theorem mem_range_constMapZHat_iff (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    η ∈ (constMapZHat D).range ↔ η ∈ (res D).ker := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    funext p
    exact evalTriv_constMapZHat p.2.1 p.2.2 x
  · intro h
    exact mem_range_constMapZHat hJ hk η fun W hW σ hσ =>
      congrFun ((MonoidHom.mem_ker).1 h) ⟨(W, σ), hW, hσ⟩

/-- **[AbsTopIII] Prop. 1.6(iii)**: `ker(res) = (kˣ)^∧`. -/
theorem ker_res (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    (res D).ker = (constMapZHat D).range := by
  ext η
  exact (mem_range_constMapZHat_iff hJ hk η).symm

/-- **[AbsTopIII] Prop. 1.6(iii), the image of `Γ(U, 𝒪^×)`**: `P_U = κ_U(Γ(U, 𝒪^×)) · (kˣ)^∧`. -/
theorem PU_eq (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    PU D = (kummerMapZHat D).range ⊔ (constMapZHat D).range := by
  ext η
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨v, hv⟩
    have hker : η * (kummerMapZHat D v)⁻¹ ∈ (res D).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hv, MonoidHom.comp_apply, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (mem_range_constMapZHat_iff hJ hk _).2 hker
    exact ⟨_, ⟨v, rfl⟩, _, ⟨x, rfl⟩, by rw [hx, mul_comm η, mul_inv_cancel_left]⟩
  · rintro ⟨a, ⟨v, hv⟩, b, hb, hab⟩
    have hb1 : res D b = 1 := (mem_range_constMapZHat_iff hJ hk b).1 hb
    rw [← hab]
    exact (PU D).mul_mem ⟨v, congrArg (res D) hv⟩ ⟨1, (map_one _).trans hb1.symm⟩

/-- `η ∈ P_U` iff `η = κ_U(v) · c` for a unit `v` of `U` and `c ∈ (kˣ)^∧`. -/
theorem mem_PU_iff (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    η ∈ PU D ↔ ∃ (v : units D) (x : KummerCompletion k),
      η = kummerMapZHat D v * constMapZHat D x := by
  rw [PU_eq hJ hk, Subgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨v, x, rfl⟩
  · rintro ⟨v, x, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, _, ⟨x, rfl⟩, rfl⟩

end CurvesJacobian.Kummer
