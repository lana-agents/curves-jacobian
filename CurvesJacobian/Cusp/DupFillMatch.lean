/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DupDecomp
import CurvesJacobian.Cusp.Cor38Unique
import CurvesJacobian.Cusp.CandidateLiftX1
import CurvesJacobian.Cusp.BelyiArithChain

/-!
# Matching the kept cusp of `E ∖ E[2]` ([AbsTopII] Cor 3.4, step G3): group theory

For an injection `c : G ↪ P` with normal image and a subgroup `I ≤ P`, the cusps
`J_g = c⁻¹(g I g⁻¹)` (`dupCusp`) and the union `dupCuspSet c I g₀` of those with `g ∉ g₀ · im c`.

* `exists_eq_closure_dupCuspSet`: if a normal subgroup `N` is the closed normal closure of the
  members of a family `𝒥 = {J_g}` it contains, and the members not in `N` form one conjugacy
  class, then `N` is the closed normal closure of `dupCuspSet c I g₀` for some `g₀` (uses that the
  normaliser of `I` lies in `im c`: then the class of `J_g` determines `g · im c`);
* `exists_twist_map_closure_dupCuspSet` (**Lemma M**): an isomorphism `φ` compatible with
  `Θ : P₁ ≅ P₂` along `c₁`, `c₂`, twisted by an inner automorphism of `P₂`, carries the closed
  normal closure of `dupCuspSet c₁ I₁ g₁` onto that of `dupCuspSet c₂ I₂ g₂`;
* `exists_lift_of_map_range`, `exists_quotient_iso`: restriction to images and passage to
  quotients for compact groups;
* `exists_pr_cor38Fill₃`, `pr_coverPiHom_self₃`: the filling and a cover over `K` lie over `G_K`
  up to inner automorphisms.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### Group theory -/

section GenericGroup

/-- Conjugation does not change membership in a normal subgroup. -/
lemma conj_mem_normal_iff₃ {P : Type*} [Group P] {H : Subgroup P} [hH : H.Normal] (h y : P) :
    h⁻¹ * y * h ∈ H ↔ y ∈ H := by
  constructor
  · intro hy
    have := hH.conj_mem _ hy h
    simpa [mul_assoc] using this
  · intro hy
    have := hH.conj_mem _ hy h⁻¹
    simpa using this

/-- Membership in a conjugate subgroup. -/
lemma mem_map_conj_iff₃ {P : Type*} [Group P] (I : Subgroup P) (g y : P) :
    y ∈ I.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨_, hy, by simp [mul_assoc]⟩

/-- **The cusps `J_g = c⁻¹(g I g⁻¹)` with `g ∉ g₀ · im c`**, as a subset of the source of `c`:
`v` with `g⁻¹ c(v) g ∈ I` for some `g` with `g₀⁻¹ g ∉ im c`. -/
def dupCuspSet {G P : Type*} [Group G] [Group P] (c : G →* P) (I : Subgroup P) (g₀ : P) :
    Set G :=
  {v | ∃ g : P, g₀⁻¹ * g ∉ c.range ∧ g⁻¹ * c v * g ∈ I}

/-- **Transport of `dupCuspSet`**: if `c₂ ∘ φ = Θ ∘ c₁` and `Θ(I₁) = h I₂ h⁻¹`, then `φ` maps
the cusps `J¹_g`, `g ∉ g₀ · im c₁`, onto the cusps `J²_{g'}`, `g' ∉ Θ(g₀) h · im c₂`. -/
theorem image_dupCuspSet {G₁ G₂ P₁ P₂ : Type*} [Group G₁] [Group G₂] [Group P₁] [Group P₂]
    (c₁ : G₁ →* P₁) (c₂ : G₂ →* P₂) [c₂.range.Normal] (Θ : P₁ ≃* P₂) (φ : G₁ ≃* G₂)
    (hφ : ∀ v, c₂ (φ v) = Θ (c₁ v)) {I₁ : Subgroup P₁} {I₂ : Subgroup P₂} {h : P₂}
    (hI : ∀ x, x ∈ I₁ ↔ h⁻¹ * Θ x * h ∈ I₂) (g₀ : P₁) :
    φ '' dupCuspSet c₁ I₁ g₀ = dupCuspSet c₂ I₂ (Θ g₀ * h) := by
  have hran : ∀ x, x ∈ c₁.range ↔ Θ x ∈ c₂.range := fun x ↦ by
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨φ v, hφ v⟩
    · rintro ⟨w, hw⟩
      refine ⟨φ.symm w, Θ.injective ?_⟩
      rw [← hφ, φ.apply_symm_apply, hw]
  have key : ∀ (g : P₁) (v : G₁), (g₀⁻¹ * g ∉ c₁.range ∧ g⁻¹ * c₁ v * g ∈ I₁) ↔
      ((Θ g₀ * h)⁻¹ * (Θ g * h) ∉ c₂.range ∧
        (Θ g * h)⁻¹ * c₂ (φ v) * (Θ g * h) ∈ I₂) := by
    intro g v
    have e1 : (Θ g₀ * h)⁻¹ * (Θ g * h) = h⁻¹ * Θ (g₀⁻¹ * g) * h := by
      rw [map_mul, map_inv]
      group
    have e2 : (Θ g * h)⁻¹ * c₂ (φ v) * (Θ g * h) = h⁻¹ * Θ (g⁻¹ * c₁ v * g) * h := by
      rw [hφ, map_mul, map_mul, map_inv]
      group
    rw [e1, e2, ← hI]
    have e3 : h⁻¹ * Θ (g₀⁻¹ * g) * h ∈ c₂.range ↔ Θ (g₀⁻¹ * g) ∈ c₂.range :=
      conj_mem_normal_iff₃ h _
    rw [e3, ← hran]
  ext w
  constructor
  · rintro ⟨v, ⟨g, hg⟩, rfl⟩
    exact ⟨Θ g * h, (key g v).1 hg⟩
  · rintro ⟨g', hg'⟩
    obtain ⟨g, rfl⟩ : ∃ g, Θ g * h = g' := ⟨Θ.symm (g' * h⁻¹), by simp⟩
    refine ⟨φ.symm w, ⟨g, (key g (φ.symm w)).2 ?_⟩, φ.apply_symm_apply w⟩
    rw [φ.apply_symm_apply]
    exact hg'

section Top

variable {G₁ G₂ P₁ P₂ : Type*} [Group G₁] [Group G₂] [Group P₁] [Group P₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

/-- **Lemma M, group theory.** Let `c_i : G_i → P_i` with `im c₂` normal, `Θ : P₁ ≅ P₂` with
`Θ(I₁) = h I₂ h⁻¹`, and `φ : G₁ ≅ G₂` with `c₂ ∘ φ = conj(g) ∘ Θ ∘ c₁`. Then `φ` maps the closed
normal closure of the cusps `J¹_{g'}`, `g' ∉ g₀ · im c₁`, onto that of the cusps `J²_{g'}`,
`g' ∉ g Θ(g₀) h · im c₂`. -/
theorem map_closure_dupCuspSet (c₁ : G₁ →* P₁) (c₂ : G₂ →* P₂) [c₂.range.Normal]
    (Θ : P₁ ≃* P₂) (g : P₂) (φ : G₁ ≃ₜ* G₂) (hφ : ∀ v, c₂ (φ v) = g * Θ (c₁ v) * g⁻¹)
    {I₁ : Subgroup P₁} {I₂ : Subgroup P₂} {h : P₂} (hI : ∀ x, x ∈ I₁ ↔ h⁻¹ * Θ x * h ∈ I₂)
    (g₀ : P₁) :
    (Subgroup.normalClosure (dupCuspSet c₁ I₁ g₀)).topologicalClosure.map
        φ.toMulEquiv.toMonoidHom =
      (Subgroup.normalClosure (dupCuspSet c₂ I₂ (g * Θ g₀ * h))).topologicalClosure := by
  have hφ' : ∀ v, c₂ (φ.toMulEquiv v) = (Θ.trans (MulAut.conj g)) (c₁ v) := hφ
  have hI' : ∀ x, x ∈ I₁ ↔ (g * h)⁻¹ * (Θ.trans (MulAut.conj g)) x * (g * h) ∈ I₂ := fun x ↦ by
    have e : (g * h)⁻¹ * (Θ.trans (MulAut.conj g)) x * (g * h) = h⁻¹ * Θ x * h := by
      change (g * h)⁻¹ * (g * Θ x * g⁻¹) * (g * h) = _
      group
    rw [e]
    exact hI x
  have e2 : (Θ.trans (MulAut.conj g)) g₀ * (g * h) = g * Θ g₀ * h := by
    change g * Θ g₀ * g⁻¹ * (g * h) = _
    group
  rw [map_topologicalClosure_normalClosure, ← e2]
  congr 2
  exact image_dupCuspSet c₁ c₂ (Θ.trans (MulAut.conj g)) φ.toMulEquiv hφ' hI' g₀

end Top

/-- Conjugation as a continuous isomorphism. -/
def conjCME₃ {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] (g : P) :
    P ≃ₜ* P where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by group
  right_inv x := by group
  map_mul' x y := by group
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma conjCME₃_apply {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (g x : P) : conjCME₃ g x = g * x * g⁻¹ := rfl

section Compact

variable {G₁ G₂ P₁ P₂ : Type*} [Group G₁] [Group G₂] [Group P₁] [Group P₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace P₁] [TopologicalSpace P₂]
  [CompactSpace G₁] [CompactSpace G₂] [T2Space P₁] [T2Space P₂]

/-- **Restriction of an isomorphism to images**: if `Θ : P₁ ≅ P₂` maps `im c₁` onto `im c₂`
(`c_i` injective, continuous, with compact source), then `Θ` restricts to `φ : G₁ ≅ G₂` with
`c₂ ∘ φ = Θ ∘ c₁`. -/
theorem exists_lift_of_map_range (c₁ : G₁ →ₜ* P₁) (c₂ : G₂ →ₜ* P₂)
    (hc₁ : Function.Injective c₁) (hc₂ : Function.Injective c₂) (Θ : P₁ ≃ₜ* P₂)
    (hΘ : c₁.toMonoidHom.range.map Θ.toMulEquiv.toMonoidHom = c₂.toMonoidHom.range) :
    ∃ φ : G₁ ≃ₜ* G₂, ∀ v, c₂ (φ v) = Θ (c₁ v) := by
  let e₁ : G₁ ≃* c₁.toMonoidHom.range := MonoidHom.ofInjective (f := c₁.toMonoidHom) hc₁
  let e₂ : G₂ ≃* c₂.toMonoidHom.range := MonoidHom.ofInjective (f := c₂.toMonoidHom) hc₂
  let m : c₁.toMonoidHom.range ≃* c₂.toMonoidHom.range :=
    (Θ.toMulEquiv.subgroupMap c₁.toMonoidHom.range).trans (MulEquiv.subgroupCongr hΘ)
  let φ₀ : G₁ ≃* G₂ := e₁.trans (m.trans e₂.symm)
  have hφ₀ : ∀ v, c₂ (φ₀ v) = Θ (c₁ v) := fun v ↦ by
    have h1 : ((e₂ (φ₀ v) : c₂.toMonoidHom.range) : P₂) = c₂ (φ₀ v) := rfl
    have h2 : e₂ (φ₀ v) = m (e₁ v) := e₂.apply_symm_apply _
    rw [← h1, h2]
    rfl
  have hφ₀' : ∀ w, c₁ (φ₀.symm w) = Θ.symm (c₂ w) := fun w ↦ by
    apply Θ.injective
    rw [ContinuousMulEquiv.apply_symm_apply, ← hφ₀, φ₀.apply_symm_apply]
  have emb₁ := (c₁.continuous.isClosedEmbedding hc₁).isEmbedding
  have emb₂ := (c₂.continuous.isClosedEmbedding hc₂).isEmbedding
  refine ⟨{ φ₀ with
    continuous_toFun := emb₂.continuous_iff.2 ?_
    continuous_invFun := emb₁.continuous_iff.2 ?_ }, hφ₀⟩
  · have e : (c₂ ∘ fun v ↦ φ₀ v) = Θ ∘ c₁ := funext hφ₀
    change Continuous (c₂ ∘ fun v ↦ φ₀ v)
    rw [e]
    exact Θ.continuous.comp c₁.continuous
  · have e : (c₁ ∘ fun w ↦ φ₀.symm w) = Θ.symm ∘ c₂ := funext hφ₀'
    change Continuous (c₁ ∘ fun w ↦ φ₀.symm w)
    rw [e]
    exact Θ.symm.continuous.comp c₂.continuous

end Compact

section Quotient

variable {G₁ G₂ Q₁ Q₂ : Type*} [Group G₁] [Group G₂] [Group Q₁] [Group Q₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace Q₁] [TopologicalSpace Q₂]
  [CompactSpace G₁] [CompactSpace G₂] [T2Space Q₁] [T2Space Q₂]

/-- **The quotient isomorphism**: if `φ : G₁ ≅ G₂` maps `ker f₁` onto `ker f₂` (`f_i`
continuous surjective with compact source and Hausdorff target), then `f₂ ∘ φ = Ψ ∘ f₁` for an
isomorphism `Ψ : Q₁ ≅ Q₂` of topological groups. -/
theorem exists_quotient_iso (f₁ : G₁ →ₜ* Q₁) (f₂ : G₂ →ₜ* Q₂) (hf₁ : Function.Surjective f₁)
    (hf₂ : Function.Surjective f₂) (φ : G₁ ≃ₜ* G₂)
    (hker : f₁.toMonoidHom.ker.map φ.toMulEquiv.toMonoidHom = f₂.toMonoidHom.ker) :
    ∃ Ψ : Q₁ ≃ₜ* Q₂, ∀ v, f₂ (φ v) = Ψ (f₁ v) := by
  let a := (QuotientGroup.quotientKerEquivOfSurjective f₁.toMonoidHom hf₁).symm
  let b := QuotientGroup.congr f₁.toMonoidHom.ker f₂.toMonoidHom.ker φ.toMulEquiv hker
  let d := QuotientGroup.quotientKerEquivOfSurjective f₂.toMonoidHom hf₂
  let Ψ₀ : Q₁ ≃* Q₂ := a.trans (b.trans d)
  have hΨ₀ : ∀ v, Ψ₀ (f₁ v) = f₂ (φ v) := fun v ↦ by
    have ha : a (f₁ v) = (v : G₁ ⧸ f₁.toMonoidHom.ker) := by
      apply a.symm.injective
      rw [MulEquiv.symm_apply_apply]
      rfl
    change d (b (a (f₁ v))) = _
    rw [ha]
    rfl
  have hΨ₀' : ∀ w, Ψ₀.symm (f₂ w) = f₁ (φ.symm w) := fun w ↦ by
    apply Ψ₀.injective
    rw [MulEquiv.apply_symm_apply, hΨ₀, ContinuousMulEquiv.apply_symm_apply]
  have q₁ := IsClosedMap.isQuotientMap f₁.continuous.isClosedMap f₁.continuous hf₁
  have q₂ := IsClosedMap.isQuotientMap f₂.continuous.isClosedMap f₂.continuous hf₂
  refine ⟨{ Ψ₀ with
    continuous_toFun := q₁.continuous_iff.2 ?_
    continuous_invFun := q₂.continuous_iff.2 ?_ }, fun v ↦ (hΨ₀ v).symm⟩
  · have e : ((fun q ↦ Ψ₀ q) ∘ f₁) = f₂ ∘ φ := funext hΨ₀
    change Continuous ((fun q ↦ Ψ₀ q) ∘ f₁)
    rw [e]
    exact f₂.continuous.comp φ.continuous
  · have e : ((fun q ↦ Ψ₀.symm q) ∘ f₂) = f₁ ∘ φ.symm := funext hΨ₀'
    change Continuous ((fun q ↦ Ψ₀.symm q) ∘ f₂)
    rw [e]
    exact f₁.continuous.comp φ.symm.continuous

end Quotient


section Classes

variable {G P : Type*} [Group G] [Group P]

/-- The pull-back `J_g = c⁻¹(g I g⁻¹)` of a conjugate of `I`. -/
abbrev dupCusp (c : G →* P) (I : Subgroup P) (g : P) : Subgroup G :=
  (I.map (MulAut.conj g).toMonoidHom).comap c

lemma mem_dupCusp_iff (c : G →* P) (I : Subgroup P) (g : P) (v : G) :
    v ∈ dupCusp c I g ↔ g⁻¹ * c v * g ∈ I := by
  rw [Subgroup.mem_comap, mem_map_conj_iff₃]

/-- `J_{c(u) g} = u J_g u⁻¹`. -/
lemma dupCusp_mul (c : G →* P) (I : Subgroup P) (u : G) (g : P) :
    dupCusp c I (c u * g) = (dupCusp c I g).map (MulAut.conj u).toMonoidHom := by
  ext v
  rw [mem_map_conj_iff₃, mem_dupCusp_iff, mem_dupCusp_iff, map_mul, map_mul, map_inv]
  have e : (c u * g)⁻¹ * c v * (c u * g) = g⁻¹ * ((c u)⁻¹ * c v * c u) * g := by group
  rw [e]

/-- If `I ≤ im c` and `im c` is normal, `c(J_g) = g I g⁻¹`. -/
lemma map_dupCusp (c : G →* P) [c.range.Normal] (I : Subgroup P) (hI : I ≤ c.range) (g : P) :
    (dupCusp c I g).map c = I.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_comap_eq, inf_eq_right]
  rintro _ ⟨x, hx, rfl⟩
  exact (inferInstance : c.range.Normal).conj_mem _ (hI hx) g

/-- **The class of `J_g` determines the coset `g · im c`**, if the normaliser of `I` lies in
`im c`. -/
lemma mem_range_of_dupCusp_eq_map (c : G →* P) [hR : c.range.Normal] (I : Subgroup P)
    (hI : I ≤ c.range)
    (hnorm : ∀ x : P, I.map (MulAut.conj x).toMonoidHom = I → x ∈ c.range) {g g' : P} {v : G}
    (h : dupCusp c I g' = (dupCusp c I g).map (MulAut.conj v).toMonoidHom) :
    g⁻¹ * g' ∈ c.range := by
  rw [← dupCusp_mul] at h
  have h2 := congrArg (Subgroup.map c) h
  rw [map_dupCusp c I hI, map_dupCusp c I hI] at h2
  have hx : I.map (MulAut.conj ((c v * g)⁻¹ * g')).toMonoidHom = I := by
    ext y
    rw [mem_map_conj_iff₃]
    have e : ((c v * g)⁻¹ * g')⁻¹ * y * ((c v * g)⁻¹ * g') =
        g'⁻¹ * ((c v * g) * y * (c v * g)⁻¹) * g' := by group
    rw [e, ← mem_map_conj_iff₃, h2, mem_map_conj_iff₃]
    constructor
    · intro hy
      simpa [mul_assoc] using hy
    · intro hy
      simpa [mul_assoc] using hy
  have h3 := hnorm _ hx
  have e : g⁻¹ * g' = (g⁻¹ * c v * g) * ((c v * g)⁻¹ * g') := by group
  rw [e]
  refine c.range.mul_mem ?_ h3
  have := hR.conj_mem _ ⟨v, rfl⟩ g⁻¹
  simpa [mul_assoc] using this

/-- **The killed cusps are the `J_g` with `g ∉ g₀ · im c`** (generic form of step G3): if every
member of `𝒥` is some `J_g`, every `J_g` is in `𝒥`, the normal subgroup `N` is the closed normal
closure of the members of `𝒥` it contains, the members of `𝒥` not in `N` form one conjugacy
class and there is one, then `N` is the closed normal closure of `dupCuspSet c I g₀` for some
`g₀`. -/
theorem exists_eq_closure_dupCuspSet [TopologicalSpace G] [IsTopologicalGroup G]
    (c : G →* P) [hR : c.range.Normal] (I : Subgroup P) (hI : I ≤ c.range)
    (hnorm : ∀ x : P, I.map (MulAut.conj x).toMonoidHom = I → x ∈ c.range)
    (𝒥 : Set (Subgroup G)) (h𝒥 : ∀ J ∈ 𝒥, ∃ g, J = dupCusp c I g)
    (h𝒥' : ∀ g, dupCusp c I g ∈ 𝒥) (N : Subgroup G) [hN : N.Normal]
    (hNeq : N =
      (Subgroup.normalClosure (⋃ (J) (_ : J ∈ 𝒥 ∧ J ≤ N), (J : Set G))).topologicalClosure)
    (hconj : ∀ J ∈ 𝒥, ∀ J' ∈ 𝒥, ¬ J ≤ N → ¬ J' ≤ N →
      ∃ v : G, J' = J.map (MulAut.conj v).toMonoidHom)
    (hex : ∃ J ∈ 𝒥, ¬ J ≤ N) :
    ∃ g₀ : P, N = (Subgroup.normalClosure (dupCuspSet c I g₀)).topologicalClosure := by
  obtain ⟨J₀, hJ₀, hJ₀N⟩ := hex
  obtain ⟨g₀, rfl⟩ := h𝒥 J₀ hJ₀
  refine ⟨g₀, hNeq.trans ?_⟩
  have hkill : ∀ g, dupCusp c I g ≤ N ↔ g₀⁻¹ * g ∉ c.range := by
    intro g
    constructor
    · intro hg hmem
      apply hJ₀N
      obtain ⟨r, hr⟩ := hmem
      obtain ⟨u, hu⟩ : ∃ u, c u = g₀ * c r * g₀⁻¹ :=
        hR.conj_mem _ ⟨r, rfl⟩ g₀
      have hg' : g = c u * g₀ := by rw [hu, hr]; group
      rw [hg', dupCusp_mul] at hg
      intro x hx
      have := hN.conj_mem _ (hg ⟨x, hx, rfl⟩) u⁻¹
      simpa [mul_assoc] using this
    · intro hg
      by_contra hle
      obtain ⟨v, hv⟩ := hconj _ hJ₀ _ (h𝒥' g) hJ₀N hle
      exact hg (mem_range_of_dupCusp_eq_map c I hI hnorm hv)
  congr 2
  ext v
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨J, ⟨hJ, hJN⟩, hv⟩
    obtain ⟨g, rfl⟩ := h𝒥 J hJ
    exact ⟨g, (hkill g).1 hJN, (mem_dupCusp_iff c I g v).1 hv⟩
  · rintro ⟨g, hg, hv⟩
    exact ⟨dupCusp c I g, ⟨h𝒥' g, (hkill g).2 hg⟩, (mem_dupCusp_iff c I g v).2 hv⟩

end Classes

section LemmaM

variable {G₁ G₂ P₁ P₂ : Type*} [Group G₁] [Group G₂] [Group P₁] [Group P₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace P₁] [TopologicalSpace P₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup P₂]
  [CompactSpace G₂] [T2Space P₂]

/-- **Lemma M, group theory** (step G3): let `c_i : G_i ↪ P_i` (`im c₂` normal),
`Θ : P₁ ≅ P₂` with `Θ(I₁) = h I₂ h⁻¹` and `φ : G₁ ≅ G₂` with `c₂ ∘ φ = Θ ∘ c₁`. Then after
twisting `φ` by conjugation with some `g ∈ P₂` (which preserves `im c₂`) it maps the closed normal
closure of `dupCuspSet c₁ I₁ g₁` onto that of `dupCuspSet c₂ I₂ g₂`, for any `g₁`, `g₂`. -/
theorem exists_twist_map_closure_dupCuspSet (c₁ : G₁ →ₜ* P₁) (c₂ : G₂ →ₜ* P₂)
    (hc₂ : Function.Injective c₂) [c₂.toMonoidHom.range.Normal] (Θ : P₁ ≃* P₂)
    (φ : G₁ ≃ₜ* G₂) (hφ : ∀ v, c₂ (φ v) = Θ (c₁ v)) {I₁ : Subgroup P₁} {I₂ : Subgroup P₂}
    {h : P₂} (hI : ∀ x, x ∈ I₁ ↔ h⁻¹ * Θ x * h ∈ I₂) (g₁ : P₁) (g₂ : P₂) :
    ∃ g : P₂, ∃ φ' : G₁ ≃ₜ* G₂, (∀ v, c₂ (φ' v) = g * Θ (c₁ v) * g⁻¹) ∧
      (Subgroup.normalClosure (dupCuspSet c₁.toMonoidHom I₁ g₁)).topologicalClosure.map
          φ'.toMulEquiv.toMonoidHom =
        (Subgroup.normalClosure (dupCuspSet c₂.toMonoidHom I₂ g₂)).topologicalClosure := by
  set g : P₂ := g₂ * (Θ g₁ * h)⁻¹
  have hran : c₂.toMonoidHom.range.map (conjCME₃ g).toMulEquiv.toMonoidHom =
      c₂.toMonoidHom.range := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (inferInstance : c₂.toMonoidHom.range.Normal).conj_mem _ hx g
    · intro x hx
      refine ⟨g⁻¹ * x * g, ?_, by change g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
      have := (inferInstance : c₂.toMonoidHom.range.Normal).conj_mem _ hx g⁻¹
      simpa [mul_assoc] using this
  obtain ⟨κ, hκ⟩ := exists_lift_of_map_range c₂ c₂ hc₂ hc₂ (conjCME₃ g) hran
  refine ⟨g, φ.trans κ, fun v ↦ ?_, ?_⟩
  · change c₂ (κ (φ v)) = _
    rw [hκ, conjCME₃_apply, hφ]
  · have hφ' : ∀ v, c₂.toMonoidHom ((φ.trans κ) v) = g * Θ (c₁.toMonoidHom v) * g⁻¹ :=
      fun v ↦ by
        change c₂ (κ (φ v)) = _
        rw [hκ, conjCME₃_apply, hφ]
        rfl
    rw [map_closure_dupCuspSet c₁.toMonoidHom c₂.toMonoidHom Θ g (φ.trans κ) hφ' hI g₁]
    congr 3
    change g₂ * (Θ g₁ * h)⁻¹ * Θ g₁ * h = g₂
    group

end LemmaM

end GenericGroup


/-! ### The projections to `G_K` along the filling and along a cover -/

section Proj

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

/-- **`cor38Fill` lies over `G_K` up to an inner automorphism**: `pr ∘ fill = conj(t) ∘ pr`. -/
theorem exists_pr_cor38Fill₃ : ∃ t : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))), ∀ v,
    projGk Ω CX hcX (cor38Fill Ω CX hcX UX hUX hne α₀ v) =
      t * projGk Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) v * t⁻¹ := by
  refine ⟨fiberIsoMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))))
    (fillPoint_spec₂ Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)
    (basePoint_spec₂ Ω CX hcX)
    (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl α₀).symm, fun v ↦ ?_⟩
  change fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))))
      (basePoint_spec₂ Ω CX hcX) ((autContinuousMulEquivOfIso
        (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl α₀)).symm
        (fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX v)) = _
  have hB := fundamentalGroupMap_autContinuousMulEquivOfIso
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))))
    (fillPoint_spec₂ Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)
    (basePoint_spec₂ Ω CX hcX)
    (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl α₀).symm
    (fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX v)
  rw [autContinuousMulEquivOfIso_symm_apply₂]
  refine hB.trans ?_
  rw [autContinuousMulEquivOfIso_self]
  have hP := projGkFill_fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX v
  rw [← hP]
  rfl

end Proj

section ProjCover

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (C' : HypCurve K)
  (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty) (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U))
  (hF : F ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K))) [IsFiniteEtale F]

include hF in
/-- **A cover over `K` lies over `G_K` up to an inner automorphism**. -/
theorem pr_coverPiHom_self₃ (γ : (arithmeticExt Ω C' hc').Pi) :
    projGk Ω C hc (coverPiHom Ω C hc C' hc' F γ) =
      coverG Ω C hc C' hc' F hF * projGk Ω C' hc' γ * (coverG Ω C hc C' hc' F hF)⁻¹ := by
  change (arithmeticExt Ω C hc).pr _ = _
  rw [pr_coverPiHom Ω C hc C' hc' F hF]
  change autContinuousMulEquivOfIso (coverG Ω C hc C' hc' F hF) (galoisMap K K Ω _) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]
  rfl

end ProjCover

end CurvesJacobian.Cusp
