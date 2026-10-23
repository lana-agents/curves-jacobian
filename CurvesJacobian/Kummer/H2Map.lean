/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Surface.H2

/-!
# Change of coefficients for `H²` with locally constant cochains

pi1's `H2lc G M` (`Pi1/Profinite/H2.lean`) is functorial in `G` (`H2lc.comap`, `H2lc.congr`). Here:
functoriality in the coefficients and its compatibility with the relator-value isomorphism
`H²(G, M) ≅ M` for `G ≃ₜ* Π̂_{g,0}` (`h2EquivOfContinuousMulEquiv`).

* `CurvesJacobian.TopClass.cocyclesMap ρ hρ`, `CurvesJacobian.TopClass.h2Map ρ hρ :
  H2lc G M →* H2lc G M'` for a `G`-equivariant `ρ : M →* M'`; `h2Map_mk`, `h2Map_id`,
  `h2Map_comp`;
* `CurvesJacobian.TopClass.h2MapEquiv` (along isomorphisms);
* `CurvesJacobian.TopClass.h2EquivAny`: `H²(G, M) ≅ M` for `G ≃ₜ* Π̂_{g,0}` and finite `M` with
  trivial action in any universe (pi1's `h2EquivOfContinuousMulEquiv` through `Shrink`), and
  **`CurvesJacobian.TopClass.h2EquivAny_h2Map`**: it is natural in `M` (from pi1's `relVal_map`).
-/

open Pi1 Pi1.Profinite Pi1.SurfaceGroup

namespace CurvesJacobian.TopClass

section Map

variable {G M M' M'' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup M']
  [CommGroup M''] [MulDistribMulAction G M] [MulDistribMulAction G M']
  [MulDistribMulAction G M'']

/-- Pushing locally constant cocycles forward along a `G`-equivariant homomorphism. -/
def cocyclesMap (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m) :
    H2lc.cocycles G M →* H2lc.cocycles G M' where
  toFun f := ⟨ρ ∘ f.1, f.2.1.comp ρ, fun a b c ↦ by
    have := congrArg ρ (f.2.2 a b c)
    simpa only [Function.comp_apply, map_mul, hρ] using this⟩
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp

@[simp]
lemma coe_cocyclesMap (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m)
    (f : H2lc.cocycles G M) : ((cocyclesMap ρ hρ f : H2lc.cocycles G M') : G × G → M') =
      ρ ∘ (f : G × G → M) :=
  rfl

lemma cocyclesMap_coboundaries (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m)
    {f : H2lc.cocycles G M} (hf : f ∈ H2lc.coboundaries G M) :
    cocyclesMap ρ hρ f ∈ H2lc.coboundaries G M' := by
  obtain ⟨x, hx, hxf⟩ := hf
  refine ⟨ρ ∘ x, hx.comp ρ, ?_⟩
  ext ⟨a, b⟩
  change _ = ρ (f.1 (a, b))
  rw [← hxf]
  simp [H2lc.dx, hρ]

/-- **Change of coefficients** `H²(G, M) → H²(G, M')` along a `G`-equivariant `ρ : M →* M'`. -/
def h2Map (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m) :
    H2lc G M →* H2lc G M' :=
  QuotientGroup.map _ _ (cocyclesMap ρ hρ) fun _ hf ↦ cocyclesMap_coboundaries ρ hρ hf

lemma h2Map_mk (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m)
    (f : H2lc.cocycles G M) :
    h2Map ρ hρ (QuotientGroup.mk f) = QuotientGroup.mk (cocyclesMap ρ hρ f) :=
  rfl

lemma h2Map_id (c : H2lc G M) : h2Map (MonoidHom.id M) (fun _ _ ↦ rfl) c = c := by
  induction c using QuotientGroup.induction_on with
  | H f => rfl

lemma h2Map_comp (ρ : M →* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m)
    (ρ' : M' →* M'') (hρ' : ∀ (g : G) (m : M'), ρ' (g • m) = g • ρ' m) (c : H2lc G M) :
    h2Map ρ' hρ' (h2Map ρ hρ c) =
      h2Map (ρ'.comp ρ) (fun g m ↦ by rw [MonoidHom.comp_apply, hρ, hρ']; rfl) c := by
  induction c using QuotientGroup.induction_on with
  | H f => rfl

/-- `h2Map` along an equivariant isomorphism, as an isomorphism. -/
def h2MapEquiv (ρ : M ≃* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m) :
    H2lc G M ≃* H2lc G M' where
  toFun := h2Map ρ.toMonoidHom hρ
  invFun := h2Map ρ.symm.toMonoidHom fun g m ↦ by
    apply ρ.injective
    simp [hρ]
  left_inv c := by
    induction c using QuotientGroup.induction_on with
    | H f =>
      change QuotientGroup.mk _ = QuotientGroup.mk f
      congr 1
      ext x
      simp
  right_inv c := by
    induction c using QuotientGroup.induction_on with
    | H f =>
      change QuotientGroup.mk _ = QuotientGroup.mk f
      congr 1
      ext x
      simp
  map_mul' := map_mul _

lemma h2MapEquiv_apply (ρ : M ≃* M') (hρ : ∀ (g : G) (m : M), ρ (g • m) = g • ρ m)
    (c : H2lc G M) : h2MapEquiv ρ hρ c = h2Map ρ.toMonoidHom hρ c :=
  rfl

end Map

section Natural0

variable {G M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup M']
  [MulDistribMulAction G M] [MulDistribMulAction G M'] {g : ℕ}

/-- Naturality of the relator value, for coefficients in `Type`. -/
theorem h2EquivOfContinuousMulEquiv_h2Map₀ {M M' : Type} [CommGroup M] [CommGroup M']
    [MulDistribMulAction G M] [MulDistribMulAction G M'] [Finite M] [Finite M']
    (hg : 0 < g) (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)
    (htriv : ∀ (γ : G) (m : M), γ • m = m) (htriv' : ∀ (γ : G) (m : M'), γ • m = m)
    (ρ : M →* M') (c : H2lc G M) :
    h2EquivOfContinuousMulEquiv hg e htriv' (h2Map ρ (fun γ m ↦ by rw [htriv, htriv']) c) =
      ρ (h2EquivOfContinuousMulEquiv hg e htriv c) := by
  induction c using QuotientGroup.induction_on with
  | H f =>
    letI := trivialAction (ProfiniteSurfaceGroup g 0) M
    letI := trivialAction (ProfiniteSurfaceGroup g 0) M'
    let f₀ : TrivCocycle (ProfiniteSurfaceGroup g 0) M :=
      ⟨f.1 ∘ Prod.map e.symm e.symm, fun a b c ↦ by
        have := f.2.2 (e.symm a) (e.symm b) (e.symm c)
        simpa [htriv] using this⟩
    exact relVal_map ρ commProd_genAhat f₀

/-- **`H²(G, M) ≅ M`** for `G ≃ₜ* Π̂_{g,0}` (`g ≥ 1`) and a finite `M` with trivial action, in
any universe (through `Shrink`; pi1's `h2EquivOfContinuousMulEquiv` needs `M : Type`). -/
noncomputable def h2EquivAny [Finite M] (hg : 0 < g) (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)
    (htriv : ∀ (γ : G) (m : M), γ • m = m) : H2lc G M ≃* M :=
  letI := trivialAction G (Shrink.{0} M)
  haveI : Finite (Shrink.{0} M) :=
    Finite.of_equiv _ (Shrink.mulEquiv.symm : M ≃* Shrink.{0} M).toEquiv
  (h2MapEquiv (Shrink.mulEquiv.symm : M ≃* Shrink.{0} M) fun γ m ↦ by rw [htriv]; rfl).trans
    ((h2EquivOfContinuousMulEquiv hg e fun _ _ ↦ rfl).trans Shrink.mulEquiv)

/-- **`H²(G, M) ≅ M` is natural in the coefficients** (`G ≃ₜ* Π̂_{g,0}`, trivial actions). -/
theorem h2EquivAny_h2Map [Finite M] [Finite M'] (hg : 0 < g)
    (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)
    (htriv : ∀ (γ : G) (m : M), γ • m = m) (htriv' : ∀ (γ : G) (m : M'), γ • m = m)
    (ρ : M →* M') (c : H2lc G M) :
    h2EquivAny hg e htriv' (h2Map ρ (fun γ m ↦ by rw [htriv, htriv']) c) =
      ρ (h2EquivAny hg e htriv c) := by
  letI := trivialAction G (Shrink.{0} M)
  letI := trivialAction G (Shrink.{0} M')
  haveI : Finite (Shrink.{0} M) :=
    Finite.of_equiv _ (Shrink.mulEquiv.symm : M ≃* Shrink.{0} M).toEquiv
  haveI : Finite (Shrink.{0} M') :=
    Finite.of_equiv _ (Shrink.mulEquiv.symm : M' ≃* Shrink.{0} M').toEquiv
  let s : M ≃* Shrink.{0} M := Shrink.mulEquiv.symm
  let s' : M' ≃* Shrink.{0} M' := Shrink.mulEquiv.symm
  let ρ' : Shrink.{0} M →* Shrink.{0} M' := s'.toMonoidHom.comp (ρ.comp s.symm.toMonoidHom)
  induction c using QuotientGroup.induction_on with
  | H f =>
    have h := h2EquivOfContinuousMulEquiv_h2Map₀ hg e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ρ'
      (QuotientGroup.mk (cocyclesMap s.toMonoidHom (fun γ m ↦ by rw [htriv]; rfl) f))
    have e1 : h2Map ρ' (fun _ _ ↦ rfl)
        (QuotientGroup.mk (cocyclesMap s.toMonoidHom (fun γ m ↦ by rw [htriv]; rfl) f) :
          H2lc G (Shrink.{0} M)) =
        QuotientGroup.mk (cocyclesMap s'.toMonoidHom (fun γ m ↦ by rw [htriv']; rfl)
          (cocyclesMap ρ (fun γ m ↦ by rw [htriv, htriv']) f)) := by
      change QuotientGroup.mk _ = QuotientGroup.mk _
      congr 1
      ext x
      simp [ρ']
    rw [e1] at h
    refine (congrArg Shrink.mulEquiv h).trans ?_
    simp only [ρ', s, s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
    rfl

end Natural0

end CurvesJacobian.TopClass
