/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CurveInertiaIsoAny
import Pi1.Surface.ProSigma

/-!
# Pro-`Σ` forms of `π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` with cuspidal inertia

Let `Σ` be a set of primes (a predicate `P : ℕ → Prop`). Passing to maximal pro-`Σ` quotients
(`Pi1.Profinite.MaxProSigma`) in the characteristic-`0` comparison theorems
`exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed` and
`exists_continuousMulEquiv_lineInertiaS` gives:

* **`exists_continuousMulEquiv_cuspInertia_curve_proSigma`**: `π₁ᵉᵗ(X ∖ D)^Σ ≃ₜ* Π^Σ_{g,r}`, where
  the image of every cuspidal inertia group is mapped onto a conjugate of the image
  `ℤ^Σ → Π^Σ_{g,r}` of the `j`-th cusp inertia (`Pi1.SurfaceGroup.cuspInertiaSigma`) for some `j`.
  For `X ∖ D = E ∖ {O}` this is `Δ^Σ ≅ Π^Σ_{1,1}` with cusp inertia (Route B, item B1, of the MR13
  plan: [SemiAnbd] Cor 3.11, the vertex/edge groups of `G^Σ`).
* **`exists_continuousMulEquiv_lineInertiaS_proSigma`**: `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))^Σ ≃ₜ* Π^Σ_{0,n+2}`
  with the inertia groups at all cusps; for `S = {0, 1}` this is `π^Σ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π^Σ_{0,3}`
  (item A4: the characteristic-`0` half of the vertex group comparison, cf. [SGA1] XIII Cor 2.12).

The generic inputs are: the `Σ`-kernel is characteristic (`sigmaKernel_map_continuousMulEquiv`),
so `G ≃ₜ* H` induces `G^Σ ≃ₜ* H^Σ` (`maxProSigmaCongr`), compatibly with conjugation
(`map_map_mk_conj_of_map_eq`); and the image of `Iⱼ = ⟨cⱼ⟩‾ ⊆ Π̂_{g,r}` in `Π^Σ_{g,r}` is the range
of `cuspInertiaSigma j` (`map_mk_inertia`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1.Profinite ProfiniteGrp
  ProfiniteGrp.ProfiniteCompletion PreGaloisCategory

universe u

namespace CurvesJacobian.Cusp

namespace ProSigma

section Generic

variable (P : ℕ → Prop) {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The preimage of an open normal subgroup of `Σ`-index under a continuous surjective
homomorphism is an open normal subgroup of `Σ`-index. -/
theorem isSigmaOpenNormal_comap {f : G →* H} (hf : Continuous f) (hs : Function.Surjective f)
    {N : Subgroup H} (hN : IsSigmaOpenNormal P H N) : IsSigmaOpenNormal P G (N.comap f) := by
  refine ⟨hN.1.preimage hf, @Subgroup.Normal.comap _ _ _ _ _ hN.2.1 f, ?_⟩
  rw [Subgroup.index_comap_of_surjective N hs]
  exact hN.2.2

/-- A continuous surjective homomorphism maps the `Σ`-kernel into the `Σ`-kernel. -/
theorem sigmaKernel_le_comap {f : G →* H} (hf : Continuous f) (hs : Function.Surjective f) :
    sigmaKernel P G ≤ (sigmaKernel P H).comap f := fun _ hg =>
  mem_sigmaKernel_iff.2 fun N hN =>
    mem_sigmaKernel_iff.1 hg (N.comap f) (isSigmaOpenNormal_comap P hf hs hN)

/-- **The `Σ`-kernel is characteristic**: a topological group isomorphism maps it onto the
`Σ`-kernel. -/
theorem sigmaKernel_map_continuousMulEquiv (e : G ≃ₜ* H) :
    (sigmaKernel P G).map (e : G →* H) = sigmaKernel P H := by
  refine le_antisymm ?_ fun h hh => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact sigmaKernel_le_comap P e.continuous e.surjective
  · refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    exact sigmaKernel_le_comap P (f := (e.symm : H →* G)) e.symm.continuous e.symm.surjective hh

/-- **Functoriality of the maximal pro-`Σ` quotient in isomorphisms**: `G ≃ₜ* H` induces
`G^Σ ≃ₜ* H^Σ`. -/
noncomputable def maxProSigmaCongr [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) :
    MaxProSigma P G ≃ₜ* MaxProSigma P H where
  toMulEquiv := QuotientGroup.congr _ _ e.toMulEquiv (sigmaKernel_map_continuousMulEquiv P e)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (MaxProSigma.continuous_mk (P := P) (G := H)).comp e.continuous
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (MaxProSigma.continuous_mk (P := P) (G := G)).comp e.symm.continuous

@[simp]
theorem maxProSigmaCongr_mk [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) (g : G) :
    maxProSigmaCongr P e (MaxProSigma.mk g) = MaxProSigma.mk (e g) := rfl

/-- `e^Σ ∘ conj (σ mod J^Σ) ∘ mk = mk ∘ e ∘ conj σ`. -/
theorem maxProSigmaCongr_conj_comp_mk [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (σ : G) :
    (((maxProSigmaCongr P e : MaxProSigma P G →* MaxProSigma P H).comp
      (MulAut.conj (MaxProSigma.mk (P := P) σ)).toMonoidHom).comp (MaxProSigma.mk (P := P))) =
      (MaxProSigma.mk (P := P)).comp ((e : G →* H).comp (MulAut.conj σ).toMonoidHom) := by
  ext x
  change maxProSigmaCongr P e (MaxProSigma.mk (σ * x * σ⁻¹)) = _
  rw [maxProSigmaCongr_mk]
  rfl

/-- **Conjugate images pass to the maximal pro-`Σ` quotients**: if `e ∘ conj σ` maps `A ≤ G` onto
`I ≤ H`, then `e^Σ ∘ conj (σ mod J^Σ)` maps the image of `A` in `G^Σ` onto the image of `I`
in `H^Σ`. -/
theorem map_map_mk_conj_of_map_eq [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H)
    (σ : G) {A : Subgroup G} {I : Subgroup H}
    (h : A.map ((e : G →* H).comp (MulAut.conj σ).toMonoidHom) = I) :
    (A.map (MaxProSigma.mk (P := P))).map
        ((maxProSigmaCongr P e : MaxProSigma P G →* MaxProSigma P H).comp
          (MulAut.conj (MaxProSigma.mk (P := P) σ)).toMonoidHom) =
      I.map (MaxProSigma.mk (P := P)) := by
  rw [Subgroup.map_map, maxProSigmaCongr_conj_comp_mk, ← Subgroup.map_map, h]

end Generic

section Surface

variable (P : ℕ → Prop) {g r : ℕ}

/-- `cuspInertiaSigma j ∘ mk = mk ∘ cuspInertia j`: the pro-`Σ` cusp inertia is induced by the
profinite one. -/
theorem cuspInertiaSigma_comp_mk (j : Fin r) :
    (Pi1.SurfaceGroup.cuspInertiaSigma P (g := g) j).comp (MaxProSigma.mk (P := P)) =
      (MaxProSigma.mk (P := P)).comp (Pi1.SurfaceGroup.cuspInertia (g := g) j) := by
  ext x
  rfl

/-- **The image of `Iⱼ = ⟨cⱼ⟩‾ ⊆ Π̂_{g,r}` in `Π^Σ_{g,r}`** is the image of the pro-`Σ` cusp
inertia `ℤ^Σ → Π^Σ_{g,r}`. -/
theorem map_mk_inertia (j : Fin r) :
    (Pi1.SurfaceGroup.inertia (g := g) j).map (MaxProSigma.mk (P := P)) =
      (Pi1.SurfaceGroup.cuspInertiaSigma P (g := g) j).range := by
  rw [← Pi1.SurfaceGroup.range_cuspInertia, MonoidHom.map_range, ← cuspInertiaSigma_comp_mk,
    MonoidHom.range_comp, MonoidHom.range_eq_top.2 MaxProSigma.mk_surjective,
    ← MonoidHom.range_eq_map]

end Surface

end ProSigma

open ProSigma

section Main

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
/-- **`π₁ᵉᵗ(X ∖ D)^Σ ≃ₜ* Π^Σ_{g,r}` with the cuspidal inertia groups going to conjugates of the
pro-`Σ` cusp inertias**, for every algebraically closed field `k` of characteristic `0` and every
set of primes `Σ` (pro-`Σ` form of
`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed`). For
`U ⊆ X` open with finite nonempty complement, `g` the genus and `r = |X ∖ U|`: for every place
`W ⊇ k` of `Ω` not centred on `U`, the image of `cuspInertia U W` in the maximal pro-`Σ` quotient
is mapped, after conjugation, onto the range of `cuspInertiaSigma j` for some `j`. -/
theorem exists_continuousMulEquiv_cuspInertia_curve_proSigma (P : ℕ → Prop) (U : X.Opens)
    [Nonempty U] (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty) :
    ∃ Θ : MaxProSigma P π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
        MaxProSigma P (Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X))),
      ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → ¬ IsCentredOn D X eL U W →
        ∃ (j : Fin (Nat.card ((U : Set X)ᶜ : Set X)))
          (σ : MaxProSigma P π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)),
          ((cuspInertia D X eL hH U W).map (MaxProSigma.mk (P := P))).map
            ((Θ : MaxProSigma P π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →*
              MaxProSigma P (Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
                (Nat.card ((U : Set X)ᶜ : Set X)))).comp (MulAut.conj σ).toMonoidHom) =
            (Pi1.SurfaceGroup.cuspInertiaSigma P j).range := by
  obtain ⟨Θ, hΘ⟩ :=
    exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed D eL hH hk hτ U hUfin hUne
  refine ⟨maxProSigmaCongr P Θ, fun W hWk hW ↦ ?_⟩
  obtain ⟨j, σ, h⟩ := hΘ W hWk hW
  exact ⟨j, MaxProSigma.mk σ, (map_map_mk_conj_of_map_eq P Θ σ h).trans (map_mk_inertia P j)⟩

end Main

section Line

/-- **`π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))^Σ ≃ₜ* Π^Σ_{0,n+2}` with the inertia groups at the cusps going to
conjugates of the pro-`Σ` cusp inertias**, over any algebraically closed field of
characteristic `0` and for every set of primes `Σ` (pro-`Σ` form of
`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertiaS`). For `S = {0, 1}` (`n = 1`) this is
`π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞})^Σ ≅ Π^Σ_{0,3}` with all three inertia groups. -/
theorem exists_continuousMulEquiv_lineInertiaS_proSigma (P : ℕ → Prop) {k Ω : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
    [IsGalois (K₀ k t) Ω] (S : Finset k) {n : ℕ} (hS : S.card = n + 1) (ht : Transcendental k t) :
    ∃ (σ : S ≃ Fin (n + 1))
      (Θ : MaxProSigma P π₁ᵉᵗ(lineGenS S ht) ≃ₜ*
        MaxProSigma P (Pi1.ProfiniteSurfaceGroup 0 (n + 2))),
      ∀ (c : Option S) (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) →
        W.valuation (cuspCoordS (c.map Subtype.val) t) < 1 →
        ∃ τ : MaxProSigma P π₁ᵉᵗ(lineGenS S ht),
          ((lineInertiaS S ht W).map (MaxProSigma.mk (P := P))).map
            ((Θ : MaxProSigma P π₁ᵉᵗ(lineGenS S ht) →*
              MaxProSigma P (Pi1.ProfiniteSurfaceGroup 0 (n + 2))).comp
              (MulAut.conj τ).toMonoidHom) =
            (Pi1.SurfaceGroup.cuspInertiaSigma P (cuspIndex σ c)).range := by
  obtain ⟨σ, Θ, hΘ⟩ := exists_continuousMulEquiv_lineInertiaS S hS ht
  refine ⟨σ, maxProSigmaCongr P Θ, fun c W hWk hWc ↦ ?_⟩
  obtain ⟨τ, h⟩ := hΘ c W hWk hWc
  exact ⟨MaxProSigma.mk τ,
    (map_map_mk_conj_of_map_eq P Θ τ h).trans (map_mk_inertia P (cuspIndex σ c))⟩

end Line

end CurvesJacobian.Cusp
