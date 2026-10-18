/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverOpen

/-!
# `π₁ᵉᵗ` of a pulled-back cover (MR8.5, [AbsTopII] Cor 3.7 (b))

For a cartesian square of connected schemes
```
U --j'--> V
|p'       |p
v         v
Y --j-->  X
```
with `p` (hence `p'`) finite étale, and `π₁ᵉᵗ(Y) → π₁ᵉᵗ(X)` surjective (e.g. `Y ⊆ X` a dense open
of a normal scheme), the image of `π₁ᵉᵗ(U) → π₁ᵉᵗ(Y)` is the preimage of the image of
`π₁ᵉᵗ(V) → π₁ᵉᵗ(X)` (**`AlgebraicGeometry.FiniteEtale.range_fundamentalGroupMap_of_isPullback`**).

Proof: `⊆` is functoriality; both subgroups have index the degree of the cover (stabilisers of
points of the fibres, on which `π₁ᵉᵗ` acts transitively; the fibre of `p'` over `y` is the fibre
of `p` over `y ≫ j`, `pullbackFiberIso`), and taking preimages under a surjection preserves the
index.
-/

open CategoryTheory Limits PreGaloisCategory

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {X Y U V : Scheme.{u}} {p : V ⟶ X} {j : Y ⟶ X} {p' : U ⟶ Y} {j' : U ⟶ V}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The index of the image of `π₁ᵉᵗ` of a connected finite étale cover is the fibre cardinality. -/
lemma index_range_fundamentalGroupMap (f : V ⟶ X) [IsFiniteEtale f] [ConnectedSpace X]
    [ConnectedSpace V] {v : Spec (.of Ω) ⟶ V} {η : Spec (.of Ω) ⟶ X} (h : v ≫ f = η) :
    (fundamentalGroupMap f h).toMonoidHom.range.index = Nat.card ((fiber η).obj (coverObj f)) := by
  haveI : IsConnected (coverObj f) := (isConnected_iff_connectedSpace (coverObj f)).2 ‹_›
  rw [range_fundamentalGroupMap_of_isFiniteEtale' f v h]
  exact MulAction.index_stabilizer_of_transitive _ _

/-- **`π₁ᵉᵗ` of a pulled-back cover**: in a cartesian square of connected schemes with `p` finite
étale and `π₁ᵉᵗ(j)` surjective, `im π₁ᵉᵗ(U) = π₁ᵉᵗ(j)⁻¹(im π₁ᵉᵗ(V))`. -/
theorem range_fundamentalGroupMap_of_isPullback (hsq : IsPullback j' p' p j) [IsFiniteEtale p]
    [IsFiniteEtale p'] [ConnectedSpace U] [ConnectedSpace V] [ConnectedSpace X] [ConnectedSpace Y]
    {y : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X} (hy : y ≫ j = η)
    (hsurj : Function.Surjective (fundamentalGroupMap j hy))
    {u : Spec (.of Ω) ⟶ U} (hu : u ≫ p' = y) (hv : (u ≫ j') ≫ p = η) :
    (fundamentalGroupMap p' hu).toMonoidHom.range =
      (fundamentalGroupMap p hv).toMonoidHom.range.comap
        (fundamentalGroupMap j hy).toMonoidHom := by
  set H' := (fundamentalGroupMap p' hu).toMonoidHom.range
  set H := (fundamentalGroupMap p hv).toMonoidHom.range
  have hle : H' ≤ H.comap (fundamentalGroupMap j hy).toMonoidHom := by
    rintro _ ⟨σ, rfl⟩
    have h1 : u ≫ p' ≫ j = η := by rw [← Category.assoc, hu, hy]
    have h2 : u ≫ j' ≫ p = η := by rw [← Category.assoc, hv]
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp p' j hu hy h1) σ
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp j' p rfl hv h2) σ
    rw [fundamentalGroupMap_congr hsq.w.symm h1 h2] at c1
    exact ⟨fundamentalGroupMap j' rfl σ, c2.symm.trans c1⟩
  -- the fibres of `p'` over `y` and of `p` over `η` correspond
  let e : coverObj p' ≅ (pullback j).obj (coverObj p) :=
    MorphismProperty.Over.isoMk hsq.isoPullback (by exact hsq.isoPullback_hom_snd)
  have hcard : Nat.card ((fiber y).obj (coverObj p')) = Nat.card ((fiber η).obj (coverObj p)) :=
    Nat.card_congr (FintypeCat.equivEquivIso.symm
      ((fiber y).mapIso e ≪≫ (pullbackFiberIso j hy).app (coverObj p)))
  have hindex : H'.index = (H.comap (fundamentalGroupMap j hy).toMonoidHom).index := by
    rw [Subgroup.index_comap_of_surjective _ hsurj, index_range_fundamentalGroupMap p' hu,
      index_range_fundamentalGroupMap p hv, hcard]
  have hne : H'.index ≠ 0 := by
    rw [index_range_fundamentalGroupMap p' hu]
    haveI : Nonempty ((fiber y).obj (coverObj p')) := ⟨coverPt p' u hu⟩
    exact Nat.card_pos.ne'
  apply le_antisymm hle
  have hrel := Subgroup.relIndex_mul_index hle
  rw [← hindex] at hrel
  have h1 : H'.relIndex (H.comap (fundamentalGroupMap j hy).toMonoidHom) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hrel.trans (one_mul _).symm)
    exact this
  exact Subgroup.relIndex_eq_one.1 h1

end AlgebraicGeometry.FiniteEtale
