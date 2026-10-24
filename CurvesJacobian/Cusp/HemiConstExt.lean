/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiArith

/-!
# Constant field extensions of the hemi-elliptic orbicurve (MR8, [AbsTopII] Cor. 3.3 (iii))

Let `D : GaloisData k t` (`H_L ≤ H ≤ Gal(Ω / k(t))`, inertia elements `S ⊆ H_L`) and let `U` be
an open normal subgroup of `Gal(Ω / k(t))` containing `S`. We cut `H_L` down to `H_L ⊓ U`:

* `CurvesJacobian.Cusp.galoisDataInf₃ D U`: the Galois data with `H := H`, `H_L := H_L ⊓ U`;
  its inertia elements are those of `D` (`galoisDataInf₃_S`);
* `Π_V := (H_L ⊓ U) ⧸ ⟨⟨S⟩⟩`, `Π_X := H_L ⧸ ⟨⟨S⟩⟩`, `Π_C := H ⧸ ⟨⟨S⟩⟩`, and the open embeddings
  `infInclX₃ : Π_V → Π_X`, `infInclC₃ : Π_V → Π_C` with `ι ∘ infInclX₃ = infInclC₃`
  (`orbiIncl_infInclX₃`); the image of `Π_V` in `Π_C` is normal (`range_infInclC₃_normal`) of
  index `[H : H_L ⊓ U]` (`index_range_infInclC₃`) with quotient `H ⧸ (H_L ⊓ U)`
  (`infQuotEquiv₃`).

For the constants we take `U = constFixer₃ t M`, the elements of `Gal(Ω / k(t))` fixing a finite
Galois extension `M ⊆ k̄` of `k` (`k̄` the algebraic closure of `k` in `Ω`); it contains `S`
(`S_subset_constFixer₃`, from `galResConst_eq_one_of_mem_inertia`). Then:

* `L_galoisDataConst₃`: the function field `Ω^{H_L ⊓ Gal(Ω / M)}` of `V` is the compositum
  `L ⊔ k(t)(M)`;
* `range_piConstX_inf₃`: the image of `Π_V` in `Gal(k̄ / k)` is `im(Π_X) ⊓ Gal(k̄ / M)`;
* `range_piConstX_inf₃_of_top`, `index_range_infInclC₃_of_top`: if `Π_X → Gal(k̄ / k)` is
  surjective (geometric connectedness of `X`), then the image of `Π_V` is `Gal(k̄ / M)` and
  `[Π_C : Π_V] = [H : H_L] · [M : k]`.

Applied to `D = hemiData E` (`C = [(E ∖ {O}) / ±1]`, `H = Gal(Ω / K(x))`, `H_L = Gal(Ω / K(E))`):
`CurvesJacobian.Cusp.hemiDataM E M` is the Galois data of `V = X_M = (E ∖ {O})_M`, with
`H_L = Gal(Ω / K(E)) ⊓ Gal(Ω / M) = Gal(Ω / K(E) · M)` (`hemiDataM_L`) normal
(`hemiDataM_HL_normal`), the same inertia (`hemiDataM_S`), `Π_V ↪ Π_X ↪ Π_C` with `Π_V ⊴ Π_C`
(`hemi_constExt`), `Π_C ⧸ Π_V ≃ A_M` (`hemiConstQuotEquiv`), and, given surjectivity of
`Π_X → Gal(k̄ / K)`, image `Gal(k̄ / M)` and index `2 · [M : K]` (`hemi_constExt_of_top`).
For `K` a number field this surjectivity holds (`range_piConstX_hemi`, from `pr : Π_X ↠ G_K`
of `arithmeticExt` and `hemiGkEquiv_pr`), so `hemi_constExt_numberField` is unconditional.
-/

open CategoryTheory AlgebraicGeometry Belyi Pi1.Orbifold AffOrbicurve Topology

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section GenericInf

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (U : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (hUo : IsOpen (U : Set (Ω ≃ₐ[K₀ k t] Ω))) (hUn : U.Normal)

/-- **The Galois data cut down by `U`**: `H := H`, `H_L := H_L ⊓ U`. -/
def galoisDataInf₃ : GaloisData k t where
  H := D.H
  HL := D.HL ⊓ U
  le := inf_le_left.trans D.le
  isOpen_HL := D.isOpen_HL.inter hUo
  conj_mem := fun h hh n hn => ⟨D.conj_mem h hh n hn.1, hUn.conj_mem n hn.2 h⟩
  transcendental := D.transcendental

lemma galoisDataInf₃_H : (galoisDataInf₃ D U hUo hUn).H = D.H := rfl

lemma galoisDataInf₃_HL : (galoisDataInf₃ D U hUo hUn).HL = D.HL ⊓ U := rfl

lemma S_inf_subset₃ : (galoisDataInf₃ D U hUo hUn).S ⊆ D.S := fun _ h => ⟨h.1.1, h.2⟩

variable {D U hUo hUn} in
lemma S_inf_supset₃ (hSU : D.S ⊆ U) : D.S ⊆ (galoisDataInf₃ D U hUo hUn).S :=
  fun _ h => ⟨⟨h.1, hSU h⟩, h.2⟩

/-- **Same inertia**: for `S ⊆ U`, the inertia elements of `galoisDataInf₃ D U` are those
of `D`. -/
theorem galoisDataInf₃_S (hSU : D.S ⊆ U) : (galoisDataInf₃ D U hUo hUn).S = D.S :=
  subset_antisymm (S_inf_subset₃ D U hUo hUn) (S_inf_supset₃ hSU)

lemma galoisDataInf₃_HL_normal (hn : D.HL.Normal) : (galoisDataInf₃ D U hUo hUn).HL.Normal :=
  Subgroup.normal_inf_normal D.HL U

variable [IsGalois (K₀ k t) Ω]

/-- `Π_V = (H_L ⊓ U) ⧸ ⟨⟨S⟩⟩ → Π_X = H_L ⧸ ⟨⟨S⟩⟩`. -/
def infInclX₃ : GaloisPi1.pi1 (galoisDataInf₃ D U hUo hUn).HL (galoisDataInf₃ D U hUo hUn).S
    (galoisDataInf₃ D U hUo hUn).isClosed_HL →ₜ* GaloisPi1.pi1 D.HL D.S D.isClosed_HL where
  toMonoidHom := GaloisPi1.pi1Map (galoisDataInf₃ D U hUo hUn).isClosed_HL D.isClosed_HL
    inf_le_left (S_inf_subset₃ D U hUo hUn)
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ (S_inf_subset₃ D U hUo hUn)

/-- `Π_V = (H_L ⊓ U) ⧸ ⟨⟨S⟩⟩ → Π_C = H ⧸ ⟨⟨S⟩⟩`. -/
def infInclC₃ : GaloisPi1.pi1 (galoisDataInf₃ D U hUo hUn).HL (galoisDataInf₃ D U hUo hUn).S
    (galoisDataInf₃ D U hUo hUn).isClosed_HL →ₜ* GaloisPi1.pi1 D.H D.S D.isClosed_H where
  toMonoidHom := GaloisPi1.pi1Map (galoisDataInf₃ D U hUo hUn).isClosed_HL D.isClosed_H
    (galoisDataInf₃ D U hUo hUn).le (S_inf_subset₃ D U hUo hUn)
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ (S_inf_subset₃ D U hUo hUn)

/-- **Compatibility**: `ι ∘ (Π_V → Π_X) = (Π_V → Π_C)`. -/
theorem orbiIncl_infInclX₃ (x : GaloisPi1.pi1 (galoisDataInf₃ D U hUo hUn).HL
    (galoisDataInf₃ D U hUo hUn).S (galoisDataInf₃ D U hUo hUn).isClosed_HL) :
    orbiIncl D (infInclX₃ D U hUo hUn x) = infInclC₃ D U hUo hUn x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

variable {D U hUo hUn}

/-- `Π_V → Π_X` is an open embedding. -/
theorem isOpenEmbedding_infInclX₃ (hSU : D.S ⊆ U) :
    IsOpenEmbedding (infInclX₃ D U hUo hUn) :=
  GaloisPi1.isOpenEmbedding_pi1Map' _ _ _ (S_inf_subset₃ D U hUo hUn) (S_inf_supset₃ hSU)
    (galoisDataInf₃ D U hUo hUn).isOpen_HL
    fun _ hh _ hs => conj_mem_S (galoisDataInf₃ D U hUo hUn) (D.le hh) hs

/-- `Π_V → Π_C` is an open embedding. -/
theorem isOpenEmbedding_infInclC₃ (hSU : D.S ⊆ U) :
    IsOpenEmbedding (infInclC₃ D U hUo hUn) :=
  GaloisPi1.isOpenEmbedding_pi1Map' _ _ _ (S_inf_subset₃ D U hUo hUn) (S_inf_supset₃ hSU)
    (galoisDataInf₃ D U hUo hUn).isOpen_HL
    fun _ hh _ hs => conj_mem_S (galoisDataInf₃ D U hUo hUn) hh hs

/-- The identification of `H ⧸ ⟨⟨S'⟩⟩` (inertia of `galoisDataInf₃ D U`) with
`H ⧸ ⟨⟨S⟩⟩`, for `S ⊆ U`. -/
def piEquivInf₃ (hSU : D.S ⊆ U) :
    GaloisPi1.pi1 (galoisDataInf₃ D U hUo hUn).H (galoisDataInf₃ D U hUo hUn).S
      (galoisDataInf₃ D U hUo hUn).isClosed_H ≃ₜ* GaloisPi1.pi1 D.H D.S D.isClosed_H where
  toMulEquiv := MonoidHom.toMulEquiv
    (GaloisPi1.pi1Map (galoisDataInf₃ D U hUo hUn).isClosed_H D.isClosed_H le_rfl
      (S_inf_subset₃ D U hUo hUn))
    (GaloisPi1.pi1Map D.isClosed_H (galoisDataInf₃ D U hUo hUn).isClosed_H le_rfl
      (S_inf_supset₃ hSU))
    (MonoidHom.ext fun x => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rfl)
    (MonoidHom.ext fun x => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rfl)
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ (S_inf_subset₃ D U hUo hUn)
  continuous_invFun := GaloisPi1.continuous_pi1Map _ _ _ (S_inf_supset₃ hSU)

lemma infInclC₃_eq (hSU : D.S ⊆ U) (x : GaloisPi1.pi1 (galoisDataInf₃ D U hUo hUn).HL
    (galoisDataInf₃ D U hUo hUn).S (galoisDataInf₃ D U hUo hUn).isClosed_HL) :
    infInclC₃ D U hUo hUn x = piEquivInf₃ hSU (orbiIncl (galoisDataInf₃ D U hUo hUn) x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- The image of `Π_V` in `Π_C` is the image of `ι` for `galoisDataInf₃ D U`. -/
theorem range_infInclC₃ (hSU : D.S ⊆ U) :
    (infInclC₃ D U hUo hUn).toMonoidHom.range =
      (orbiIncl (galoisDataInf₃ D U hUo hUn)).toMonoidHom.range.map
        ((piEquivInf₃ hSU).toMulEquiv : _ →* _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, (infInclC₃_eq hSU x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, infInclC₃_eq hSU x⟩

/-- **`Π_V ⊴ Π_C`.** -/
theorem range_infInclC₃_normal (hSU : D.S ⊆ U) :
    (infInclC₃ D U hUo hUn).toMonoidHom.range.Normal := by
  rw [range_infInclC₃ hSU]
  exact Subgroup.Normal.map (range_orbiIncl_normal _) _ (piEquivInf₃ hSU).toMulEquiv.surjective

/-- **`[Π_C : Π_V] = [H : H_L ⊓ U]`.** -/
theorem index_range_infInclC₃ (hSU : D.S ⊆ U) :
    (infInclC₃ D U hUo hUn).toMonoidHom.range.index =
      (galoisDataInf₃ D U hUo hUn).HL.relIndex D.H := by
  rw [range_infInclC₃ hSU, Subgroup.index_map_equiv]
  exact index_range_orbiIncl _

/-- **`Π_C ⧸ Π_V ≃ H ⧸ (H_L ⊓ U)`.** -/
def infQuotEquiv₃ (hSU : D.S ⊆ U) :
    letI := range_infInclC₃_normal (hUo := hUo) (hUn := hUn) hSU
    GaloisPi1.pi1 D.H D.S D.isClosed_H ⧸ (infInclC₃ D U hUo hUn).toMonoidHom.range ≃*
      (galoisDataInf₃ D U hUo hUn).A :=
  letI := range_infInclC₃_normal (hUo := hUo) (hUn := hUn) hSU
  (QuotientGroup.congr _ _ (piEquivInf₃ hSU).toMulEquiv (range_infInclC₃ hSU).symm).symm.trans
    (orbiQuotEquiv _)

end GenericInf

section Constants

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- The image of `piConst H S` is the restriction of `H` to the constants. -/
lemma range_piConst₃ [IsGalois (K₀ k t) Ω] (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω))
    (S : Set (Ω ≃ₐ[K₀ k t] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω)))
    (hS : ∀ s ∈ S, galResConst t s = 1) : (piConst H S hH hS).range = H.map (galResConst t) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk (⟨x, hx⟩ : H), rfl⟩

variable (t) in
/-- **The elements of `Gal(Ω / k(t))` fixing `M ⊆ k̄`**: the preimage of `Gal(k̄ / M)` under the
restriction to the constants. -/
def constFixer₃ (M : IntermediateField k (ConstField₂ k Ω)) : Subgroup (Ω ≃ₐ[K₀ k t] Ω) :=
  M.fixingSubgroup.comap (galResConst t)

lemma isOpen_constFixer₃ (M : IntermediateField k (ConstField₂ k Ω)) [FiniteDimensional k M] :
    IsOpen (constFixer₃ t M : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  M.fixingSubgroup_isOpen.preimage (continuous_galResConst t)

/-- The inertia elements fix the constants, hence lie in `constFixer₃ t M`. -/
lemma S_subset_constFixer₃ (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω)) :
    D.S ⊆ constFixer₃ t M := fun s hs => by
  change galResConst t s ∈ M.fixingSubgroup
  rw [galResConst_S D hs]
  exact one_mem _

variable [IsAlgClosed Ω] [CharZero k]

instance isGalois_constField₃ : IsGalois k (ConstField₂ k Ω) := {}

lemma constFixer₃_normal (M : IntermediateField k (ConstField₂ k Ω)) [IsGalois k M] :
    (constFixer₃ t M).Normal :=
  Subgroup.Normal.comap ((InfiniteGalois.normal_iff_isGalois M).2 inferInstance) _

variable [IsGalois (K₀ k t) Ω] (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω))
  [FiniteDimensional k M] [IsGalois k M]

/-- The Galois data cut down to the constant extension `M`: `H_L := H_L ⊓ Gal(Ω / M)`. -/
abbrev galoisDataConst₃ : GaloisData k t :=
  galoisDataInf₃ D (constFixer₃ t M) (isOpen_constFixer₃ M) (constFixer₃_normal M)

/-- The image of `M ⊆ k̄` in `Ω`. -/
def constSet₃ : Set Ω := Set.range fun m : M => ((m : ConstField₂ k Ω) : Ω)

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
/-- `constFixer₃ t M` is the fixing subgroup of `k(t)(M)`. -/
lemma fixingSubgroup_adjoin_constSet₃ :
    (IntermediateField.adjoin (K₀ k t) (constSet₃ M)).fixingSubgroup = constFixer₃ t M := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    change galResConst t σ ∈ M.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro m hm
    exact Subtype.ext (h _ (IntermediateField.subset_adjoin _ _ ⟨⟨m, hm⟩, rfl⟩))
  · intro h x hx
    have h' : galResConst t σ ∈ M.fixingSubgroup := h
    rw [IntermediateField.mem_fixingSubgroup_iff] at h'
    refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := K₀ k t)
      (S := constSet₃ M) σ).2 ?_ x hx
    rintro _ ⟨m, rfl⟩
    exact congrArg Subtype.val (h' m m.2)

/-- **The function field of `V` is the compositum `L · M`**:
`Ω^{H_L ⊓ Gal(Ω / M)} = L ⊔ k(t)(M)`. -/
theorem L_galoisDataConst₃ : (galoisDataConst₃ D M).L =
    D.L ⊔ IntermediateField.adjoin (K₀ k t) (constSet₃ M) := by
  change IntermediateField.fixedField (D.HL ⊓ constFixer₃ t M) = _
  rw [← fixingSubgroup_adjoin_constSet₃, ← D.fixingSubgroup_L,
    ← IntermediateField.fixingSubgroup_sup, InfiniteGalois.fixedField_fixingSubgroup]

/-- **Compatibility with the projections to `Gal(k̄ / k)`.** -/
theorem piConstC_comp_infInclC₃ :
    (piConstC D).comp (infInclC₃ D (constFixer₃ t M) (isOpen_constFixer₃ M)
      (constFixer₃_normal M)).toMonoidHom = piConstX (galoisDataConst₃ D M) := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- **The image of `Π_V` in `Gal(k̄ / k)` is `im(Π_X) ⊓ Gal(k̄ / M)`.** -/
theorem range_piConstX_inf₃ :
    (piConstX (galoisDataConst₃ D M)).range = (piConstX D).range ⊓ M.fixingSubgroup := by
  rw [range_piConst₃, range_piConst₃]
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, hx1, rfl⟩, hx2⟩
  · rintro ⟨⟨x, hx, rfl⟩, hv⟩
    exact ⟨x, ⟨hx, hv⟩, rfl⟩

/-- If `Π_X → Gal(k̄ / k)` is surjective, the image of `Π_V` is `Gal(k̄ / M)`. -/
theorem range_piConstX_inf₃_of_top (hgeom : (piConstX D).range = ⊤) :
    (piConstX (galoisDataConst₃ D M)).range = M.fixingSubgroup := by
  rw [range_piConstX_inf₃, hgeom, top_inf_eq]

/-- If `Π_X → Gal(k̄ / k)` is surjective, `[Π_C : Π_V] = [H : H_L] · [M : k]`. -/
theorem index_range_infInclC₃_of_top (hgeom : (piConstX D).range = ⊤) :
    (infInclC₃ D (constFixer₃ t M) (isOpen_constFixer₃ M)
      (constFixer₃_normal M)).toMonoidHom.range.index =
      D.HL.relIndex D.H * Module.finrank k M := by
  rw [index_range_infInclC₃ (S_subset_constFixer₃ D M)]
  have hle : (galoisDataConst₃ D M).HL ≤ D.HL := inf_le_left
  refine (Subgroup.relIndex_mul_relIndex _ _ _ hle D.le).symm.trans ?_
  rw [mul_comm]
  congr 1
  have hmap : D.HL.map (galResConst t) = ⊤ := by
    rw [← range_piConst₃ D.HL D.S D.isClosed_HL fun _ hs => galResConst_S D hs]
    exact hgeom
  have h1 : (D.HL ⊓ constFixer₃ t M).relIndex D.HL = (constFixer₃ t M).relIndex D.HL := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  change (D.HL ⊓ constFixer₃ t M).relIndex D.HL = _
  rw [h1, constFixer₃, Subgroup.relIndex_comap, hmap, Subgroup.relIndex_top_right,
    IntermediateField.finrank_eq_fixingSubgroup_index]

end Constants

section Hemi

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E)))) [FiniteDimensional K M]
  [IsGalois K M]

/-- **The Galois data of `V = X_M = (E ∖ {O})_M`** inside the hemi-elliptic orbicurve
`C = [(E ∖ {O}) / ±1]`: `H = Gal(Ω / K(x))`, `H_L = Gal(Ω / K(E)) ⊓ Gal(Ω / M)`. -/
abbrev hemiDataM : GaloisData K (coordT (xN E)) := galoisDataConst₃ (hemiData E) M

lemma hemiDataM_H : (hemiDataM E M).H = ⊤ := rfl

lemma hemiDataM_HL :
    (hemiDataM E M).HL = (hemiData E).HL ⊓ constFixer₃ (coordT (xN E)) M := rfl

/-- **`L_M = K(E) · M`**: the function field of `V = X_M` is the compositum of `K(E)` and `M`. -/
theorem hemiDataM_L : (hemiDataM E M).L =
    (hemiData E).L ⊔ IntermediateField.adjoin (K₀ K (coordT (xN E))) (constSet₃ M) :=
  L_galoisDataConst₃ _ M

/-- `H_L = Gal(Ω / M · K(E))` is normal in `Gal(Ω / K(x))`. -/
theorem hemiDataM_HL_normal : (hemiDataM E M).HL.Normal :=
  galoisDataInf₃_HL_normal _ _ _ _ (hemiHL_normal E)

/-- `H_L` is open. -/
theorem isOpen_hemiDataM_HL :
    IsOpen ((hemiDataM E M).HL : Set (FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))]
      FFClosure (curveE E))) :=
  (hemiDataM E M).isOpen_HL

/-- **Same inertia**: the inertia elements of `hemiDataM E M` are those of `hemiData E`. -/
theorem hemiDataM_S : (hemiDataM E M).S = (hemiData E).S :=
  galoisDataInf₃_S _ _ _ _ (S_subset_constFixer₃ _ M)

/-- **`Π_V ↪ Π_X ↪ Π_C`** for `V = X_M`: open embeddings, compatible, with `Π_V` normal in `Π_C`
of index `[M · K(E) : K(x)]`, compatible with the projections to `Gal(k̄ / K)`, and the image of
`Π_V` in `Gal(k̄ / K)` is `im(Π_X) ⊓ Gal(k̄ / M)`. -/
theorem hemi_constExt :
    IsOpenEmbedding (infInclX₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)) ∧
      IsOpenEmbedding (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)) ∧
      (∀ x, orbiIncl (hemiData E) (infInclX₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M) x) =
          infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M) x) ∧
      (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom.range.Normal ∧
      (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom.range.index =
          Module.finrank (K₀ K (coordT (xN E))) (hemiDataM E M).L ∧
      (piConstC (hemiData E)).comp (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom = piConstX (hemiDataM E M) ∧
      (piConstX (hemiDataM E M)).range = (piConstX (hemiData E)).range ⊓ M.fixingSubgroup := by
  have hSU := S_subset_constFixer₃ (hemiData E) M
  refine ⟨isOpenEmbedding_infInclX₃ hSU, isOpenEmbedding_infInclC₃ hSU,
    orbiIncl_infInclX₃ _ _ _ _, range_infInclC₃_normal hSU, ?_,
    piConstC_comp_infInclC₃ _ M, range_piConstX_inf₃ _ M⟩
  rw [index_range_infInclC₃ hSU, IntermediateField.finrank_eq_fixingSubgroup_index,
    (hemiDataM E M).fixingSubgroup_L]
  exact Subgroup.relIndex_top_right _

/-- **`Π_C ⧸ Π_V ≃ A_M = Gal(Ω / K(x)) ⧸ H_L ≅ Gal(M · K(E) / K(x))`.** -/
def hemiConstQuotEquiv :
    letI := range_infInclC₃_normal (hUo := isOpen_constFixer₃ M) (hUn := constFixer₃_normal M)
      (S_subset_constFixer₃ (hemiData E) M)
    GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H ⧸
      (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom.range ≃* (hemiDataM E M).A :=
  infQuotEquiv₃ (S_subset_constFixer₃ (hemiData E) M)

/-- **Given surjectivity of `Π_X → Gal(k̄ / K)`** (geometric connectedness of `E ∖ {O}`), the
image of `Π_V` in `Gal(k̄ / K)` is `Gal(k̄ / M)` and `[Π_C : Π_V] = 2 · [M : K]`. -/
theorem hemi_constExt_of_top (hgeom : (piConstX (hemiData E)).range = ⊤) :
    (piConstX (hemiDataM E M)).range = M.fixingSubgroup ∧
      (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom.range.index = 2 * Module.finrank K M := by
  refine ⟨range_piConstX_inf₃_of_top _ M hgeom, ?_⟩
  rw [index_range_infInclC₃_of_top _ M hgeom, ← index_range_orbiIncl (hemiData E),
    index_range_orbiIncl_hemi]

/-- **Geometric connectedness, for `K` a number field**: `Π_X → Gal(k̄ / K)` is surjective
(from `pr : Π_X ↠ G_K` of `arithmeticExt` and `hemiGkEquiv_pr`). -/
theorem range_piConstX_hemi [NumberField K] : (piConstX (hemiData E)).range = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨γ, hγ⟩ := (arithmeticExt (AlgebraicClosure K) (hypCurveX E)
    (compl_XE_nonempty E)).pr_surjective ((hemiGkEquiv E (AlgebraicClosure K)).symm g)
  refine ⟨hemiPiXGal E (AlgebraicClosure K) γ, ?_⟩
  rw [← hemiGkEquiv_pr, hγ, ContinuousMulEquiv.apply_symm_apply]

/-- **For `K` a number field** (e.g. `F_mod`): the image of `Π_V` in `Gal(k̄ / K)` is
`Gal(k̄ / M)` and `[Π_C : Π_V] = 2 · [M : K]`. -/
theorem hemi_constExt_numberField [NumberField K] :
    (piConstX (hemiDataM E M)).range = M.fixingSubgroup ∧
      (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M)
        (constFixer₃_normal M)).toMonoidHom.range.index = 2 * Module.finrank K M :=
  hemi_constExt_of_top E M (range_piConstX_hemi E)

end Hemi

end CurvesJacobian.Cusp
