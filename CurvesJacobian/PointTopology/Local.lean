/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.PointTopology.Proper

/-!
# Fibre products and compact open neighbourhoods in `X(L)`

`L` is a proper normed field and `S` an affine scheme.

* **`continuous_pullbackLift`**: for `f : X ⟶ S`, `g : Y ⟶ S` (`X`, `Y` quasi-separated,
  `X ×_S Y` quasi-compact), the map `X(L) ×_{S(L)} Y(L) → (X ×_S Y)(L)`, `(x, y) ↦ (x, y)`, is
  continuous;
* **`exists_isOpen_isCompact`**: for `f : X ⟶ S` locally of finite type and `L` ultrametric,
  every neighbourhood of a point `x₀ ∈ X(L)` contains an open neighbourhood `K` of `x₀` whose
  intersection with each fibre `X(L)_{s₀}` is compact (a polydisc in the coordinates of an affine
  open).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Topology Filter Limits

noncomputable section

namespace CurvesJacobian.PointTopology

variable {X Y S : Scheme.{u}} {L : Type u} [NormedField L]

lemma ev_congr {R : CommRingCat.{u}} {x x' : Spec R ⟶ X} (e : x = x') {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (a : Γ(X, U)) : ev x U h a = ev x' U h' a := by
  subst e
  rfl

/-- **Continuity of `(x, y) ↦ (x, y) : X(L) ×_{S(L)} Y(L) → (X ×_S Y)(L)`.** -/
theorem continuous_pullbackLift [ProperSpace L] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) [CompactSpace ↥(Limits.pullback f g)] :
    Continuous fun p : {p : (Spec (CommRingCat.of L) ⟶ X) × (Spec (CommRingCat.of L) ⟶ Y) //
        p.1 ≫ f = p.2 ≫ g} ↦ pullback.lift p.1.1 p.1.2 p.2 := by
  refine continuous_iff_ultrafilter.mpr fun p 𝒱 h𝒱 ↦ ?_
  have hX : Tendsto (fun q : {p : (Spec (CommRingCat.of L) ⟶ X) × (Spec (CommRingCat.of L) ⟶ Y)
      // p.1 ≫ f = p.2 ≫ g} ↦ q.1.1) 𝒱 (𝓝 p.1.1) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto p).comp h𝒱
  have hY : Tendsto (fun q : {p : (Spec (CommRingCat.of L) ⟶ X) × (Spec (CommRingCat.of L) ⟶ Y)
      // p.1 ≫ f = p.2 ≫ g} ↦ q.1.2) 𝒱 (𝓝 p.1.2) :=
    ((continuous_snd.comp continuous_subtype_val).tendsto p).comp h𝒱
  obtain ⟨UX, hUX, -, hpX⟩ := exists_affine_lands p.1.1 (U := ⊤) (fun _ _ ↦ trivial)
  obtain ⟨UY, hUY, -, hpY⟩ := exists_affine_lands p.1.2 (U := ⊤) (fun _ _ ↦ trivial)
  obtain ⟨ξX, hξX, -⟩ := exists_isGermPt (𝒰 := 𝒱) _ hUX
    (((tendsto_iff.mp hX) UX 0 Set.univ isOpen_univ hpX trivial).mono fun _ ⟨h, _⟩ ↦ h)
  obtain ⟨ξY, hξY, -⟩ := exists_isGermPt (𝒰 := 𝒱) _ hUY
    (((tendsto_iff.mp hY) UY 0 Set.univ isOpen_univ hpY trivial).mono fun _ ⟨h, _⟩ ↦ h)
  obtain ⟨ℓX, hℓX, hstX⟩ := exists_lift_of_tendsto hξX hX
  obtain ⟨ℓY, hℓY, hstY⟩ := exists_lift_of_tendsto hξY hY
  obtain ⟨U₀, hU₀, hz⟩ := exists_affine_eventually
    (fun q : {p : (Spec (CommRingCat.of L) ⟶ X) × (Spec (CommRingCat.of L) ⟶ Y) //
      p.1 ≫ f = p.2 ≫ g} ↦ pullback.lift q.1.1 q.1.2 q.2) 𝒱
  obtain ⟨ζ, hζ, -⟩ := exists_isGermPt _ hU₀ hz
  have h1 : ζ ≫ pullback.fst f g = ξX := by
    have := hζ.comp (pullback.fst f g)
    simp only [pullback.lift_fst] at this
    exact this.unique hξX
  have h2 : ζ ≫ pullback.snd f g = ξY := by
    have := hζ.comp (pullback.snd f g)
    simp only [pullback.lift_snd] at this
    exact this.unique hξY
  have hcond : ℓX ≫ f = ℓY ≫ g := eq_of_specMap_ιV_comp (by
    rw [← Category.assoc, hℓX, ← Category.assoc, hℓY, ← h1, ← h2, Category.assoc,
      Category.assoc, pullback.condition])
  have hℓ : Spec.map (ιV 𝒱 L) ≫ pullback.lift ℓX ℓY hcond = ζ :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, hℓX, h1])
      (by rw [Category.assoc, pullback.lift_snd, hℓY, h2])
  have := tendsto_of_lift hζ _ hℓ
  convert this using 2
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hstX]
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hstY]

/-- **Compact open neighbourhoods**: for `f : X ⟶ S` locally of finite type (`S` affine) and `L`
ultrametric, every neighbourhood `W` of `x₀ ∈ X(L)` contains an open neighbourhood `K` of `x₀`
with `K ∩ X(L)_{s₀}` compact. -/
theorem exists_isOpen_isCompact [ProperSpace L] [IsUltrametricDist L] [IsAffine S] {f : X ⟶ S}
    [LocallyOfFiniteType f] (s₀ : Spec (CommRingCat.of L) ⟶ S) {x₀ : Spec (CommRingCat.of L) ⟶ X}
    {W : Set (Spec (CommRingCat.of L) ⟶ X)} (hW : W ∈ 𝓝 x₀) :
    ∃ K : Set (Spec (CommRingCat.of L) ⟶ X), IsOpen K ∧ x₀ ∈ K ∧ K ⊆ W ∧
      IsCompact (K ∩ {x | x ≫ f = s₀}) := by
  classical
  -- a finite intersection of subbasic sets inside `W`
  obtain ⟨_, ⟨F, ⟨hFfin, hFsub⟩, rfl⟩, hx₀F, hFW⟩ :=
    (TopologicalSpace.isTopologicalBasis_of_subbasis (s := subbasis X L) rfl).mem_nhds_iff.mp hW
  have hd : ∀ s ∈ F, ∃ (U : X.Opens) (a : Γ(X, U)) (O : Set L), IsOpen O ∧
      s = {x : Spec (CommRingCat.of L) ⟶ X | ∃ h : ⊤ ≤ x ⁻¹ᵁ U, ev x U h a ∈ O} :=
    fun s hs ↦ hFsub hs
  choose! U a O hO hs using hd
  have hx₀s : ∀ s ∈ F, ∃ h : ⊤ ≤ x₀ ⁻¹ᵁ U s, ev x₀ (U s) h (a s) ∈ O s := fun s hsF ↦ by
    have := hx₀F s hsF
    rw [hs s hsF] at this
    exact this
  -- an affine open `W₀ ∋ x₀` inside all `U s`
  let V : X.Opens := ⟨⋂ s ∈ F, (U s : Set X), hFfin.isOpen_biInter fun s _ ↦ (U s).isOpen⟩
  have hx₀V : x₀ (pt L) ∈ V := Set.mem_iInter₂.mpr fun s hsF ↦
    mem_of_lands x₀ (hx₀s s hsF).1
  obtain ⟨W₀, hW₀, hx₀W₀', hW₀V⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx₀V
  have hx₀W₀ : ⊤ ≤ x₀ ⁻¹ᵁ W₀ := lands_of_mem x₀ _ hx₀W₀'
  have hW₀U : ∀ s ∈ F, W₀ ≤ U s := fun s hsF p hp ↦
    Set.mem_iInter₂.mp (hW₀V hp) s hsF
  -- generators of `Γ(X, W₀)` over `Γ(S, ⊤)`
  have e : W₀ ≤ f ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  let φ := f.appLE ⊤ W₀ e
  have hft : φ.hom.FiniteType := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f
    inferInstance ⟨⊤, isAffineOpen_top S⟩ ⟨W₀, hW₀⟩ e
  letI := φ.hom.toAlgebra
  obtain ⟨gens, hgens⟩ := hft.out
  -- the coordinates used: the generators and the restrictions of the `a s`
  let res : F → Γ(X, W₀) := fun s ↦ X.presheaf.map (homOfLE (hW₀U s.1 s.2)).op (a s.1)
  let T : Finset Γ(X, W₀) := gens ∪ hFfin.toFinset.attach.image
    (fun s ↦ res ⟨s.1, hFfin.mem_toFinset.mp s.2⟩)
  -- a radius
  have hr : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ s ∈ F, Metric.closedBall (evT x₀ (U s) (a s)) r ⊆ O s := by
    refine (Filter.eventually_all_finite hFfin).mpr fun s hsF ↦ ?_
    obtain ⟨h, hmem⟩ := hx₀s s hsF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO s hsF) _ hmem
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    rw [evT_eq _ h]
    exact (Metric.closedBall_subset_ball hr.2).trans hball
  obtain ⟨r, hrF, hr0⟩ := (hr.and self_mem_nhdsWithin).exists
  let K : Set (Spec (CommRingCat.of L) ⟶ X) :=
    {x | ∃ h : ⊤ ≤ x ⁻¹ᵁ W₀, ∀ b ∈ T, ev x W₀ h b ∈ Metric.closedBall (evT x₀ W₀ b) r}
  have hKeq : K = {x : Spec (CommRingCat.of L) ⟶ X | ⊤ ≤ x ⁻¹ᵁ W₀} ∩ ⋂ b ∈ T,
      {x : Spec (CommRingCat.of L) ⟶ X |
        ∃ h : ⊤ ≤ x ⁻¹ᵁ W₀, ev x W₀ h b ∈ Metric.closedBall (evT x₀ W₀ b) r} := by
    ext x
    simp only [K, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h, hb⟩ ↦ ⟨h, fun b hbT ↦ ⟨h, hb b hbT⟩⟩, fun ⟨h, hb⟩ ↦ ⟨h, fun b hbT ↦
      (hb b hbT).2⟩⟩
  refine ⟨K, ?_, ⟨hx₀W₀, fun b _ ↦ ?_⟩, ?_, ?_⟩
  · rw [hKeq]
    exact (isOpen_setOf_lands W₀).inter (isOpen_biInter_finset fun b _ ↦
      isOpen_setOf_ev W₀ b (IsUltrametricDist.isOpen_closedBall _ (ne_of_gt hr0)))
  · rw [evT_eq _ hx₀W₀]
    exact Metric.mem_closedBall_self (le_of_lt hr0)
  · rintro x ⟨hx, hxT⟩
    apply hFW
    intro s hsF
    rw [hs s hsF]
    refine ⟨lands_mono (hW₀U s hsF) hx, ?_⟩
    have hb : res ⟨s, hsF⟩ ∈ T := Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨⟨s, hFfin.mem_toFinset.mpr hsF⟩, Finset.mem_attach _ _, rfl⟩)
    have h1 := hxT _ hb
    rw [← ev_res x (hW₀U s hsF) hx, evT_eq _ hx₀W₀, ← ev_res x₀ (hW₀U s hsF) hx₀W₀,
      ← evT_eq _ (lands_mono (hW₀U s hsF) hx₀W₀)] at h1
    exact hrF s hsF h1
  · -- compactness
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro 𝒱 h𝒱
    have hK : ∀ᶠ x in (𝒱 : Filter _), x ∈ K ∧ x ≫ f = s₀ := h𝒱 (Filter.mem_principal_self _)
    have hy : ∀ᶠ x in (𝒱 : Filter (Spec (CommRingCat.of L) ⟶ X)), ⊤ ≤ x ⁻¹ᵁ W₀ :=
      hK.mono fun _ h ↦ h.1.1
    obtain ⟨ξ, hξ, hξW₀⟩ := exists_isGermPt (𝒰 := 𝒱) (fun x ↦ x) hW₀ hy
    have hsq := hξ.comp_eq (hK.mono fun _ h ↦ h.2)
    have hconst : ∀ c : Γ(S, ⊤), ev ξ W₀ hξW₀ (φ c) =
        ((constV 𝒱 L (ev s₀ ⊤ (fun _ _ ↦ trivial) c) : finiteGerms 𝒱 L) : UPow 𝒱 L) := by
      intro c
      rw [← ev_comp ξ f e hξW₀ c,
        ev_congr hsq _ (lands_specMap_comp (U := ⊤) _ (fun _ _ ↦ trivial)),
        ev_specMap_comp s₀ _ (U := ⊤) (fun _ _ ↦ trivial)]
      rfl
    have hmemT : ∀ b ∈ T, ev ξ W₀ hξW₀ b ∈ finiteGerms 𝒱 L := by
      intro b hbT
      rw [hξ.ev_eq hW₀ hξW₀]
      refine (mem_finiteGerms_iff 𝒱 L _).mpr ⟨‖evT x₀ W₀ b‖ + r, hK.mono fun x ⟨⟨h, hx⟩, _⟩ ↦ ?_⟩
      rw [evT_eq _ h]
      exact norm_le_of_mem_closedBall (hx b hbT)
    let R' : Subalgebra Γ(S, ⊤) Γ(X, W₀) :=
      { (finiteGerms 𝒱 L).comap (ev ξ W₀ hξW₀) with
        algebraMap_mem' := fun c ↦ by
          change ev ξ W₀ hξW₀ (φ c) ∈ finiteGerms 𝒱 L
          rw [hconst]
          exact (constV 𝒱 L _).2 }
    have hall : ∀ b, ev ξ W₀ hξW₀ b ∈ finiteGerms 𝒱 L := fun b ↦ by
      have hle : Algebra.adjoin Γ(S, ⊤) (gens : Set Γ(X, W₀)) ≤ R' :=
        Algebra.adjoin_le fun b hb ↦ hmemT b (Finset.mem_union_left _ hb)
      rw [hgens] at hle
      exact hle (Algebra.mem_top (x := b))
    let ψ : Γ(X, W₀) →+* finiteGerms 𝒱 L := (ev ξ W₀ hξW₀).codRestrict _ hall
    let ℓ : Spec (CommRingCat.of (finiteGerms 𝒱 L)) ⟶ X :=
      Spec.map (CommRingCat.ofHom ψ) ≫ hW₀.fromSpec
    have hℓ : Spec.map (ιV 𝒱 L) ≫ ℓ = ξ := by
      rw [← Category.assoc, ← Spec.map_comp]
      conv_rhs => rw [eq_specMap_ev_fromSpec ξ hW₀ hξW₀]
      rfl
    have hxW : ⊤ ≤ (Spec.map (stV 𝒱 L) ≫ ℓ) ⁻¹ᵁ W₀ :=
      lands_specMap_comp _ (lands_specMap_fromSpec hW₀ _)
    have hevx : ∀ b, ev (Spec.map (stV 𝒱 L) ≫ ℓ) W₀ hxW b = stdPart 𝒱 L (ψ b) := fun b ↦ by
      rw [ev_specMap_comp ℓ (stV 𝒱 L) (lands_specMap_fromSpec hW₀ _),
        ev_specMap_fromSpec hW₀]
      rfl
    refine ⟨Spec.map (stV 𝒱 L) ≫ ℓ, ⟨⟨hxW, fun b hbT ↦ ?_⟩, ?_⟩,
      tendsto_id'.mp (tendsto_of_lift hξ ℓ hℓ)⟩
    · have hψb : ψ b = ⟨_, (mem_finiteGerms_iff 𝒱 L _).mpr
          ((mem_finiteGerms_iff 𝒱 L _).mp ((hξ.ev_eq hW₀ hξW₀ b) ▸ hall b))⟩ :=
        Subtype.ext (hξ.ev_eq hW₀ hξW₀ b)
      rw [hevx, hψb]
      refine Metric.isClosed_closedBall.mem_of_tendsto (tendsto_stdPart 𝒱 L _ _)
        (hK.mono fun x ⟨⟨h, hx⟩, _⟩ ↦ ?_)
      change evT x W₀ b ∈ _
      rw [evT_eq _ h]
      exact hx b hbT
    · refine ext_of_ev (isAffineOpen_top S) (fun _ _ ↦ trivial) (fun _ _ ↦ trivial) fun c ↦ ?_
      rw [ev_comp _ f e hxW, hevx]
      have : ψ (φ c) = constV 𝒱 L (ev s₀ ⊤ (fun _ _ ↦ trivial) c) := Subtype.ext (hconst c)
      rw [this]
      exact stdPart_const 𝒱 L _

end CurvesJacobian.PointTopology
