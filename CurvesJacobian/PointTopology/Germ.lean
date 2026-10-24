/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.PointTopology.Basic
import CurvesJacobian.PointTopology.UltraValuation
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.QuasiSeparated

/-!
# Ultrapower points and limits of `L`-points

Let `y : I → X(L)` be a family of `L`-points of a scheme `X` and `𝒰` an ultrafilter on `I`.
A point `ξ ∈ X(L^𝒰)` with values in the ultrapower `L^𝒰 = Filter.Germ 𝒰 L` is a *germ point*
of `(y, 𝒰)` (`IsGermPt`) if for every affine open `U` with `ξ ∈ U(L^𝒰)`, eventually
`y i ∈ U(L)`, and `a(ξ)` is the germ of `i ↦ a(y i)` for `a ∈ Γ(X, U)`.

* `exists_isGermPt`: a germ point exists as soon as eventually all `y i` lie in one affine open;
* `IsGermPt.comp`: germ points are compatible with morphisms;
* `IsGermPt.lands_of_eventually`, `IsGermPt.unique`: for quasi-separated `X`, `ξ ∈ U` iff
  eventually `y i ∈ U`, and germ points are unique;
* `isGermPt_const`: the germ point of a constant family.

With `V ⊆ L^𝒰` the valuation ring of finite germs and `st : V → L` the standard part
(`UltraValuation.lean`, `L` a proper normed field), limits of `y` along `𝒰` are the closed
points of lifts `Spec V ⟶ X` of `ξ`:

* **`tendsto_of_lift`**: if `ℓ : Spec V ⟶ X` restricts to `ξ` on `Spec L^𝒰`, then `y → ℓ ∘ st`;
* **`exists_lift_of_tendsto`**: conversely (`X` quasi-separated), if `y → x` there is such an `ℓ`
  with `ℓ ∘ st = x`.

This translates the valuative criteria into compactness and Hausdorffness (`Proper.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Topology Filter

noncomputable section

namespace CurvesJacobian.PointTopology

variable {X Y : Scheme.{u}}

/-! ### Points with values in a field -/

section Field

variable {K : Type u} [Field K]

lemma lands_of_mem (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens} (p : Spec (CommRingCat.of K))
    (hp : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  have : q = p := Subsingleton.elim (α := PrimeSpectrum K) q p
  subst this
  exact hp

/-- The unique point of `Spec K`. -/
abbrev pt (K : Type u) [Field K] : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K

lemma mem_of_lands (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x (pt K) ∈ U :=
  h (Set.mem_univ _)

lemma exists_affine_lands (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ U ∧ ⊤ ≤ x ⁻¹ᵁ W := by
  obtain ⟨W, hW, hpW, hWU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (mem_of_lands x h)
  exact ⟨W, hW, hWU, lands_of_mem x _ hpW⟩

end Field

/-- **Local description of sections on a basic open**: for `f ∈ Γ(X, U₀)` (`U₀` affine) and a
section `a` over an open `U ⊇ D(f)`, there are `n` and `b ∈ Γ(X, U₀)` with `a = b / fⁿ` at every
field-valued point of `D(f)`. -/
lemma exists_ev_mul_pow_eq {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (f : Γ(X, U₀)) {U : X.Opens}
    (hDU : X.basicOpen f ≤ U) (a : Γ(X, U)) :
    ∃ (n : ℕ) (b : Γ(X, U₀)), ∀ {K : Type u} [Field K] (z : Spec (CommRingCat.of K) ⟶ X)
      (hz : ⊤ ≤ z ⁻¹ᵁ X.basicOpen f),
      ev z U (lands_mono hDU hz) a * ev z U₀ (lands_mono (X.basicOpen_le f) hz) f ^ n =
        ev z U₀ (lands_mono (X.basicOpen_le f) hz) b := by
  haveI := hU₀.isLocalization_basicOpen f
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj f (X.presheaf.map (homOfLE hDU).op a)
  refine ⟨n, b, fun z hz ↦ ?_⟩
  have := congrArg (ev z (X.basicOpen f) hz) hb
  rw [map_mul, map_pow] at this
  rw [ev_res z hDU hz, ev_res z (X.basicOpen_le f) hz f, ev_res z (X.basicOpen_le f) hz b]
  exact this

/-! ### Germ points -/

variable {L : Type u} [Field L] {I : Type u} (𝒰 : Ultrafilter I)

/-- The ultrapower `L^𝒰`. -/
abbrev UPow (𝒰 : Ultrafilter I) (L : Type u) [Field L] : Type u := Filter.Germ (𝒰 : Filter I) L

open Classical in
/-- Evaluation, extended by `0` outside `U`. -/
def evT (x : Spec (CommRingCat.of L) ⟶ X) (U : X.Opens) (a : Γ(X, U)) : L :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then ev x U h a else 0

lemma evT_eq (x : Spec (CommRingCat.of L) ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    evT x U a = ev x U h a := dif_pos h

/-- The germ of `i ↦ a(y i)`. -/
def germOf (y : I → (Spec (CommRingCat.of L) ⟶ X)) (U : X.Opens) (a : Γ(X, U)) : UPow 𝒰 L :=
  ((fun i ↦ evT (y i) U a : I → L) : Filter.Germ (𝒰 : Filter I) L)

lemma germ_ne_zero_iff (g : I → L) :
    ((g : Filter.Germ (𝒰 : Filter I) L) ≠ 0) ↔ ∀ᶠ i in (𝒰 : Filter I), g i ≠ 0 := by
  rw [Ne, ← Filter.Germ.coe_zero, Filter.Germ.coe_eq, Ultrafilter.eventually_not]
  rfl

/-- `ξ ∈ X(L^𝒰)` is a **germ point** of the family `y` along `𝒰`. -/
structure IsGermPt (y : I → (Spec (CommRingCat.of L) ⟶ X))
    (ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X) : Prop where
  eventually_lands {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U
  ev_eq {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (a : Γ(X, U)) :
    ev ξ U h a = germOf 𝒰 y U a

variable {𝒰}

lemma germOf_congr {y : I → (Spec (CommRingCat.of L) ⟶ X)} {y' : I → (Spec (CommRingCat.of L) ⟶ Y)}
    {U : X.Opens} {V : Y.Opens} {a : Γ(X, U)}
    {b : Γ(Y, V)} (h : ∀ᶠ i in (𝒰 : Filter I), evT (y i) U a = evT (y' i) V b) :
    germOf 𝒰 y U a = germOf 𝒰 y' V b :=
  Filter.Germ.coe_eq.mpr h

/-- Germ points for arbitrary opens. -/
lemma IsGermPt.lands_ev {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ) {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    (∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U) ∧ ∀ a, ev ξ U h a = germOf 𝒰 y U a := by
  obtain ⟨W, hW, hWU, hξW⟩ := exists_affine_lands ξ h
  have hev := hξ.eventually_lands hW hξW
  refine ⟨hev.mono fun i hi ↦ lands_mono hWU hi, fun a ↦ ?_⟩
  rw [ev_res ξ hWU hξW, hξ.ev_eq hW hξW]
  refine germOf_congr (hev.mono fun i hi ↦ ?_)
  rw [evT_eq _ hi, evT_eq _ (lands_mono hWU hi), ev_res (y i) hWU hi]

/-- **Germ points are compatible with morphisms.** -/
lemma IsGermPt.comp {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ) (f : X ⟶ Y) :
    IsGermPt 𝒰 (fun i ↦ y i ≫ f) (ξ ≫ f) where
  eventually_lands {V} _ h := by
    obtain ⟨W, -, hWV, hξW⟩ := exists_affine_lands ξ (U := f ⁻¹ᵁ V) h
    exact ((hξ.lands_ev hξW).1).mono fun i hi ↦ lands_comp hWV hi
  ev_eq {V} _ h b := by
    obtain ⟨W, -, hWV, hξW⟩ := exists_affine_lands ξ (U := f ⁻¹ᵁ V) h
    obtain ⟨hev, hval⟩ := hξ.lands_ev hξW
    rw [ev_comp ξ f hWV hξW, hval]
    refine germOf_congr (hev.mono fun i hi ↦ ?_)
    rw [evT_eq _ hi, evT_eq _ (lands_comp hWV hi), ev_comp (y i) f hWV hi]

/-- **Existence of germ points** when eventually all `y i` lie in an affine open `U₀`. -/
theorem exists_isGermPt (y : I → (Spec (CommRingCat.of L) ⟶ X)) {U₀ : X.Opens}
    (hU₀ : IsAffineOpen U₀) (hy : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U₀) :
    ∃ ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X, IsGermPt 𝒰 y ξ ∧ ⊤ ≤ ξ ⁻¹ᵁ U₀ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hy.exists
  -- ring maps `Γ(X, U₀) → L`, equal to the evaluation at `y i` whenever `y i ∈ U₀`
  let ψ : I → (Γ(X, U₀) →+* L) := fun i ↦
    if h : ⊤ ≤ y i ⁻¹ᵁ U₀ then ev (y i) U₀ h else ev (y i₀) U₀ hi₀
  have hψ : ∀ i (h : ⊤ ≤ y i ⁻¹ᵁ U₀) x, ψ i x = ev (y i) U₀ h x := fun i h x ↦ by
    simp only [ψ, dif_pos h]
  let φ : Γ(X, U₀) →+* UPow 𝒰 L :=
    (Filter.Germ.coeRingHom (𝒰 : Filter I)).comp (RingHom.pi ψ)
  have hφ : ∀ a, φ a = ((fun i ↦ ψ i a : I → L) : Filter.Germ _ L) := fun _ ↦ rfl
  let ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU₀.fromSpec
  have hξ₀ : ⊤ ≤ ξ ⁻¹ᵁ U₀ := lands_specMap_fromSpec hU₀ _
  have evξ : ∀ a, ev ξ U₀ hξ₀ a = φ a := ev_specMap_fromSpec hU₀ _
  -- the basic-open argument
  have key : ∀ {U : X.Opens}, IsAffineOpen U → ⊤ ≤ ξ ⁻¹ᵁ U →
      ∃ f : Γ(X, U₀), X.basicOpen f ≤ U ∧ ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen f ∧
        ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ X.basicOpen f := by
    intro U hU h
    obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter hU₀ hU (ξ (pt _))
      ⟨mem_of_lands ξ hξ₀, mem_of_lands ξ h⟩
    have hξf : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen f := lands_of_mem ξ _ hpf
    refine ⟨f, hfg ▸ X.basicOpen_le g, hξf, ?_⟩
    have h1 : φ f ≠ 0 := by rw [← evξ]; exact (lands_basicOpen_iff ξ hξ₀ f).mp hξf
    rw [hφ, germ_ne_zero_iff] at h1
    refine (h1.and hy).mono fun i ⟨hi, hi0⟩ ↦ ?_
    rw [hψ i hi0] at hi
    exact (lands_basicOpen_iff (y i) hi0 f).mpr hi
  refine ⟨ξ, ⟨fun {U} hU h ↦ ?_, fun {U} hU h a ↦ ?_⟩, hξ₀⟩
  · obtain ⟨f, hfU, -, hev⟩ := key hU h
    exact hev.mono fun i hi ↦ lands_mono hfU hi
  · obtain ⟨f, hfU, hξf, hev⟩ := key hU h
    obtain ⟨n, b, hb⟩ := exists_ev_mul_pow_eq hU₀ f hfU a
    have e1 : ev ξ U h a = φ b / φ f ^ n := by
      rw [eq_div_iff (pow_ne_zero _ (by rw [← evξ]; exact (lands_basicOpen_iff ξ _ f).mp hξf)),
        ← evξ, ← evξ]
      exact hb ξ hξf
    rw [e1, hφ, hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_div]
    refine (Filter.Germ.coe_eq.mpr ((hev.and hy).mono fun i ⟨hi, hi0⟩ ↦ ?_))
    have hne : ev (y i) U₀ hi0 f ≠ 0 := (lands_basicOpen_iff (y i) hi0 f).mp hi
    simp only [Pi.div_apply, Pi.pow_apply, hψ i hi0]
    rw [evT_eq _ (lands_mono hfU hi), eq_comm, eq_div_iff (pow_ne_zero _ hne)]
    exact hb (y i) hi

/-- **`ξ ∈ U` iff eventually `y i ∈ U`** (quasi-separated `X`, `U` affine). -/
lemma IsGermPt.lands_of_eventually [QuasiSeparatedSpace X] {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ) {U : X.Opens}
    (hU : IsAffineOpen U) (hy : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U) : ⊤ ≤ ξ ⁻¹ᵁ U := by
  obtain ⟨U₀, hU₀, -, hξ₀⟩ := exists_affine_lands ξ (U := ⊤) (fun _ _ ↦ trivial)
  have hy₀ := hξ.eventually_lands hU₀ hξ₀
  -- cover `U₀ ∩ U` by finitely many basic opens `D(f) ⊆ U` of `U₀`
  have hc : IsCompact ((U₀ : Set X) ∩ U) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U₀.isOpen hU₀.isCompact U.isOpen hU.isCompact
  have hcov : ∀ q : ((U₀ : Set X) ∩ U : Set X), ∃ f : Γ(X, U₀),
      X.basicOpen f ≤ U ∧ (q : X) ∈ X.basicOpen f := fun q ↦ by
    obtain ⟨f, hf, hqf⟩ := hU₀.exists_basicOpen_le (V := U) ⟨q, q.2.2⟩ q.2.1
    exact ⟨f, hf, hqf⟩
  choose F hFU hqF using hcov
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun q ↦ (X.basicOpen (F q) : Set X))
    (fun q ↦ (X.basicOpen (F q)).isOpen) fun q hq ↦ Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hqF _⟩
  have hev : ∀ᶠ i in (𝒰 : Filter I), y i (pt L) ∈ ⋃ q ∈ t, (X.basicOpen (F q) : Set X) :=
    (hy₀.and hy).mono fun i ⟨h0, h1⟩ ↦ ht ⟨mem_of_lands _ h0, mem_of_lands _ h1⟩
  have hmem : (⋃ q ∈ (t : Set _), {i | y i (pt L) ∈ X.basicOpen (F q)}) ∈ 𝒰 :=
    Filter.mem_of_superset hev fun i hi ↦ by simpa using hi
  obtain ⟨q, -, hq⟩ := (Ultrafilter.finite_biUnion_mem_iff t.finite_toSet).mp hmem
  have hq' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ X.basicOpen (F q) :=
    Filter.mem_of_superset (Ultrafilter.mem_coe.mpr hq) fun i hi ↦ lands_of_mem _ _ hi
  have hne : germOf 𝒰 y U₀ (F q) ≠ 0 := by
    rw [germOf, germ_ne_zero_iff]
    refine (hq'.and hy₀).mono fun i ⟨hi, hi0⟩ ↦ ?_
    rw [evT_eq _ hi0]
    exact (lands_basicOpen_iff _ hi0 _).mp hi
  rw [← hξ.ev_eq hU₀ hξ₀] at hne
  exact lands_mono (hFU q) ((lands_basicOpen_iff ξ hξ₀ _).mpr hne)

/-- **Uniqueness of germ points** (quasi-separated `X`). -/
lemma IsGermPt.unique [QuasiSeparatedSpace X] {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ ξ' : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ)
    (hξ' : IsGermPt 𝒰 y ξ') : ξ = ξ' := by
  obtain ⟨U₀, hU₀, -, hξ₀⟩ := exists_affine_lands ξ (U := ⊤) (fun _ _ ↦ trivial)
  have hξ'₀ := hξ'.lands_of_eventually hU₀ (hξ.eventually_lands hU₀ hξ₀)
  exact ext_of_ev hU₀ hξ₀ hξ'₀ fun a ↦ by rw [hξ.ev_eq hU₀ hξ₀, hξ'.ev_eq hU₀ hξ'₀]

/-- The constant ring map `L → L^𝒰`. -/
def constHom (𝒰 : Ultrafilter I) (L : Type u) [Field L] : L →+* UPow 𝒰 L :=
  (Filter.Germ.coeRingHom (𝒰 : Filter I)).comp (Pi.constRingHom I L)

/-- **The germ point of a constant family.** -/
lemma isGermPt_const (s : Spec (CommRingCat.of L) ⟶ X) :
    IsGermPt 𝒰 (fun _ ↦ s) (Spec.map (CommRingCat.ofHom (constHom 𝒰 L)) ≫ s) where
  eventually_lands {U} _ h :=
    Filter.Eventually.of_forall fun _ ↦ lands_of_mem s _ (h (Set.mem_univ (pt _)))
  ev_eq {U} _ h a := by
    have hs : ⊤ ≤ s ⁻¹ᵁ U := lands_of_mem s _ (h (Set.mem_univ (pt _)))
    rw [ev_specMap_comp s _ hs]
    exact Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun _ ↦ (evT_eq s hs a).symm)

/-! ### Limits and lifts to the valuation ring of finite germs -/

section Limit

variable {L : Type u} [NormedField L] [ProperSpace L]

/-- The inclusion `V ⟶ L^𝒰` of the finite germs. -/
abbrev ιV (𝒰 : Ultrafilter I) (L : Type u) [NormedField L] :
    CommRingCat.of (finiteGerms 𝒰 L) ⟶ CommRingCat.of (UPow 𝒰 L) :=
  CommRingCat.ofHom (finiteGerms 𝒰 L).subtype

/-- The standard part `V ⟶ L`. -/
abbrev stV (𝒰 : Ultrafilter I) (L : Type u) [NormedField L] [ProperSpace L] :
    CommRingCat.of (finiteGerms 𝒰 L) ⟶ CommRingCat.of L :=
  CommRingCat.ofHom (stdPart 𝒰 L)

lemma stdPart_surjective : Function.Surjective (stdPart 𝒰 L) := fun c ↦
  ⟨⟨_, const_mem_finiteGerms 𝒰 L c⟩, stdPart_const 𝒰 L c⟩

/-- A morphism `Spec V ⟶ X` whose closed point lands in `U` lands in `U`. -/
lemma lands_of_lands_stV (ℓ : Spec (CommRingCat.of (finiteGerms 𝒰 L)) ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ (Spec.map (stV 𝒰 L) ≫ ℓ) ⁻¹ᵁ U) : ⊤ ≤ ℓ ⁻¹ᵁ U := by
  have hmax : (RingHom.ker (stdPart 𝒰 L)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ stdPart_surjective
  let q : Spec (CommRingCat.of (finiteGerms 𝒰 L)) := Spec.map (stV 𝒰 L) (pt L)
  have hq : ℓ q ∈ U := h (Set.mem_univ (pt L))
  have hqm : q.asIdeal = RingHom.ker (stdPart 𝒰 L) := by
    change Ideal.comap (stdPart 𝒰 L) (IsLocalRing.maximalIdeal L) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker]
  intro p _
  have hpq : p ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (R := finiteGerms 𝒰 L) p q).mp ?_
    change p.asIdeal ≤ q.asIdeal
    rw [hqm, IsLocalRing.eq_maximalIdeal hmax]
    exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  exact hpq.mem_open (ℓ ⁻¹ᵁ U).isOpen hq

/-- **A lift `Spec V ⟶ X` of a germ point gives a limit**: if `ℓ : Spec V ⟶ X` restricts to the
germ point `ξ` of `(y, 𝒰)` on `Spec L^𝒰`, then `y` converges along `𝒰` to the restriction of
`ℓ` to the closed point `Spec L` (via the standard part). -/
theorem tendsto_of_lift {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ)
    (ℓ : Spec (CommRingCat.of (finiteGerms 𝒰 L)) ⟶ X) (hℓ : Spec.map (ιV 𝒰 L) ≫ ℓ = ξ) :
    Tendsto y 𝒰 (𝓝 (Spec.map (stV 𝒰 L) ≫ ℓ)) := by
  subst hℓ
  rw [tendsto_iff]
  intro U a O hO h ha
  have hℓ' := lands_of_lands_stV ℓ h
  obtain ⟨hev, hval⟩ := hξ.lands_ev (lands_specMap_comp (ιV 𝒰 L) hℓ')
  have e1 : germOf 𝒰 y U a = ((ev ℓ U hℓ' a : finiteGerms 𝒰 L) : UPow 𝒰 L) := by
    rw [← hval]
    exact ev_specMap_comp ℓ (ιV 𝒰 L) hℓ' a
  have hmem : ((fun i ↦ evT (y i) U a : I → L) : Filter.Germ (𝒰 : Filter I) L) ∈
      finiteGerms 𝒰 L := by
    change germOf 𝒰 y U a ∈ _
    rw [e1]
    exact (ev ℓ U hℓ' a).2
  have hst : stdPart 𝒰 L ⟨_, hmem⟩ = ev (Spec.map (stV 𝒰 L) ≫ ℓ) U h a := by
    rw [ev_specMap_comp ℓ (stV 𝒰 L) hℓ']
    congr 1
    exact Subtype.ext e1
  have ht := tendsto_stdPart 𝒰 L _ hmem
  rw [hst] at ht
  exact ((ht.eventually_mem (hO.mem_nhds ha)).and hev).mono fun i ⟨hi, hl⟩ ↦
    ⟨hl, by rw [← evT_eq _ hl]; exact hi⟩

/-- **A limit gives a lift of the germ point** (`X` quasi-separated): if `y → x` along `𝒰`,
there is `ℓ : Spec V ⟶ X` restricting to `ξ` on `Spec L^𝒰` and to `x` on the closed point. -/
theorem exists_lift_of_tendsto [QuasiSeparatedSpace X] {y : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ)
    {x : Spec (CommRingCat.of L) ⟶ X} (hy : Tendsto y 𝒰 (𝓝 x)) :
    ∃ ℓ : Spec (CommRingCat.of (finiteGerms 𝒰 L)) ⟶ X,
      Spec.map (ιV 𝒰 L) ≫ ℓ = ξ ∧ Spec.map (stV 𝒰 L) ≫ ℓ = x := by
  obtain ⟨U, hU, -, hxU⟩ := exists_affine_lands x (U := ⊤) (fun _ _ ↦ trivial)
  rw [tendsto_iff] at hy
  have hlands : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U :=
    (hy U 0 Set.univ isOpen_univ hxU trivial).mono fun i ⟨h, _⟩ ↦ h
  have hξU := hξ.lands_of_eventually hU hlands
  have htend : ∀ a, Tendsto (fun i ↦ evT (y i) U a) 𝒰 (𝓝 (ev x U hxU a)) := fun a ↦
    tendsto_nhds.mpr fun O hO ha ↦ (hy U a O hO hxU ha).mono fun i ⟨h, hi⟩ ↦ by
      change evT (y i) U a ∈ O; rw [evT_eq _ h]; exact hi
  have hmem : ∀ a, ev ξ U hξU a ∈ finiteGerms 𝒰 L := fun a ↦ by
    rw [hξ.ev_eq hU hξU]
    exact (exists_mem_finiteGerms_of_tendsto 𝒰 L _ _ (htend a)).1
  let ψ : Γ(X, U) →+* finiteGerms 𝒰 L := (ev ξ U hξU).codRestrict _ hmem
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    conv_rhs => rw [eq_specMap_ev_fromSpec ξ hU hξU]
    rfl
  · rw [← Category.assoc, ← Spec.map_comp]
    conv_rhs => rw [eq_specMap_ev_fromSpec x hU hxU]
    congr 2
    ext a
    obtain ⟨hf, hfa⟩ := exists_mem_finiteGerms_of_tendsto 𝒰 L _ _ (htend a)
    change stdPart 𝒰 L (ψ a) = ev x U hxU a
    rw [← hfa]
    congr 1
    exact Subtype.ext (hξ.ev_eq hU hξU a)

end Limit

end CurvesJacobian.PointTopology
