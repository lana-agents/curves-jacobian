/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbCurve
import CurvesJacobian.Picard.RelEffCartierSub

/-!
# Adding a point: `Hilb^d_{C/k} ×_k C ⟶ Hilb^{d+1}_{C/k}`, and `Hilb^d_{C/k}` is universally closed

Let `C` be a curve over a perfect field `k`. A `T`-point `(D, c)` of `Hilb^d_{C/k} ×_k C`
(`D` a relative effective Cartier divisor of degree `d` on `C_T/T`, `c : T ⟶ C`) gives the
divisor `x_c + D` of degree `d + 1`, where `x_c` is the divisor of the section
`(c, id) : T ⟶ C ×_k T` (`RelEffCartier.ofSection`, `RelEffCartier.add`). This is the addition
morphism `hilbAdd : Hilb^d ×_k C ⟶ Hilb^{d+1}`.

* `CurvesJacobian.comp_addPt`: the construction is natural in `T`; the key input is
  `ker_comap_bcMap`: the ideal of the base change of a section is the pullback of its ideal.
* **`CurvesJacobian.surjective_hilbAdd`**: `hilbAdd` is surjective. A point `z` of
  `Hilb^{d+1}` is a divisor `E` of degree `d + 1` over the residue field `κ(z)`; `E` is nonempty,
  and over the residue field `L` of a point of `E` the divisor `E_L` contains an `L`-rational
  point `x`, so `E_L = x + D'` with `deg D' = d` (Stacks, Lemma 44.3.3, Tag 0B9F,
  `exists_eq_ofSection_add`); `(D', x)` is an `L`-point of `Hilb^d ×_k C` over `z`.
* `CurvesJacobian.surjective_hilbZeroPt`: `Hilb^0_{C/k}` has only the point of the empty divisor
  (`RelEffCartier.zero`; a divisor of degree `0` is empty, `ideal_eq_top_of_degree_eq_zero`).
* **`CurvesJacobian.universallyClosed_hilbCurveHom`**: `Hilb^d_{C/k} → Spec k` is universally
  closed, by induction on `d` (`UniversallyClosed.of_comp_surjective`), since `C` is proper over
  `k`. This is the route `C^d → Hilb^d` to the properness of `Hilb^d` and `Pic^d`
  (Stacks, Lemma 44.6.7, Tag 0BA0, uses that `Hilb^d = C^{(d)}` is proper).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Belyi

universe u

noncomputable section

namespace CurvesJacobian

section Generic

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The base change of a section along `a : T' ⟶ T` is the pullback of the section along
`X_{T'} ⟶ X_T`. -/
lemma isPullback_section_bcMap {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S)
    (w : a ≫ g = g') (s : T ⟶ pullback f g) (hs : s ≫ pullback.snd f g = 𝟙 T)
    (s' : T' ⟶ pullback f g') (hs' : s' ≫ pullback.snd f g' = 𝟙 T')
    (h : s' ≫ bcMap f a g g' w = a ≫ s) :
    IsPullback s' a (bcMap f a g g' w) s := by
  refine IsPullback.of_right (h₁₂ := pullback.snd f g') (h₂₂ := pullback.snd f g) (v₁₃ := a) ?_ h
    (isPullback_bcMap f a g g' w).flip
  rw [hs, hs']
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **The ideal of the base change of a section** is the pullback of the ideal of the section. -/
lemma ker_comap_bcMap {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S)
    (w : a ≫ g = g') (s : T ⟶ pullback f g) [IsClosedImmersion s]
    (hs : s ≫ pullback.snd f g = 𝟙 T)
    (s' : T' ⟶ pullback f g') (hs' : s' ≫ pullback.snd f g' = 𝟙 T')
    (h : s' ≫ bcMap f a g g' w = a ≫ s) :
    s.ker.comap (bcMap f a g g' w) = s'.ker := by
  have H := isPullback_section_bcMap f a g g' w s hs s' hs' h
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

lemma bcMap_congr {T T' : Scheme.{u}} {a a' : T' ⟶ T} (ha : a = a') (g : T ⟶ S) (g' : T' ⟶ S)
    (w : a ≫ g = g') (w' : a' ≫ g = g') : bcMap f a g g' w = bcMap f a' g g' w' := by
  subst ha
  rfl

lemma bcMap_id' {T : Scheme.{u}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) :
    bcMap f (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

lemma bcMap_id_comp {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g₁ g₂ : T' ⟶ S)
    (w₁ : a ≫ g = g₁) (w : 𝟙 T' ≫ g₁ = g₂) (w₂ : a ≫ g = g₂) :
    bcMap f (𝟙 T') g₁ g₂ w ≫ bcMap f a g g₁ w₁ = bcMap f a g g₂ w₂ := by
  apply pullback.hom_ext <;> simp

end Generic

namespace RelEffCartier

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The zero divisor: the empty closed subscheme. -/
def zero : RelEffCartier f where
  ideal := ⊤
  locally_principal x := by
    obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨⟨U, hU⟩, 1, hxU, by rw [Ideal.span_singleton_one]; rfl, IsSMulRegular.one _⟩
  flat := Scheme.IdealSheafData.flat_of_flat_quotient f ⊤ fun x hx ↦ absurd hx (by
    rw [Scheme.IdealSheafData.support_top]
    exact id)

@[simp]
lemma zero_ideal : (zero f).ideal = ⊤ := rfl

lemma zero_add_zero : (zero f).add (zero f) = zero f :=
  AlgebraicGeometry.RelEffCartier.ext_ideal (by
    change (⊤ : X.IdealSheafData) * ⊤ = ⊤
    exact Scheme.IdealSheafData.ext (funext fun U ↦ Ideal.mul_top ⊤))

end RelEffCartier

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]

local notation "Sk" => Spec (CommRingCat.of k)

section Divisors

variable {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k))

/-- The zero divisor on `C ×_k T` has degree `0`. -/
lemma degree_zero (t : T) : (RelEffCartier.zero (pullback.snd (C ↘ Sk) g)).degree t = 0 := by
  have h := degree_add_curve C g (RelEffCartier.zero _) (RelEffCartier.zero _) t
  rw [RelEffCartier.zero_add_zero] at h
  omega

/-- **A divisor of degree `0` is empty.** -/
lemma ideal_eq_top_of_degree_eq_zero (D : RelEffCartier (pullback.snd (C ↘ Sk) g))
    (hD : ∀ t, D.degree t = 0) : D.ideal = ⊤ := by
  haveI := D.isFinite C g
  haveI := D.flat
  haveI : IsEmpty D.ideal.subscheme := by
    refine ⟨fun y ↦ ?_⟩
    have h1 := Scheme.Hom.one_le_finrank_map (D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) g) y
    have h2 := hD ((D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) g) y)
    change (D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) g).finrank _ = 0 at h2
    omega
  rw [← D.ideal.ker_subschemeι, Scheme.ker_eq_top_of_isEmpty]

/-- The section `(c, id) : T ⟶ C ×_k T` of a `T`-point `c` of `C`. -/
def graphSec (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) : T ⟶ pullback (C ↘ Sk) g :=
  pullback.lift c (𝟙 T) (by rw [hc, Category.id_comp])

omit [PerfectField k] [IsCurveOver k C] in
@[reassoc (attr := simp)]
lemma graphSec_fst (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) :
    graphSec C g c hc ≫ pullback.fst _ _ = c :=
  pullback.lift_fst _ _ _

omit [PerfectField k] [IsCurveOver k C] in
@[reassoc (attr := simp)]
lemma graphSec_snd (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) :
    graphSec C g c hc ≫ pullback.snd _ _ = 𝟙 T :=
  pullback.lift_snd _ _ _

omit [PerfectField k] [IsCurveOver k C] in
lemma graphSec_congr {c c' : T ⟶ C} (hcc : c = c') (hc : c ≫ (C ↘ Sk) = g)
    (hc' : c' ≫ (C ↘ Sk) = g) : graphSec C g c hc = graphSec C g c' hc' := by
  subst hcc
  rfl

instance (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) : IsClosedImmersion (graphSec C g c hc) :=
  isClosedImmersion_of_section C g _ (graphSec_snd C g c hc)

/-- The divisor `x_c + D`, where `x_c` is the divisor of the section `(c, id)`. -/
def addDiv (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) :
    RelEffCartier (pullback.snd (C ↘ Sk) g) :=
  (RelEffCartier.ofSection C g (graphSec C g c hc) (graphSec_snd C g c hc)).add D

lemma addDiv_ideal (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g)
    (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) :
    (addDiv C g c hc D).ideal = (graphSec C g c hc).ker * D.ideal :=
  rfl

lemma degree_addDiv (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g)
    (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) {d : ℕ} (hD : ∀ t, D.degree t = d) (t : T) :
    (addDiv C g c hc D).degree t = d + 1 := by
  rw [addDiv, degree_add_curve, RelEffCartier.degree_ofSection, hD, Pi.one_apply, add_comm]

/-- Pulling back `x_c + D` along `T' ⟶ T`. -/
lemma comap_addDiv {T' : Scheme.{u}} (q : T' ⟶ T) (g' : T' ⟶ Sk) (w : q ≫ g = g')
    (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = g) (D : RelEffCartier (pullback.snd (C ↘ Sk) g)) :
    (addDiv C g c hc D).ideal.comap (bcMap (C ↘ Sk) q g g' w) =
      (graphSec C g' (q ≫ c) (by rw [Category.assoc, hc, w])).ker *
        D.ideal.comap (bcMap (C ↘ Sk) q g g' w) := by
  rw [addDiv_ideal, Scheme.IdealSheafData.comap_mul]
  congr 1
  refine ker_comap_bcMap (C ↘ Sk) q g g' w _ (graphSec_snd C g c hc) _ (graphSec_snd C _ _ _) ?_
  apply pullback.hom_ext <;> simp

end Divisors

section HilbEquiv

variable (k)

local notation "E" => hilbCurveEquiv k C

lemma hilbCurveEquiv_comp_fst {d : ℕ} {T T' : Scheme.{u}} (q : T' ⟶ T)
    (a : T ⟶ hilbCurve k C d) : (E d T' (q ≫ a)).1 = q ≫ (E d T a).1 := by
  rw [hilbCurveEquiv_fst, hilbCurveEquiv_fst, Category.assoc]

omit [PerfectField k] [IsCurveOver k C] in
lemma hilbSch_ideal_of_eq_map {d : ℕ} {T T' : Scheme.{u}} (q : T' ⟶ T)
    (x : (hilbSch (C ↘ Sk) d).obj (op T)) (y : (hilbSch (C ↘ Sk) d).obj (op T'))
    (hy : y = (hilbSch (C ↘ Sk) d).map q.op x) (w : q ≫ x.1 = y.1) :
    y.2.ideal = x.2.ideal.comap (bcMap (C ↘ Sk) q x.1 y.1 w) := by
  subst hy
  obtain ⟨g, P⟩ := x
  exact pullback_ideal_eq_comap_bcMap (C ↘ Sk) q g (q ≫ g) rfl P

/-- **Naturality of `hilbCurveEquiv`**: the divisor of `q ≫ a` is the pullback of the divisor
of `a`. -/
lemma hilbCurveEquiv_comp_ideal {d : ℕ} {T T' : Scheme.{u}} (q : T' ⟶ T)
    (a : T ⟶ hilbCurve k C d) (w : q ≫ (E d T a).1 = (E d T' (q ≫ a)).1) :
    (E d T' (q ≫ a)).2.1.ideal =
      (E d T a).2.1.ideal.comap (bcMap (C ↘ Sk) q _ _ w) := by
  have key : hilbCurveHomEquiv k C d T' (q ≫ a) =
      (hilbSch (C ↘ Sk) d).map q.op (hilbCurveHomEquiv k C d T a) := by
    rw [hilbCurveHomEquiv_apply, hilbCurveHomEquiv_apply, op_comp, Functor.map_comp_apply]
  exact hilbSch_ideal_of_eq_map k C q _ _ key w

/-- `hilbCurveEquiv_comp_ideal` with the divisors given by equations. -/
lemma hilbCurveEquiv_comp_ideal' {d : ℕ} {T T' : Scheme.{u}} (q : T' ⟶ T)
    (a : T ⟶ hilbCurve k C d) (x : Σ g : T ⟶ Sk,
      {D : RelEffCartier (pullback.snd (C ↘ Sk) g) // ∀ t, D.degree t = d})
    (hx : E d T a = x) (y : Σ g : T' ⟶ Sk,
      {D : RelEffCartier (pullback.snd (C ↘ Sk) g) // ∀ t, D.degree t = d})
    (hy : E d T' (q ≫ a) = y) (w : q ≫ x.1 = y.1) :
    y.2.1.ideal = x.2.1.ideal.comap (bcMap (C ↘ Sk) q _ _ w) := by
  subst hx hy
  exact hilbCurveEquiv_comp_ideal k C q a w

omit [PerfectField k] [IsCurveOver k C] in
lemma sigma_ext_of_ideal {d : ℕ} {T : Scheme.{u}} (x y : Σ g : T ⟶ Sk,
      {D : RelEffCartier (pullback.snd (C ↘ Sk) g) // ∀ t, D.degree t = d})
    (w : 𝟙 T ≫ y.1 = x.1)
    (h : x.2.1.ideal = y.2.1.ideal.comap (bcMap (C ↘ Sk) (𝟙 T) y.1 x.1 w)) : x = y := by
  obtain ⟨g, D, hD⟩ := x
  obtain ⟨g', D', hD'⟩ := y
  have w' : g' = g := by simpa using w
  subst w'
  rw [bcMap_id', Scheme.IdealSheafData.comap_id] at h
  have : D = D' := RelEffCartier.ext_ideal h
  subst this
  rfl

/-- Two morphisms to `Hilb^d_{C/k}` agree if their divisors agree. -/
lemma hilbCurve_ext {d : ℕ} {T : Scheme.{u}} (a b : T ⟶ hilbCurve k C d)
    (w : 𝟙 T ≫ (E d T b).1 = (E d T a).1)
    (h : (E d T a).2.1.ideal = (E d T b).2.1.ideal.comap (bcMap (C ↘ Sk) (𝟙 T) _ _ w)) :
    a = b :=
  (E d T).injective (sigma_ext_of_ideal k C _ _ w h)

end HilbEquiv

section Add

variable (k) {d : ℕ}

local notation "E" => hilbCurveEquiv k C

/-- The point `x_c + D` of `Hilb^{d+1}` attached to a point `a = D` of `Hilb^d` and a point `c`
of `C`. -/
def addPt {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) (c : T ⟶ C)
    (hc : c ≫ (C ↘ Sk) = (E d T a).1) : T ⟶ hilbCurve k C (d + 1) :=
  (E (d + 1) T).symm ⟨_, addDiv C _ c hc (E d T a).2.1,
    degree_addDiv C _ c hc _ (E d T a).2.2⟩

lemma addPt_eq {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) (x : Σ g : T ⟶ Sk,
      {D : RelEffCartier (pullback.snd (C ↘ Sk) g) // ∀ t, D.degree t = d})
    (hx : E d T a = x) (c : T ⟶ C) (hc : c ≫ (C ↘ Sk) = x.1)
    (hc' : c ≫ (C ↘ Sk) = (E d T a).1) :
    addPt k C a c hc' = (E (d + 1) T).symm ⟨_, addDiv C _ c hc x.2.1,
      degree_addDiv C _ c hc _ x.2.2⟩ := by
  subst hx
  rfl

lemma addPt_congr {T : Scheme.{u}} {a a' : T ⟶ hilbCurve k C d} {c c' : T ⟶ C} (ha : a = a')
    (hcc : c = c') (hc : c ≫ (C ↘ Sk) = (E d T a).1) (hc' : c' ≫ (C ↘ Sk) = (E d T a').1) :
    addPt k C a c hc = addPt k C a' c' hc' := by
  subst ha hcc
  rfl

lemma addPt_fst {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) (c : T ⟶ C)
    (hc : c ≫ (C ↘ Sk) = (E d T a).1) : (E (d + 1) T (addPt k C a c hc)).1 = (E d T a).1 := by
  rw [addPt, Equiv.apply_symm_apply]

/-- **Naturality of `addPt`.** -/
lemma comp_addPt {T T' : Scheme.{u}} (q : T' ⟶ T) (a : T ⟶ hilbCurve k C d) (c : T ⟶ C)
    (hc : c ≫ (C ↘ Sk) = (E d T a).1) (hc' : (q ≫ c) ≫ (C ↘ Sk) = (E d T' (q ≫ a)).1) :
    q ≫ addPt k C a c hc = addPt k C (q ≫ a) (q ≫ c) hc' := by
  have w₁ : q ≫ (E d T a).1 = (E (d + 1) T' (q ≫ addPt k C a c hc)).1 := by
    rw [hilbCurveEquiv_comp_fst, addPt_fst]
  have w₂ : q ≫ (E d T a).1 = (E d T' (q ≫ a)).1 := (hilbCurveEquiv_comp_fst k C q a).symm
  have w : 𝟙 T' ≫ (E d T' (q ≫ a)).1 = (E (d + 1) T' (q ≫ addPt k C a c hc)).1 := by
    rw [Category.id_comp, ← w₂, w₁]
  apply (E (d + 1) T').injective
  rw [show addPt k C (q ≫ a) (q ≫ c) hc' = (E (d + 1) T').symm ⟨_, addDiv C _ (q ≫ c) hc'
      (E d T' (q ≫ a)).2.1, degree_addDiv C _ (q ≫ c) hc' _ (E d T' (q ≫ a)).2.2⟩ from rfl,
    Equiv.apply_symm_apply]
  refine sigma_ext_of_ideal k C _ _ w ?_
  rw [hilbCurveEquiv_comp_ideal' k C q (addPt k C a c hc) _ (Equiv.apply_symm_apply _ _) _ rfl
    w₁]
  change (addDiv C _ c hc (E d T a).2.1).ideal.comap _ =
    (addDiv C _ (q ≫ c) hc' (E d T' (q ≫ a)).2.1).ideal.comap _
  rw [comap_addDiv, comap_addDiv, hilbCurveEquiv_comp_ideal k C q a w₂,
    ← Scheme.IdealSheafData.comap_comp, bcMap_id_comp _ q _ _ _ w₂ w w₁,
    graphSec_congr C _ (Category.id_comp (q ≫ c))]

end Add

section Morphism

variable (k) (d : ℕ)

local notation "E" => hilbCurveEquiv k C

/-- **The addition morphism** `Hilb^d_{C/k} ×_k C ⟶ Hilb^{d+1}_{C/k}`, `(D, x) ↦ x + D`. -/
def hilbAdd : pullback (hilbCurveHom k C d) (C ↘ Sk) ⟶ hilbCurve k C (d + 1) :=
  addPt k C (pullback.fst _ _) (pullback.snd _ _)
    (by rw [hilbCurveEquiv_fst]; exact pullback.condition.symm)

lemma hilbAdd_comp : hilbAdd k C d ≫ hilbCurveHom k C (d + 1) =
    pullback.snd (hilbCurveHom k C d) (C ↘ Sk) ≫ (C ↘ Sk) := by
  rw [← hilbCurveEquiv_fst, hilbAdd, addPt_fst, hilbCurveEquiv_fst, pullback.condition]

lemma comp_hilbAdd {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) (c : T ⟶ C)
    (hc : c ≫ (C ↘ Sk) = (E d T a).1) :
    pullback.lift a c (by rw [hc, hilbCurveEquiv_fst]) ≫ hilbAdd k C d = addPt k C a c hc := by
  rw [hilbAdd, comp_addPt k C _ _ _ _ (by
    simp only [hilbCurveEquiv_fst, Category.assoc]
    rw [pullback.condition])]
  exact addPt_congr k C (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) _ _

/-- **The addition morphism `Hilb^d ×_k C ⟶ Hilb^{d+1}` is surjective** (via Stacks,
Lemma 44.3.3, Tag 0B9F). -/
theorem surjective_hilbAdd : Surjective (hilbAdd k C d) := by
  constructor
  intro z
  let p0 := (hilbCurve k C (d + 1)).fromSpecResidueField z
  obtain ⟨x, hx⟩ : ∃ x, E (d + 1) _ p0 = x := ⟨_, rfl⟩
  obtain ⟨g0, E0, hE0⟩ := x
  haveI := E0.isFinite C g0
  haveI := E0.flat
  have hsurj : Surjective (E0.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) g0) :=
    (Scheme.Hom.one_le_finrank_iff_surjective _).mp fun t ↦ by
      change 1 ≤ E0.degree t
      rw [hE0]
      omega
  obtain ⟨y, -⟩ := hsurj.surj (IsLocalRing.closedPoint ((hilbCurve k C (d + 1)).residueField z))
  let m : Spec (E0.ideal.subscheme.residueField y) ⟶ pullback (C ↘ Sk) g0 :=
    E0.ideal.subscheme.fromSpecResidueField y ≫ E0.ideal.subschemeι
  let h := m ≫ pullback.snd (C ↘ Sk) g0
  let c := m ≫ pullback.fst (C ↘ Sk) g0
  obtain ⟨y', hy'⟩ : ∃ y', E (d + 1) _ (h ≫ p0) = y' := ⟨_, rfl⟩
  have w : h ≫ g0 = y'.1 := by
    rw [← hy', hilbCurveEquiv_comp_fst, hx]
  have hideal := hilbCurveEquiv_comp_ideal' k C h p0 _ hx y' hy' w
  obtain ⟨G', E', hE'⟩ := y'
  change E'.ideal = E0.ideal.comap (bcMap (C ↘ Sk) h g0 G' w) at hideal
  change h ≫ g0 = G' at w
  have hc : c ≫ (C ↘ Sk) = G' := by
    rw [← w]
    simp only [c, h, Category.assoc, pullback.condition]
  let s' := graphSec C G' c hc
  have hm : s' ≫ bcMap (C ↘ Sk) h g0 G' w = m := by
    apply pullback.hom_ext
    · simp [s', c]
    · simp [s', h]
  have H : E0.ideal ≤ s'.ker.map (bcMap (C ↘ Sk) h g0 G' w) := by
    rw [Scheme.IdealSheafData.map_ker, hm]
    conv_lhs => rw [← E0.ideal.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _
  have hle : E'.ideal ≤ s'.ker := hideal ▸ Scheme.IdealSheafData.le_map_iff_comap_le.mp H
  obtain ⟨D', hD', hdeg⟩ := exists_eq_ofSection_add C G' s' (graphSec_snd C G' c hc) E' hle
  have hD'deg : ∀ t, D'.degree t = d := fun t ↦ by
    have := hdeg t
    rw [hE'] at this
    omega
  let a' := (E d _).symm ⟨G', D', hD'deg⟩
  have hEa' : E d _ a' = ⟨G', D', hD'deg⟩ := Equiv.apply_symm_apply _ _
  have hc' : c ≫ (C ↘ Sk) = (E d _ a').1 := by rw [hEa']; exact hc
  have key : addPt k C a' c hc' = h ≫ p0 := by
    rw [addPt_eq k C a' _ hEa' c hc hc']
    apply (E (d + 1) _).injective
    rw [Equiv.apply_symm_apply, hy']
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hD'))
  refine ⟨pullback.lift a' c (by rw [hc', hilbCurveEquiv_fst])
    (IsLocalRing.closedPoint (E0.ideal.subscheme.residueField y)), ?_⟩
  rw [← Scheme.Hom.comp_apply, comp_hilbAdd k C d a' c hc', key, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

/-- The point of `Hilb^0_{C/k}` given by the empty divisor. -/
def hilbZeroPt : Sk ⟶ hilbCurve k C 0 :=
  (E 0 Sk).symm ⟨𝟙 Sk, RelEffCartier.zero _, degree_zero C _⟩

lemma hilbZeroPt_comp : hilbZeroPt k C ≫ hilbCurveHom k C 0 = 𝟙 Sk := by
  rw [← hilbCurveEquiv_fst, hilbZeroPt, Equiv.apply_symm_apply]

/-- Morphisms to `Hilb^0_{C/k}` are determined by their structure morphisms. -/
lemma hilbCurve_zero_ext {T : Scheme.{u}} (a b : T ⟶ hilbCurve k C 0)
    (h : a ≫ hilbCurveHom k C 0 = b ≫ hilbCurveHom k C 0) : a = b := by
  have w : 𝟙 T ≫ (E 0 T b).1 = (E 0 T a).1 := by
    rw [Category.id_comp, hilbCurveEquiv_fst, hilbCurveEquiv_fst, h]
  refine hilbCurve_ext k C a b w ?_
  rw [ideal_eq_top_of_degree_eq_zero C _ _ (E 0 T a).2.2,
    ideal_eq_top_of_degree_eq_zero C _ _ (E 0 T b).2.2, Scheme.IdealSheafData.comap_top]

theorem surjective_hilbZeroPt : Surjective (hilbZeroPt k C) := by
  constructor
  intro z
  let p0 := (hilbCurve k C 0).fromSpecResidueField z
  have := hilbCurve_zero_ext k C p0 ((p0 ≫ hilbCurveHom k C 0) ≫ hilbZeroPt k C) (by
    rw [Category.assoc, hilbZeroPt_comp, Category.comp_id])
  refine ⟨(p0 ≫ hilbCurveHom k C 0) (IsLocalRing.closedPoint _), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← this, Scheme.fromSpecResidueField_apply]

/-- **`Hilb^d_{C/k} → Spec k` is universally closed**, by induction on `d`:
`Hilb^d ×_k C → Spec k` is universally closed since `C` is proper over `k`, and it surjects onto
`Hilb^{d+1}` (`surjective_hilbAdd`). -/
theorem universallyClosed_hilbCurveHom : ∀ d : ℕ, UniversallyClosed (hilbCurveHom k C d)
  | 0 => by
    haveI := surjective_hilbZeroPt k C
    haveI : UniversallyClosed (hilbZeroPt k C ≫ hilbCurveHom k C 0) := by
      rw [hilbZeroPt_comp]
      infer_instance
    exact UniversallyClosed.of_comp_surjective (hilbZeroPt k C) _
  | d + 1 => by
    haveI := universallyClosed_hilbCurveHom d
    haveI := surjective_hilbAdd k C d
    haveI : UniversallyClosed (hilbAdd k C d ≫ hilbCurveHom k C (d + 1)) := by
      rw [hilbAdd_comp]
      infer_instance
    exact UniversallyClosed.of_comp_surjective (hilbAdd k C d) _

instance : UniversallyClosed (hilbCurveHom k C d) := universallyClosed_hilbCurveHom k C d

end Morphism

end CurvesJacobian
