/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicMap
import CurvesJacobian.Picard.HilbSheaf
import CurvesJacobian.Picard.OverSigma

/-!
# The rigidified Picard functor `Pic_{X/S,σ}` (Stacks, Section 44.6, Tag 0B9R)

Let `f : X ⟶ S` be a morphism of schemes with a section `σ : S ⟶ X` (`σ ≫ f = 𝟙 S`). For a
scheme `T` with `g : T ⟶ S` write `X_T = X ×_S T` and `σ_T : T ⟶ X_T` for the base change of
`σ` (`secT`). Following Stacks, Section 44.6 (Tag 0B9R), we define

  `Pic_{X/S,σ}(T) = Ker(σ_T^* : Pic(X_T) ⟶ Pic(T))`

(`picSigmaGrp`), a functor `(Over S)ᵒᵖ ⥤ AddCommGrpCat` (`picSigma`) and, via
`CurvesJacobian.overSigma`, a functor on all schemes (`picSigmaSch`). Stacks shows that for a
smooth projective curve over a field `k` with a rational point `σ` this functor is isomorphic to
the Picard functor `Pic_{X/k}` (the fppf sheafification of `T ↦ Pic(X_T)`, Definition 44.4.1,
Tag 0B9L) by Lemmas 44.6.1 (Tag 0B9U) and 44.4.3 (Tag 0B9N); following the plan (fppf
descent of invertible modules is not available), `Pic_{X/S,σ}` is our working definition of
the Picard functor.

We also prove the algebraic part of Stacks, Lemma 44.4.3 (Tag 0B9N): `Pic(X_T)` is the direct
sum of `Pic(T)` (pulled back along `X_T ⟶ T`) and `Pic_{X/S,σ}(T)`, the splitting being given
by `σ_T^*` (`picSplit`).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The base change `σ_T : T ⟶ X ×_S T` of the section `σ` along `g : T ⟶ S`. -/
def secT {T : Scheme.{u}} (g : T ⟶ S) : T ⟶ pullback f g :=
  pullback.lift (g ≫ σ) (𝟙 T) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

variable {T T' T'' : Scheme.{u}}

@[reassoc (attr := simp)]
lemma secT_fst (g : T ⟶ S) : secT f σ hσ g ≫ pullback.fst f g = g ≫ σ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma secT_snd (g : T ⟶ S) : secT f σ hσ g ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma secT_bcMap (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g') :
    secT f σ hσ g' ≫ bcMap f a g g' w = a ≫ secT f σ hσ g := by
  subst w
  apply pullback.hom_ext <;> simp

lemma bcMap_self (a : T ⟶ T) (ha : a = 𝟙 T) (g : T ⟶ S) (w : a ≫ g = g) :
    bcMap f a g g w = 𝟙 _ := by
  subst ha
  apply pullback.hom_ext <;> simp

@[reassoc]
lemma bcMap_comp (a' : T'' ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (g'' : T'' ⟶ S)
    (w : a ≫ g = g') (w' : a' ≫ g' = g'') (w'' : (a' ≫ a) ≫ g = g'') :
    bcMap f (a' ≫ a) g g'' w'' = bcMap f a' g' g'' w' ≫ bcMap f a g g' w := by
  apply pullback.hom_ext <;> simp

/-- `Pic_{X/S,σ}(T) = Ker(σ_T^* : Pic(X_T) ⟶ Pic(T))` for `g : T ⟶ S` (Stacks, Section 44.6,
Tag 0B9R). -/
def picSigmaGrp (g : T ⟶ S) : AddSubgroup (pullback f g).Pic :=
  (Scheme.Pic.map (secT f σ hσ g)).ker

lemma mem_picSigmaGrp {g : T ⟶ S} (x : (pullback f g).Pic) :
    x ∈ picSigmaGrp f σ hσ g ↔ Scheme.Pic.map (secT f σ hσ g) x = 0 :=
  Iff.rfl

lemma map_bcMap_mem (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g')
    {x : (pullback f g).Pic} (hx : x ∈ picSigmaGrp f σ hσ g) :
    Scheme.Pic.map (bcMap f a g g' w) x ∈ picSigmaGrp f σ hσ g' := by
  rw [mem_picSigmaGrp, ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, secT_bcMap,
    Scheme.Pic.map_comp, AddMonoidHom.comp_apply, (mem_picSigmaGrp f σ hσ x).1 hx, map_zero]

/-- The pullback map `Pic_{X/S,σ}(T) ⟶ Pic_{X/S,σ}(T')` along `a : T' ⟶ T` over `S`. -/
def picSigmaMap (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g') :
    picSigmaGrp f σ hσ g →+ picSigmaGrp f σ hσ g' :=
  ((Scheme.Pic.map (bcMap f a g g' w)).comp (picSigmaGrp f σ hσ g).subtype).codRestrict _
    fun x ↦ map_bcMap_mem f σ hσ a g g' w x.2

@[simp]
lemma coe_picSigmaMap (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g')
    (x : picSigmaGrp f σ hσ g) :
    (picSigmaMap f σ hσ a g g' w x : (pullback f g').Pic) =
      Scheme.Pic.map (bcMap f a g g' w) x :=
  rfl

/-- The rigidified Picard functor `Pic_{X/S,σ} : (Sch/S)ᵒᵖ ⥤ Ab` (Stacks, Section 44.6,
Tag 0B9R). -/
def picSigma : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (picSigmaGrp f σ hσ T.unop.hom)
  map a := AddCommGrpCat.ofHom (picSigmaMap f σ hσ a.unop.left _ _ (Over.w a.unop))
  map_id T := by
    ext x
    change Scheme.Pic.map (bcMap f _ _ _ _) x.1 = x.1
    rw [bcMap_self f _ (by simp), Scheme.Pic.map_id, AddMonoidHom.id_apply]
  map_comp a b := by
    ext x
    change Scheme.Pic.map (bcMap f _ _ _ _) x.1 =
      Scheme.Pic.map (bcMap f _ _ _ _) (Scheme.Pic.map (bcMap f _ _ _ _) x.1)
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← bcMap_comp]
    rfl

lemma picSigma_map_apply {T T' : Over S} (a : T' ⟶ T) (x : picSigmaGrp f σ hσ T.hom) :
    Subtype.val (p := (· ∈ picSigmaGrp f σ hσ T'.hom)) ((picSigma f σ hσ).map a.op x) =
      Scheme.Pic.map (bcMap f a.left T.hom T'.hom (Over.w a)) x.1 :=
  rfl

/-- The rigidified Picard functor as a functor on all schemes:
`T ↦ Σ (g : T ⟶ S), Pic_{X/S,σ}(T, g)`. -/
def picSigmaSch : Scheme.{u}ᵒᵖ ⥤ Type u :=
  overSigma (picSigma f σ hσ ⋙ forget AddCommGrpCat)

/-! ### Stacks, Lemma 44.4.3 (Tag 0B9N), algebraic part -/

lemma map_secT_map_snd (g : T ⟶ S) (y : T.Pic) :
    Scheme.Pic.map (secT f σ hσ g) (Scheme.Pic.map (pullback.snd f g) y) = y := by
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, secT_snd, Scheme.Pic.map_id,
    AddMonoidHom.id_apply]

include σ hσ in
/-- The pullback `Pic(T) ⟶ Pic(X_T)` is injective (it is split by `σ_T^*`). -/
lemma injective_map_snd (g : T ⟶ S) : Function.Injective (Scheme.Pic.map (pullback.snd f g)) :=
  Function.LeftInverse.injective (map_secT_map_snd f σ hσ g)

/-- **Stacks, Lemma 44.4.3 (Tag 0B9N)**, algebraic part: `Pic(X_T) = Pic(T) ⊕ Pic_{X/S,σ}(T)`,
where `Pic(T)` is embedded by pullback along `X_T ⟶ T`, and the projection to `Pic(T)` is
`σ_T^*`. -/
def picSplit (g : T ⟶ S) : (pullback f g).Pic ≃+ T.Pic × picSigmaGrp f σ hσ g where
  toFun x := (Scheme.Pic.map (secT f σ hσ g) x,
    ⟨x - Scheme.Pic.map (pullback.snd f g) (Scheme.Pic.map (secT f σ hσ g) x), by
      rw [mem_picSigmaGrp, map_sub, map_secT_map_snd, sub_self]⟩)
  invFun y := Scheme.Pic.map (pullback.snd f g) y.1 + y.2
  left_inv x := by simp
  right_inv y := by
    obtain ⟨y, z, hz⟩ := y
    have hz' : Scheme.Pic.map (secT f σ hσ g) z = 0 := hz
    ext
    · simp [map_secT_map_snd, hz']
    · simp [map_secT_map_snd, hz']
  map_add' x y := by
    ext
    · simp
    · simp only [map_add, Prod.snd_add, AddSubgroup.coe_add]
      abel

lemma picSplit_apply_fst (g : T ⟶ S) (x : (pullback f g).Pic) :
    (picSplit f σ hσ g x).1 = Scheme.Pic.map (secT f σ hσ g) x :=
  rfl

lemma coe_picSplit_apply_snd (g : T ⟶ S) (x : (pullback f g).Pic) :
    ((picSplit f σ hσ g x).2 : (pullback f g).Pic) =
      x - Scheme.Pic.map (pullback.snd f g) (Scheme.Pic.map (secT f σ hσ g) x) :=
  rfl

lemma picSplit_symm_apply (g : T ⟶ S) (y : T.Pic × picSigmaGrp f σ hσ g) :
    (picSplit f σ hσ g).symm y = Scheme.Pic.map (pullback.snd f g) y.1 + y.2 :=
  rfl

end CurvesJacobian
