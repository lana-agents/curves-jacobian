/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Poincare

/-!
# Calculus of rigidified isomorphisms and the cocycle of the Poincaré descent datum (JAC J1b)

Rigidified line bundles on a base along which `X_T` is rigid have at most one rigidified
isomorphism between any two of them (`exists_unique_rigidIso`, van der Geer–Moonen VI §1). This
file turns that into a calculus:

* `Rigidified.IsRigidIso.refl`, `.symm`, `.trans`; the pullback `Rigidified.pullIso` of an
  isomorphism along `a : T' ⟶ T` is rigidified if the isomorphism is (`IsRigidIso.pull`);
* `Rigidified.pullComp`: the rigidified isomorphism `b^* a^* R ≅ (b ≫ a)^* R` and
  `Rigidified.pullId`: `𝟙^* R ≅ R` (unique, so every coherence between them holds, e.g.
  `IsRigidIso.eq_pullComp`).

For the Poincaré bundle `P` on `C ×_k J_L` (`Picard/Poincare.lean`) and its descent datum
`φ_g = poincareGalIso g : (1 × g)^* P ≅ P` this gives

* **`poincareGalIso_mul`** (the cocycle condition): `φ_{gh} = c⁻¹ ≫ g^* φ_h ≫ φ_g`, where
  `c : g^* h^* P ≅ (gh)^* P` is `pullComp` (`act g ≫ act h = act (g h)`);
* **`poincareGalIso_one`**: `φ_1 = pullId`.

(Lead decision 2026-10-25, JAC agent 31: the descent of `P` to `C × J_K` (J1c) is not needed —
`ThetaPullbackG` only needs a `G`-invariant divisor on `C_{k̄}`, so J2–J6 work on `C_L × J_L` with
the descent datum `(P, φ_g)`.)
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Scheme Scheme.Modules ModulesGlue Belyi

section Generic

variable {X S : Scheme.{u}} {f : X ⟶ S} {σ : S ⟶ X} {hσ : σ ≫ f = 𝟙 S}
  {T T' T'' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} {g'' : T'' ⟶ S}

namespace Rigidified

lemma IsRigidIso.refl (R : Rigidified f σ hσ g) : R.IsRigidIso R (Iso.refl _) := by
  unfold IsRigidIso
  rw [Iso.refl_hom, (Modules.pullback (secT f σ hσ g)).map_id, Category.id_comp]

lemma IsRigidIso.trans {R R' R'' : Rigidified f σ hσ g} {φ : R.L ≅ R'.L} {ψ : R'.L ≅ R''.L}
    (h₁ : R.IsRigidIso R' φ) (h₂ : R'.IsRigidIso R'' ψ) : R.IsRigidIso R'' (φ ≪≫ ψ) := by
  unfold IsRigidIso at *
  rw [Iso.trans_hom, Functor.map_comp, Category.assoc, h₂, h₁]

lemma IsRigidIso.symm {R R' : Rigidified f σ hσ g} {φ : R.L ≅ R'.L}
    (h : R.IsRigidIso R' φ) : R'.IsRigidIso R φ.symm := by
  unfold IsRigidIso at *
  rw [← h, Iso.symm_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Isomorphic line bundles have the same class. -/
lemma cls_eq_of_iso {R R' : Rigidified f σ hσ g} (φ : R.L ≅ R'.L) : R.cls = R'.cls :=
  Subtype.ext (@Scheme.Pic.mk_eq_of_iso _ _ _ R.isInvertible R'.isInvertible φ)

/-- The pullback of an isomorphism of rigidified line bundles along `a : T' ⟶ T`. -/
def pullIso {R R' : Rigidified f σ hσ g} (φ : R.L ≅ R'.L) (a : T' ⟶ T) (g' : T' ⟶ S)
    (w : a ≫ g = g') : (R.pull a g' w).L ≅ (R'.pull a g' w).L :=
  (Modules.pullback (bcMap f a g g' w)).mapIso φ

@[reassoc]
lemma pullback_map_eqToHom {A B : Scheme.{u}} {x y : A ⟶ B} (h : x = y) {M N : B.Modules}
    (φ : M ⟶ N) :
    (Modules.pullback x).map φ ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (Modules.pullback y).map φ := by
  subst h
  simp

/-- **The pullback of a rigidified isomorphism is rigidified.** -/
lemma IsRigidIso.pull {R R' : Rigidified f σ hσ g} {φ : R.L ≅ R'.L} (h : R.IsRigidIso R' φ)
    (a : T' ⟶ T) (g' : T' ⟶ S) (w : a ≫ g = g') :
    (R.pull a g' w).IsRigidIso (R'.pull a g' w) (pullIso φ a g' w) := by
  unfold IsRigidIso at *
  have n₁ := (Modules.pullbackComp (secT f σ hσ g') (bcMap f a g g' w)).hom.naturality φ.hom
  have n₂ := (Modules.pullbackComp a (secT f σ hσ g)).inv.naturality φ.hom
  simp only [Functor.comp_map] at n₁ n₂
  change (Modules.pullback (secT f σ hσ g')).map ((Modules.pullback (bcMap f a g g' w)).map φ.hom) ≫
      (Modules.pullbackComp (secT f σ hσ g') (bcMap f a g g' w)).hom.app R'.L ≫
      eqToHom (by rw [secT_bcMap]) ≫ (Modules.pullbackComp a (secT f σ hσ g)).inv.app R'.L ≫
      (Modules.pullback a).map R'.α.hom ≫ pullbackStructureSheafHom a =
    (Modules.pullbackComp (secT f σ hσ g') (bcMap f a g g' w)).hom.app R.L ≫
      eqToHom (by rw [secT_bcMap]) ≫ (Modules.pullbackComp a (secT f σ hσ g)).inv.app R.L ≫
      (Modules.pullback a).map R.α.hom ≫ pullbackStructureSheafHom a
  erw [reassoc_of% n₁, pullback_map_eqToHom_assoc (secT_bcMap f σ hσ a g g' w), reassoc_of% n₂]
  erw [← CategoryTheory.Functor.map_comp_assoc, h]
  rfl

variable (hσ) in
lemma picSigmaMap_comp (a : T' ⟶ T) (b : T'' ⟶ T') (w : a ≫ g = g') (w' : b ≫ g' = g'')
    (w'' : (b ≫ a) ≫ g = g'') (x : picSigmaGrp f σ hσ g) :
    picSigmaMap f σ hσ b g' g'' w' (picSigmaMap f σ hσ a g g' w x) =
      picSigmaMap f σ hσ (b ≫ a) g g'' w'' x := by
  apply Subtype.ext
  simp only [coe_picSigmaMap]
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← bcMap_comp]

lemma cls_pull_pull (R : Rigidified f σ hσ g) (a : T' ⟶ T) (b : T'' ⟶ T') (c : T'' ⟶ T)
    (hc : b ≫ a = c) (w : a ≫ g = g') (w' : b ≫ g' = g'') (w'' : c ≫ g = g'') :
    ((R.pull a g' w).pull b g'' w').cls = (R.pull c g'' w'').cls := by
  subst hc
  rw [cls_pull, cls_pull, cls_pull, picSigmaMap_comp]

/-- **`b^* a^* R ≅ c^* R`** (`b ≫ a = c`), the unique rigidified isomorphism. -/
def pullComp (hrig : IsRigidAlong (secT f σ hσ g'')) (R : Rigidified f σ hσ g) (a : T' ⟶ T)
    (b : T'' ⟶ T') (c : T'' ⟶ T) (hc : b ≫ a = c) (w : a ≫ g = g') (w' : b ≫ g' = g'')
    (w'' : c ≫ g = g'') : ((R.pull a g' w).pull b g'' w').L ≅ (R.pull c g'' w'').L :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_pull R a b c hc w w' w'')).exists.choose

lemma isRigidIso_pullComp (hrig : IsRigidAlong (secT f σ hσ g'')) (R : Rigidified f σ hσ g)
    (a : T' ⟶ T) (b : T'' ⟶ T') (c : T'' ⟶ T) (hc : b ≫ a = c) (w : a ≫ g = g')
    (w' : b ≫ g' = g'') (w'' : c ≫ g = g'') :
    ((R.pull a g' w).pull b g'' w').IsRigidIso _ (pullComp hrig R a b c hc w w' w'') :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_pull R a b c hc w w' w'')).exists.choose_spec

/-- Every rigidified isomorphism `b^* a^* R ≅ c^* R` is `pullComp`. -/
lemma IsRigidIso.eq_pullComp (hrig : IsRigidAlong (secT f σ hσ g'')) {R : Rigidified f σ hσ g}
    {a : T' ⟶ T} {b : T'' ⟶ T'} {c : T'' ⟶ T} (hc : b ≫ a = c) {w : a ≫ g = g'}
    {w' : b ≫ g' = g''} {w'' : c ≫ g = g''} {φ : ((R.pull a g' w).pull b g'' w').L ≅
      (R.pull c g'' w'').L} (h : ((R.pull a g' w).pull b g'' w').IsRigidIso _ φ) :
    φ = pullComp hrig R a b c hc w w' w'' :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_pull R a b c hc w w' w'')).unique h
    (isRigidIso_pullComp hrig R a b c hc w w' w'')

lemma cls_pull_id (R : Rigidified f σ hσ g) (a : T ⟶ T) (ha : a = 𝟙 T) (w : a ≫ g = g) :
    (R.pull a g w).cls = R.cls := by
  rw [cls_pull]
  apply Subtype.ext
  rw [coe_picSigmaMap, bcMap_self f a ha, Scheme.Pic.map_id, AddMonoidHom.id_apply]

/-- **`𝟙^* R ≅ R`**, the unique rigidified isomorphism. -/
def pullId (hrig : IsRigidAlong (secT f σ hσ g)) (R : Rigidified f σ hσ g) (a : T ⟶ T)
    (ha : a = 𝟙 T) (w : a ≫ g = g) : (R.pull a g w).L ≅ R.L :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_id R a ha w)).exists.choose

lemma isRigidIso_pullId (hrig : IsRigidAlong (secT f σ hσ g)) (R : Rigidified f σ hσ g)
    (a : T ⟶ T) (ha : a = 𝟙 T) (w : a ≫ g = g) :
    (R.pull a g w).IsRigidIso R (pullId hrig R a ha w) :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_id R a ha w)).exists.choose_spec

/-- Every rigidified isomorphism `𝟙^* R ≅ R` is `pullId`. -/
lemma IsRigidIso.eq_pullId (hrig : IsRigidAlong (secT f σ hσ g)) {R : Rigidified f σ hσ g}
    {a : T ⟶ T} (ha : a = 𝟙 T) {w : a ≫ g = g} {φ : (R.pull a g w).L ≅ R.L}
    (h : (R.pull a g w).IsRigidIso R φ) : φ = pullId hrig R a ha w :=
  (exists_unique_rigidIso hrig _ _ (cls_pull_id R a ha w)).unique h
    (isRigidIso_pullId hrig R a ha w)

end Rigidified

end Generic

section Curve

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "LD" => jacFieldD C σ hσ Ω

open Rigidified

lemma isRigidIso_poincareGalIso (g : Gal(LD/k)) :
    ((poincare C σ hσ Ω).pull _ _ (Over.w (galHom C σ hσ Ω g))).IsRigidIso
      (poincare C σ hσ Ω) (poincareGalIso C σ hσ Ω g) :=
  (exists_unique_poincareGalIso C σ hσ Ω g).exists.choose_spec

/-- Every rigidified isomorphism `(1 × g)^* P ≅ P` is `poincareGalIso g`. -/
lemma IsRigidIso.eq_poincareGalIso (g : Gal(LD/k))
    {φ : ((poincare C σ hσ Ω).pull (galHom C σ hσ Ω g).left _
      (Over.w (galHom C σ hσ Ω g))).L ≅ (poincare C σ hσ Ω).L}
    (h : ((poincare C σ hσ Ω).pull _ _ (Over.w (galHom C σ hσ Ω g))).IsRigidIso
      (poincare C σ hσ Ω) φ) : φ = poincareGalIso C σ hσ Ω g :=
  (exists_unique_poincareGalIso C σ hσ Ω g).unique h (isRigidIso_poincareGalIso C σ hσ Ω g)

lemma galHom_mul_left (g h : Gal(LD/k)) :
    (galHom C σ hσ Ω g).left ≫ (galHom C σ hσ Ω h).left = (galHom C σ hσ Ω (g * h)).left :=
  (jacDAction C σ hσ Ω).act_mul g h

lemma galHom_one_left : (galHom C σ hσ Ω 1).left = 𝟙 _ :=
  (jacDAction C σ hσ Ω).act_one

/-- **The cocycle condition of the Poincaré descent datum**: `φ_{gh} = c⁻¹ ≫ g^* φ_h ≫ φ_g`,
`c = pullComp : g^* h^* P ≅ (gh)^* P` (`act g ≫ act h = act (g h)`). -/
theorem poincareGalIso_mul (g h : Gal(LD/k)) :
    poincareGalIso C σ hσ Ω (g * h) =
      (pullComp (isRigidAlong_curve C σ hσ _) (poincare C σ hσ Ω) (galHom C σ hσ Ω h).left
        (galHom C σ hσ Ω g).left _ (galHom_mul_left C σ hσ Ω g h)
        (Over.w (galHom C σ hσ Ω h)) (Over.w (galHom C σ hσ Ω g))
        (Over.w (galHom C σ hσ Ω (g * h)))).symm ≪≫
      pullIso (poincareGalIso C σ hσ Ω h) _ _ (Over.w (galHom C σ hσ Ω g)) ≪≫
      poincareGalIso C σ hσ Ω g := by
  symm
  refine IsRigidIso.eq_poincareGalIso C σ hσ Ω (g * h) ?_
  exact ((isRigidIso_pullComp _ _ _ _ _ _ _ _ _).symm.trans
    ((isRigidIso_poincareGalIso C σ hσ Ω h).pull _ _ _)).trans
    (isRigidIso_poincareGalIso C σ hσ Ω g)

/-- **The descent datum at `1`** is `pullId : 𝟙^* P ≅ P`. -/
theorem poincareGalIso_one :
    poincareGalIso C σ hσ Ω 1 =
      pullId (isRigidAlong_curve C σ hσ _) (poincare C σ hσ Ω) _ (galHom_one_left C σ hσ Ω)
        (Over.w (galHom C σ hσ Ω 1)) :=
  (isRigidIso_poincareGalIso C σ hσ Ω 1).eq_pullId _ _

end Curve

end CurvesJacobian
