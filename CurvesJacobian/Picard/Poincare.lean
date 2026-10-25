/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.JacobianDescentField
import CurvesJacobian.Picard.RigidIso
import CurvesJacobian.Picard.PicRigid
import CurvesJacobian.Picard.PicSpecEquiv

/-!
# Rigidified line bundles and the Poincaré bundle on `C × J_L` (JAC J1, first part)

Following van der Geer–Moonen, *Abelian varieties*, Ch. VI §1 (rigidified line bundles, the
functor `P_{X/S,ε}` and the Poincaré bundle with its universal property), for `f : X ⟶ S` with a
section `σ` and `g : T ⟶ S`:

* `CurvesJacobian.Rigidified f σ hσ g`: a line bundle `L` on `X_T` with a rigidification
  `α : σ_T^* L ≅ 𝒪_T`; its class `Rigidified.cls ∈ Pic_{X/S,σ}(T)`, every class has a
  rigidified representative (`exists_rigidified`); pullback along `a : T' ⟶ T` over `S`
  (`Rigidified.pull`, `cls_pull`);
* **`exists_unique_rigidIso`**: if `X_T` is rigid along `σ_T` (for a curve: `isRigidAlong_curve`),
  two rigidified bundles with the same class are isomorphic by a **unique** isomorphism compatible
  with the rigidifications.

For a curve `C/k` with a rational point and `J_L = jacD C σ hσ Ω`:

* `univClass`: the universal element of `Pic⁰_{C/k,σ}(J_L)` (`jacDRepresentableBy`);
  **`univClass_galois`**: it is invariant under the semilinear `Gal(L/k)`-action on `J_L`;
* **`poincare`**: a rigidified line bundle on `C ×_k J_L` of class `univClass` (the Poincaré
  bundle), with the universal property **`poincare_universal`** (every rigidified bundle of
  degree `0` on `C ×_k T`, `T` over `L`, is the pullback along a unique `T ⟶ J_L`, up to a unique
  rigidified isomorphism) and the **Galois descent datum** `poincareGalIso g : (1 × g)^* P ≅ P`
  (`exists_unique_poincareGalIso`: unique rigidified isomorphism).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Scheme Scheme.Modules ModulesGlue Belyi

section Generic

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- **A rigidified line bundle** on `X_T = X ×_S T` (van der Geer–Moonen VI §1): an invertible
sheaf `L` with an isomorphism `σ_T^* L ≅ 𝒪_T`. -/
structure Rigidified {T : Scheme.{u}} (g : T ⟶ S) where
  /-- The line bundle on `X_T`. -/
  L : (pullback f g).Modules
  [isInvertible : L.IsInvertible]
  /-- The rigidification along `σ_T`. -/
  α : (Modules.pullback (secT f σ hσ g)).obj L ≅ structureSheaf T

attribute [instance] Rigidified.isInvertible

variable {f σ hσ} {T T' : Scheme.{u}} {g : T ⟶ S}

/-- The class of a rigidified line bundle in `Pic_{X/S,σ}(T)`. -/
def Rigidified.cls (R : Rigidified f σ hσ g) : picSigmaGrp f σ hσ g :=
  ⟨Scheme.Pic.mk R.L, by
    rw [mem_picSigmaGrp, Scheme.Pic.map_mk, Scheme.Pic.mk_eq_zero_iff]
    exact ⟨R.α ≪≫ structureSheafIsoUnit T⟩⟩

variable (f σ hσ) in
/-- Every class of `Pic_{X/S,σ}(T)` has a rigidified representative. -/
theorem exists_rigidified (x : picSigmaGrp f σ hσ g) :
    ∃ R : Rigidified f σ hσ g, R.cls = x := by
  have hx := (mem_picSigmaGrp f σ hσ _).1 x.2
  rw [← Scheme.Pic.mk_rep (x : (pullback f g).Pic), Scheme.Pic.map_mk,
    Scheme.Pic.mk_eq_zero_iff] at hx
  exact ⟨⟨Scheme.Pic.rep (x : (pullback f g).Pic), hx.some ≪≫ (structureSheafIsoUnit T).symm⟩,
    Subtype.ext (Scheme.Pic.mk_rep _)⟩

/-- **Rigidified isomorphisms**: `φ : L ≅ L'` with `σ^* φ ∘ α = α'`. -/
def Rigidified.IsRigidIso (R R' : Rigidified f σ hσ g) (φ : R.L ≅ R'.L) : Prop :=
  (Modules.pullback (secT f σ hσ g)).map φ.hom ≫ R'.α.hom = R.α.hom

/-- **Rigidified line bundles with the same class are isomorphic by a unique rigidified
isomorphism**, if `X_T` is rigid along `σ_T` (van der Geer–Moonen VI §1: rigidified line bundles
have no non-trivial automorphisms). -/
theorem exists_unique_rigidIso (hrig : IsRigidAlong (secT f σ hσ g))
    (R R' : Rigidified f σ hσ g) (h : R.cls = R'.cls) :
    ∃! φ : R.L ≅ R'.L, R.IsRigidIso R' φ := by
  have hmk : Scheme.Pic.mk R.L = Scheme.Pic.mk R'.L := congrArg Subtype.val h
  obtain ⟨φ₀⟩ := (Scheme.Pic.mk_eq_mk_iff).1 hmk
  obtain ⟨φ, hφ⟩ := exists_iso_pullback_map_eq (pullback.snd f g) (secT f σ hσ g)
    (secT_snd f σ hσ g) φ₀ (R.α ≪≫ R'.α.symm)
  refine ⟨φ, ?_, fun ψ hψ ↦ ?_⟩
  · change _ ≫ _ = _
    rw [hφ]
    simp
  · refine iso_ext_of_pullback_map_eq _ hrig ?_
    rw [hφ]
    have : (Modules.pullback (secT f σ hσ g)).map ψ.hom = R.α.hom ≫ R'.α.inv := by
      rw [← hψ]
      simp
    rw [this]
    rfl

/-- **Pullback of a rigidified line bundle** along `a : T' ⟶ T` over `S`. -/
def Rigidified.pull (R : Rigidified f σ hσ g) (a : T' ⟶ T) (g' : T' ⟶ S) (w : a ≫ g = g') :
    Rigidified f σ hσ g' where
  L := (Modules.pullback (bcMap f a g g' w)).obj R.L
  α := ((Modules.pullbackComp (secT f σ hσ g') (bcMap f a g g' w)).app R.L) ≪≫
    eqToIso (by rw [secT_bcMap]) ≪≫
    ((Modules.pullbackComp a (secT f σ hσ g)).app R.L).symm ≪≫
    (Modules.pullback a).mapIso R.α ≪≫ asIso (pullbackStructureSheafHom a)

/-- The class of the pullback is the pullback of the class. -/
lemma Rigidified.cls_pull (R : Rigidified f σ hσ g) (a : T' ⟶ T) (g' : T' ⟶ S)
    (w : a ≫ g = g') : (R.pull a g' w).cls = picSigmaMap f σ hσ a g g' w R.cls :=
  Subtype.ext (Scheme.Pic.map_mk _ _).symm

end Generic

section Curve

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)

/-- For a curve, `C_T` is rigid along `σ_T` (`𝒪_T ≅ f_{T,*}𝒪_{C_T}`, Stacks 0B9U). -/
lemma isRigidAlong_curve {T : Scheme.{u}} (g : T ⟶ Sk) :
    IsRigidAlong (secT (C ↘ Sk) σ hσ g) :=
  isRigidAlong_of_surjective (pullback.snd (C ↘ Sk) g) _ (secT_snd _ σ hσ g)
    (IsCurveOver.surjective_app_pullback_snd k C g ⊤)

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "LD" => jacFieldD C σ hσ Ω
local notation "pL" => Belyi.specAlgebraMap (k₀ := k) LD
local notation "JL" => jacD C σ hσ Ω
local notation "RJ" => jacDRepresentableBy C σ hσ Ω

/-- `J_L` as a `k`-scheme. -/
abbrev jacDk : Over Sk := (Over.map pL).obj JL

/-- **The universal class** `ξ ∈ Pic⁰_{C/k,σ}(J_L)`. -/
def univClass : picSigmaGrp (C ↘ Sk) σ hσ (jacDk C σ hσ Ω).hom :=
  ((RJ).homEquiv (𝟙 JL)).1

/-- **Universality of `ξ`**: the class of `f : T ⟶ J_L` is the pullback of `ξ`. -/
lemma homEquiv_eq_pull {T : Over (Spec (CommRingCat.of LD))} (x : T ⟶ JL) :
    ((RJ).homEquiv x).1 = picSigmaMap (C ↘ Sk) σ hσ x.left _ _
      (Over.w ((Over.map pL).map x)) (univClass C σ hσ Ω) :=
  congrArg Subtype.val (homEquiv_eq_map pL _ (RJ) x)

/-- The semilinear action of `g ∈ Gal(L/k)` on `J_L` as an endomorphism of the `k`-scheme `J_L`. -/
def galHom (g : Gal(LD/k)) : jacDk C σ hσ Ω ⟶ jacDk C σ hσ Ω :=
  Over.homMk ((jacDAction C σ hσ Ω).act g) (by
    change (jacDAction C σ hσ Ω).act g ≫ (JL).hom ≫ pL = (JL).hom ≫ pL
    have hα : GaloisDescent.specGal g ≫ pL = pL := GaloisDescent.specGal_comp_sL g
    rw [(jacDAction C σ hσ Ω).act_comp_assoc, hα])

/-- **The universal class is Galois-invariant**: `(1 × g)^* ξ = ξ`. -/
theorem univClass_galois (g : Gal(LD/k)) :
    picSigmaMap (C ↘ Sk) σ hσ (galHom C σ hσ Ω g).left _ _ (Over.w (galHom C σ hσ Ω g))
      (univClass C σ hσ Ω) = univClass C σ hσ Ω := by
  set P := picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat
  have hα := GaloisDescent.specGal_comp_sL (k := k) (L := LD) g
  have h1 := homEquiv_eq_map pL P (RJ) (twistHom pL P (RJ) hα)
  rw [homEquiv_twistHom] at h1
  have h2 := congrArg (P.map (twistIso pL hα JL).inv.op) h1
  rw [map_map_op, map_map_op, Iso.inv_hom_id, op_id, Functor.map_id_apply] at h2
  have h3 : P.map (galHom C σ hσ Ω g).op ((RJ).homEquiv (𝟙 JL)) = (RJ).homEquiv (𝟙 JL) :=
    (map_eq_of_left_eq P (by
      change twistLeft pL P (RJ) hα = 𝟙 _ ≫ twistLeft pL P (RJ) hα
      rw [Category.id_comp]) _).trans h2.symm
  exact congrArg Subtype.val h3

/-- **The Poincaré bundle** on `C ×_k J_L`: a rigidified line bundle of class `ξ`. -/
def poincare : Rigidified (C ↘ Sk) σ hσ (jacDk C σ hσ Ω).hom :=
  (exists_rigidified _ σ hσ (univClass C σ hσ Ω)).choose

lemma poincare_cls : (poincare C σ hσ Ω).cls = univClass C σ hσ Ω :=
  (exists_rigidified _ σ hσ (univClass C σ hσ Ω)).choose_spec

/-- **Universal property of the Poincaré bundle** (van der Geer–Moonen VI §1): for `T` over `L`,
every rigidified line bundle of degree `0` on `C ×_k T` has the class of the pullback of the
Poincaré bundle along a unique `x : T ⟶ J_L`, and is then isomorphic to that pullback by a unique
rigidified isomorphism. -/
theorem poincare_universal {T : Over (Spec (CommRingCat.of LD))}
    (M : Rigidified (C ↘ Sk) σ hσ ((Over.map pL).obj T).hom)
    (hM : M.cls ∈ picZeroGrp (curveToP1 k C) σ hσ ((Over.map pL).obj T).hom) :
    ∃! x : T ⟶ JL, ∃! φ : M.L ≅ ((poincare C σ hσ Ω).pull x.left _
      (Over.w ((Over.map pL).map x))).L, M.IsRigidIso _ φ := by
  have key : ∀ x : T ⟶ JL, ((poincare C σ hσ Ω).pull x.left _
      (Over.w ((Over.map pL).map x))).cls = ((RJ).homEquiv x).1 := fun x ↦ by
    rw [Rigidified.cls_pull, poincare_cls, homEquiv_eq_pull]
    rfl
  refine ⟨(RJ).homEquiv.symm ⟨M.cls, hM⟩, ?_, fun x hx ↦ ?_⟩
  · refine exists_unique_rigidIso (isRigidAlong_curve C σ hσ _) _ _ ?_
    exact ((key _).trans (congrArg Subtype.val ((RJ).homEquiv.apply_symm_apply ⟨M.cls, hM⟩))).symm
  · obtain ⟨φ, -, -⟩ := hx
    have hc : M.cls = ((poincare C σ hσ Ω).pull x.left _ (Over.w ((Over.map pL).map x))).cls :=
      Subtype.ext (@Scheme.Pic.mk_eq_of_iso _ _ _ M.isInvertible (Rigidified.isInvertible _) φ)
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    change ((RJ).homEquiv x).1 = M.cls
    rw [← key, ← hc]

/-- **The Galois descent datum of the Poincaré bundle**: for `g ∈ Gal(L/k)` the pullback of `P`
along `1 × g` is isomorphic to `P` by a unique rigidified isomorphism. -/
theorem exists_unique_poincareGalIso (g : Gal(LD/k)) :
    ∃! φ : ((poincare C σ hσ Ω).pull (galHom C σ hσ Ω g).left _
      (Over.w (galHom C σ hσ Ω g))).L ≅ (poincare C σ hσ Ω).L,
      ((poincare C σ hσ Ω).pull _ _ (Over.w (galHom C σ hσ Ω g))).IsRigidIso
        (poincare C σ hσ Ω) φ := by
  refine exists_unique_rigidIso (isRigidAlong_curve C σ hσ _) _ _ ?_
  rw [Rigidified.cls_pull, poincare_cls, univClass_galois]

/-- The rigidified isomorphism `(1 × g)^* P ≅ P`. -/
def poincareGalIso (g : Gal(LD/k)) :
    ((poincare C σ hσ Ω).pull (galHom C σ hσ Ω g).left _
      (Over.w (galHom C σ hσ Ω g))).L ≅ (poincare C σ hσ Ω).L :=
  (exists_unique_poincareGalIso C σ hσ Ω g).exists.choose

end Curve

end CurvesJacobian
