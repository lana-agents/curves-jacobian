/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.LineBundle

/-!
# Duals of line bundles

For a presheaf of modules `P` on a scheme `X` we define the presheaf of modules `dualPre P` whose
sections over `U` are the compatible families of linear forms `P(V) → 𝒪(V)`, `V ≤ U`
(a presheaf version of `ℋom(P, 𝒪_X)`), and the evaluation `P ⊗ dualPre P ⟶ 𝟙_`.
A basis `e` of `P` on `U` gives the dual basis `e^∨` of `dualPre P` on `U`, and the evaluation is
bijective on every `V ≤ U`; hence for an invertible sheaf `L` the evaluation becomes an
isomorphism `L ⊗ L^∨ ≅ 𝒪_X` after sheafification (`Modules.tensorDualIso`), and
`L^∨ := sheafify (dualPre L)` is invertible (Stacks, Tag 0B8K: an invertible module `L` has an
inverse, namely `ℋom(L, 𝒪_X)`).
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

open CurvesJacobian

variable {X : Scheme.{u}}

namespace PresheafOfModules

/-- Restriction of functions along `V ≤ U`. -/
noncomputable abbrev rres {U V : X.Opens} (h : V ≤ U) (r : X.ringCatSheaf.obj.obj (op U)) :
    X.ringCatSheaf.obj.obj (op V) :=
  X.ringCatSheaf.obj.map (homOfLE h).op r

lemma rres_rres {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (r : X.ringCatSheaf.obj.obj (op U)) :
    rres h' (rres h r) = rres (h'.trans h) r := by
  change (X.ringCatSheaf.obj.map _ ≫ X.ringCatSheaf.obj.map _) r = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

lemma rres_self {U : X.Opens} (r : X.ringCatSheaf.obj.obj (op U)) : rres (le_refl U) r = r := by
  change X.ringCatSheaf.obj.map (𝟙 _) r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

variable (P : X.PresheafOfModules)

/-- Sections of the dual presheaf over `U`: compatible families of linear forms on `P(V)`,
`V ≤ U`. -/
@[ext]
structure DualSec (U : X.Opens) where
  /-- the linear form on `P(V)` -/
  toFun : ∀ V : X.Opens, V ≤ U → P.obj (op V) → X.ringCatSheaf.obj.obj (op V)
  map_add' : ∀ V h a b, toFun V h (a + b) = toFun V h a + toFun V h b
  map_smul' : ∀ V h (r : X.ringCatSheaf.obj.obj (op V)) a, toFun V h (r • a) = r * toFun V h a
  natural' : ∀ V W (hV : V ≤ U) (hW : W ≤ V) a,
    toFun W (hW.trans hV) (res P hW a) = rres hW (toFun V hV a)

namespace DualSec

variable {P} {U : X.Opens}

/-- The underlying family of functions, indexed by the opens contained in `U`. -/
def toPi (φ : DualSec P U) :
    (V : {V : X.Opens // V ≤ U}) → P.obj (op V.1) → X.ringCatSheaf.obj.obj (op V.1) :=
  fun V ↦ φ.toFun V.1 V.2

lemma toPi_injective : Function.Injective (toPi (P := P) (U := U)) := by
  intro φ ψ h
  ext V hV a
  exact congrFun (congrFun h ⟨V, hV⟩) a

instance : Zero (DualSec P U) where
  zero := ⟨fun _ _ _ ↦ 0, fun _ _ _ _ ↦ (add_zero 0).symm, fun _ _ r _ ↦ (mul_zero r).symm,
    fun _ _ _ hW _ ↦ (map_zero (X.ringCatSheaf.obj.map (homOfLE hW).op).hom).symm⟩

instance : Add (DualSec P U) where
  add φ ψ := ⟨fun V h a ↦ φ.toFun V h a + ψ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', ψ.map_add']; abel,
    fun V h r a ↦ by rw [φ.map_smul', ψ.map_smul', mul_add],
    fun V W hV hW a ↦ by
      rw [φ.natural', ψ.natural']
      exact (map_add (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _ _).symm⟩

instance : Neg (DualSec P U) where
  neg φ := ⟨fun V h a ↦ -φ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', neg_add],
    fun V h r a ↦ by rw [φ.map_smul', mul_neg],
    fun V W hV hW a ↦ by
      rw [φ.natural']
      exact (map_neg (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _).symm⟩

instance : Sub (DualSec P U) where
  sub φ ψ := ⟨fun V h a ↦ φ.toFun V h a - ψ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', ψ.map_add']; abel,
    fun V h r a ↦ by rw [φ.map_smul', ψ.map_smul', mul_sub],
    fun V W hV hW a ↦ by
      rw [φ.natural', ψ.natural']
      exact (map_sub (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _ _).symm⟩

instance : SMul ℕ (DualSec P U) where
  smul n φ := ⟨fun V h a ↦ n • φ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', smul_add],
    fun V h r a ↦ by rw [φ.map_smul', mul_smul_comm],
    fun V W hV hW a ↦ by
      rw [φ.natural']
      exact (map_nsmul (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _ _).symm⟩

instance : SMul ℤ (DualSec P U) where
  smul n φ := ⟨fun V h a ↦ n • φ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', smul_add],
    fun V h r a ↦ by rw [φ.map_smul', mul_smul_comm],
    fun V W hV hW a ↦ by
      rw [φ.natural']
      exact (map_zsmul (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _ _).symm⟩

instance : AddCommGroup (DualSec P U) :=
  Function.Injective.addCommGroup _ toPi_injective rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp] lemma add_toFun (φ ψ : DualSec P U) (V h a) :
    (φ + ψ).toFun V h a = φ.toFun V h a + ψ.toFun V h a := rfl

@[simp] lemma zero_toFun (V h a) : (0 : DualSec P U).toFun V h a = 0 := rfl

instance : SMul (X.ringCatSheaf.obj.obj (op U)) (DualSec P U) where
  smul c φ := ⟨fun V h a ↦ rres h c * φ.toFun V h a,
    fun V h a b ↦ by rw [φ.map_add', mul_add],
    fun V h r a ↦ by rw [φ.map_smul']; ring,
    fun V W hV hW a ↦ by
      rw [φ.natural', ← rres_rres hV hW c]
      exact (map_mul (X.ringCatSheaf.obj.map (homOfLE hW).op).hom _ _).symm⟩

@[simp] lemma smul_toFun (c : X.ringCatSheaf.obj.obj (op U)) (φ : DualSec P U) (V h a) :
    (c • φ).toFun V h a = rres h c * φ.toFun V h a := rfl

instance : Module (X.ringCatSheaf.obj.obj (op U)) (DualSec P U) where
  one_smul φ := by
    ext V h a
    change rres h (1 : X.ringCatSheaf.obj.obj (op U)) * φ.toFun V h a = φ.toFun V h a
    rw [show rres h (1 : X.ringCatSheaf.obj.obj (op U)) = 1 from
      map_one (X.ringCatSheaf.obj.map (homOfLE h).op).hom, one_mul]
  mul_smul c d φ := by
    ext V h a
    change rres h (c * d) * φ.toFun V h a = rres h c * (rres h d * φ.toFun V h a)
    rw [show rres h (c * d) = rres h c * rres h d from
      map_mul (X.ringCatSheaf.obj.map (homOfLE h).op).hom _ _, mul_assoc]
  smul_zero c := by
    ext V h a
    exact mul_zero (rres h c)
  smul_add c φ ψ := by
    ext V h a
    exact mul_add (rres h c) (φ.toFun V h a) (ψ.toFun V h a)
  add_smul c d φ := by
    ext V h a
    change rres h (c + d) * φ.toFun V h a = rres h c * φ.toFun V h a + rres h d * φ.toFun V h a
    rw [show rres h (c + d) = rres h c + rres h d from
      map_add (X.ringCatSheaf.obj.map (homOfLE h).op).hom _ _, add_mul]
  zero_smul φ := by
    ext V h a
    change rres h (0 : X.ringCatSheaf.obj.obj (op U)) * φ.toFun V h a = 0
    rw [show rres h (0 : X.ringCatSheaf.obj.obj (op U)) = 0 from
      map_zero (X.ringCatSheaf.obj.map (homOfLE h).op).hom, zero_mul]

/-- Restriction of dual sections. -/
def restrict {U' : X.Opens} (hU : U' ≤ U) (φ : DualSec P U) : DualSec P U' :=
  ⟨fun V h a ↦ φ.toFun V (h.trans hU) a, fun V _ ↦ φ.map_add' V _,
    fun V _ ↦ φ.map_smul' V _, fun V W _ hW ↦ φ.natural' V W _ hW⟩

@[simp] lemma restrict_toFun {U' : X.Opens} (hU : U' ≤ U) (φ : DualSec P U) (V h a) :
    (φ.restrict hU).toFun V h a = φ.toFun V (h.trans hU) a := rfl

end DualSec


/-- The abelian presheaf of dual sections. -/
def dualPresheaf : (X.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (DualSec P U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := DualSec.restrict f.unop.le, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance (U : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) ((dualPresheaf P).obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op U.unop)) (DualSec P U.unop))

/-- The dual presheaf of modules `U ↦ Hom(P|_U, 𝒪_U)`. -/
def dualPre : X.PresheafOfModules :=
  _root_.PresheafOfModules.ofPresheaf (dualPresheaf P) (fun U U' f r φ ↦ by
    refine DualSec.ext ?_
    funext V h a
    change rres (h.trans f.unop.le) r * φ.toFun V _ a =
      rres h (X.ringCatSheaf.obj.map f r) * φ.toFun V _ a
    rw [← rres_rres f.unop.le h]
    rfl)

lemma dualPre_res_toFun {U U' : X.Opens} (hU : U' ≤ U) (φ : DualSec P U) (V : X.Opens)
    (h : V ≤ U') (a : P.obj (op V)) :
    DualSec.toFun (res (dualPre P) hU φ : DualSec P U') V h a = φ.toFun V (h.trans hU) a := rfl

lemma dualPre_smul_toFun {U : X.Opens} (r : X.ringCatSheaf.obj.obj (op U)) (φ : DualSec P U)
    (V : X.Opens) (h : V ≤ U) (a : P.obj (op V)) :
    DualSec.toFun (r • φ : (dualPre P).obj (op U)) V h a = rres h r * φ.toFun V h a := rfl

variable {P}

section DualBasis

variable {U : X.Opens} {e : P.obj (op U)} (he : IsBasisOn P U e)

/-- The coordinate of `a ∈ P(V)` with respect to the basis `e|_V`. -/
def coord {V : X.Opens} (h : V ≤ U) (a : P.obj (op V)) : X.ringCatSheaf.obj.obj (op V) :=
  (Equiv.ofBijective _ (he h)).symm a

lemma coord_smul {V : X.Opens} (h : V ≤ U) (a : P.obj (op V)) :
    coord he h a • res P h e = a :=
  Equiv.ofBijective_apply_symm_apply _ (he h) a

lemma coord_eq {V : X.Opens} (h : V ≤ U) (a : P.obj (op V)) (r : X.ringCatSheaf.obj.obj (op V))
    (hr : r • res P h e = a) : coord he h a = r :=
  (he h).1 ((coord_smul he h a).trans hr.symm)

/-- The dual basis. -/
def dualBasis : DualSec P U where
  toFun V h a := coord he h a
  map_add' V h a b := coord_eq he h _ _ (by rw [add_smul, coord_smul, coord_smul])
  map_smul' V h r a := coord_eq he h _ _ (by rw [mul_smul, coord_smul])
  natural' V W hV hW a := coord_eq he _ _ _ (by
    rw [← res_res P hV hW, ← res_smul, coord_smul])

lemma coord_res_self {V : X.Opens} (h : V ≤ U) : coord he h (res P h e) = 1 :=
  coord_eq he h _ _ (one_smul _ _)

/-- The dual basis is a basis of the dual presheaf. -/
lemma isBasisOn_dualBasis : IsBasisOn (dualPre P) U (dualBasis he) := by
  intro V h
  constructor
  · intro r r' hrr'
    have := congrArg (fun φ : DualSec P V ↦ φ.toFun V le_rfl (res P h e)) hrr'
    change rres le_rfl r * coord he _ (res P h e) = rres le_rfl r' * coord he _ (res P h e)
      at this
    rwa [coord_res_self, rres_self, rres_self, mul_one, mul_one] at this
  · intro ψ
    refine ⟨ψ.toFun V le_rfl (res P h e), ?_⟩
    refine DualSec.ext ?_
    funext W hW a
    change rres hW (ψ.toFun V le_rfl (res P h e)) * coord he _ a = ψ.toFun W hW a
    conv_rhs => rw [← coord_smul he (hW.trans h) a, ψ.map_smul', ← res_res P h hW,
      ψ.natural' V W le_rfl hW]
    exact mul_comm _ _

end DualBasis

variable (P)

/-- The evaluation pairing `P ⊗ P^∨ ⟶ 𝒪`. -/
def ev : P ⊗ dualPre P ⟶ 𝟙_ X.PresheafOfModules where
  app V := ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ _
    (fun (a : P.obj V) (φ : DualSec P V.unop) ↦ φ.toFun V.unop le_rfl a)
    (fun a a' φ ↦ φ.map_add' _ _ a a')
    (fun r a φ ↦ φ.map_smul' _ _ r a)
    (fun a φ ψ ↦ rfl)
    (fun r a φ ↦ by
      change rres le_rfl (show X.ringCatSheaf.obj.obj (op V.unop) from r) *
        φ.toFun V.unop le_rfl a = (show X.ringCatSheaf.obj.obj (op V.unop) from r) *
          φ.toFun V.unop le_rfl a
      rw [rres_self])))
  naturality {V V'} f := ModuleCat.MonoidalCategory.tensor_ext (fun a φ ↦ by
    change (φ.restrict f.unop.le).toFun V'.unop le_rfl (P.map f a) =
      X.ringCatSheaf.obj.map f (φ.toFun V.unop le_rfl a)
    rw [DualSec.restrict_toFun]
    exact φ.natural' V.unop V'.unop le_rfl f.unop.le a)

lemma ev_tmul {V : X.Opens} (a : P.obj (op V)) (φ : DualSec P V) :
    (ev P).app (op V) (a ⊗ₜ φ : (P ⊗ dualPre P).obj (op V)) = φ.toFun V le_rfl a := rfl

/-- The evaluation is bijective on opens on which `P` has a basis. -/
lemma bijective_ev_app {U : X.Opens} {e : P.obj (op U)} (he : IsBasisOn P U e) {V : X.Opens}
    (h : V ≤ U) : Function.Bijective ((ev P).app (op V)) := by
  have hb := ((he.restrict h).tensor ((isBasisOn_dualBasis he).restrict h)) (le_refl V)
  rw [res_self] at hb
  let ψ := Equiv.ofBijective _ hb
  have hleft : ∀ r, (ev P).app (op V) (ψ r) = r := by
    intro r
    have := map_smul ((ev P).app (op V)).hom r
      (show ↑((P ⊗ dualPre P).obj (op V)) from res P h e ⊗ₜ res (dualPre P) h (dualBasis he))
    refine this.trans ?_
    change r * coord he _ (res P h e) = r
    rw [coord_res_self, mul_one]
  have : ((ev P).app (op V) : _ → _) = ψ.symm := by
    funext x
    obtain ⟨r, rfl⟩ := ψ.surjective x
    rw [hleft, Equiv.symm_apply_apply]
  rw [this]
  exact ψ.symm.bijective
end PresheafOfModules

namespace Modules

/-- The dual `L^∨ = ℋom(L, 𝒪_X)` of a sheaf of modules (the sheafification of `dualPre`). -/
def dual (L : X.Modules) : X.Modules := (sheafify X).obj (PresheafOfModules.dualPre (toPre L))

instance (L : X.Modules) [L.IsInvertible] : (dual L).IsInvertible :=
  isInvertible_sheafify _ (fun x ↦ by
    obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) x
    exact ⟨U, _, hxU, PresheafOfModules.isBasisOn_dualBasis hs.toPre⟩)

lemma sheafificationW_ev (L : X.Modules) [L.IsInvertible] :
    sheafificationW X (PresheafOfModules.ev (toPre L)) := by
  change (Opens.grothendieckTopology X).W ((_root_.PresheafOfModules.toPresheaf _).map _)
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  have H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U,
      Function.Bijective ((PresheafOfModules.ev (toPre L)).app (op V)) := fun x ↦ by
    obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) x
    exact ⟨U, hxU, fun V hV ↦ PresheafOfModules.bijective_ev_app _ hs.toPre hV⟩
  exact ⟨PresheafOfModules.isLocallyInjective_of_locally_bijective _ H,
    PresheafOfModules.isLocallySurjective_of_locally_bijective _ H⟩

instance (L : X.Modules) [L.IsInvertible] :
    IsIso ((sheafify X).map (PresheafOfModules.ev (toPre L))) :=
  Localization.inverts (sheafificationFunctor X) (sheafificationW X) _ (sheafificationW_ev L)

/-- An invertible sheaf tensored with its dual is trivial. -/
def tensorDualIso (L : X.Modules) [L.IsInvertible] : L ⊗ dual L ≅ 𝟙_ X.Modules :=
  whiskerRightIso (sheafifyToPreIso L).symm _ ≪≫ Functor.Monoidal.μIso (sheafify X) _ _ ≪≫
    asIso ((sheafify X).map (PresheafOfModules.ev (toPre L))) ≪≫
      (Functor.Monoidal.εIso (sheafify X)).symm

end Modules

end AlgebraicGeometry.Scheme

end
