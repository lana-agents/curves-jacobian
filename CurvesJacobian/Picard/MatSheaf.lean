/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ModulesGlue
import CurvesJacobian.Picard.PicRigid

/-!
# Sheaves of modules from matrix data on a two-set covering

This file is generic. Let `Y` be a scheme and `U`, `V` two opens. *Matrix data*
(`CurvesJacobian.MatSheaf.Data`) consist of idempotent matrices `e_U` over `Γ(Y, U)` and `e_V`
over `Γ(Y, V)` and gluing matrices `Φ`, `Ψ` over `Γ(Y, U ∩ V)` with `Φ Ψ = e_U`, `Ψ Φ = e_V`,
`e_U Φ = Φ = Φ e_V` (the matrix form of two finite projective modules glued over `U ∩ V`, cf.
`CurvesJacobian.ChartMatrix.MatData`). The associated sheaf of `𝒪_Y`-modules `D.sheaf` has as
sections over `W` the pairs `(a, b) ∈ 𝒪(U ∩ W)ⁿ × 𝒪(V ∩ W)ᵐ` with `e_U a = a`, `e_V b = b`
and `a = Φ b` on `U ∩ V ∩ W` (`Data.sec`).

* `Data.isInvertible`: if `U ∪ V = Y` and `e_U`, `e_V` are locally of the form `p λᵀ` with
  `λ ⬝ p = 1` (rank one), the sheaf is invertible (`Data.isBasisOn_basisU`,
  `Data.isBasisOn_basisV` give the local bases).

This is the construction used to lift invertible sheaves along square-zero thickenings
(`CurvesJacobian.Picard.PicLift`): matrix data lift, sheaves do not obviously.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Matrix

universe u

noncomputable section

namespace CurvesJacobian.MatSheaf

open Scheme ModulesGlue

variable {Y : Scheme.{u}}

/-! ### Restrictions of functions and vectors -/

/-- Restriction of functions, as a ring homomorphism. -/
abbrev ρ {W W' : Y.Opens} (h : W' ≤ W) : Γ(Y, W) →+* Γ(Y, W') :=
  (Y.presheaf.map (homOfLE h).op).hom

lemma ρ_ρ {W W' W'' : Y.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (x : Γ(Y, W)) :
    ρ h' (ρ h x) = ρ (h'.trans h) x :=
  rr_rr h h' x

lemma ρ_self {W : Y.Opens} (h : W ≤ W) (x : Γ(Y, W)) : ρ h x = x :=
  rr_self h x

lemma ρ_bijective_of_eq {W W' : Y.Opens} (e : W' = W) : Function.Bijective (ρ (Y := Y) e.le) :=
  rr_bijective_of_eq e

/-- Restriction of vectors of functions. -/
abbrev rv {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) (v : Fin n → Γ(Y, W)) : Fin n → Γ(Y, W') :=
  fun i ↦ ρ h (v i)

lemma rv_rv {n : ℕ} {W W' W'' : Y.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (v : Fin n → Γ(Y, W)) :
    rv h' (rv h v) = rv (h'.trans h) v :=
  funext fun i ↦ ρ_ρ h h' (v i)

lemma rv_self {n : ℕ} {W : Y.Opens} (h : W ≤ W) (v : Fin n → Γ(Y, W)) : rv h v = v :=
  funext fun i ↦ ρ_self h (v i)

@[simp]
lemma rv_add {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) (v w : Fin n → Γ(Y, W)) :
    rv h (v + w) = rv h v + rv h w :=
  funext fun i ↦ map_add (ρ h) (v i) (w i)

@[simp]
lemma rv_zero {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) : rv h (0 : Fin n → Γ(Y, W)) = 0 :=
  funext fun _ ↦ map_zero (ρ h)

@[simp]
lemma rv_neg {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) (v : Fin n → Γ(Y, W)) :
    rv h (-v) = -rv h v :=
  funext fun i ↦ map_neg (ρ h) (v i)

@[simp]
lemma rv_smul {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) (c : Γ(Y, W)) (v : Fin n → Γ(Y, W)) :
    rv h (c • v) = ρ h c • rv h v :=
  funext fun i ↦ map_mul (ρ h) c (v i)

lemma map_ρ_ρ {n m : ℕ} {W W' W'' : Y.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (M : Matrix (Fin n) (Fin m) Γ(Y, W)) : (M.map (ρ h)).map (ρ h') = M.map (ρ (h'.trans h)) :=
  by rw [Matrix.map_map]; exact congrArg M.map (funext fun x ↦ ρ_ρ h h' x)

lemma rv_mulVec {n m : ℕ} {O W W' : Y.Opens} (hO : W ≤ O) (h : W' ≤ W)
    (M : Matrix (Fin n) (Fin m) Γ(Y, O)) (v : Fin m → Γ(Y, W)) :
    rv h (M.map (ρ hO) *ᵥ v) = M.map (ρ (h.trans hO)) *ᵥ rv h v := by
  funext i
  rw [rv, RingHom.map_mulVec, map_ρ_ρ]
  rfl

/-! ### The structure sheaf: gluing on `O ∩ W_k` -/

lemma existsUnique_gluing_inter (O : Y.Opens) {ι : Type u} (W : ι → Y.Opens)
    (a : ∀ k, Γ(Y, O ⊓ W k))
    (h : ∀ k l, ρ (inf_le_inf_left O inf_le_left : O ⊓ (W k ⊓ W l) ≤ O ⊓ W k) (a k) =
      ρ (inf_le_inf_left O inf_le_right : O ⊓ (W k ⊓ W l) ≤ O ⊓ W l) (a l)) :
    ∃! s : Γ(Y, O ⊓ iSup W), ∀ k, ρ (inf_le_inf_left O (le_iSup W k)) s = a k := by
  refine Y.sheaf.existsUnique_gluing' (fun k ↦ O ⊓ W k) (O ⊓ iSup W)
    (fun k ↦ homOfLE (inf_le_inf_left O (le_iSup W k))) (by rw [inf_iSup_eq]) a ?_
  intro k l
  have hkl : (O ⊓ W k) ⊓ (O ⊓ W l) ≤ O ⊓ (W k ⊓ W l) := fun x hx ↦ ⟨hx.1.1, hx.1.2, hx.2.2⟩
  have := congrArg (ρ hkl) (h k l)
  rw [ρ_ρ, ρ_ρ] at this
  exact this

lemma eq_of_locally_eq_inter (O : Y.Opens) {ι : Type u} (W : ι → Y.Opens)
    (s t : Γ(Y, O ⊓ iSup W))
    (h : ∀ k, ρ (inf_le_inf_left O (le_iSup W k)) s = ρ (inf_le_inf_left O (le_iSup W k)) t) :
    s = t :=
  Y.sheaf.eq_of_locally_eq' (fun k ↦ O ⊓ W k) (O ⊓ iSup W)
    (fun k ↦ homOfLE (inf_le_inf_left O (le_iSup W k))) (by rw [inf_iSup_eq]) s t h

lemma vec_eq_of_locally_eq_inter {n : ℕ} (O : Y.Opens) {ι : Type u} (W : ι → Y.Opens)
    (s t : Fin n → Γ(Y, O ⊓ iSup W))
    (h : ∀ k, rv (inf_le_inf_left O (le_iSup W k)) s = rv (inf_le_inf_left O (le_iSup W k)) t) :
    s = t :=
  funext fun i ↦ eq_of_locally_eq_inter O W (s i) (t i) fun k ↦ congrFun (h k) i

/-! ### Matrix data -/

variable (U V : Y.Opens)

/-- **Matrix data** on the two-set covering `(U, V)`: idempotents `e_U`, `e_V` and gluing
matrices `Φ` (from `V` to `U`) and `Ψ` (from `U` to `V`) over `U ∩ V`. -/
structure Data where
  /-- the size of `e_U` -/
  n : ℕ
  /-- the size of `e_V` -/
  m : ℕ
  /-- the idempotent on `U` -/
  eU : Matrix (Fin n) (Fin n) Γ(Y, U)
  /-- the idempotent on `V` -/
  eV : Matrix (Fin m) (Fin m) Γ(Y, V)
  /-- gluing from `V` to `U` -/
  Φ : Matrix (Fin n) (Fin m) Γ(Y, U ⊓ V)
  /-- gluing from `U` to `V` -/
  Ψ : Matrix (Fin m) (Fin n) Γ(Y, U ⊓ V)
  eU_mul : eU * eU = eU
  eV_mul : eV * eV = eV
  Φ_Ψ : Φ * Ψ = eU.map (ρ (inf_le_left : U ⊓ V ≤ U))
  Ψ_Φ : Ψ * Φ = eV.map (ρ (inf_le_right : U ⊓ V ≤ V))
  eU_Φ : eU.map (ρ (inf_le_left : U ⊓ V ≤ U)) * Φ = Φ
  Φ_eV : Φ * eV.map (ρ (inf_le_right : U ⊓ V ≤ V)) = Φ

namespace Data

variable {U V} (D : Data U V)

/-- The ambient type of sections over `W`. -/
abbrev Amb (W : Y.Opens) : Type u := (Fin D.n → Γ(Y, U ⊓ W)) × (Fin D.m → Γ(Y, V ⊓ W))

/-- The conditions on a section over `W`. -/
def Cond (W : Y.Opens) (s : D.Amb W) : Prop :=
  D.eU.map (ρ (inf_le_left : U ⊓ W ≤ U)) *ᵥ s.1 = s.1 ∧
  D.eV.map (ρ (inf_le_left : V ⊓ W ≤ V)) *ᵥ s.2 = s.2 ∧
  rv (inf_le_inf_right W inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ W) s.1 =
    D.Φ.map (ρ (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V)) *ᵥ
      rv (inf_le_inf_right W inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) s.2

/-- The sections of `D.sheaf` over `W`. -/
def sec (W : Y.Opens) : AddSubgroup (D.Amb W) where
  carrier := {s | D.Cond W s}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  add_mem' {s t} hs ht := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Prod.fst_add, mulVec_add, hs.1, ht.1]
    · simp only [Prod.snd_add, mulVec_add, hs.2.1, ht.2.1]
    · simp only [Prod.fst_add, Prod.snd_add, rv_add, mulVec_add, hs.2.2, ht.2.2]
  neg_mem' {s} hs := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Prod.fst_neg, mulVec_neg, hs.1]
    · simp only [Prod.snd_neg, mulVec_neg, hs.2.1]
    · simp only [Prod.fst_neg, Prod.snd_neg, rv_neg, mulVec_neg, hs.2.2]

lemma cond (W : Y.Opens) (s : D.sec W) : D.Cond W s.1 := s.2

instance (W : Y.Opens) : SMul Γ(Y, W) (D.sec W) where
  smul r s := ⟨(ρ (inf_le_right : U ⊓ W ≤ W) r • s.1.1, ρ (inf_le_right : V ⊓ W ≤ W) r • s.1.2),
    by
      obtain ⟨h1, h2, h3⟩ := D.cond W s
      refine ⟨?_, ?_, ?_⟩
      · simp only [mulVec_smul, h1]
      · simp only [mulVec_smul, h2]
      · simp only [rv_smul, mulVec_smul, h3, ρ_ρ]⟩

lemma smul_coe (W : Y.Opens) (r : Γ(Y, W)) (s : D.sec W) :
    (r • s).1 = (ρ (inf_le_right : U ⊓ W ≤ W) r • s.1.1, ρ (inf_le_right : V ⊓ W ≤ W) r • s.1.2) :=
  rfl

instance (W : Y.Opens) : Module Γ(Y, W) (D.sec W) where
  one_smul s := Subtype.ext <| Prod.ext (by simp [smul_coe]) (by simp [smul_coe])
  mul_smul r r' s := Subtype.ext <| Prod.ext (by simp [smul_coe, mul_smul])
    (by simp [smul_coe, mul_smul])
  smul_zero r := Subtype.ext <| Prod.ext (by simp [smul_coe]) (by simp [smul_coe])
  smul_add r s t := Subtype.ext <| Prod.ext (by simp [smul_coe]) (by simp [smul_coe])
  add_smul r r' s := Subtype.ext <| Prod.ext (by simp [smul_coe, add_smul])
    (by simp [smul_coe, add_smul])
  zero_smul s := Subtype.ext <| Prod.ext (by simp [smul_coe]) (by simp [smul_coe])

/-- Restriction of sections. -/
def restrictSec {W W' : Y.Opens} (h : W' ≤ W) : D.sec W →+ D.sec W' where
  toFun s := ⟨(rv (inf_le_inf_left U h) s.1.1, rv (inf_le_inf_left V h) s.1.2), by
    obtain ⟨h1, h2, h3⟩ := D.cond W s
    refine ⟨?_, ?_, ?_⟩
    · change _ = rv _ s.1.1
      conv_rhs => rw [← h1]
      rw [rv_mulVec]
    · change _ = rv _ s.1.2
      conv_rhs => rw [← h2]
      rw [rv_mulVec]
    · change rv _ (rv _ s.1.1) = _ *ᵥ rv _ (rv _ s.1.2)
      rw [rv_rv, rv_rv,
        ← rv_rv (inf_le_inf_right W inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ W)
          (inf_le_inf_left (U ⊓ V) h), h3, rv_mulVec, rv_rv]⟩
  map_zero' := Subtype.ext <| Prod.ext (rv_zero _) (rv_zero _)
  map_add' s t := Subtype.ext <| Prod.ext (rv_add _ _ _) (rv_add _ _ _)

lemma restrictSec_coe {W W' : Y.Opens} (h : W' ≤ W) (s : D.sec W) :
    (D.restrictSec h s).1 = (rv (inf_le_inf_left U h) s.1.1, rv (inf_le_inf_left V h) s.1.2) :=
  rfl

lemma restrictSec_smul {W W' : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) (s : D.sec W) :
    D.restrictSec h (r • s) = ρ h r • D.restrictSec h s :=
  Subtype.ext <| Prod.ext (by simp [restrictSec_coe, smul_coe, ρ_ρ])
    (by simp [restrictSec_coe, smul_coe, ρ_ρ])

/-- The presheaf of abelian groups of sections. -/
def pre : (Y.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (D.sec W.unop)
  map f := AddCommGrpCat.ofHom (D.restrictSec f.unop.le)
  map_id W := by
    ext s
    · exact ρ_self _ _
    · exact ρ_self _ _
  map_comp f g := by
    ext s
    · exact (ρ_ρ _ _ _).symm
    · exact (ρ_ρ _ _ _).symm

instance (W : Y.Opensᵒᵖ) : Module (Y.ringCatSheaf.obj.obj W) (D.pre.obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (D.sec W.unop))

/-- The presheaf of modules of sections. -/
def preMod : Y.PresheafOfModules :=
  _root_.PresheafOfModules.ofPresheaf D.pre (fun {_ _} f r s ↦ D.restrictSec_smul f.unop.le r s)

theorem isSheaf_pre : TopCat.Presheaf.IsSheaf D.pre := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  have hsf' : ∀ k l, D.restrictSec (inf_le_left : W k ⊓ W l ≤ W k) (sf k) =
      D.restrictSec (inf_le_right : W k ⊓ W l ≤ W l) (sf l) := hsf
  have hA : ∀ i, ∃! x : Γ(Y, U ⊓ iSup W), ∀ k,
      ρ (inf_le_inf_left U (le_iSup W k)) x = (sf k).1.1 i := fun i ↦
    existsUnique_gluing_inter U W (fun k ↦ (sf k).1.1 i)
      (fun k l ↦ congrFun (congrArg (fun s : D.sec (W k ⊓ W l) ↦ s.1.1) (hsf' k l)) i)
  have hB : ∀ j, ∃! x : Γ(Y, V ⊓ iSup W), ∀ k,
      ρ (inf_le_inf_left V (le_iSup W k)) x = (sf k).1.2 j := fun j ↦
    existsUnique_gluing_inter V W (fun k ↦ (sf k).1.2 j)
      (fun k l ↦ congrFun (congrArg (fun s : D.sec (W k ⊓ W l) ↦ s.1.2) (hsf' k l)) j)
  choose a ha hau using hA
  choose b hb hbu using hB
  have ha' : ∀ k, rv (inf_le_inf_left U (le_iSup W k)) a = (sf k).1.1 :=
    fun k ↦ funext fun i ↦ ha i k
  have hb' : ∀ k, rv (inf_le_inf_left V (le_iSup W k)) b = (sf k).1.2 :=
    fun k ↦ funext fun j ↦ hb j k
  have hcond : D.Cond (iSup W) (a, b) := by
    refine ⟨?_, ?_, ?_⟩
    · refine vec_eq_of_locally_eq_inter U W _ _ fun k ↦ ?_
      rw [rv_mulVec, ha']
      exact (D.cond _ (sf k)).1
    · refine vec_eq_of_locally_eq_inter V W _ _ fun k ↦ ?_
      rw [rv_mulVec, hb']
      exact (D.cond _ (sf k)).2.1
    · refine vec_eq_of_locally_eq_inter (U ⊓ V) W _ _ fun k ↦ ?_
      rw [rv_mulVec, rv_rv, rv_rv,
        ← rv_rv (inf_le_inf_left U (le_iSup W k)) (inf_le_inf_right (W k) inf_le_left), ha',
        ← rv_rv (inf_le_inf_left V (le_iSup W k)) (inf_le_inf_right (W k) inf_le_right), hb']
      exact (D.cond _ (sf k)).2.2
  refine ⟨⟨(a, b), hcond⟩, fun k ↦ Subtype.ext <| Prod.ext (ha' k) (hb' k), ?_⟩
  intro s hs
  have hs' : ∀ k, D.restrictSec (le_iSup W k) s = sf k := hs
  refine Subtype.ext <| Prod.ext (funext fun i ↦ hau i _ fun k ↦ ?_)
    (funext fun j ↦ hbu j _ fun k ↦ ?_)
  · exact congrFun (congrArg (fun s : D.sec (W k) ↦ s.1.1) (hs' k)) i
  · exact congrFun (congrArg (fun s : D.sec (W k) ↦ s.1.2) (hs' k)) j

/-- **The sheaf of modules of matrix data.** -/
def sheaf : Y.Modules where
  val := D.preMod
  isSheaf := D.isSheaf_pre

lemma sheaf_sections (W : Y.Opens) : Γ(D.sheaf, W) = AddCommGrpCat.of (D.sec W) := rfl

lemma sheaf_res {W W' : Y.Opens} (h : W' ≤ W) (s : D.sec W) :
    Scheme.PresheafOfModules.res ((Scheme.Modules.toPresheafOfModules Y).obj D.sheaf) h s =
      D.restrictSec h s :=
  rfl

/-! ### Local bases -/

lemma vecMulVec_mulVec' {R : Type*} [CommRing R] {n : ℕ} (u v w : Fin n → R) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma map_vecMulVec {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (u v : Fin n → R) : (vecMulVec u v).map f = vecMulVec (f ∘ u) (f ∘ v) := by
  ext i j
  simp [vecMulVec_apply]

lemma rv_injective_of_eq {n : ℕ} {W W' : Y.Opens} (e : W' = W) :
    Function.Injective (rv (n := n) (Y := Y) e.le) :=
  fun _ _ h ↦ funext fun i ↦ (ρ_bijective_of_eq e).1 (congrFun h i)

lemma rv_dotProduct {n : ℕ} {W W' : Y.Opens} (h : W' ≤ W) (v w : Fin n → Γ(Y, W)) :
    rv h v ⬝ᵥ rv h w = ρ h (v ⬝ᵥ w) :=
  (RingHom.map_dotProduct (ρ h) v w).symm

/-- Rank-one data for `e_U` on an open `O ⊆ U`: `e_U = p λᵀ` with `λ ⬝ p = 1`. -/
structure RankOneU (O : Y.Opens) where
  le : O ≤ U
  /-- the column -/
  p : Fin D.n → Γ(Y, O)
  /-- the row -/
  l : Fin D.n → Γ(Y, O)
  eU_eq : D.eU.map (ρ le) = vecMulVec p l
  dot : l ⬝ᵥ p = 1

/-- Rank-one data for `e_V` on an open `O ⊆ V`. -/
structure RankOneV (O : Y.Opens) where
  le : O ≤ V
  /-- the column -/
  p : Fin D.m → Γ(Y, O)
  /-- the row -/
  l : Fin D.m → Γ(Y, O)
  eV_eq : D.eV.map (ρ le) = vecMulVec p l
  dot : l ⬝ᵥ p = 1

namespace RankOneU

variable {D} {O : Y.Opens} (R : D.RankOneU O)

/-- Restriction of rank-one data. -/
def restrict {W : Y.Opens} (h : W ≤ O) : D.RankOneU W where
  le := h.trans R.le
  p := rv h R.p
  l := rv h R.l
  eU_eq := by rw [← map_ρ_ρ R.le h, R.eU_eq, map_vecMulVec]; rfl
  dot := by rw [rv_dotProduct, R.dot, map_one]

lemma eU_mulVec_p {W : Y.Opens} (h : W ≤ O) (h' : W ≤ U) :
    D.eU.map (ρ h') *ᵥ rv h R.p = rv h R.p := by
  have := (R.restrict h).eU_eq
  change D.eU.map (ρ h') = vecMulVec (rv h R.p) (rv h R.l) at this
  have hd : rv h R.l ⬝ᵥ rv h R.p = 1 := (R.restrict h).dot
  rw [this, vecMulVec_mulVec', hd, one_smul]

lemma eV_mul_Ψ {W : Y.Opens} (hW : W ≤ U ⊓ V) (h' : W ≤ V) :
    D.eV.map (ρ h') * D.Ψ.map (ρ hW) = D.Ψ.map (ρ hW) * D.eU.map (ρ (hW.trans inf_le_left)) := by
  rw [← map_ρ_ρ (inf_le_right : U ⊓ V ≤ V) hW, ← D.Ψ_Φ, ← map_ρ_ρ (inf_le_left : U ⊓ V ≤ U) hW,
    ← D.Φ_Ψ, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc]

/-- The local basis of `D.sheaf` on `O` given by rank-one data: `(p, Ψ p)`. -/
def sec : D.sec O :=
  ⟨(rv (inf_le_right : U ⊓ O ≤ O) R.p,
    D.Ψ.map (ρ (le_inf (inf_le_right.trans R.le) inf_le_left : V ⊓ O ≤ U ⊓ V)) *ᵥ
      rv (inf_le_right : V ⊓ O ≤ O) R.p), by
    refine ⟨R.eU_mulVec_p _ _, ?_, ?_⟩
    · change D.eV.map _ *ᵥ (D.Ψ.map _ *ᵥ _) = D.Ψ.map _ *ᵥ _
      rw [mulVec_mulVec, eV_mul_Ψ, ← mulVec_mulVec, R.eU_mulVec_p]
    · change rv _ (rv _ R.p) = D.Φ.map _ *ᵥ rv _ (D.Ψ.map _ *ᵥ rv _ R.p)
      rw [rv_mulVec, rv_rv, rv_rv, mulVec_mulVec, ← Matrix.map_mul, D.Φ_Ψ, map_ρ_ρ,
        R.eU_mulVec_p]⟩

lemma sec_fst : R.sec.1.1 = rv (inf_le_right : U ⊓ O ≤ O) R.p := rfl

lemma sec_snd : R.sec.1.2 = D.Ψ.map (ρ (le_inf (inf_le_right.trans R.le) inf_le_left :
    V ⊓ O ≤ U ⊓ V)) *ᵥ rv (inf_le_right : V ⊓ O ≤ O) R.p := rfl

lemma restrictSec_sec {W : Y.Opens} (h : W ≤ O) : D.restrictSec h R.sec = (R.restrict h).sec := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change rv _ (rv _ R.p) = rv _ (rv h R.p)
    rw [rv_rv, rv_rv]
  · change rv _ (D.Ψ.map _ *ᵥ rv _ R.p) = D.Ψ.map _ *ᵥ rv _ (rv h R.p)
    rw [rv_mulVec, rv_rv, rv_rv]

lemma bijective_smul : Function.Bijective (fun r : Γ(Y, O) ↦ r • R.sec) := by
  have hUO : U ⊓ O = O := inf_eq_right.2 R.le
  have hb := ρ_bijective_of_eq (Y := Y) hUO
  have hdot := (R.restrict (inf_le_right : U ⊓ O ≤ O)).dot
  change rv _ R.l ⬝ᵥ rv _ R.p = 1 at hdot
  have hfst : ∀ r : Γ(Y, O), (r • R.sec).1.1 = ρ (inf_le_right : U ⊓ O ≤ O) r •
      rv (inf_le_right : U ⊓ O ≤ O) R.p := fun r ↦ rfl
  constructor
  · intro r r' e
    have e1 := congrArg (fun s : D.sec O ↦ rv (inf_le_right : U ⊓ O ≤ O) R.l ⬝ᵥ s.1.1) e
    simp only [hfst, dotProduct_smul, hdot, smul_eq_mul, mul_one] at e1
    exact hb.1 e1
  · intro t
    obtain ⟨h1, h2, h3⟩ := D.cond O t
    obtain ⟨r, hr⟩ := hb.2 (rv (inf_le_right : U ⊓ O ≤ O) R.l ⬝ᵥ t.1.1)
    have hE := (R.restrict (inf_le_right : U ⊓ O ≤ O)).eU_eq
    change D.eU.map _ = vecMulVec (rv _ R.p) (rv _ R.l) at hE
    have e1 : (r • R.sec).1.1 = t.1.1 := by
      rw [hfst, hr]
      conv_rhs => rw [← h1, hE]
      rw [vecMulVec_mulVec']
    refine ⟨r, Subtype.ext (Prod.ext e1 ?_)⟩
    have hVO : U ⊓ V ⊓ O = V ⊓ O := by
      rw [inf_comm U V, inf_assoc, inf_eq_right.2 R.le]
    refine rv_injective_of_eq hVO ?_
    change rv _ (ρ (inf_le_right : V ⊓ O ≤ O) r • (D.Ψ.map _ *ᵥ rv _ R.p)) = rv _ t.1.2
    conv_rhs => rw [← h2, rv_mulVec, ← map_ρ_ρ (inf_le_right : U ⊓ V ≤ V)
      (inf_le_left : U ⊓ V ⊓ O ≤ U ⊓ V), ← D.Ψ_Φ, Matrix.map_mul, ← mulVec_mulVec, ← h3, ← e1]
    rw [rv_smul, rv_mulVec, rv_rv, ρ_ρ]
    change _ = D.Ψ.map _ *ᵥ rv _ (ρ _ r • rv _ R.p)
    rw [rv_smul, rv_rv, ρ_ρ, mulVec_smul]

theorem isBasisOn : D.sheaf.IsBasisOn O R.sec := by
  intro W h
  change Function.Bijective (fun r : Γ(Y, W) ↦ r • D.restrictSec h R.sec)
  rw [R.restrictSec_sec h]
  exact (R.restrict h).bijective_smul

end RankOneU

namespace RankOneV

variable {D} {O : Y.Opens} (R : D.RankOneV O)

/-- Restriction of rank-one data. -/
def restrict {W : Y.Opens} (h : W ≤ O) : D.RankOneV W where
  le := h.trans R.le
  p := rv h R.p
  l := rv h R.l
  eV_eq := by rw [← map_ρ_ρ R.le h, R.eV_eq, map_vecMulVec]; rfl
  dot := by rw [rv_dotProduct, R.dot, map_one]

lemma eV_mulVec_p {W : Y.Opens} (h : W ≤ O) (h' : W ≤ V) :
    D.eV.map (ρ h') *ᵥ rv h R.p = rv h R.p := by
  have := (R.restrict h).eV_eq
  change D.eV.map (ρ h') = vecMulVec (rv h R.p) (rv h R.l) at this
  have hd : rv h R.l ⬝ᵥ rv h R.p = 1 := (R.restrict h).dot
  rw [this, vecMulVec_mulVec', hd, one_smul]

/-- The local basis of `D.sheaf` on `O` given by rank-one data: `(Φ p, p)`. -/
def sec : D.sec O :=
  ⟨(D.Φ.map (ρ (le_inf inf_le_left (inf_le_right.trans R.le) : U ⊓ O ≤ U ⊓ V)) *ᵥ
      rv (inf_le_right : U ⊓ O ≤ O) R.p, rv (inf_le_right : V ⊓ O ≤ O) R.p), by
    refine ⟨?_, R.eV_mulVec_p _ _, ?_⟩
    · change D.eU.map _ *ᵥ (D.Φ.map _ *ᵥ _) = D.Φ.map _ *ᵥ _
      rw [mulVec_mulVec, ← map_ρ_ρ (inf_le_left : U ⊓ V ≤ U)
        (le_inf inf_le_left (inf_le_right.trans R.le) : U ⊓ O ≤ U ⊓ V), ← Matrix.map_mul,
        D.eU_Φ]
    · change rv _ (D.Φ.map _ *ᵥ rv _ R.p) = D.Φ.map _ *ᵥ rv _ (rv _ R.p)
      rw [rv_mulVec, rv_rv, rv_rv]⟩

lemma restrictSec_sec {W : Y.Opens} (h : W ≤ O) : D.restrictSec h R.sec = (R.restrict h).sec := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change rv _ (D.Φ.map _ *ᵥ rv _ R.p) = D.Φ.map _ *ᵥ rv _ (rv h R.p)
    rw [rv_mulVec, rv_rv, rv_rv]
  · change rv _ (rv _ R.p) = rv _ (rv h R.p)
    rw [rv_rv, rv_rv]

lemma bijective_smul : Function.Bijective (fun r : Γ(Y, O) ↦ r • R.sec) := by
  have hVO : V ⊓ O = O := inf_eq_right.2 R.le
  have hb := ρ_bijective_of_eq (Y := Y) hVO
  have hdot := (R.restrict (inf_le_right : V ⊓ O ≤ O)).dot
  change rv _ R.l ⬝ᵥ rv _ R.p = 1 at hdot
  have hsnd : ∀ r : Γ(Y, O), (r • R.sec).1.2 = ρ (inf_le_right : V ⊓ O ≤ O) r •
      rv (inf_le_right : V ⊓ O ≤ O) R.p := fun r ↦ rfl
  constructor
  · intro r r' e
    have e1 := congrArg (fun s : D.sec O ↦ rv (inf_le_right : V ⊓ O ≤ O) R.l ⬝ᵥ s.1.2) e
    simp only [hsnd, dotProduct_smul, hdot, smul_eq_mul, mul_one] at e1
    exact hb.1 e1
  · intro t
    obtain ⟨h1, h2, h3⟩ := D.cond O t
    obtain ⟨r, hr⟩ := hb.2 (rv (inf_le_right : V ⊓ O ≤ O) R.l ⬝ᵥ t.1.2)
    have hE := (R.restrict (inf_le_right : V ⊓ O ≤ O)).eV_eq
    change D.eV.map _ = vecMulVec (rv _ R.p) (rv _ R.l) at hE
    have e2 : (r • R.sec).1.2 = t.1.2 := by
      rw [hsnd, hr]
      conv_rhs => rw [← h2, hE]
      rw [vecMulVec_mulVec']
    refine ⟨r, Subtype.ext (Prod.ext ?_ e2)⟩
    have hUO : U ⊓ V ⊓ O = U ⊓ O := by
      rw [inf_assoc, inf_eq_right.2 R.le]
    refine rv_injective_of_eq hUO ?_
    change rv _ (ρ (inf_le_right : U ⊓ O ≤ O) r • (D.Φ.map _ *ᵥ rv _ R.p)) = rv _ t.1.1
    rw [h3, ← e2, rv_smul, rv_mulVec, rv_rv, ρ_ρ]
    change _ = D.Φ.map _ *ᵥ rv _ (ρ _ r • rv _ R.p)
    rw [rv_smul, rv_rv, ρ_ρ, mulVec_smul]

theorem isBasisOn : D.sheaf.IsBasisOn O R.sec := by
  intro W h
  change Function.Bijective (fun r : Γ(Y, W) ↦ r • D.restrictSec h R.sec)
  rw [R.restrictSec_sec h]
  exact (R.restrict h).bijective_smul

end RankOneV

/-- **The sheaf of matrix data is invertible** if near every point `e_U` or `e_V` has rank
one. -/
theorem isInvertible
    (H : ∀ y : Y, (∃ O : Y.Opens, y ∈ O ∧ Nonempty (D.RankOneU O)) ∨
      (∃ O : Y.Opens, y ∈ O ∧ Nonempty (D.RankOneV O))) :
    D.sheaf.IsInvertible where
  exists_basis y := by
    rcases H y with ⟨O, hy, ⟨R⟩⟩ | ⟨O, hy, ⟨R⟩⟩
    · exact ⟨O, R.sec, hy, R.isBasisOn⟩
    · exact ⟨O, R.sec, hy, R.isBasisOn⟩

/-! ### Pullbacks: a criterion -/

section Criterion

lemma rs_add {T : Scheme.{u}} (N : T.Modules) {A B : T.Opens} (h : B ≤ A) (a b : Γ(N, A)) :
    rs N h (a + b) = rs N h a + rs N h b := by
  simp only [rs, map_add]

lemma rs_zero {T : Scheme.{u}} (N : T.Modules) {A B : T.Opens} (h : B ≤ A) :
    rs N h (0 : Γ(N, A)) = 0 := by
  simp only [rs, map_zero]

variable {T : Scheme.{u}}

open Scheme.Modules in
/-- A morphism `M ⟶ s_* N` mapping, near every point of `T`, a basis of `M` to a basis of `N`
identifies `s^* M` with `N`. -/
theorem nonempty_iso_pullback (s : T ⟶ Y) {M : Y.Modules} {N : T.Modules}
    (φ : M ⟶ (pushforward s).obj N)
    (H : ∀ t : T, ∃ (O : Y.Opens) (e : Γ(M, O)), s.base t ∈ O ∧ M.IsBasisOn O e ∧
      N.IsBasisOn (s ⁻¹ᵁ O) (φ.app O e)) :
    Nonempty ((pullback s).obj M ≅ N) := by
  let adj := pullbackPushforwardAdjunction s
  let ψ := (adj.homEquiv _ _).symm φ
  have key : ∀ (W : Y.Opens) (m : Γ(M, W)), ψ.app (s ⁻¹ᵁ W) (pullbackSection s m) = φ.app W m := by
    intro W m
    have h : φ = adj.unit.app M ≫ (pushforward s).map ψ :=
      ((adj.homEquiv _ _).apply_symm_apply _).symm.trans (adj.homEquiv_unit (f := ψ))
    exact (congrArg (fun g ↦ g.app W m) h).symm
  have : IsIso ψ := by
    refine isIso_of_isBasisOn ψ fun t ↦ ?_
    obtain ⟨O, e, htO, he, he'⟩ := H t
    refine ⟨s ⁻¹ᵁ O, pullbackSection s e, htO, isBasisOn_pullbackSection s O he, ?_⟩
    rw [key]
    exact he'
  exact ⟨asIso ψ⟩

/-- Gluing two sections of a sheaf of modules. -/
lemma existsUnique_glue₂ (N : T.Modules) {A B W : T.Opens} (hA : A ≤ W) (hB : B ≤ W)
    (hW : W ≤ A ⊔ B) (x : Γ(N, A)) (y : Γ(N, B))
    (h : rs N (inf_le_left : A ⊓ B ≤ A) x = rs N (inf_le_right : A ⊓ B ≤ B) y) :
    ∃! z : Γ(N, W), rs N hA z = x ∧ rs N hB z = y := by
  let Uf : Bool → T.Opens := fun b ↦ _root_.cond b A B
  let sf : ∀ b, Γ(N, Uf b) := fun b ↦ match b with
    | true => x
    | false => y
  have hle : ∀ b, Uf b ≤ W := fun b ↦ by cases b; exacts [hB, hA]
  let NS : TopCat.Sheaf Ab.{u} T := ⟨N.presheaf, N.isSheaf⟩
  obtain ⟨z, hz, hu⟩ := NS.existsUnique_gluing' Uf W (fun b ↦ homOfLE (hle b))
    (by rw [iSup_bool_eq]; exact hW) sf (by
      intro i j
      cases i <;> cases j
      · rfl
      · change rs N (inf_le_left : B ⊓ A ≤ B) y = rs N (inf_le_right : B ⊓ A ≤ A) x
        have h' := congrArg (rs N (le_inf inf_le_right inf_le_left : B ⊓ A ≤ A ⊓ B)) h
        rw [rs_rs, rs_rs] at h'
        exact h'.symm
      · exact h
      · rfl)
  refine ⟨z, ⟨hz true, hz false⟩, fun z' hz' ↦ hu z' fun b ↦ ?_⟩
  cases b
  · exact hz'.2
  · exact hz'.1

end Criterion

/-! ### Evaluation of matrix data in a sheaf on `T` -/

section Eval

variable {T : Scheme.{u}} (s : T ⟶ Y) (N : T.Modules)

/-- The linear combination `Σ s^♯(a_i) e_i|_{s⁻¹ O}`. -/
def lc {k : ℕ} {P : Y.Opens} (e : Fin k → Γ(N, s ⁻¹ᵁ P)) {O : Y.Opens} (hO : O ≤ P)
    (a : Fin k → Γ(Y, O)) : Γ(N, s ⁻¹ᵁ O) :=
  ∑ i, s.app O (a i) • rs N (s.preimage_mono hO) (e i)

variable {s N}

lemma rs_lc {k : ℕ} {P : Y.Opens} (e : Fin k → Γ(N, s ⁻¹ᵁ P)) {O O' : Y.Opens} (hO : O ≤ P)
    (h : O' ≤ O) (a : Fin k → Γ(Y, O)) :
    rs N (s.preimage_mono h) (lc s N e hO a) = lc s N e (h.trans hO) (rv h a) := by
  simp only [lc, map_sum, rs_smul, rs_rs]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact (app_rr s h (a i)).symm

lemma lc_add {k : ℕ} {P : Y.Opens} (e : Fin k → Γ(N, s ⁻¹ᵁ P)) {O : Y.Opens} (hO : O ≤ P)
    (a b : Fin k → Γ(Y, O)) : lc s N e hO (a + b) = lc s N e hO a + lc s N e hO b := by
  simp only [lc, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

lemma lc_smul {k : ℕ} {P : Y.Opens} (e : Fin k → Γ(N, s ⁻¹ᵁ P)) {O : Y.Opens} (hO : O ≤ P)
    (c : Γ(Y, O)) (a : Fin k → Γ(Y, O)) : lc s N e hO (c • a) = s.app O c • lc s N e hO a := by
  simp only [lc, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

lemma lc_mulVec {k l : ℕ} {P P' Q : Y.Opens} (e : Fin k → Γ(N, s ⁻¹ᵁ P))
    (f : Fin l → Γ(N, s ⁻¹ᵁ P')) (hQP : Q ≤ P) (hQP' : Q ≤ P')
    (Φ : Matrix (Fin k) (Fin l) Γ(Y, Q))
    (hf : ∀ j, rs N (s.preimage_mono hQP') (f j) = lc s N e hQP (fun i ↦ Φ i j))
    {O : Y.Opens} (hO : O ≤ Q) (b : Fin l → Γ(Y, O)) :
    lc s N e (hO.trans hQP) (Φ.map (ρ hO) *ᵥ b) = lc s N f (hO.trans hQP') b := by
  have key : ∀ j, lc s N e (hO.trans hQP) (fun i ↦ ρ hO (Φ i j)) =
      rs N (s.preimage_mono (hO.trans hQP')) (f j) := by
    intro j
    rw [← rs_rs N (s.preimage_mono hQP') (s.preimage_mono hO), hf, rs_lc]
  simp only [lc, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_smul,
    mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← key j, lc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_comm]

variable (ε : Fin D.n → Γ(N, s ⁻¹ᵁ U)) (δ : Fin D.m → Γ(N, s ⁻¹ᵁ V))

/-- The compatibility of the sections `ε` on `U` and `δ` on `V` with the gluing matrix `Φ`. -/
def Compat : Prop :=
  ∀ j, rs N (s.preimage_mono (inf_le_right : U ⊓ V ≤ V)) (δ j) =
    lc s N ε (inf_le_left : U ⊓ V ≤ U) (fun i ↦ D.Φ i j)

variable {ε δ}

lemma exists_eval (hUV : U ⊔ V = ⊤) (hc : D.Compat ε δ) (W : Y.Opens) (x : D.sec W) :
    ∃! z : Γ(N, s ⁻¹ᵁ W),
      rs N (s.preimage_mono (inf_le_right : U ⊓ W ≤ W)) z =
        lc s N ε (inf_le_left : U ⊓ W ≤ U) x.1.1 ∧
      rs N (s.preimage_mono (inf_le_right : V ⊓ W ≤ W)) z =
        lc s N δ (inf_le_left : V ⊓ W ≤ V) x.1.2 := by
  obtain ⟨-, -, h3⟩ := D.cond W x
  refine existsUnique_glue₂ N _ _ ?_ _ _ ?_
  · intro t ht
    have hW : s.base t ∈ W := ht
    have : s.base t ∈ U ⊔ V := by rw [hUV]; trivial
    rcases (Opens.mem_sup.mp this) with hU | hV
    · exact Opens.mem_sup.mpr (Or.inl ⟨hU, hW⟩)
    · exact Opens.mem_sup.mpr (Or.inr ⟨hV, hW⟩)
  · have hC : s ⁻¹ᵁ (U ⊓ W) ⊓ s ⁻¹ᵁ (V ⊓ W) ≤ s ⁻¹ᵁ (U ⊓ V ⊓ W) :=
      fun t ht ↦ ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
    have k1 : U ⊓ V ⊓ W ≤ U ⊓ W := inf_le_inf_right W inf_le_left
    have k2 : U ⊓ V ⊓ W ≤ V ⊓ W := inf_le_inf_right W inf_le_right
    rw [← rs_rs N (s.preimage_mono k1) hC, ← rs_rs N (s.preimage_mono k2) hC,
      rs_lc ε inf_le_left k1, rs_lc δ inf_le_left k2, h3]
    exact congrArg (rs N hC) (lc_mulVec ε δ inf_le_left inf_le_right D.Φ hc inf_le_left _)

variable (hUV : U ⊔ V = ⊤) (hc : D.Compat ε δ)

/-- The evaluation of a section of `D.sheaf` in `N`: the section of `N` which is
`Σ s^♯(a_i) ε_i` on `s⁻¹ U` and `Σ s^♯(b_j) δ_j` on `s⁻¹ V`. -/
def eval (W : Y.Opens) (x : D.sec W) : Γ(N, s ⁻¹ᵁ W) :=
  (D.exists_eval hUV hc W x).exists.choose

lemma eval_spec (W : Y.Opens) (x : D.sec W) :
    rs N (s.preimage_mono (inf_le_right : U ⊓ W ≤ W)) (D.eval hUV hc W x) =
        lc s N ε (inf_le_left : U ⊓ W ≤ U) x.1.1 ∧
      rs N (s.preimage_mono (inf_le_right : V ⊓ W ≤ W)) (D.eval hUV hc W x) =
        lc s N δ (inf_le_left : V ⊓ W ≤ V) x.1.2 :=
  (D.exists_eval hUV hc W x).exists.choose_spec

lemma eval_eq (W : Y.Opens) (x : D.sec W) (z : Γ(N, s ⁻¹ᵁ W))
    (h1 : rs N (s.preimage_mono (inf_le_right : U ⊓ W ≤ W)) z =
      lc s N ε (inf_le_left : U ⊓ W ≤ U) x.1.1)
    (h2 : rs N (s.preimage_mono (inf_le_right : V ⊓ W ≤ W)) z =
      lc s N δ (inf_le_left : V ⊓ W ≤ V) x.1.2) : D.eval hUV hc W x = z :=
  (D.exists_eval hUV hc W x).unique (D.eval_spec hUV hc W x) ⟨h1, h2⟩

lemma eval_add (W : Y.Opens) (x y : D.sec W) :
    D.eval hUV hc W (x + y) = D.eval hUV hc W x + D.eval hUV hc W y := by
  refine D.eval_eq hUV hc W _ _ ?_ ?_
  · rw [rs_add, (D.eval_spec hUV hc W x).1, (D.eval_spec hUV hc W y).1]
    exact (lc_add ε _ _ _).symm
  · rw [rs_add, (D.eval_spec hUV hc W x).2, (D.eval_spec hUV hc W y).2]
    exact (lc_add δ _ _ _).symm

lemma eval_smul (W : Y.Opens) (r : Γ(Y, W)) (x : D.sec W) :
    D.eval hUV hc W (r • x) = s.app W r • D.eval hUV hc W x := by
  refine D.eval_eq hUV hc W _ _ ?_ ?_
  · rw [rs_smul, (D.eval_spec hUV hc W x).1]
    change _ = lc s N ε _ (ρ _ r • x.1.1)
    rw [lc_smul]
    congr 1
    exact (app_rr s _ r).symm
  · rw [rs_smul, (D.eval_spec hUV hc W x).2]
    change _ = lc s N δ _ (ρ _ r • x.1.2)
    rw [lc_smul]
    congr 1
    exact (app_rr s _ r).symm

lemma eval_rs {W W' : Y.Opens} (h : W' ≤ W) (x : D.sec W) :
    D.eval hUV hc W' (D.restrictSec h x) = rs N (s.preimage_mono h) (D.eval hUV hc W x) := by
  refine D.eval_eq hUV hc W' _ _ ?_ ?_
  · rw [rs_rs, ← rs_rs N (s.preimage_mono (inf_le_right : U ⊓ W ≤ W))
      (s.preimage_mono (inf_le_inf_left U h)), (D.eval_spec hUV hc W x).1, rs_lc]
    rfl
  · rw [rs_rs, ← rs_rs N (s.preimage_mono (inf_le_right : V ⊓ W ≤ W))
      (s.preimage_mono (inf_le_inf_left V h)), (D.eval_spec hUV hc W x).2, rs_lc]
    rfl

/-- The evaluation, as an additive map. -/
def evalHom (W : Y.Opens) : D.sec W →+ Γ(N, s ⁻¹ᵁ W) where
  toFun := D.eval hUV hc W
  map_zero' := by
    refine D.eval_eq hUV hc W _ _ ?_ ?_
    · rw [rs_zero]
      simp [lc]
    · rw [rs_zero]
      simp [lc]
  map_add' := D.eval_add hUV hc W

/-- The evaluation, as a morphism `D.sheaf ⟶ s_* N`. -/
def toPushforward : D.sheaf ⟶ (Scheme.Modules.pushforward s).obj N :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (_root_.PresheafOfModules.homMk
      { app W := AddCommGrpCat.ofHom (D.evalHom hUV hc W.unop)
        naturality W W' f := by
          ext x
          exact D.eval_rs hUV hc f.unop.le x }
      (fun W r x ↦ D.eval_smul hUV hc W.unop r x))

lemma toPushforward_app (W : Y.Opens) (x : D.sec W) :
    (D.toPushforward hUV hc).app W x = D.eval hUV hc W x :=
  rfl

lemma eval_sec_U {O : Y.Opens} (R : D.RankOneU O) :
    D.eval hUV hc O R.sec = lc s N ε R.le R.p := by
  have hUO : U ⊓ O = O := inf_eq_right.2 R.le
  refine (rs_bijective_of_eq N (show s ⁻¹ᵁ (U ⊓ O) = s ⁻¹ᵁ O by rw [hUO])).1 ?_
  rw [(D.eval_spec hUV hc O R.sec).1, rs_lc]
  rfl

lemma eval_sec_V {O : Y.Opens} (R : D.RankOneV O) :
    D.eval hUV hc O R.sec = lc s N δ R.le R.p := by
  have hVO : V ⊓ O = O := inf_eq_right.2 R.le
  refine (rs_bijective_of_eq N (show s ⁻¹ᵁ (V ⊓ O) = s ⁻¹ᵁ O by rw [hVO])).1 ?_
  rw [(D.eval_spec hUV hc O R.sec).2, rs_lc]
  rfl

include hUV hc in
/-- **Pullback of the sheaf of matrix data.** If near the image of every point of `T` there is
rank-one data whose column evaluates to a basis of `N`, then `s^* D.sheaf ≅ N`. -/
theorem nonempty_iso_pullback_sheaf
    (H : ∀ t : T, (∃ (O : Y.Opens) (R : D.RankOneU O), s.base t ∈ O ∧
        N.IsBasisOn (s ⁻¹ᵁ O) (lc s N ε R.le R.p)) ∨
      (∃ (O : Y.Opens) (R : D.RankOneV O), s.base t ∈ O ∧
        N.IsBasisOn (s ⁻¹ᵁ O) (lc s N δ R.le R.p))) :
    Nonempty ((Scheme.Modules.pullback s).obj D.sheaf ≅ N) := by
  refine nonempty_iso_pullback s (D.toPushforward hUV hc) fun t ↦ ?_
  rcases H t with ⟨O, R, ht, hb⟩ | ⟨O, R, ht, hb⟩
  · refine ⟨O, R.sec, ht, R.isBasisOn, ?_⟩
    rw [toPushforward_app, eval_sec_U]
    exact hb
  · refine ⟨O, R.sec, ht, R.isBasisOn, ?_⟩
    rw [toPushforward_app, eval_sec_V]
    exact hb

/-- Under the hypothesis of `nonempty_iso_pullback_sheaf`, if `s` is surjective, the sheaf of
matrix data is invertible. -/
theorem isInvertible_of_surjective (hs : Function.Surjective s.base)
    (H : ∀ t : T, (∃ (O : Y.Opens) (R : D.RankOneU O), s.base t ∈ O ∧
        N.IsBasisOn (s ⁻¹ᵁ O) (lc s N ε R.le R.p)) ∨
      (∃ (O : Y.Opens) (R : D.RankOneV O), s.base t ∈ O ∧
        N.IsBasisOn (s ⁻¹ᵁ O) (lc s N δ R.le R.p))) :
    D.sheaf.IsInvertible := by
  refine D.isInvertible fun y ↦ ?_
  obtain ⟨t, rfl⟩ := hs y
  rcases H t with ⟨O, R, ht, -⟩ | ⟨O, R, ht, -⟩
  · exact Or.inl ⟨O, ht, ⟨R⟩⟩
  · exact Or.inr ⟨O, ht, ⟨R⟩⟩

end Eval

end Data

end CurvesJacobian.MatSheaf
