/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.FundamentalGroup.Functoriality
import Pi1.FundamentalGroup.Point
import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMapInjective

/-!
# `π₁ᵉᵗ` of a connected finite étale cover is an open subgroup (operations of type `⋏`)

[AbsTopI] Definition 4.2 (iii)(a) (`Topics in Absolute Anabelian Geometry I.txt` l.3005–3006):
an elementary operation of type `⋏` is an open immersion `Π_{j+1} ↪ Π_j`; geometrically
([AbsTopI] Remark 4.2.1, l.3083–3092) it comes from a connected finite étale covering
`X_{j+1} → X_j`. This file
proves the geometric input (SGA 1 V.6.11, Stacks 0BN6): for a finite étale morphism `f : V ⟶ U`
(`V` connected) and a geometric point `η` of `V`,

* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_injective_of_isFiniteEtale`:
  `π₁ᵉᵗ(V, η) → π₁ᵉᵗ(U, η ≫ f)` is injective;
* `AlgebraicGeometry.FiniteEtale.range_fundamentalGroupMap_of_isFiniteEtale`: its image is the
  stabiliser of the point `η` in the fibre of `V` over `η ≫ f`, an open subgroup
  (`isOpen_range_fundamentalGroupMap_of_isFiniteEtale`);
* `AlgebraicGeometry.FiniteEtale.coverEquiv`: `π₁ᵉᵗ(V, η) ≃ₜ*` this open subgroup.

The surjectivity onto the stabiliser restricts an automorphism `τ` of the fibre functor of `U`
fixing `η` to the fibres of the `V`-schemes `A`, viewed as `U`-schemes via `f`
(`CategoryTheory.PreGaloisCategory.exists_aut_restrict`).
-/

open CategoryTheory Limits PreGaloisCategory

universe u

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F : C ⥤ FintypeCat.{u}}
  {G : D ⥤ FintypeCat.{u}}

/-- **Restriction of automorphisms of fibre functors along a natural injection.** Let
`j : G ⟶ S ⋙ F` be componentwise injective and `τ ∈ Aut F` such that `τ` and `τ⁻¹` preserve the
images of all `j_A`. Then there is `σ ∈ Aut G` with `j ∘ σ = τ ∘ j`. -/
theorem exists_aut_restrict (S : D ⥤ C) (j : G ⟶ S ⋙ F) (hj : ∀ A, Function.Injective (j.app A))
    (τ : Aut F) (hτ : ∀ A x, ∃ y, j.app A y = τ.hom.app (S.obj A) (j.app A x))
    (hτ' : ∀ A x, ∃ y, j.app A y = τ.inv.app (S.obj A) (j.app A x)) :
    ∃ σ : Aut G, ∀ A x, j.app A (σ.hom.app A x) = τ.hom.app (S.obj A) (j.app A x) := by
  choose s hs using hτ
  choose s' hs' using hτ'
  have hinv : ∀ A x, τ.inv.app (S.obj A) (τ.hom.app (S.obj A) x) = x := fun A x ↦
    ConcreteCategory.congr_hom (τ.hom_inv_id_app (S.obj A)) x
  have hinv' : ∀ A x, τ.hom.app (S.obj A) (τ.inv.app (S.obj A) x) = x := fun A x ↦
    ConcreteCategory.congr_hom (τ.inv_hom_id_app (S.obj A)) x
  let e : ∀ A, G.obj A ≃ G.obj A := fun A ↦
    { toFun := s A
      invFun := s' A
      left_inv := fun x ↦ hj A (by rw [hs', hs, hinv])
      right_inv := fun x ↦ hj A (by rw [hs, hs', hinv']) }
  refine ⟨NatIso.ofComponents (fun A ↦ FintypeCat.equivEquivIso (e A)) ?_, fun A x ↦ hs A x⟩
  intro A B g
  ext x
  apply hj B
  change j.app B (s B (G.map g x)) = j.app B (G.map g (s A x))
  rw [hs]
  have h1 := ConcreteCategory.congr_hom (j.naturality g) x
  have h2 := ConcreteCategory.congr_hom (j.naturality g) (s A x)
  simp only [Functor.comp_map, ConcreteCategory.comp_apply] at h1 h2
  rw [h1, h2, hs]
  exact NatTrans.naturality_apply τ.hom (S.map g) (j.app A x)

end CategoryTheory.PreGaloisCategory

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {U V : Scheme.{u}} (f : V ⟶ U) [IsFiniteEtale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ V)

/-- A finite étale `V`-scheme viewed as a finite étale `U`-scheme via `f : V ⟶ U`. -/
@[simps! obj_left obj_hom map_left]
def restrictScalars : FiniteEtale V ⥤ FiniteEtale U where
  obj A :=
    haveI : IsFiniteEtale (A.hom ≫ f) := MorphismProperty.comp_mem _ _ _ A.prop ‹_›
    mk (A.hom ≫ f)
  map {A B} g := MorphismProperty.Over.homMk g.left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (Over.w g.hom))) trivial

omit [IsSepClosed Ω] in
lemma w_left {S : Scheme.{u}} {ζ : Spec (.of Ω) ⟶ S} {A : FiniteEtale S}
    (p : Over.mk ζ ⟶ A.toComma) : p.left ≫ A.hom = ζ :=
  Over.w p

omit [IsSepClosed Ω] [IsFiniteEtale f] in
lemma w_left_comp {A : FiniteEtale V} (p : Over.mk η ⟶ A.toComma) :
    p.left ≫ A.hom ≫ f = η ≫ f :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (w_left p))

/-- `f` as an object of `FiniteEtale U`. -/
abbrev coverObj : FiniteEtale U := mk f

/-- The point `η` of the fibre of `V` over `η' = η ≫ f`. -/
def coverPt {η' : Spec (.of Ω) ⟶ U} (h : η ≫ f = η') : (fiber η').obj (coverObj f) :=
  (fiberObjEquivHom η' (coverObj f)).symm (Over.homMk η h)

/-- The underlying map of `fiberRestrict`. -/
def fiberRestrictFun (A : FiniteEtale V) (x : (fiber η).obj A) :
    (fiber (η ≫ f)).obj ((restrictScalars f).obj A) :=
  (fiberObjEquivHom (η ≫ f) ((restrictScalars f).obj A)).symm
    (Over.homMk (fiberObjEquivHom η A x).left (w_left_comp f η _))

lemma fiberRestrictFun_symm (A : FiniteEtale V) (p : Over.mk η ⟶ A.toComma) :
    fiberRestrictFun f η A ((fiberObjEquivHom η A).symm p) =
      (fiberObjEquivHom (η ≫ f) ((restrictScalars f).obj A)).symm
        (Over.homMk p.left (w_left_comp f η p)) := by
  unfold fiberRestrictFun
  congr 2
  rw [Equiv.apply_symm_apply]

/-- The natural injection of the fibre of a finite étale `V`-scheme `A` over `η` into the fibre of
`A` (as a `U`-scheme) over `η ≫ f`. -/
def fiberRestrict : fiber η ⟶ restrictScalars f ⋙ fiber (η ≫ f) where
  app A := FintypeCat.homMk (fiberRestrictFun f η A)
  naturality A B g := by
    ext x
    obtain ⟨p, rfl⟩ := (fiberObjEquivHom η A).symm.surjective x
    change fiberRestrictFun f η B ((fiber η).map g _) =
      (fiber (η ≫ f)).map ((restrictScalars f).map g) (fiberRestrictFun f η A _)
    rw [fiberObjEquivHom_symm_naturality, fiberRestrictFun_symm, fiberRestrictFun_symm,
      fiberObjEquivHom_symm_naturality]
    rfl

lemma fiberRestrict_app_apply (A : FiniteEtale V) (p : Over.mk η ⟶ A.toComma) :
    (fiberRestrict f η).app A ((fiberObjEquivHom η A).symm p) =
      (fiberObjEquivHom (η ≫ f) ((restrictScalars f).obj A)).symm
        (Over.homMk p.left (w_left_comp f η p)) :=
  fiberRestrictFun_symm f η A p

lemma fiberRestrict_injective (A : FiniteEtale V) :
    Function.Injective ((fiberRestrict f η).app A) := by
  intro x y h
  obtain ⟨p, rfl⟩ := (fiberObjEquivHom η A).symm.surjective x
  obtain ⟨q, rfl⟩ := (fiberObjEquivHom η A).symm.surjective y
  rw [fiberRestrict_app_apply, fiberRestrict_app_apply] at h
  have := congr_arg CommaMorphism.left ((fiberObjEquivHom (η ≫ f) _).symm.injective h)
  simp only [Over.homMk_left] at this
  congr 1
  ext
  exact this

/-- The graph `A ⟶ f^*(A)` of the structure morphism of a finite étale `V`-scheme `A` (with `A`
viewed as a `U`-scheme): a section of the projection, hence a monomorphism. -/
def graphHom (A : FiniteEtale V) : A ⟶ (pullback f).obj ((restrictScalars f).obj A) :=
  MorphismProperty.Over.homMk (Limits.pullback.lift (𝟙 A.left) A.hom (Category.id_comp _))
    (Limits.pullback.lift_snd _ _ _) trivial

instance (A : FiniteEtale V) : Mono (graphHom f A) := by
  haveI : IsSplitMono (Limits.pullback.lift (𝟙 A.left) A.hom (Category.id_comp _) :
      A.left ⟶ Limits.pullback (A.hom ≫ f) f) :=
    ⟨⟨⟨Limits.pullback.fst _ _, Limits.pullback.lift_fst _ _ _⟩⟩⟩
  exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mono_of_mono_map
    (show Mono (Limits.pullback.lift (𝟙 A.left) A.hom (Category.id_comp _) :
      A.left ⟶ Limits.pullback (A.hom ≫ f) f) from inferInstance)

/-- **`π₁ᵉᵗ(V) → π₁ᵉᵗ(U)` is injective** for a finite étale `f : V ⟶ U` with `V` connected
(SGA 1 V.6.11): every finite étale `V`-scheme embeds into the base change of a finite étale
`U`-scheme (`graphHom`). -/
theorem fundamentalGroupMap_injective_of_isFiniteEtale [ConnectedSpace V] :
    Function.Injective (fundamentalGroupMap f (rfl : η ≫ f = η ≫ f)) := fun _ _ h ↦
  fiberAutMap_injective (fiber η) (pullbackFiberIso f rfl)
    (fun A _ ↦ ⟨(restrictScalars f).obj A, graphHom f A, inferInstance⟩) h

/-- The projection `f^* B ⟶ B`, as a morphism of finite étale `U`-schemes. -/
def projHom (B : FiniteEtale U) : (restrictScalars f).obj ((pullback f).obj B) ⟶ B :=
  MorphismProperty.Over.homMk (Limits.pullback.fst B.hom f) Limits.pullback.condition trivial

omit [IsSepClosed Ω] [IsFiniteEtale f] in
lemma w_left_fst {B : FiniteEtale U} (p : Over.mk η ⟶ ((pullback f).obj B).toComma) :
    p.left ≫ Limits.pullback.fst B.hom f ≫ B.hom = η ≫ f := by
  have h : p.left ≫ Limits.pullback.snd B.hom f = η := w_left p
  exact (congrArg (p.left ≫ ·) Limits.pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h))

omit [IsFiniteEtale f] in
lemma pullbackFiberIso_hom_app_symm (B : FiniteEtale U)
    (p : Over.mk η ⟶ ((pullback f).obj B).toComma) :
    (pullbackFiberIso f rfl).hom.app B ((fiberObjEquivHom η _).symm p) =
      (fiberObjEquivHom (η ≫ f) B).symm (Over.homMk (p.left ≫ Limits.pullback.fst B.hom f)
        ((Category.assoc _ _ _).trans (w_left_fst f η p))) := by
  rw [fiberObjEquivHom_symm_apply, fiberObjEquivHom_symm_apply, pullbackFiberIso_hom_app]
  change ((MorphismProperty.Over.pullbackComp η f (η ≫ f) rfl).inv.app B).left _ = _
  have h : p.left ≫ Limits.pullback.snd B.hom f = η := w_left p
  have hfst : ((MorphismProperty.Over.pullbackComp η f (η ≫ f) rfl).inv.app B).left ≫
      Limits.pullback.fst B.hom (η ≫ f) =
        Limits.pullback.fst _ _ ≫ Limits.pullback.fst B.hom f := by
    simp only [Functor.id_obj, MorphismProperty.Over.pullbackComp_inv_app_left,
      Limits.pullback.map_id, Category.comp_id]
    exact Limits.pullbackLeftPullbackSndIso_hom_fst _ _ _
  have hsnd : ((MorphismProperty.Over.pullbackComp η f (η ≫ f) rfl).inv.app B).left ≫
      Limits.pullback.snd B.hom (η ≫ f) = Limits.pullback.snd _ _ := by
    simp only [Functor.id_obj, MorphismProperty.Over.pullbackComp_inv_app_left,
      Limits.pullback.map_id, Category.comp_id]
    exact Limits.pullbackLeftPullbackSndIso_hom_snd _ _ _
  have : Limits.pullback.lift p.left (𝟙 _) (h.trans (Category.id_comp _).symm) ≫
      ((MorphismProperty.Over.pullbackComp η f (η ≫ f) rfl).inv.app B).left =
      Limits.pullback.lift (p.left ≫ Limits.pullback.fst B.hom f) (𝟙 _)
        (((Category.assoc _ _ _).trans (w_left_fst f η p)).trans (Category.id_comp _).symm) := by
    apply Limits.pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hfst).trans
        ((Limits.pullback.lift_fst_assoc _ _ _ _).trans (Limits.pullback.lift_fst _ _ _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hsnd).trans
        ((Limits.pullback.lift_snd _ _ _).trans (Limits.pullback.lift_snd _ _ _).symm))
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans congr($this _)

/-- The identification `fiber η (f^* B) ≅ fiber (η ≫ f) B` is the projection on fibres. -/
lemma pullbackFiberIso_hom_app_eq (B : FiniteEtale U) (z : (fiber η).obj ((pullback f).obj B)) :
    (pullbackFiberIso f rfl).hom.app B z =
      (fiber (η ≫ f)).map (projHom f B) ((fiberRestrict f η).app _ z) := by
  obtain ⟨p, rfl⟩ := (fiberObjEquivHom η _).symm.surjective z
  rw [pullbackFiberIso_hom_app_symm, fiberRestrict_app_apply, fiberObjEquivHom_symm_naturality]
  congr 1

/-- The morphism `A ⟶ V` of finite étale `U`-schemes. -/
def toCover (A : FiniteEtale V) : (restrictScalars f).obj A ⟶ coverObj f :=
  MorphismProperty.Over.homMk A.hom rfl trivial

lemma mem_range_fiberRestrict_iff (A : FiniteEtale V)
    (z : (fiber (η ≫ f)).obj ((restrictScalars f).obj A)) :
    (∃ y, (fiberRestrict f η).app A y = z) ↔
      (fiber (η ≫ f)).map (toCover f A) z = coverPt f η rfl := by
  obtain ⟨a, rfl⟩ := (fiberObjEquivHom (η ≫ f) _).symm.surjective z
  rw [fiberObjEquivHom_symm_naturality, coverPt, Equiv.apply_eq_iff_eq]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := (fiberObjEquivHom η A).symm.surjective y
    rw [fiberRestrict_app_apply] at hy
    have hy' := (fiberObjEquivHom (η ≫ f) ((restrictScalars f).obj A)).symm.injective hy
    subst hy'
    ext
    exact w_left p
  · intro h
    have h' : a.left ≫ A.hom = η := congr_arg CommaMorphism.left h
    refine ⟨(fiberObjEquivHom η A).symm (Over.homMk a.left h'), ?_⟩
    rw [fiberRestrict_app_apply]
    congr 1


lemma subsingleton_fiber_id : Subsingleton ((fiber η).obj (mk (𝟙 V))) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨p, rfl⟩ := (fiberObjEquivHom η _).symm.surjective a
  obtain ⟨q, rfl⟩ := (fiberObjEquivHom η _).symm.surjective b
  congr 1
  ext
  have hp : p.left ≫ 𝟙 V = η := w_left p
  have hq : q.left ≫ 𝟙 V = η := w_left q
  exact (Category.comp_id _).symm.trans (hp.trans (hq.symm.trans (Category.comp_id _)))

/-- The diagonal `V ⟶ V ×_U V`, as a morphism of finite étale `V`-schemes. -/
def diagHom : mk (𝟙 V) ⟶ (pullback f).obj (coverObj f) :=
  MorphismProperty.Over.homMk (Limits.pullback.lift (𝟙 V) (𝟙 V) rfl)
    (Limits.pullback.lift_snd _ _ _) trivial

/-- The point `η` of `V ×_U V` over `η` (on the diagonal). -/
def diagPt : (fiber η).obj ((pullback f).obj (coverObj f)) :=
  (fiber η).map (diagHom f) ((fiberObjEquivHom η _).symm (Over.homMk η (Category.comp_id _)))

lemma diagPt_fixed (σ : π₁ᵉᵗ(η)) :
    σ.hom.app ((pullback f).obj (coverObj f)) (diagPt f η) = diagPt f η := by
  unfold diagPt
  rw [NatTrans.naturality_apply σ.hom (diagHom f)]
  haveI := subsingleton_fiber_id η
  congr 1
  exact Subsingleton.elim _ _

lemma pullbackFiberIso_hom_app_diag :
    (pullbackFiberIso f rfl).hom.app (coverObj f) (diagPt f η) = coverPt f η rfl := by
  rw [diagPt, fiberObjEquivHom_symm_naturality, pullbackFiberIso_hom_app_symm, coverPt]
  congr 1
  ext
  exact (Category.assoc _ _ _).trans ((congrArg (η ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
    (Category.comp_id _))

/-- **The image of `π₁ᵉᵗ(V) → π₁ᵉᵗ(U)` is the stabiliser of the point `η` of the fibre of `V`**
(SGA 1 V.6.11, Stacks 0BN6 (2)), for a finite étale `f : V ⟶ U`. -/
theorem range_fundamentalGroupMap_of_isFiniteEtale :
    (fundamentalGroupMap f (rfl : η ≫ f = η ≫ f)).toMonoidHom.range =
      MulAction.stabilizer π₁ᵉᵗ(η ≫ f) (coverPt f η rfl) := by
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    change (fiberAutMap (pullbackFiberIso f rfl) σ).hom.app (coverObj f) (coverPt f η rfl) =
      coverPt f η rfl
    have hi : ∀ y : (fiber η).obj ((pullback f).obj (coverObj f)),
        (pullbackFiberIso f rfl).inv.app (coverObj f)
        ((pullbackFiberIso f rfl).hom.app (coverObj f) y) = y := fun y ↦
      FintypeCat.hom_inv_id_apply ((pullbackFiberIso f rfl).app (coverObj f)) y
    rw [fiberAutMap_hom_app_apply, ← pullbackFiberIso_hom_app_diag f η, hi, diagPt_fixed]
  · intro hτ
    rw [MulAction.mem_stabilizer_iff, mulAction_def] at hτ
    have hτ' : τ.inv.app (coverObj f) (coverPt f η rfl) = coverPt f η rfl := by
      conv_lhs => rw [← hτ]
      exact FintypeCat.hom_inv_id_apply (τ.app (coverObj f)) _
    have key : ∀ (φ : (fiber (η ≫ f)) ⟶ fiber (η ≫ f)),
        φ.app (coverObj f) (coverPt f η rfl) = coverPt f η rfl → ∀ A x,
        ∃ y, (fiberRestrict f η).app A y = φ.app ((restrictScalars f).obj A)
          ((fiberRestrict f η).app A x) := by
      intro φ hφ A x
      rw [mem_range_fiberRestrict_iff, ← NatTrans.naturality_apply φ (toCover f A), ← hφ]
      congr 1
      exact (mem_range_fiberRestrict_iff f η A _).1 ⟨x, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_aut_restrict (restrictScalars f) (fiberRestrict f η)
      (fiberRestrict_injective f η) τ (key τ.hom hτ) (key τ.inv hτ')
    refine ⟨σ, ?_⟩
    refine Iso.ext (NatTrans.ext (funext fun B ↦ FintypeCat.hom_ext _ _ fun x ↦ ?_))
    change (fiberAutMap (pullbackFiberIso f rfl) σ).hom.app B x = τ.hom.app B x
    have hi : ∀ y : (fiber (η ≫ f)).obj B, (pullbackFiberIso f rfl).hom.app B
        ((pullbackFiberIso f rfl).inv.app B y) = y := fun y ↦
      FintypeCat.inv_hom_id_apply ((pullbackFiberIso f rfl).app B) y
    rw [fiberAutMap_hom_app_apply, pullbackFiberIso_hom_app_eq, hσ,
      ← NatTrans.naturality_apply τ.hom (projHom f B), ← pullbackFiberIso_hom_app_eq, hi]

/-- `range_fundamentalGroupMap_of_isFiniteEtale` for an arbitrary base point `η' = η ≫ f`. -/
theorem range_fundamentalGroupMap_of_isFiniteEtale' {η' : Spec (.of Ω) ⟶ U} (h : η ≫ f = η') :
    (fundamentalGroupMap f h).toMonoidHom.range =
      MulAction.stabilizer π₁ᵉᵗ(η') (coverPt f η h) := by
  subst h
  exact range_fundamentalGroupMap_of_isFiniteEtale f η

/-- `fundamentalGroupMap_injective_of_isFiniteEtale` for an arbitrary base point `η' = η ≫ f`. -/
theorem fundamentalGroupMap_injective_of_isFiniteEtale' [ConnectedSpace V] {η' : Spec (.of Ω) ⟶ U}
    (h : η ≫ f = η') : Function.Injective (fundamentalGroupMap f h) := by
  subst h
  exact fundamentalGroupMap_injective_of_isFiniteEtale f η

variable [ConnectedSpace V] {η' : Spec (.of Ω) ⟶ U} (h : η ≫ f = η')

/-- The open subgroup `π₁ᵉᵗ(V) ⊆ π₁ᵉᵗ(U)` of a connected finite étale cover: the stabiliser of the
point `η` of the fibre of `V` over `η' = η ≫ f`. -/
def coverSubgroup : OpenSubgroup π₁ᵉᵗ(η') where
  toSubgroup := MulAction.stabilizer π₁ᵉᵗ(η') (coverPt f η h)
  isOpen' := stabilizer_isOpen _ _

omit [ConnectedSpace V] in
lemma range_fundamentalGroupMap_eq_coverSubgroup :
    (fundamentalGroupMap f h).toMonoidHom.range = (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) :=
  range_fundamentalGroupMap_of_isFiniteEtale' f η h

omit [ConnectedSpace V] in
/-- **`π₁ᵉᵗ(V) → π₁ᵉᵗ(U)` has open image** for a finite étale `f : V ⟶ U`. -/
theorem isOpen_range_fundamentalGroupMap_of_isFiniteEtale :
    IsOpen (Set.range (fundamentalGroupMap f h)) := by
  have e : Set.range (fundamentalGroupMap f h) =
      ((coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) : Set π₁ᵉᵗ(η')) := by
    rw [← range_fundamentalGroupMap_eq_coverSubgroup]
    rfl
  rw [e]
  exact (coverSubgroup f η h).isOpen

/-- **`π₁ᵉᵗ(V, η) ≃ₜ*` the open subgroup `coverSubgroup f η h ⊆ π₁ᵉᵗ(U, η')`** for a connected
finite étale cover `f : V ⟶ U` and `η' = η ≫ f` ([AbsTopI] Definition 4.2 (iii)(a), operations of
type `⋏`), given by `fundamentalGroupMap f h`. -/
def coverEquiv : π₁ᵉᵗ(η) ≃ₜ* (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) := by
  let φ := fundamentalGroupMap f h
  have hmem : ∀ σ, φ σ ∈ (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) := fun σ ↦ by
    rw [← range_fundamentalGroupMap_eq_coverSubgroup]
    exact ⟨σ, rfl⟩
  let ψ : π₁ᵉᵗ(η) →* (coverSubgroup f η h : Subgroup π₁ᵉᵗ(η')) :=
    φ.toMonoidHom.codRestrict _ hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun a b hab ↦ fundamentalGroupMap_injective_of_isFiniteEtale' f η h
      (congrArg Subtype.val hab), fun y ↦ ?_⟩
    have hy : (y : π₁ᵉᵗ(η')) ∈ φ.toMonoidHom.range := by
      rw [range_fundamentalGroupMap_eq_coverSubgroup]
      exact y.2
    obtain ⟨σ, hσ⟩ := hy
    exact ⟨σ, Subtype.ext hσ⟩
  have hcont : Continuous ψ := φ.continuous.subtype_mk _
  let e := MulEquiv.ofBijective ψ hbij
  exact
    { e with
      continuous_toFun := hcont
      continuous_invFun := (hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

@[simp]
lemma coe_coverEquiv_apply (σ : π₁ᵉᵗ(η)) :
    (coverEquiv f η h σ : π₁ᵉᵗ(η')) = fundamentalGroupMap f h σ := rfl

end AlgebraicGeometry.FiniteEtale
