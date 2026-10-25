/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Poincare
import CurvesJacobian.Picard.JacobianKProps
import CurvesJacobian.Picard.JacobianDensity

/-!
# The Jacobians `J_L` and `J_Ω` are integral schemes

* `CurvesJacobian.isReduced_of_etale_of_isDomain`: an étale algebra over a domain is reduced
  (it embeds, by flatness, into its generic fibre, which is reduced being unramified over a
  field);
* `CurvesJacobian.isReduced_of_smooth`: a scheme smooth over an integral scheme is reduced
  (locally it is étale over a polynomial ring over a domain);
* `Smooth (jacD C σ hσ Ω).hom`: `J_L ≅ J_k ×_k L` is smooth over `L`;
* `IsIntegral (jacD C σ hσ Ω).left`: `J_L ≅ J_k ×_k L` is irreducible (`J_k` is geometrically
  irreducible) and reduced (smooth over `L`);
* `IsIntegral (jacOmega C σ hσ Ω).left`.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

open Belyi

/-- **An étale algebra over a domain is reduced**: `S ↪ Frac(A) ⊗_A S` by flatness, and the
latter is unramified of finite type over a field, hence reduced. -/
theorem isReduced_of_etale_of_isDomain {A S : Type u} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Algebra.Etale A S] : IsReduced S := by
  let F := FractionRing A
  let f := Algebra.TensorProduct.includeRight (R := A) (A := F) (B := S)
  have hf : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor S (Algebra.ofId A F).toLinearMap).comp
        (Algebra.TensorProduct.lid A S).symm.toLinearMap := by
      ext s
      simp [f]
    rw [this]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective A F)).comp (Algebra.TensorProduct.lid A S).symm.injective
  have : IsReduced (F ⊗[A] S) := Algebra.FormallyUnramified.isReduced_of_field F _
  exact isReduced_of_injective f hf

/-- **A scheme smooth over an integral scheme is reduced.** -/
theorem isReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral Y] :
    IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
    obtain ⟨n, g, -, hg⟩ := hs.exists_etale_mvPolynomial
    haveI : Nonempty U := ⟨⟨f x, e hx⟩⟩
    algebraize [g]
    haveI : _root_.IsReduced Γ(X, V) := isReduced_of_etale_of_isDomain
      (A := MvPolynomial (Fin n) Γ(Y, U))
    haveI : IsReduced V.toScheme := by
      haveI : IsAffine V.toScheme := hV
      haveI : _root_.IsReduced Γ(V.toScheme, ⊤) :=
        isReduced_of_injective _ (V.topIso.commRingCatIsoToRingEquiv.injective)
      exact isReduced_of_isAffine_isReduced V.toScheme
    let e := (asIso (V.ι.stalkMap ⟨x, hx⟩)).commRingCatIsoToRingEquiv
    have : _root_.IsReduced (X.presheaf.stalk (V.ι ⟨x, hx⟩)) :=
      isReduced_of_injective e e.injective
    exact this
  exact isReduced_of_isReduced_stalk _

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

/-- **`J_L` is smooth over `L`**: `J_L ≅ J_k ×_k L` and `J_k` is smooth over `k`. -/
instance : Smooth (jacD C σ hσ Ω).hom := by
  have h : (jacD C σ hσ Ω).hom = (jacKBaseChangeIso C σ hσ Ω).inv ≫
      pullback.snd (jacK C σ hσ Ω).hom (GaloisDescent.sL k (jacFieldD C σ hσ Ω)) := by
    rw [← jacKBaseChangeIso_hom_comp, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- `J_L ≅ J_k ×_k L` is irreducible, as `J_k` is geometrically irreducible over `k`. -/
instance : IrreducibleSpace (jacD C σ hσ Ω).left :=
  (jacKBaseChangeIso C σ hσ Ω).hom.homeomorph.irreducibleSpace_iff.mp inferInstance

/-- **The Jacobian `J_L` is an integral scheme.** -/
instance : IsIntegral (jacD C σ hσ Ω).left :=
  haveI := isReduced_of_smooth (jacD C σ hσ Ω).hom
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The Jacobian `J_Ω` is an integral scheme.** -/
instance : IsIntegral (jacOmega C σ hσ Ω).left :=
  haveI := isReduced_of_smooth (jacOmega C σ hσ Ω).hom
  isIntegral_of_irreducibleSpace_of_isReduced _

end CurvesJacobian
