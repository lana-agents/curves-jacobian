/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Etale.Kummer
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The Kummer long exact sequence in étale cohomology

For a scheme `X` and `n ≥ 1` invertible on `X`, with `Hᵏ(X, F) := Sheaf.H F k` (Mathlib's sheaf
cohomology, `Ext` from the constant sheaf `ℤ` in `Sheaf X.smallEtaleTopology Ab`):

* `CurvesJacobian.etaleTerminal X`, `CurvesJacobian.isTerminal_etaleTerminal`: `X` itself is the
  terminal object of the small étale site;
* `CurvesJacobian.H0GmEquiv`: `H⁰(X, 𝔾ₘ) ≃ Γ(X, 𝒪_X)ˣ`;
* `CurvesJacobian.kummerδ`: the connecting map `Hᵏ(X, 𝔾ₘ) → Hᵏ⁺¹(X, μₙ)`;
* the exactness of the Kummer long exact sequence
  `⋯ → Hᵏ(μₙ) → Hᵏ(𝔾ₘ) →ⁿ Hᵏ(𝔾ₘ) →δ Hᵏ⁺¹(μₙ) → Hᵏ⁺¹(𝔾ₘ) → ⋯`
  at each of its three kinds of terms (`CurvesJacobian.kummer_exact_Gm`,
  `CurvesJacobian.kummer_exact_δ`, `CurvesJacobian.kummer_exact_mu`).

In degree `0` this is Kummer theory: `Γ(X)ˣ / (Γ(X)ˣ)ⁿ ↪ H¹(X, μₙ)`, with cokernel the `n`-torsion
of `H¹(X, 𝔾ₘ)` (which is `Pic X` by Hilbert 90 — not formalised here).
-/

open CategoryTheory Opposite Limits AlgebraicGeometry Abelian

namespace CurvesJacobian

universe u

variable (X : Scheme.{u})

/-- `X`, as the terminal object of its small étale site. -/
noncomputable def etaleTerminal : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- `X` is terminal in its small étale site. -/
noncomputable def isTerminal_etaleTerminal : IsTerminal (etaleTerminal X) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial)
    (fun U f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f))

/-- **`H⁰(X, 𝔾ₘ) = Γ(X, 𝒪_X)ˣ`.** -/
noncomputable def H0GmEquiv : Sheaf.H.{u} (Gm X) 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
  Sheaf.H.equiv₀ (Gm X) (isTerminal_etaleTerminal X)

variable {X}

/-- The constant sheaf `ℤ` on the small étale site. -/
noncomputable abbrev constZ (X : Scheme.{u}) : Sheaf X.smallEtaleTopology Ab.{u} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))

section LES

variable {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤)))

/-- The connecting map `Hᵏ(X, 𝔾ₘ) → Hᵏ⁺¹(X, μₙ)` of the Kummer sequence. -/
noncomputable def kummerδ (k : ℕ) (x : Sheaf.H.{u} (Gm X) k) : Sheaf.H.{u} (mu X n) (k + 1) :=
  x.comp (kummer_shortExact hn hnX).extClass rfl

include hn hnX in
/-- Exactness at `Hᵏ(𝔾ₘ)` (source of `n`): the kernel of `H(n)` is the image of `Hᵏ(μₙ)`. -/
theorem kummer_exact_Gm {k : ℕ} (x : Sheaf.H.{u} (Gm X) k)
    (hx : Sheaf.H.map (kummerMap X n) k x = 0) :
    ∃ y : Sheaf.H.{u} (mu X n) k, Sheaf.H.map (kernel.ι (kummerMap X n)) k y = x :=
  Ext.covariant_sequence_exact₂.{u} (constZ X) (S := kummerComplex X n)
    (kummer_shortExact hn hnX) x hx

/-- Exactness at `Hᵏ(𝔾ₘ)` (target of `n`): the kernel of `δ` is the image of `H(n)`. -/
theorem kummer_exact_δ {k : ℕ} (x : Sheaf.H.{u} (Gm X) k) (hx : kummerδ hn hnX k x = 0) :
    ∃ y : Sheaf.H.{u} (Gm X) k, Sheaf.H.map (kummerMap X n) k y = x :=
  Ext.covariant_sequence_exact₃.{u} (constZ X) (S := kummerComplex X n)
    (kummer_shortExact hn hnX) x rfl hx

/-- Exactness at `Hᵏ⁺¹(μₙ)`: the kernel of `Hᵏ⁺¹(μₙ) → Hᵏ⁺¹(𝔾ₘ)` is the image of `δ`. -/
theorem kummer_exact_mu {k : ℕ} (x : Sheaf.H.{u} (mu X n) (k + 1))
    (hx : Sheaf.H.map (kernel.ι (kummerMap X n)) (k + 1) x = 0) :
    ∃ y : Sheaf.H.{u} (Gm X) k, kummerδ hn hnX k y = x :=
  Ext.covariant_sequence_exact₁.{u} (constZ X) (S := kummerComplex X n)
    (kummer_shortExact hn hnX) x hx rfl

end LES

end CurvesJacobian
