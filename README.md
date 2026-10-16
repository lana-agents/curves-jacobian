# curves-jacobian

Lean 4 / Mathlib algebraic geometry of curves needed by Mochizuki's relative p-adic
Grothendieck conjecture ([LocAn] = *The Local Pro-p Anabelian Geometry of Curves*) and by the
weights track (Weil RH, ℓ-adic weights) of the formalisation of the multiradial algorithm
(IUT III, Thm 3.11).

Scope (see `Blueprint.md` for the milestone list CJ0–CJ11): commutative algebra (Serre's
normality criterion, depth), smooth proper curves as schemes, comparison with function fields,
Picard schemes, Jacobians, theta divisors, étale cohomology of curves (Kummer sequence),
stable models, Néron models.

**Not here**: function fields, places, divisors, Riemann–Roch, zeta functions over perfect fields
— these live in `lana-agents/weil-curves` and will be a pinned lake dependency.

Toolchain `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0` (commit 81a5d25), the same pin as `iut`.
No `sorry`, no `axiom`; CI builds with `--wfail`.

## Status

See `Blueprint.md`.
