import Smale5.Orders
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Finite divisor arithmetic for the global two-boundary-point argument.

Every geometric premise is an explicit parameter. In an eventual application,
`totalOrder (v p)` must be the usual order at a point of the smooth projective
normalization, with compatible normalization at all points. Arbitrarily rescaled
Puiseux exponents need not have degree zero. This file does not establish the
existence of that normalization or the principal-divisor degree theorem.
-/
namespace Smale5
open scoped BigOperators

/-- A finite zero-sum family with a positive entry has a negative entry. -/
theorem exists_negative_of_sum_zero_of_positive {Point : Type*}
    (support : Finset Point) (d : Point → ℚ)
    (degree_zero : (∑ p ∈ support, d p) = 0)
    {p : Point} (hp : p ∈ support) (positive : 0 < d p) :
    ∃ q ∈ support, d q < 0 := by
  classical
  by_contra no_negative
  push Not at no_negative
  have hle : d p ≤ ∑ q ∈ support, d q :=
    Finset.single_le_sum no_negative hp
  linarith

/-- A finite-support zero-degree order function sends any zero to a pole.
The support may contain additional points with order zero. -/
theorem zero_has_pole_of_degree_zero {Point : Type*}
    (d : Point → ℚ) (support : Finset Point)
    (zero_off_support : ∀ p, p ∉ support → d p = 0)
    (degree_zero : (∑ p ∈ support, d p) = 0)
    (has_zero : ∃ p, 0 < d p) : ∃ q, d q < 0 := by
  classical
  obtain ⟨p, positive⟩ := has_zero
  have hp : p ∈ support := by
    by_contra outside
    have hz := zero_off_support p outside
    linarith
  obtain ⟨q, _, negative⟩ :=
    exists_negative_of_sum_zero_of_positive support d degree_zero hp positive
  exact ⟨q, negative⟩

/-- The global contradiction with explicit finite-support and degree-zero
premises. Its local-vanishing and initial-pole premises remain geometric
obligations; it is not a proof of five-body finiteness by itself. -/
theorem globalOrderContradiction_from_degreeZero {Point : Type*}
    (v : Point → Edge → ℚ) (support : Finset Point)
    (zero_off_support : ∀ p, p ∉ support → totalOrder (v p) = 0)
    (degree_zero : (∑ p ∈ support, totalOrder (v p)) = 0)
    (local_vanishing : ∀ p,
      (∃ e, fourOrder (v p) e < 0) → 0 < totalOrder (v p))
    (initial_pole : ∃ p e, fourOrder (v p) e < 0) : False := by
  obtain ⟨p, e, hp⟩ := initial_pole
  have hp0 := local_vanishing p ⟨e, hp⟩
  obtain ⟨q, hq⟩ := zero_has_pole_of_degree_zero
    (fun p => totalOrder (v p)) support zero_off_support degree_zero ⟨p, hp0⟩
  have hq0 := local_vanishing q (exists_negative_fourOrder (v q) hq)
  linarith

end Smale5


