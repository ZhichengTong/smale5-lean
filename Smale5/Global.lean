import Smale5.Orders

/-! The arithmetic core of the two-boundary-point argument. The two geometric
hypotheses are explicit parameters. This is not the five-body finiteness theorem. -/
namespace Smale5

/-- On a curve with nonzero affine total product: zero implies a pole, and every
four-product pole implies a zero of the total product. These premises rule out
an initial four-product pole. -/
theorem globalOrderContradiction {Point : Type*} (v : Point → Edge → ℚ)
    (zero_has_pole : (∃ p, 0 < totalOrder (v p)) → ∃ q, totalOrder (v q) < 0)
    (local_vanishing : ∀ p, (∃ e, fourOrder (v p) e < 0) → 0 < totalOrder (v p))
    (initial_pole : ∃ p e, fourOrder (v p) e < 0) : False := by
  obtain ⟨p, e, hp⟩ := initial_pole
  have hp0 := local_vanishing p ⟨e, hp⟩
  obtain ⟨q, hq⟩ := zero_has_pole ⟨p, hp0⟩
  have hq0 := local_vanishing q (exists_negative_fourOrder (v q) hq)
  linarith

/-- A reusable finiteness reduction. `produces_orders` is a geometric obligation,
not supplied for the configuration space in this development. -/
theorem finite_of_order_reduction {X Point : Type*} (S : Set X)
    (produces_orders : S.Infinite → ∃ v : Point → Edge → ℚ,
      ((∃ p, 0 < totalOrder (v p)) → ∃ q, totalOrder (v q) < 0) ∧
      (∀ p, (∃ e, fourOrder (v p) e < 0) → 0 < totalOrder (v p)) ∧
      (∃ p e, fourOrder (v p) e < 0)) : S.Finite := by
  by_contra h
  obtain ⟨v, hz, hl, hp⟩ := produces_orders h
  exact globalOrderContradiction v hz hl hp
end Smale5
