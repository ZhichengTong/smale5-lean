import Smale5.Balance

/-! Weighted pair-distance formula for the manuscript's five-body coordinates.
The first result is an unconditional polynomial identity.  The normalized
corollaries use only the center-of-mass consequences of the balance equations;
they do not use positivity or any computational appendix assumptions. -/
namespace Smale5
open scoped BigOperators
open Edge

/-- Total mass times inertia differs from the weighted squared-distance sum by
exactly the product of the two weighted coordinate sums. -/
theorem weighted_pair_distance_identity (m : Fin 5 → ℝ) (q : Configuration) :
    (∑ k : Fin 5, (m k : ℂ)) * inertia m q -
      (∑ k : Fin 5, (m k : ℂ) * q.z k) *
        (∑ k : Fin 5, (m k : ℂ) * q.w k) =
    ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) * squaredDistance q e := by
  have huniv : (Finset.univ : Finset Edge) =
      {e12, e13, e14, e15, e23, e24, e25, e34, e35, e45} := rfl
  unfold inertia
  simp only [Fin.sum_univ_succ]
  rw [huniv]
  simp [squaredDistance, Edge.left, Edge.right]
  ring

/-- With the center of mass at the origin, the correction term vanishes. -/
theorem mass_mul_inertia_of_centerOfMass_zero (m : Fin 5 → ℝ) (q : Configuration)
    (hz : (∑ k : Fin 5, (m k : ℂ) * q.z k) = 0)
    (hw : (∑ k : Fin 5, (m k : ℂ) * q.w k) = 0) :
    (∑ k : Fin 5, (m k : ℂ)) * inertia m q =
      ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) * squaredDistance q e := by
  simpa only [hz, hw, zero_mul, sub_zero] using weighted_pair_distance_identity m q

/-- Every normalized solution satisfies the weighted pair-distance formula
`M I = ∑_{i<j} m_i m_j r_{ij}²`. -/
theorem normalized_mass_mul_inertia {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) :
    (∑ k : Fin 5, (m k : ℂ)) * inertia m q =
      ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) * squaredDistance q e :=
  mass_mul_inertia_of_centerOfMass_zero m q
    (normalized_centerOfMass_z h) (normalized_centerOfMass_w h)

end Smale5
