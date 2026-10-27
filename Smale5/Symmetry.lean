import Smale5.Configuration

/-!
# Complex scaling and the gauge condition

The action z ↦ c z, w ↦ c⁻¹ w preserves the force and distance equations
for c ≠ 0. It does not automatically preserve the chosen gauge z₁₀ = w₁₀:
the exact extra condition is proved below. These are algebraic statements;
no analytic germ, compactification, or computational certificate is assumed.
-/

namespace Smale5
open scoped BigOperators

/-- The normalized equations with the gauge omitted. -/
structure IsForceDistanceSolution (m : Fin 5 → ℝ) (q : Configuration) : Prop where
  z_balance : ∀ k, q.z k = ∑ l : Fin 5,
    (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l)
  w_balance : ∀ k, q.w k = ∑ l : Fin 5,
    (m l : ℂ) * q.inversePair k l ^ 3 * (q.w k - q.w l)
  distance_constraint : ∀ e, q.delta e ^ 2 * squaredDistance q e = 1

def SatisfiesGauge (q : Configuration) : Prop :=
  q.z 1 - q.z 0 = q.w 1 - q.w 0

theorem IsNormalized.toForceDistanceSolution {m : Fin 5 → ℝ}
    {q : Configuration} (h : IsNormalized m q) : IsForceDistanceSolution m q :=
  ⟨h.z_balance, h.w_balance, h.distance_constraint⟩

/-- The reciprocal scaling of the two complex coordinate families. -/
noncomputable def Configuration.cStarScale (q : Configuration) (c : ℂ) : Configuration where
  z := fun k => c * q.z k
  w := fun k => c⁻¹ * q.w k
  delta := q.delta

@[simp] theorem inversePair_cStarScale (q : Configuration) (c : ℂ) (i j : Fin 5) :
    (q.cStarScale c).inversePair i j = q.inversePair i j := by
  rfl

theorem squaredDistance_cStarScale (q : Configuration) (c : ℂ) (hc : c ≠ 0)
    (e : Edge) : squaredDistance (q.cStarScale c) e = squaredDistance q e := by
  dsimp [squaredDistance, Configuration.cStarScale]
  calc
    _ = (c * c⁻¹) * ((q.z e.right - q.z e.left) *
        (q.w e.right - q.w e.left)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc, one_mul]

/-- Force and distance equations are invariant under every nonzero complex scale. -/
theorem IsForceDistanceSolution.cStarScale {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsForceDistanceSolution m q) (c : ℂ) (hc : c ≠ 0) :
    IsForceDistanceSolution m (q.cStarScale c) := by
  constructor
  · intro k
    change c * q.z k = ∑ l : Fin 5,
      (m l : ℂ) * q.inversePair k l ^ 3 * (c * q.z k - c * q.z l)
    calc
      c * q.z k = c * (∑ l : Fin 5,
          (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l)) :=
        congrArg (fun v : ℂ => c * v) (h.z_balance k)
      _ = ∑ l : Fin 5, c * ((m l : ℂ) * q.inversePair k l ^ 3 *
          (q.z k - q.z l)) := Finset.mul_sum ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        ring
  · intro k
    change c⁻¹ * q.w k = ∑ l : Fin 5,
      (m l : ℂ) * q.inversePair k l ^ 3 * (c⁻¹ * q.w k - c⁻¹ * q.w l)
    calc
      c⁻¹ * q.w k = c⁻¹ * (∑ l : Fin 5,
          (m l : ℂ) * q.inversePair k l ^ 3 * (q.w k - q.w l)) :=
        congrArg (fun v : ℂ => c⁻¹ * v) (h.w_balance k)
      _ = ∑ l : Fin 5, c⁻¹ * ((m l : ℂ) * q.inversePair k l ^ 3 *
          (q.w k - q.w l)) := Finset.mul_sum ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        ring
  · intro e
    change q.delta e ^ 2 * squaredDistance (q.cStarScale c) e = 1
    rw [squaredDistance_cStarScale q c hc e]
    exact h.distance_constraint e

/-- The precise condition needed to restore the manuscript's gauge. -/
theorem gauge_cStarScale_iff (q : Configuration) (c : ℂ) (hc : c ≠ 0) :
    SatisfiesGauge (q.cStarScale c) ↔
      c ^ 2 * (q.z 1 - q.z 0) = q.w 1 - q.w 0 := by
  simp only [SatisfiesGauge, Configuration.cStarScale, ← mul_sub]
  constructor
  · intro hg
    calc
      c ^ 2 * (q.z 1 - q.z 0) = c * (c * (q.z 1 - q.z 0)) := by ring
      _ = c * (c⁻¹ * (q.w 1 - q.w 0)) := by rw [hg]
      _ = q.w 1 - q.w 0 := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · intro hg
    calc
      c * (q.z 1 - q.z 0) = (c⁻¹ * c) * (c * (q.z 1 - q.z 0)) := by
        rw [inv_mul_cancel₀ hc, one_mul]
      _ = c⁻¹ * (c ^ 2 * (q.z 1 - q.z 0)) := by ring
      _ = c⁻¹ * (q.w 1 - q.w 0) := by rw [hg]

/-- For an already gauged collision-free solution, the residual scale freedom
is exactly c² = 1. This rules out silently preserving the gauge under arbitrary
nonzero complex scales. -/
theorem normalized_gauge_cStarScale_iff_square_one {m : Fin 5 → ℝ}
    {q : Configuration} (h : IsNormalized m q) (c : ℂ) (hc : c ≠ 0) :
    SatisfiesGauge (q.cStarScale c) ↔ c ^ 2 = 1 := by
  have hz : q.z 1 - q.z 0 ≠ 0 := by
    intro hz
    have hd := squaredDistance_ne_zero h Edge.e12
    apply hd
    simp [squaredDistance, Edge.left, Edge.right, hz]
  rw [gauge_cStarScale_iff q c hc, ← h.gauge]
  constructor
  · intro hg
    have hprod : (c ^ 2 - 1) * (q.z 1 - q.z 0) = 0 := by
      linear_combination hg
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hz)
  · intro hc2
    rw [hc2, one_mul]

/-- The full normalized system is preserved when the additional gauge equation holds. -/
theorem IsNormalized.cStarScale_of_gauge {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (c : ℂ) (hc : c ≠ 0)
    (hg : c ^ 2 * (q.z 1 - q.z 0) = q.w 1 - q.w 0) :
    IsNormalized m (q.cStarScale c) := by
  have hs := h.toForceDistanceSolution.cStarScale c hc
  exact ⟨hs.z_balance, hs.w_balance, hs.distance_constraint,
    (gauge_cStarScale_iff q c hc).2 hg⟩

/-- Once the gauge has been imposed, scales whose square is one preserve it. -/
theorem IsNormalized.cStarScale_of_square_one {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (c : ℂ) (hc : c ≠ 0) (hc2 : c ^ 2 = 1) :
    IsNormalized m (q.cStarScale c) := by
  apply h.cStarScale_of_gauge c hc
  rw [hc2, one_mul]
  exact h.gauge

theorem potential_cStarScale (m : Fin 5 → ℝ) (q : Configuration) (c : ℂ) :
    potential m (q.cStarScale c) = potential m q := by
  rfl

theorem inertia_cStarScale (m : Fin 5 → ℝ) (q : Configuration) (c : ℂ)
    (hc : c ≠ 0) : inertia m (q.cStarScale c) = inertia m q := by
  unfold inertia
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [Configuration.cStarScale]
  calc
    _ = (c * c⁻¹) * ((m k : ℂ) * q.z k * q.w k) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc, one_mul]

end Smale5

