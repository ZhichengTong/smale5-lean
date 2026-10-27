import Smale5.Configuration
import Mathlib.Basic.Complex.BigOperators

/-! Positivity statements use actual complex conjugacy and positive real masses. -/
namespace Smale5
open scoped BigOperators

def realInertia (m : Fin 5 → ℝ) (q : Configuration) : ℝ :=
  ∑ k : Fin 5, m k * Complex.normSq (q.z k)

theorem inertia_eq_ofReal_realInertia (m : Fin 5 → ℝ) (q : Configuration)
    (hr : IsReal q) : inertia m q = (realInertia m q : ℂ) := by
  unfold inertia realInertia
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hr k, Complex.ofReal_mul]
  simp only [mul_assoc, Complex.star_def, Complex.mul_conj]

theorem exists_nonzero_z {m : Fin 5 → ℝ} {q : Configuration}
    (hn : IsNormalized m q) : ∃ k, q.z k ≠ 0 := by
  by_contra h
  push Not at h
  have hs := squaredDistance_ne_zero hn Edge.e12
  apply hs
  simp [squaredDistance, Edge.left, Edge.right, h]

theorem realInertia_pos {m : Fin 5 → ℝ} {q : Configuration}
    (hm : PositiveMasses m) (hn : IsNormalized m q) : 0 < realInertia m q := by
  unfold realInertia
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (le_of_lt (hm k)) (Complex.normSq_nonneg (q.z k))
  · obtain ⟨k, hk⟩ := exists_nonzero_z hn
    exact ⟨k, Finset.mem_univ _, mul_pos (hm k) (Complex.normSq_pos.mpr hk)⟩

/-- The real-point contradiction used in Diagram 7, once inertia vanishing
has actually been proved. This does not establish the Diagram 7 asymptotics. -/
theorem real_normalized_inertia_ne_zero {m : Fin 5 → ℝ} {q : Configuration}
    (hm : PositiveMasses m) (hn : IsNormalized m q) (hr : IsReal q) :
    inertia m q ≠ 0 := by
  rw [inertia_eq_ofReal_realInertia m q hr]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (realInertia_pos hm hn))

/-- Positive inverse distances contradict the Diagram 3 signed relation. -/
theorem positive_inverse_distances_exclude_d3 {q : Configuration}
    (hp : PositiveInverseDistances q) : q.delta Edge.e15 + 2 * q.delta Edge.e13 ≠ 0 := by
  obtain ⟨a, ha, hea⟩ := hp Edge.e15
  obtain ⟨b, hb, heb⟩ := hp Edge.e13
  rw [hea, heb]
  intro heq
  have hre : a + 2 * b = 0 := by exact_mod_cast heq
  linarith
end Smale5

