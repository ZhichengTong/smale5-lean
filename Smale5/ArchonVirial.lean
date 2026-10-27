import Smale5.Configuration

/-! Virial identity obtained from the five normalized balance equations.
This file is authored and checked locally. The separately prepared external
Archon proving invocation was blocked before execution by approval review. -/
namespace Smale5
open scoped BigOperators
open Edge

/-- Pairing the two orientations of each of the ten edges. -/
theorem virial_pair_sum (m : Fin 5 → ℝ) (q : Configuration) :
    (∑ k : Fin 5, ∑ l : Fin 5,
      (m k : ℂ) * (m l : ℂ) * q.inversePair k l ^ 3 *
        (q.z k - q.z l) * q.w k) =
    ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) *
      q.delta e ^ 3 * squaredDistance q e := by
  have huniv : (Finset.univ : Finset Edge) =
      {e12, e13, e14, e15, e23, e24, e25, e34, e35, e45} := rfl
  simp only [Fin.sum_univ_succ]
  rw [huniv]
  simp [Configuration.inversePair, edgeFor, squaredDistance, Edge.left, Edge.right]
  ring

/-- Manuscript energy identity U = I; no positivity assumption is needed. -/
theorem normalized_potential_eq_inertia {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) : potential m q = inertia m q := by
  have hi : inertia m q =
      ∑ k : Fin 5, ∑ l : Fin 5,
        (m k : ℂ) * (m l : ℂ) * q.inversePair k l ^ 3 *
          (q.z k - q.z l) * q.w k := by
    unfold inertia
    apply Finset.sum_congr rfl
    intro k hk
    conv_lhs => rw [h.z_balance k]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hi, virial_pair_sum]
  unfold potential
  apply Finset.sum_congr rfl
  intro e he
  have hc := h.distance_constraint e
  calc
    (m e.left : ℂ) * (m e.right : ℂ) * q.delta e =
        (m e.left : ℂ) * (m e.right : ℂ) * q.delta e *
          (q.delta e ^ 2 * squaredDistance q e) := by rw [hc, mul_one]
    _ = (m e.left : ℂ) * (m e.right : ℂ) *
        q.delta e ^ 3 * squaredDistance q e := by ring

end Smale5

