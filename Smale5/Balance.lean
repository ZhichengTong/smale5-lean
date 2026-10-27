import Smale5.Configuration

/-! Pairwise cancellation in the force equations, with no positivity assumption. -/
namespace Smale5
open scoped BigOperators

/-- The total internal force vanishes for a symmetric interaction coefficient. -/
theorem internal_force_sum_zero {ι : Type*} [Fintype ι]
    (m z : ι → ℂ) (d : ι → ι → ℂ) (hd : ∀ i j, d i j = d j i) :
    (∑ i, ∑ j, m i * m j * d i j ^ 3 * (z i - z j)) = 0 := by
  let F : ι → ι → ℂ := fun i j => m i * m j * d i j ^ 3 * (z i - z j)
  have anti : ∀ i j, F j i = -F i j := by
    intro i j
    dsimp [F]
    rw [hd j i]
    ring
  have hs : (∑ i, ∑ j, F i j) = -(∑ i, ∑ j, F i j) := by
    calc
      (∑ i, ∑ j, F i j) = ∑ j, ∑ i, F i j := Finset.sum_comm
      _ = ∑ i, ∑ j, -F i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact anti i j
      _ = -(∑ i, ∑ j, F i j) := by simp only [Finset.sum_neg_distrib]
  have hz : (2 : ℂ) * (∑ i, ∑ j, F i j) = 0 := by linear_combination hs
  have hz' : (∑ i, ∑ j, F i j) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact hz'

theorem centerOfMass_from_balance {ι : Type*} [Fintype ι]
    (m z : ι → ℂ) (d : ι → ι → ℂ) (hd : ∀ i j, d i j = d j i)
    (hb : ∀ i, z i = ∑ j, m j * d i j ^ 3 * (z i - z j)) :
    (∑ i, m i * z i) = 0 := by
  calc
    (∑ i, m i * z i) = ∑ i, m i * (∑ j, m j * d i j ^ 3 * (z i - z j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun x => m i * x) (hb i)
    _ = ∑ i, ∑ j, m i * m j * d i j ^ 3 * (z i - z j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 0 := internal_force_sum_zero m z d hd

theorem normalized_centerOfMass_z {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) : (∑ k : Fin 5, (m k : ℂ) * q.z k) = 0 :=
  centerOfMass_from_balance (fun k => (m k : ℂ)) q.z q.inversePair
    q.inversePair_symm h.z_balance

theorem normalized_centerOfMass_w {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) : (∑ k : Fin 5, (m k : ℂ) * q.w k) = 0 :=
  centerOfMass_from_balance (fun k => (m k : ℂ)) q.w q.inversePair
    q.inversePair_symm h.w_balance
end Smale5
