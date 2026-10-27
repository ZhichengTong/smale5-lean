import Smale5.Configuration

/-! The polynomial inertia decomposition in manuscript Lemma d7-identity
(lines 4850–4880).  Fin 5 labels 0,1 form the upper wing; 2,3 form the
lower wing; label 4 is the distinguished fifth body.  This file checks only
the identity and its restriction to normalized solutions.  It makes no claim
about analytic germs, orders, bounded chart coordinates, or vanishing limits. -/
namespace Smale5.Diagram7
open scoped BigOperators

/-- The z balance row, with the identically zero diagonal term included. -/
def forceResidualZ (m : Fin 5 → ℝ) (q : Configuration) (k : Fin 5) : ℂ :=
  q.z k - ∑ l : Fin 5, (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l)

/-- The w balance row, with the identically zero diagonal term included. -/
def forceResidualW (m : Fin 5 → ℝ) (q : Configuration) (k : Fin 5) : ℂ :=
  q.w k - ∑ l : Fin 5, (m l : ℂ) * q.inversePair k l ^ 3 * (q.w k - q.w l)

/-- The manuscript's S₅: crossed-force torque about the fifth body. -/
def crossedTorque (m : Fin 5 → ℝ) (q : Configuration) : ℂ :=
  ∑ j ∈ ({2, 3} : Finset (Fin 5)), ∑ l ∈ ({0, 1} : Finset (Fin 5)),
    (m j : ℂ) * (m l : ℂ) * q.inversePair j l ^ 3 *
      ((q.z j - q.z 4) * (q.w l - q.w 4) -
        (q.w j - q.w 4) * (q.z l - q.z 4))

/-- The full polynomial identity, before any force equations are imposed. -/
theorem inertia_identity (m : Fin 5 → ℝ) (q : Configuration) :
    inertia m q =
      (∑ k ∈ ({0, 1} : Finset (Fin 5)), (m k : ℂ) * q.z k * (q.w k - q.w 4)) +
      (∑ j ∈ ({2, 3} : Finset (Fin 5)), (m j : ℂ) * q.w j * (q.z j - q.z 4)) +
      crossedTorque m q -
      (∑ j ∈ ({2, 3} : Finset (Fin 5)), (m j : ℂ) *
        ((q.z j - q.z 4) * forceResidualW m q j -
          (q.w j - q.w 4) * forceResidualZ m q j)) +
      q.w 4 * (∑ k : Fin 5, (m k : ℂ) * forceResidualZ m q k) := by
  simp [inertia, crossedTorque, forceResidualZ, forceResidualW,
    Fin.sum_univ_succ, Configuration.inversePair, edgeFor]
  ring

theorem normalized_forceResidualZ {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (k : Fin 5) : forceResidualZ m q k = 0 := by
  unfold forceResidualZ
  exact sub_eq_zero.mpr (h.z_balance k)

theorem normalized_forceResidualW {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (k : Fin 5) : forceResidualW m q k = 0 := by
  unfold forceResidualW
  exact sub_eq_zero.mpr (h.w_balance k)

/-- On normalized solutions the residual terms in d7-identity vanish. -/
theorem normalized_inertia_identity {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) :
    inertia m q =
      (∑ k ∈ ({0, 1} : Finset (Fin 5)), (m k : ℂ) * q.z k * (q.w k - q.w 4)) +
      (∑ j ∈ ({2, 3} : Finset (Fin 5)), (m j : ℂ) * q.w j * (q.z j - q.z 4)) +
      crossedTorque m q := by
  simpa only [normalized_forceResidualZ h, normalized_forceResidualW h,
    mul_zero, sub_self, Finset.sum_const_zero, sub_zero, add_zero] using
    inertia_identity m q

end Smale5.Diagram7
