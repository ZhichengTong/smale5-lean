import Smale5.Products
import Mathlib.Basic.Complex.Basic

/-! Faithful twenty-complex-coordinate target: five z, five w and ten inverse
distances. Positivity includes the real condition and positive real δ. -/
namespace Smale5
open scoped BigOperators

structure Configuration where
  z : Fin 5 → ℂ
  w : Fin 5 → ℂ
  delta : Edge → ℂ

def Configuration.inversePair (q : Configuration) (i j : Fin 5) : ℂ :=
  match edgeFor i j with
  | some e => q.delta e
  | none => 0

theorem Configuration.inversePair_symm (q : Configuration) (i j : Fin 5) :
    q.inversePair i j = q.inversePair j i := by
  simp only [Configuration.inversePair, edgeFor_symm i j]

def squaredDistance (q : Configuration) (e : Edge) : ℂ :=
  (q.z e.right - q.z e.left) * (q.w e.right - q.w e.left)

structure IsNormalized (m : Fin 5 → ℝ) (q : Configuration) : Prop where
  z_balance : ∀ k, q.z k = ∑ l : Fin 5,
    (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l)
  w_balance : ∀ k, q.w k = ∑ l : Fin 5,
    (m l : ℂ) * q.inversePair k l ^ 3 * (q.w k - q.w l)
  distance_constraint : ∀ e, q.delta e ^ 2 * squaredDistance q e = 1
  gauge : q.z 1 - q.z 0 = q.w 1 - q.w 0

def PositiveMasses (m : Fin 5 → ℝ) : Prop := ∀ k, 0 < m k

def IsReal (q : Configuration) : Prop := ∀ k, q.w k = star (q.z k)

def PositiveInverseDistances (q : Configuration) : Prop :=
  ∀ e, ∃ d : ℝ, 0 < d ∧ q.delta e = (d : ℂ)

def IsPositiveNormalized (m : Fin 5 → ℝ) (q : Configuration) : Prop :=
  IsNormalized m q ∧ IsReal q ∧ PositiveInverseDistances q

/-- Exact target proposition, deliberately not asserted as a theorem. -/
def FiveBodyFiniteness : Prop :=
  ∀ m : Fin 5 → ℝ, PositiveMasses m → {q : Configuration | IsPositiveNormalized m q}.Finite

def potential (m : Fin 5 → ℝ) (q : Configuration) : ℂ :=
  ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) * q.delta e

def inertia (m : Fin 5 → ℝ) (q : Configuration) : ℂ :=
  ∑ k : Fin 5, (m k : ℂ) * q.z k * q.w k

theorem squaredDistance_ne_zero {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (e : Edge) : squaredDistance q e ≠ 0 := by
  intro hz
  have hc := h.distance_constraint e
  rw [hz, mul_zero] at hc
  exact zero_ne_one hc

theorem inverseDistance_ne_zero {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (e : Edge) : q.delta e ≠ 0 := by
  intro hz
  have hc := h.distance_constraint e
  simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hc
  exact zero_ne_one hc

theorem normalized_totalProduct_ne_zero {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) : totalProduct (squaredDistance q) ≠ 0 :=
  totalProduct_ne_zero _ (squaredDistance_ne_zero h)

theorem normalized_product_identity {m : Fin 5 → ℝ} {q : Configuration}
    (_h : IsNormalized m q) :
    totalProduct (fourProduct (squaredDistance q)) = totalProduct (squaredDistance q) ^ 4 :=
  product_fourProducts _
end Smale5

