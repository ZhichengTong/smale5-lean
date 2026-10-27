import Smale5.Edges

/-! Order arithmetic. Geometric assertions identifying these numbers with
meromorphic orders are separate obligations, not axioms of this module. -/
namespace Smale5
open Edge

def totalOrder (v : Edge → ℚ) : ℚ :=
  v e12 + v e13 + v e14 + v e15 + v e23 + v e24 + v e25 + v e34 + v e35 + v e45

def complementaryOrder (v : Edge → ℚ) : Edge → ℚ
  | e12 => v e34 + v e35 + v e45
  | e13 => v e24 + v e25 + v e45
  | e14 => v e23 + v e25 + v e35
  | e15 => v e23 + v e24 + v e34
  | e23 => v e14 + v e15 + v e45
  | e24 => v e13 + v e15 + v e35
  | e25 => v e13 + v e14 + v e34
  | e34 => v e12 + v e15 + v e25
  | e35 => v e12 + v e14 + v e24
  | e45 => v e12 + v e13 + v e23

def fourOrder (v : Edge → ℚ) (e : Edge) : ℚ := v e + complementaryOrder v e

theorem sum_fourOrders (v : Edge → ℚ) :
    totalOrder (fourOrder v) = 4 * totalOrder v := by
  simp only [totalOrder, fourOrder, complementaryOrder]
  ring

theorem complementary_fourOrders (v : Edge → ℚ) (e : Edge) :
    complementaryOrder (fourOrder v) e = 2 * v e + totalOrder v := by
  cases e <;> simp only [complementaryOrder, fourOrder, totalOrder] <;> ring

theorem exists_negative_of_totalOrder_neg (v : Edge → ℚ) (h : totalOrder v < 0) :
    ∃ e, v e < 0 := by
  by_contra hn
  push Not at hn
  have h12 := hn e12
  have h13 := hn e13
  have h14 := hn e14
  have h15 := hn e15
  have h23 := hn e23
  have h24 := hn e24
  have h25 := hn e25
  have h34 := hn e34
  have h35 := hn e35
  have h45 := hn e45
  simp only [totalOrder] at h
  linarith

theorem exists_negative_fourOrder (v : Edge → ℚ) (h : totalOrder v < 0) :
    ∃ e, fourOrder v e < 0 := by
  apply exists_negative_of_totalOrder_neg
  rw [sum_fourOrders]
  linarith

/-- The squared-distance order pattern asserted in Diagram 9. -/
def diagram9Orders (a : ℚ) : Edge → ℚ
  | e12 | e13 | e23 => 2 * a
  | e14 | e25 | e45 => 0
  | e15 | e24 | e34 | e35 => -a

theorem diagram9_totalOrder (a : ℚ) : totalOrder (diagram9Orders a) = 2 * a := by
  simp only [totalOrder, diagram9Orders]
  ring

theorem diagram9_totalOrder_pos (a : ℚ) (ha : 0 < a) :
    0 < totalOrder (diagram9Orders a) := by
  rw [diagram9_totalOrder]
  linarith

theorem diagram9_unbounded_fourProducts (a : ℚ) (ha : 0 < a) :
    fourOrder (diagram9Orders a) e15 < 0 ∧ fourOrder (diagram9Orders a) e24 < 0 := by
  simp only [fourOrder, complementaryOrder, diagram9Orders]
  constructor <;> linarith
end Smale5
