import Mathlib.Tactic

/-! The ten unordered pairs of five labelled bodies. Labels follow the manuscript. -/
namespace Smale5

inductive Edge where
  | e12 | e13 | e14 | e15 | e23 | e24 | e25 | e34 | e35 | e45
  deriving DecidableEq, Repr

open Edge

instance edgeFintype : Fintype Edge :=
  ⟨{e12, e13, e14, e15, e23, e24, e25, e34, e35, e45}, by
    intro e; cases e <;> simp⟩

def Edge.left : Edge → Fin 5
  | e12 | e13 | e14 | e15 => 0
  | e23 | e24 | e25 => 1
  | e34 | e35 => 2
  | e45 => 3

def Edge.right : Edge → Fin 5
  | e12 => 1
  | e13 | e23 => 2
  | e14 | e24 | e34 => 3
  | e15 | e25 | e35 | e45 => 4

theorem Edge.left_ne_right (e : Edge) : e.left ≠ e.right := by
  cases e <;> decide

def edgeFor (i j : Fin 5) : Option Edge :=
  match i.val, j.val with
  | 0, 1 | 1, 0 => some e12
  | 0, 2 | 2, 0 => some e13
  | 0, 3 | 3, 0 => some e14
  | 0, 4 | 4, 0 => some e15
  | 1, 2 | 2, 1 => some e23
  | 1, 3 | 3, 1 => some e24
  | 1, 4 | 4, 1 => some e25
  | 2, 3 | 3, 2 => some e34
  | 2, 4 | 4, 2 => some e35
  | 3, 4 | 4, 3 => some e45
  | _, _ => none

theorem edgeFor_symm (i j : Fin 5) : edgeFor i j = edgeFor j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem edgeFor_self (i : Fin 5) : edgeFor i i = none := by
  fin_cases i <;> rfl

end Smale5
