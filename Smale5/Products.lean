import Smale5.Edges

/-! Exact polynomial identities for the four-products; no geometric assumptions. -/
namespace Smale5
open Edge

variable {R : Type*} [CommSemiring R]

def totalProduct (s : Edge → R) : R :=
  s e12 * s e13 * s e14 * s e15 * s e23 * s e24 * s e25 * s e34 * s e35 * s e45

def complementaryProduct (s : Edge → R) : Edge → R
  | e12 => s e34 * s e35 * s e45
  | e13 => s e24 * s e25 * s e45
  | e14 => s e23 * s e25 * s e35
  | e15 => s e23 * s e24 * s e34
  | e23 => s e14 * s e15 * s e45
  | e24 => s e13 * s e15 * s e35
  | e25 => s e13 * s e14 * s e34
  | e34 => s e12 * s e15 * s e25
  | e35 => s e12 * s e14 * s e24
  | e45 => s e12 * s e13 * s e23

def fourProduct (s : Edge → R) (e : Edge) : R :=
  s e * complementaryProduct s e

/-- Manuscript Lemma `lem:total-product`. -/
theorem product_fourProducts (s : Edge → R) :
    totalProduct (fourProduct s) = totalProduct s ^ 4 := by
  simp only [totalProduct, fourProduct, complementaryProduct]
  ring

/-- A direct identity replacing the Petersen spectral calculation. -/
theorem complementary_fourProducts (s : Edge → R) (e : Edge) :
    complementaryProduct (fourProduct s) e = s e ^ 2 * totalProduct s := by
  cases e <;> simp only [complementaryProduct, fourProduct, totalProduct] <;> ring

/-- A denominator-free inverse relation; exponent 8 suffices instead of 128. -/
theorem eighthPower_recovery (s : Edge → R) (e : Edge) :
    s e ^ 8 * totalProduct (fourProduct s) =
      complementaryProduct (fourProduct s) e ^ 4 := by
  rw [product_fourProducts, complementary_fourProducts]
  ring

section Nonzero
variable [NoZeroDivisors R]

theorem totalProduct_ne_zero (s : Edge → R) (h : ∀ e, s e ≠ 0) :
    totalProduct s ≠ 0 := by
  simp [totalProduct, h]

theorem fourProduct_ne_zero (s : Edge → R) (h : ∀ e, s e ≠ 0) (e : Edge) :
    fourProduct s e ≠ 0 := by
  cases e <;> simp [fourProduct, complementaryProduct, h]
end Nonzero
end Smale5
