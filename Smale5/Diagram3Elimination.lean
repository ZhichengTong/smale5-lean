import Smale5.Edges

/-!
# Diagram 3: the polynomial elimination step

This file checks only the exact algebra in manuscript `cor:d3-order3`
(lines 2686–2693). It does not prove that the analytic jet obstruction vanishes,
that a boundary point gives the two polynomial equations, or that the resulting
mass relation excludes a germ. Those are separate obligations.

The abstract variables `x`, `y`, `z` stand for the cubes of masses 1, 2, 4;
`q` stands for the manuscript's positive quantity Q = m₅² M.
-/

namespace Smale5.Diagram3

variable {R : Type*} [CommRing R]

def n1 (x y z q : R) : R :=
  (x * y * z - q * (x ^ 2 + y * z)) ^ 2 - 4 * q ^ 2 * x ^ 2 * y * z

def n2 (x y z q : R) : R :=
  (x * y * z - q * x * (y + z)) ^ 2 - 4 * q ^ 2 * x ^ 2 * y * z

def obstruction (x y z q : R) : R :=
  (x - y) * (x - z) * (2 * x * y * z - q * (x + y) * (x + z))

/-- Exact polynomial identity; no sign or nonzero hypotheses are needed. -/
theorem elimination_identity (x y z q : R) :
    n1 x y z q - n2 x y z q + q * obstruction x y z q = 0 := by
  unfold n1 n2 obstruction
  ring

/-- If the two computed equations are supplied and Q is nonzero, their
algebraic consequence S = 0 follows. The equations themselves are hypotheses. -/
theorem obstruction_of_two_equations [IsDomain R] (x y z q : R)
    (hq : q ≠ 0) (h1 : n1 x y z q = 0) (h2 : n2 x y z q = 0) :
    obstruction x y z q = 0 := by
  have hprod : q * obstruction x y z q = 0 := by
    simpa only [h1, h2, sub_self, zero_add] using elimination_identity x y z q
  exact (mul_eq_zero.mp hprod).resolve_left hq

/-- The manuscript's N₁, with the masses and Q as independent inputs. -/
def massN1 (m1 m2 m4 q : R) : R :=
  ((m1 * m2 * m4) ^ 3 - q * (m1 ^ 6 + m2 ^ 3 * m4 ^ 3)) ^ 2 -
    4 * q ^ 2 * m1 ^ 6 * m2 ^ 3 * m4 ^ 3

/-- The manuscript's N₂. -/
def massN2 (m1 m2 m4 q : R) : R :=
  ((m1 * m2 * m4) ^ 3 - q * m1 ^ 3 * (m2 ^ 3 + m4 ^ 3)) ^ 2 -
    4 * q ^ 2 * m1 ^ 6 * m2 ^ 3 * m4 ^ 3

/-- The manuscript's factor S. -/
def massObstruction (m1 m2 m4 q : R) : R :=
  (m1 ^ 3 - m2 ^ 3) * (m1 ^ 3 - m4 ^ 3) *
    (2 * (m1 * m2 * m4) ^ 3 - q * (m1 ^ 3 + m2 ^ 3) * (m1 ^ 3 + m4 ^ 3))

theorem mass_elimination_identity (m1 m2 m4 q : R) :
    massN1 m1 m2 m4 q - massN2 m1 m2 m4 q +
      q * massObstruction m1 m2 m4 q = 0 := by
  unfold massN1 massN2 massObstruction
  ring

theorem mass_obstruction_of_two_equations [IsDomain R] (m1 m2 m4 q : R)
    (hq : q ≠ 0) (h1 : massN1 m1 m2 m4 q = 0)
    (h2 : massN2 m1 m2 m4 q = 0) :
    massObstruction m1 m2 m4 q = 0 := by
  have hprod : q * massObstruction m1 m2 m4 q = 0 := by
    simpa only [h1, h2, sub_self, zero_add] using mass_elimination_identity m1 m2 m4 q
  exact (mul_eq_zero.mp hprod).resolve_left hq

end Smale5.Diagram3
