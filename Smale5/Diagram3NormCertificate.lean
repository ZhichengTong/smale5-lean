import Smale5.Configuration

/-! Exact algebra extracted from the public N5 P66 certificate.
Source: hitchenzhe/smale-n5-paper, commit 7389c875bd3d8c5fa01617b4d27a3562118b8081,
verification/certificates/d3_fifth_order_norm.json.
The coefficient vector is DATA, not an assumed proof. Lean checks its
factorization and strict positivity below. An exact positive-coefficient
decomposition replaces the negative-argument Sturm check. This does not
prove the G5-to-L jet identity. -/
namespace Smale5.Diagram3Norm
set_option maxHeartbeats 4000000

section Algebra
variable {R : Type*} [CommRing R]

def f4 (a b : R) : R := a^4 + a^3*b + a^2*b^2 + a*b^3 + b^4
def f2 (a b : R) : R := a^2 + a*b + b^2
def f8 (a b : R) : R := a^8 + a^6*b^2 + a^4*b^4 + a^2*b^6 + b^8

def p66 (a b : R) : R :=
    1 * a ^ 66 * b ^ 0 +
    9 * a ^ 65 * b ^ 1 +
    51 * a ^ 64 * b ^ 2 +
    219 * a ^ 63 * b ^ 3 +
    783 * a ^ 62 * b ^ 4 +
    2430 * a ^ 61 * b ^ 5 +
    6734 * a ^ 60 * b ^ 6 +
    16956 * a ^ 59 * b ^ 7 +
    39321 * a ^ 58 * b ^ 8 +
    84823 * a ^ 57 * b ^ 9 +
    171642 * a ^ 56 * b ^ 10 +
    328020 * a ^ 55 * b ^ 11 +
    595544 * a ^ 54 * b ^ 12 +
    1032381 * a ^ 53 * b ^ 13 +
    1716231 * a ^ 52 * b ^ 14 +
    2745980 * a ^ 51 * b ^ 15 +
    4241397 * a ^ 50 * b ^ 16 +
    6339153 * a ^ 49 * b ^ 17 +
    9184702 * a ^ 48 * b ^ 18 +
    12918708 * a ^ 47 * b ^ 19 +
    17659359 * a ^ 46 * b ^ 20 +
    23481038 * a ^ 45 * b ^ 21 +
    30393384 * a ^ 44 * b ^ 22 +
    38322291 * a ^ 43 * b ^ 23 +
    47097818 * a ^ 42 * b ^ 24 +
    56450631 * a ^ 41 * b ^ 25 +
    66024102 * a ^ 40 * b ^ 26 +
    75402964 * a ^ 39 * b ^ 27 +
    84158037 * a ^ 38 * b ^ 28 +
    91890756 * a ^ 37 * b ^ 29 +
    98264701 * a ^ 36 * b ^ 30 +
    103014636 * a ^ 35 * b ^ 31 +
    105946389 * a ^ 34 * b ^ 32 +
    106937618 * a ^ 33 * b ^ 33 +
    105946389 * a ^ 32 * b ^ 34 +
    103014636 * a ^ 31 * b ^ 35 +
    98264701 * a ^ 30 * b ^ 36 +
    91890756 * a ^ 29 * b ^ 37 +
    84158037 * a ^ 28 * b ^ 38 +
    75402964 * a ^ 27 * b ^ 39 +
    66024102 * a ^ 26 * b ^ 40 +
    56450631 * a ^ 25 * b ^ 41 +
    47097818 * a ^ 24 * b ^ 42 +
    38322291 * a ^ 23 * b ^ 43 +
    30393384 * a ^ 22 * b ^ 44 +
    23481038 * a ^ 21 * b ^ 45 +
    17659359 * a ^ 20 * b ^ 46 +
    12918708 * a ^ 19 * b ^ 47 +
    9184702 * a ^ 18 * b ^ 48 +
    6339153 * a ^ 17 * b ^ 49 +
    4241397 * a ^ 16 * b ^ 50 +
    2745980 * a ^ 15 * b ^ 51 +
    1716231 * a ^ 14 * b ^ 52 +
    1032381 * a ^ 13 * b ^ 53 +
    595544 * a ^ 12 * b ^ 54 +
    328020 * a ^ 11 * b ^ 55 +
    171642 * a ^ 10 * b ^ 56 +
    84823 * a ^ 9 * b ^ 57 +
    39321 * a ^ 8 * b ^ 58 +
    16956 * a ^ 7 * b ^ 59 +
    6734 * a ^ 6 * b ^ 60 +
    2430 * a ^ 5 * b ^ 61 +
    783 * a ^ 4 * b ^ 62 +
    219 * a ^ 3 * b ^ 63 +
    51 * a ^ 2 * b ^ 64 +
    9 * a ^ 1 * b ^ 65 +
    1 * a ^ 0 * b ^ 66

def core (a b : R) : R :=
  (a^2+b^2) * f4 a b ^ 3 * f8 a b - 2*a^6*b^6*(a^2-b^2)^2*f2 a b ^ 3

/-- The 67 published coefficients equal the exact cleared double cubic norm factor. -/
theorem p66_factorization (a b : R) :
    core a b ^ 3 - 54*a^16*b^16*(a^2+b^2)^2*f4 a b ^ 6*f2 a b ^ 3 = p66 a b := by
  unfold core f4 f2 f8 p66
  ring

/-- Division-free form of the certificate's complete homogeneous norm factorization. -/
theorem cleared_nine_root_norm (a b : R) :
    ((a^10-b^10)*(a^2+b^2)*f4 a b ^ 3 - 2*a^6*b^6*(a^2-b^2)^3*f2 a b ^ 3)^3 -
      54*a^16*b^16*(a^2+b^2)^2*f4 a b ^ 6*(a^2-b^2)^3*f2 a b ^ 3 =
      (a-b)^3*(a+b)^3*p66 a b := by
  rw [← p66_factorization]
  unfold core f4 f2 f8
  ring

/-- Algebraic vanishing of the iterated cubic norm at an actual common-root label. -/
theorem cubic_norm_vanishes (A B C x y r s : R)
    (hx : x^3=r) (hy : y^3=s) (hL : A*x+B*y+C=0) :
    (A^3*r+B^3*s+C^3)^3 - 27*A^3*B^3*C^3*r*s = 0 := by
  have hsum : (A*x)^3+(B*y)^3+C^3=3*(A*x)*(B*y)*C := by
    linear_combination ((A*x)^2+(B*y)^2+C^2-(A*x)*(B*y)-(B*y)*C-C*(A*x)) * hL
  calc
    _ = ((A*x)^3+(B*y)^3+C^3)^3 - 27*(A*x)^3*(B*y)^3*C^3 := by
      simp only [mul_pow, hx, hy]
      ring
    _ = 0 := by rw [hsum]; ring
/-- Positive coefficient decomposition replacing the external negative-argument Sturm computation. -/
def negativeRepresentation (a b : R) : R :=
    1 * (a*b) ^ 0 * ((a-b)^2) ^ 33 +
    57 * (a*b) ^ 1 * ((a-b)^2) ^ 32 +
    1554 * (a*b) ^ 2 * ((a-b)^2) ^ 31 +
    26977 * (a*b) ^ 3 * ((a-b)^2) ^ 30 +
    334917 * (a*b) ^ 4 * ((a-b)^2) ^ 29 +
    3166242 * (a*b) ^ 5 * ((a-b)^2) ^ 28 +
    23698711 * (a*b) ^ 6 * ((a-b)^2) ^ 27 +
    144157887 * (a*b) ^ 7 * ((a-b)^2) ^ 26 +
    725944176 * (a*b) ^ 8 * ((a-b)^2) ^ 25 +
    3067288103 * (a*b) ^ 9 * ((a-b)^2) ^ 24 +
    10982721297 * (a*b) ^ 10 * ((a-b)^2) ^ 23 +
    33571930248 * (a*b) ^ 11 * ((a-b)^2) ^ 22 +
    88086999861 * (a*b) ^ 12 * ((a-b)^2) ^ 21 +
    199159285527 * (a*b) ^ 13 * ((a-b)^2) ^ 20 +
    389019925398 * (a*b) ^ 14 * ((a-b)^2) ^ 19 +
    657480777637 * (a*b) ^ 15 * ((a-b)^2) ^ 18 +
    962004924486 * (a*b) ^ 16 * ((a-b)^2) ^ 17 +
    1218211809009 * (a*b) ^ 17 * ((a-b)^2) ^ 16 +
    1333639686113 * (a*b) ^ 18 * ((a-b)^2) ^ 15 +
    1259818179312 * (a*b) ^ 19 * ((a-b)^2) ^ 14 +
    1024192946691 * (a*b) ^ 20 * ((a-b)^2) ^ 13 +
    714117051641 * (a*b) ^ 21 * ((a-b)^2) ^ 12 +
    425219813880 * (a*b) ^ 22 * ((a-b)^2) ^ 11 +
    215101260075 * (a*b) ^ 23 * ((a-b)^2) ^ 10 +
    91852019089 * (a*b) ^ 24 * ((a-b)^2) ^ 9 +
    32850122688 * (a*b) ^ 25 * ((a-b)^2) ^ 8 +
    9742570353 * (a*b) ^ 26 * ((a-b)^2) ^ 7 +
    2365032453 * (a*b) ^ 27 * ((a-b)^2) ^ 6 +
    461573364 * (a*b) ^ 28 * ((a-b)^2) ^ 5 +
    70566861 * (a*b) ^ 29 * ((a-b)^2) ^ 4 +
    8121073 * (a*b) ^ 30 * ((a-b)^2) ^ 3 +
    658812 * (a*b) ^ 31 * ((a-b)^2) ^ 2 +
    33348 * (a*b) ^ 32 * ((a-b)^2) ^ 1 +
    784 * (a*b) ^ 33 * ((a-b)^2) ^ 0

/-- The decomposition is an exact polynomial identity, checked by the Lean kernel. -/
theorem p66_negative_decomposition (a b : R) : p66 a (-b) = negativeRepresentation a b := by
  unfold p66 negativeRepresentation
  ring
end Algebra

section Field
variable {K : Type*} [Field K]

def coeffA (a b : K) : K := a^2*f4 a b
def coeffB (a b : K) : K := -(b^4/a^2)*f4 a b
def coeffC (a b : K) : K := -b^2*(a^2-b^2)*f2 a b
def rootR (a b : K) : K := (a^2+b^2)/(2*a^2)
def rootS (a b : K) : K := (a^2+b^2)/(2*b^2)

/-- The rational norm formula, with every denominator hypothesis explicit. -/
theorem rational_nine_root_norm [CharZero K] (a b : K) (ha : a≠0) (_hb : b≠0) :
    ((coeffA a b)^3*rootR a b + (coeffB a b)^3*rootS a b + (coeffC a b)^3)^3 -
      27*(coeffA a b)^3*(coeffB a b)^3*(coeffC a b)^3*rootR a b*rootS a b =
      (a-b)^3*(a+b)^3*p66 a b/(8*a^18) := by
  rw [← p66_factorization]
  unfold coeffA coeffB coeffC rootR rootS core f4 f2 f8
  field_simp
  ring

/-- Nonvanishing at all cubic-root labels follows from the checked norm factor. -/
theorem root_form_ne_zero [CharZero K] (a b x y : K) (ha : a≠0) (hb : b≠0)
    (hminus : a-b≠0) (hplus : a+b≠0) (hp : p66 a b≠0)
    (hx : x^3=rootR a b) (hy : y^3=rootS a b) :
    coeffA a b*x+coeffB a b*y+coeffC a b≠0 := by
  intro hz
  have hn := cubic_norm_vanishes (coeffA a b) (coeffB a b) (coeffC a b) x y
    (rootR a b) (rootS a b) hx hy hz
  rw [rational_nine_root_norm a b ha hb] at hn
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hminus)
    (pow_ne_zero _ hplus)) hp) (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))) hn
end Field

/-- The displayed P66 is strictly positive on the positive quadrant. -/
theorem p66_pos (a b : ℝ) (ha : 0<a) (hb : 0<b) : 0 < p66 a b := by
  unfold p66
  positivity

/-- In particular the positive-argument norm factor cannot vanish away from a=b. -/
theorem positive_norm_factor_ne_zero (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a≠b) :
    (a-b)^3*(a+b)^3*p66 a b ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hab))
    (pow_ne_zero _ (ne_of_gt (add_pos ha hb)))) (ne_of_gt (p66_pos a b ha hb))

/-- The same integer coefficient data commute with the real-to-complex embedding. -/
theorem p66_ofReal (a b : ℝ) : p66 (a : ℂ) (b : ℂ) = ((p66 a b : ℝ) : ℂ) := by
  unfold p66
  push_cast
  ring

/-- The positive-family obstruction is nonzero for every pair of complex cubic roots. -/
theorem positive_family_root_form_ne_zero (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a≠b)
    (x y : ℂ) (hx : x^3=rootR (a : ℂ) (b : ℂ))
    (hy : y^3=rootS (a : ℂ) (b : ℂ)) :
    coeffA (a : ℂ) (b : ℂ)*x + coeffB (a : ℂ) (b : ℂ)*y + coeffC (a : ℂ) (b : ℂ)≠0 := by
  apply root_form_ne_zero (a : ℂ) (b : ℂ) x y
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ha))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hb))
  · exact_mod_cast (sub_ne_zero.mpr hab)
  · exact_mod_cast (ne_of_gt (add_pos ha hb))
  · rw [p66_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (p66_pos a b ha hb))
  · exact hx
  · exact hy

/-- P66(a,-b)>0 for all positive a,b, by a finite exact sum of nonnegative terms
with strictly positive final term 784*(a*b)^33. No Sturm algorithm is assumed. -/
theorem p66_negative_pos (a b : ℝ) (ha : 0<a) (hb : 0<b) : 0 < p66 a (-b) := by
  rw [p66_negative_decomposition]
  unfold negativeRepresentation
  positivity

/-- The negative-family obstruction is nonzero at every complex cubic-root label. -/
theorem negative_family_root_form_ne_zero (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a≠b)
    (x y : ℂ) (hx : x^3=rootR (a : ℂ) (-b : ℂ))
    (hy : y^3=rootS (a : ℂ) (-b : ℂ)) :
    coeffA (a : ℂ) (-b : ℂ)*x + coeffB (a : ℂ) (-b : ℂ)*y + coeffC (a : ℂ) (-b : ℂ)≠0 := by
  apply root_form_ne_zero (a : ℂ) (-b : ℂ) x y
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ha))
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hb)))
  · have h : (a : ℂ)+(b : ℂ)≠0 := by exact_mod_cast (ne_of_gt (add_pos ha hb))
    simpa only [sub_neg_eq_add] using h
  · have h : (a : ℂ)-(b : ℂ)≠0 := by exact_mod_cast (sub_ne_zero.mpr hab)
    simpa only [sub_eq_add_neg] using h
  · have h := Complex.ofReal_ne_zero.mpr (ne_of_gt (p66_negative_pos a b ha hb))
    simpa only [Complex.ofReal_neg, ← p66_ofReal] using h
  · exact hx
  · exact hy

end Smale5.Diagram3Norm
