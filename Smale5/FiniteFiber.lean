import Smale5.QuadraticRecovery
import Smale5.Balance
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Basic.Finite.Prod

/-!
The fixed-squared-distance fibre lemma (manuscript lines 548–578).

The proof uses quadratic coordinate recovery, finite choices of inverse
distances, and the centre-of-mass identities from the force equations.
It does not use Witt's theorem or assume the desired fibre is finite.
-/
namespace Smale5
open Edge
open scoped BigOperators

/-- Translation-free coordinates based at body 1. -/
def configurationOffsets (q : Configuration) (k : Fin 5) : ℂ × ℂ :=
  (q.z k - q.z 0, q.w k - q.w 0)

def configurationGauge (q : Configuration) : ℂ := q.z 1 - q.z 0

/-- Squared distances from body 1, with its self-distance set to zero. -/
def firstBodyDistances (s : Edge → ℂ) (k : Fin 5) : ℂ :=
  match k.val with
  | 0 => 0
  | 1 => s e12
  | 2 => s e13
  | 3 => s e14
  | _ => s e15

/-- Squared distances from body 2, with its self-distance set to zero. -/
def secondBodyDistances (s : Edge → ℂ) (k : Fin 5) : ℂ :=
  match k.val with
  | 0 => s e12
  | 1 => 0
  | 2 => s e23
  | 3 => s e24
  | _ => s e25

theorem normalized_gauge_square {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (s : Edge → ℂ)
    (hs : ∀ e, squaredDistance q e = s e) :
    configurationGauge q ^ 2 = s e12 := by
  have h12 := hs e12
  change (q.z 1 - q.z 0) * (q.w 1 - q.w 0) = s e12 at h12
  rw [← h.gauge] at h12
  simpa only [configurationGauge, pow_two] using h12

/-- The two relevant distance equations hold for every offset, including
those of the first and second bodies. -/
theorem normalized_offset_constraints {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (s : Edge → ℂ)
    (hs : ∀ e, squaredDistance q e = s e) :
    ∀ k, (configurationOffsets q k).1 * (configurationOffsets q k).2 =
        firstBodyDistances s k ∧
      ((configurationOffsets q k).1 - configurationGauge q) *
        ((configurationOffsets q k).2 - configurationGauge q) = secondBodyDistances s k := by
  have hfirst : ∀ k, (configurationOffsets q k).1 * (configurationOffsets q k).2 =
      firstBodyDistances s k := by
    intro k
    fin_cases k
    · simp [configurationOffsets, firstBodyDistances]
    · simpa [configurationOffsets, firstBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e12
    · simpa [configurationOffsets, firstBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e13
    · simpa [configurationOffsets, firstBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e14
    · simpa [configurationOffsets, firstBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e15
  have hsecond : ∀ k, (q.z k - q.z 1) * (q.w k - q.w 1) =
      secondBodyDistances s k := by
    intro k
    fin_cases k
    · change (q.z 0 - q.z 1) * (q.w 0 - q.w 1) = s e12
      calc
        (q.z 0 - q.z 1) * (q.w 0 - q.w 1) =
            (q.z 1 - q.z 0) * (q.w 1 - q.w 0) := by ring
        _ = s e12 := hs e12
    · simp [secondBodyDistances]
    · simpa [secondBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e23
    · simpa [secondBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e24
    · simpa [secondBodyDistances, squaredDistance, Edge.left, Edge.right] using hs e25
  intro k
  constructor
  · exact hfirst k
  · dsimp only [configurationOffsets, configurationGauge]
    have hz : (q.z k - q.z 0) - (q.z 1 - q.z 0) = q.z k - q.z 1 := by ring
    have hw : (q.w k - q.w 0) - (q.z 1 - q.z 0) = q.w k - q.w 1 := by
      rw [h.gauge]
      ring
    rw [hz, hw]
    exact hsecond k

/-- Nonzero total mass makes centered coordinates recoverable from offsets. -/
theorem centered_offsets_injective {K : Type*} [Field K]
    {Index : Type*} [Fintype Index] (base : Index) (m x y : Index → K)
    (mass_ne_zero : (∑ k, m k) ≠ 0)
    (hx : (∑ k, m k * x k) = 0) (hy : (∑ k, m k * y k) = 0)
    (hoffsets : ∀ k, x k - x base = y k - y base) : x = y := by
  let d : K := x base - y base
  have hxy : ∀ k, x k = y k + d := by
    intro k
    dsimp only [d]
    linear_combination hoffsets k
  have hsum : (∑ k, m k) * d = 0 := by
    calc
      (∑ k, m k) * d = ∑ k, m k * d := by rw [Finset.sum_mul]
      _ = ∑ k, (m k * x k - m k * y k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hxy k]
        ring
      _ = (∑ k, m k * x k) - (∑ k, m k * y k) := by rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hx, hy, sub_self]
  have hd : d = 0 := (mul_eq_zero.mp hsum).resolve_left mass_ne_zero
  funext k
  rw [hxy k, hd, add_zero]

private theorem configuration_eq_of_coordinates {q r : Configuration}
    (hz : q.z = r.z) (hw : q.w = r.w) (hd : q.delta = r.delta) : q = r := by
  cases q
  cases r
  cases hz
  cases hw
  cases hd
  rfl

/-- The offset/inverse-distance record is injective on normalized solutions
when the total mass is nonzero. -/
theorem normalized_offsets_delta_injective {m : Fin 5 → ℝ}
    (mass_ne_zero : (∑ k : Fin 5, (m k : ℂ)) ≠ 0)
    {q r : Configuration} (hq : IsNormalized m q) (hr : IsNormalized m r)
    (hoffsets : configurationOffsets q = configurationOffsets r)
    (hdelta : q.delta = r.delta) : q = r := by
  have hz : q.z = r.z := centered_offsets_injective 0 (fun k => (m k : ℂ)) q.z r.z
    mass_ne_zero (normalized_centerOfMass_z hq) (normalized_centerOfMass_z hr) (by
      intro k
      exact congrArg Prod.fst (congrFun hoffsets k))
  have hw : q.w = r.w := centered_offsets_injective 0 (fun k => (m k : ℂ)) q.w r.w
    mass_ne_zero (normalized_centerOfMass_w hq) (normalized_centerOfMass_w hr) (by
      intro k
      exact congrArg Prod.snd (congrFun hoffsets k))
  exact configuration_eq_of_coordinates hz hw hdelta

/-- Fixed nonzero squared distances determine finitely many normalized
configurations for positive masses. This is the manuscript's finite-fibre lemma. -/
theorem finite_normalized_fixed_distances (m : Fin 5 → ℝ)
    (hm : PositiveMasses m) (s : Edge → ℂ) (hsne : ∀ e, s e ≠ 0) :
    {q : Configuration | IsNormalized m q ∧ ∀ e, squaredDistance q e = s e}.Finite := by
  classical
  let S : Set Configuration :=
    {q | IsNormalized m q ∧ ∀ e, squaredDistance q e = s e}
  let gaugeRoots : Set ℂ := {t | t ^ 2 = s e12}
  let offsetChoices (t : ℂ) : Set (Fin 5 → ℂ × ℂ) :=
    {a | ∀ k, (a k).1 * (a k).2 = firstBodyDistances s k ∧
      ((a k).1 - t) * ((a k).2 - t) = secondBodyDistances s k}
  let allOffsets : Set (Fin 5 → ℂ × ℂ) := ⋃ t ∈ gaugeRoots, offsetChoices t
  let deltaChoices : Set (Edge → ℂ) := {d | ∀ e, d e ^ 2 = (s e)⁻¹}
  let encode (q : Configuration) := (configurationOffsets q, q.delta)
  have hGaugeFinite : gaugeRoots.Finite := finite_square_roots (s e12)
  have hOffsetsFinite : allOffsets.Finite := hGaugeFinite.biUnion (by
    intro t ht
    apply finite_offset_families t (firstBodyDistances s) (secondBodyDistances s)
    intro hzero
    have hsq : t ^ 2 = s e12 := ht
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsq
    exact hsne e12 hsq.symm)
  have hDeltaFinite : deltaChoices.Finite :=
    finite_square_root_families (fun e => (s e)⁻¹)
  have hImage : (encode '' S).Finite := by
    apply (hOffsetsFinite.prod hDeltaFinite).subset
    rintro _ ⟨q, hq, rfl⟩
    constructor
    · change configurationOffsets q ∈ ⋃ t ∈ gaugeRoots, offsetChoices t
      apply Set.mem_iUnion.mpr
      refine ⟨configurationGauge q, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨normalized_gauge_square hq.1 s hq.2, ?_⟩
      exact normalized_offset_constraints hq.1 s hq.2
    · change ∀ e, q.delta e ^ 2 = (s e)⁻¹
      intro e
      have hc := hq.1.distance_constraint e
      rw [hq.2 e] at hc
      have hd : q.delta e ^ 2 = 1 / s e := (eq_div_iff (hsne e)).2 hc
      simpa only [one_div] using hd
  have mass_pos : 0 < ∑ k : Fin 5, m k := by
    apply Finset.sum_pos
    · intro k hk
      exact hm k
    · exact Finset.univ_nonempty
  have mass_ne_zero : (∑ k : Fin 5, (m k : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt mass_pos)
  apply hImage.of_finite_image
  intro q hq r hr heq
  exact normalized_offsets_delta_injective mass_ne_zero hq.1 hr.1
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)

end Smale5


