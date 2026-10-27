import Smale5.FourProductFiber
import Mathlib.Basic.Complex.BigOperators

/-!
Bridge to Tejasvi Singh Tomar's public Lean formalization (Zenodo 23202861).
The copied interface definitions in namespace `Upstream` reproduce
CC5Full/System.lean, Apache-2.0, with only the namespace changed. The affine
force argument is adapted from CC5Full/Theory/RealPos.lean by the same author.
No upstream main theorem is assumed as an axiom or imported into this checked
module. The adapter theorem names any upstream finiteness premise explicitly.
-/
namespace Smale5
open scoped BigOperators

namespace Upstream
abbrev Masses := Fin 5 → ℝ
abbrev Conf := Fin 5 → ℂ

def CollisionFree (q : Conf) : Prop := ∀ i j, i ≠ j → q i ≠ q j

def IsCC (m : Masses) (q : Conf) : Prop :=
  CollisionFree q ∧ ∃ (lam : ℝ) (c : ℂ), ∀ i,
    ((lam * m i : ℝ) : ℂ) * (q i - c) =
      ∑ j ∈ Finset.univ.erase i, ((m i * m j / ‖q i - q j‖ ^ 3 : ℝ) : ℂ) * (q i - q j)

def Similar (q q' : Conf) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ((∀ i, q' i = a * q i + b) ∨
    (∀ i, q' i = a * starRingEnd ℂ (q i) + b))

def FinitelyManyCC (m : Masses) : Prop :=
  ∃ F : Finset Conf, ∀ q, IsCC m q → ∃ q' ∈ F, Similar q' q

def MainTheorem : Prop := ∀ m : Masses, (∀ i, 0 < m i) → FinitelyManyCC m

/-- An auxiliary normalized Newton equation used only inside the adapter. -/
def NormEq (m : Masses) (q : Conf) : Prop :=
  ∀ k, q k = ∑ l ∈ Finset.univ.erase k,
    ((m l / ‖q k - q l‖ ^ 3 : ℝ) : ℂ) * (q k - q l)
end Upstream

private theorem pair_lookup (i j : Fin 5) (hij : i ≠ j) :
    ∃ e : Edge, edgeFor i j = some e ∧
      ((e.left = i ∧ e.right = j) ∨ (e.left = j ∧ e.right = i)) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [edgeFor, Edge.left, Edge.right]

theorem normalized_collisionFree {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) : Upstream.CollisionFree q.z := by
  intro i j hij heq
  obtain ⟨e, _, he | he⟩ := pair_lookup i j hij
  · have hs := squaredDistance_ne_zero h e
    apply hs
    simp [squaredDistance, he.1, he.2, heq]
  · have hs := squaredDistance_ne_zero h e
    apply hs
    simp [squaredDistance, he.1, he.2, heq]

theorem real_squaredDistance_norm (q : Configuration) (hr : IsReal q) (e : Edge) :
    squaredDistance q e = ((‖q.z e.right - q.z e.left‖ ^ 2 : ℝ) : ℂ) := by
  have hw : q.w e.right - q.w e.left = star (q.z e.right - q.z e.left) := by
    rw [star_sub, hr e.right, hr e.left]
  unfold squaredDistance
  rw [hw, Complex.star_def, Complex.mul_conj, Complex.sq_norm]

theorem positive_delta_inverse_norm {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsPositiveNormalized m q) (e : Edge) :
    q.delta e = ((1 / ‖q.z e.right - q.z e.left‖ : ℝ) : ℂ) := by
  obtain ⟨d, hd, hδ⟩ := h.2.2 e
  have hc := h.1.distance_constraint e
  rw [hδ, real_squaredDistance_norm q h.2.1 e] at hc
  have hs : d ^ 2 * ‖q.z e.right - q.z e.left‖ ^ 2 = 1 := by exact_mod_cast hc
  have hp : d * ‖q.z e.right - q.z e.left‖ = 1 := by
    apply (pow_left_inj₀ (mul_nonneg hd.le (norm_nonneg _)) zero_le_one two_ne_zero).mp
    rw [mul_pow, hs, one_pow]
  have hn : ‖q.z e.right - q.z e.left‖ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hp
    exact zero_ne_one hp
  have heq : d = 1 / ‖q.z e.right - q.z e.left‖ := (eq_div_iff hn).2 hp
  rw [hδ, heq]

theorem positive_inversePair_inverse_norm {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsPositiveNormalized m q) (i j : Fin 5) (hij : i ≠ j) :
    q.inversePair i j = ((1 / ‖q.z i - q.z j‖ : ℝ) : ℂ) := by
  obtain ⟨e, he, hends | hends⟩ := pair_lookup i j hij
  · simp only [Configuration.inversePair, he]
    rw [positive_delta_inverse_norm h e, hends.1, hends.2, norm_sub_rev]
  · simp only [Configuration.inversePair, he]
    rw [positive_delta_inverse_norm h e, hends.1, hends.2]

theorem positive_normalized_normEq {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsPositiveNormalized m q) : Upstream.NormEq m q.z := by
  intro k
  conv_lhs => rw [h.1.z_balance k]
  have he : (∑ l ∈ Finset.univ.erase k,
      (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l)) =
      ∑ l : Fin 5, (m l : ℂ) * q.inversePair k l ^ 3 * (q.z k - q.z l) := by
    exact Finset.sum_erase Finset.univ (by simp)
  rw [← he]
  apply Finset.sum_congr rfl
  intro l hl
  rw [positive_inversePair_inverse_norm h k l (Finset.ne_of_mem_erase hl).symm]
  push_cast
  ring

theorem positive_normalized_isCC {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsPositiveNormalized m q) : Upstream.IsCC m q.z := by
  refine ⟨normalized_collisionFree h.1, 1, 0, ?_⟩
  intro k
  simp only [one_mul, sub_zero]
  conv_lhs => rw [positive_normalized_normEq h k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  push_cast
  ring

end Smale5



namespace Smale5.Upstream
open scoped BigOperators

/-- Similarity is symmetric, including the allowed reflection. -/
theorem similar_symm {q r : Conf} (h : Similar q r) : Similar r q := by
  obtain ⟨a, b, ha, h | h⟩ := h
  · refine ⟨a⁻¹, -(a⁻¹ * b), inv_ne_zero ha, Or.inl ?_⟩
    intro i
    rw [h i]
    field_simp
    ring
  · refine ⟨(starRingEnd ℂ a)⁻¹, -((starRingEnd ℂ a)⁻¹ * starRingEnd ℂ b),
      inv_ne_zero (by simpa using ha), Or.inr ?_⟩
    intro i
    rw [h i]
    simp only [map_add, map_mul, starRingEnd_self_apply]
    have hsa : starRingEnd ℂ a ≠ 0 := by simpa using ha
    field_simp [hsa]
    ring

/-- Similarities compose, with the two reflection parities tracked explicitly. -/
theorem similar_trans {q r s : Conf} (hqr : Similar q r) (hrs : Similar r s) : Similar q s := by
  obtain ⟨a, b, ha, h | h⟩ := hqr <;> obtain ⟨c, d, hc, g | g⟩ := hrs
  · refine ⟨c * a, c * b + d, mul_ne_zero hc ha, Or.inl ?_⟩
    intro i
    rw [g i, h i]
    ring
  · refine ⟨c * starRingEnd ℂ a, c * starRingEnd ℂ b + d,
      mul_ne_zero hc (by simpa using ha), Or.inr ?_⟩
    intro i
    rw [g i, h i, map_add, map_mul]
    ring
  · refine ⟨c * a, c * b + d, mul_ne_zero hc ha, Or.inr ?_⟩
    intro i
    rw [g i, h i]
    ring
  · refine ⟨c * starRingEnd ℂ a, c * starRingEnd ℂ b + d,
      mul_ne_zero hc (by simpa using ha), Or.inl ?_⟩
    intro i
    rw [g i, h i, map_add, map_mul, starRingEnd_self_apply]
    ring

/-- Conjugation preserves the normalized real-coefficient Newton equations. -/
theorem normEq_conj {m : Masses} {q : Conf} (h : NormEq m q) :
    NormEq m (fun k => starRingEnd ℂ (q k)) := by
  intro k
  have hn : ∀ i j, ‖starRingEnd ℂ (q i) - starRingEnd ℂ (q j)‖ = ‖q i - q j‖ := by
    intro i j
    rw [← map_sub, Complex.norm_conj]
  simp only [hn]
  have he := congrArg (starRingEnd ℂ) (h k)
  simpa only [map_sum, map_mul, map_sub, Complex.conj_ofReal] using he

/-- Homogeneity of the Newton force under an affine complex similarity. -/
theorem affine_rhs (m : Masses) (q r : Conf) (a b : ℂ)
    (hr : ∀ k, r k = a * q k + b) (k : Fin 5) :
    (∑ l ∈ Finset.univ.erase k, ((m l / ‖r k - r l‖ ^ 3 : ℝ) : ℂ) * (r k - r l)) =
      a / ((‖a‖ ^ 3 : ℝ) : ℂ) *
        ∑ l ∈ Finset.univ.erase k, ((m l / ‖q k - q l‖ ^ 3 : ℝ) : ℂ) * (q k - q l) := by
  have he : ∀ l, r k - r l = a * (q k - q l) := fun l => by rw [hr, hr]; ring
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [he, norm_mul]
  push_cast
  ring

/-- Two normalized configurations related by a similarity have unit scale. -/
theorem normEq_affine_scale_one {m : Masses} {q r : Conf}
    (hcf : CollisionFree q) (hq : NormEq m q) (hr : NormEq m r)
    {a b : ℂ} (ha : a ≠ 0) (hab : ∀ k, r k = a * q k + b) : ‖a‖ = 1 := by
  have he : ∀ k, a * q k + b = a / ((‖a‖ ^ 3 : ℝ) : ℂ) * q k := by
    intro k
    calc
      a * q k + b = r k := (hab k).symm
      _ = _ := hr k
      _ = a / ((‖a‖ ^ 3 : ℝ) : ℂ) * q k := by
        rw [affine_rhs m q r a b hab k, ← hq k]
  have hd : q 0 - q 1 ≠ 0 := sub_ne_zero.mpr (hcf 0 1 (by decide))
  have hn0 : ((‖a‖ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 3 (norm_ne_zero_iff.mpr ha)
  have hdiff : a * (q 0 - q 1) = a / ((‖a‖ ^ 3 : ℝ) : ℂ) * (q 0 - q 1) := by
    linear_combination he 0 - he 1
  have hm : (a * (q 0 - q 1)) * ((‖a‖ ^ 3 : ℝ) : ℂ) = a * (q 0 - q 1) := by
    conv_lhs => rw [hdiff]
    field_simp
  have hn3 : ((‖a‖ ^ 3 : ℝ) : ℂ) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero ha hd)
    simpa only [mul_one] using hm
  have hn3' : ‖a‖ ^ 3 = (1 : ℝ) := by exact_mod_cast hn3
  exact (pow_left_inj₀ (norm_nonneg a) zero_le_one (by decide : 3 ≠ 0)).mp (by simpa using hn3')

/-- Similar normalized configurations have the same ordinary mutual distances. -/
theorem normEq_similar_distances {m : Masses} {q r : Conf}
    (hcf : CollisionFree q) (hq : NormEq m q) (hr : NormEq m r)
    (hs : Similar q r) (i j : Fin 5) : ‖r i - r j‖ = ‖q i - q j‖ := by
  obtain ⟨a, b, ha, hab | hab⟩ := hs
  · have hn := normEq_affine_scale_one hcf hq hr ha hab
    have he : r i - r j = a * (q i - q j) := by rw [hab, hab]; ring
    rw [he, norm_mul, hn, one_mul]
  · have hcf' : CollisionFree (fun k => starRingEnd ℂ (q k)) := by
      intro k l hkl he
      apply hcf k l hkl
      exact (starRingEnd ℂ).injective he
    have hn := normEq_affine_scale_one hcf' (normEq_conj hq) hr ha hab
    have he : r i - r j = a * starRingEnd ℂ (q i - q j) := by
      rw [hab, hab, map_sub]
      ring
    rw [he, norm_mul, hn, one_mul, Complex.norm_conj]
end Smale5.Upstream

namespace Smale5
open scoped BigOperators

theorem positive_normalized_similar_squaredDistances {m : Fin 5 → ℝ} {q r : Configuration}
    (hq : IsPositiveNormalized m q) (hr : IsPositiveNormalized m r)
    (hs : Upstream.Similar q.z r.z) (e : Edge) : squaredDistance r e = squaredDistance q e := by
  rw [real_squaredDistance_norm r hr.2.1 e, real_squaredDistance_norm q hq.2.1 e]
  rw [Upstream.normEq_similar_distances (normalized_collisionFree hq.1)
    (positive_normalized_normEq hq) (positive_normalized_normEq hr) hs]

/-- Each similarity class has a finite positive normalized fibre, including reflection. -/
theorem finite_positive_normalized_similar (m : Fin 5 → ℝ) (hm : PositiveMasses m)
    (p : Upstream.Conf) :
    {q : Configuration | IsPositiveNormalized m q ∧ Upstream.Similar p q.z}.Finite := by
  classical
  let S : Set Configuration := {q | IsPositiveNormalized m q ∧ Upstream.Similar p q.z}
  by_cases hn : S.Nonempty
  · obtain ⟨q, hq⟩ := hn
    apply (finite_normalized_fixed_distances_any m hm (squaredDistance q)).subset
    intro r hr
    refine ⟨hr.1.1, fun e => ?_⟩
    exact positive_normalized_similar_squaredDistances hq.1 hr.1
      (Upstream.similar_trans (Upstream.similar_symm hq.2) hr.2) e
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change S.Finite
    rw [he]
    exact Set.finite_empty

/-- Exact adapter from the published finite-similarity-representative statement
at one mass vector to the manuscript's positive normalized finiteness statement. -/
theorem finite_positive_normalized_of_upstream (m : Fin 5 → ℝ) (hm : PositiveMasses m)
    (upstream_finiteness : Upstream.FinitelyManyCC m) :
    {q : Configuration | IsPositiveNormalized m q}.Finite := by
  classical
  obtain ⟨F, hF⟩ := upstream_finiteness
  have hUnion : (⋃ p ∈ (↑F : Set Upstream.Conf),
      {q : Configuration | IsPositiveNormalized m q ∧ Upstream.Similar p q.z}).Finite :=
    F.finite_toSet.biUnion (fun p _ => finite_positive_normalized_similar m hm p)
  apply hUnion.subset
  intro q hq
  obtain ⟨p, hp, hs⟩ := hF q.z (positive_normalized_isCC hq)
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hq, hs⟩⟩

/-- The upstream premise is the literal published all-positive-mass theorem.
This checked bridge is not itself a proof of that premise. A separate integration
file applies it to CC5Full.Core.Compose.MainTheorem_holds after that project builds. -/
theorem fiveBodyFiniteness_of_upstream (upstream_main : Upstream.MainTheorem) :
    FiveBodyFiniteness := by
  intro m hm
  exact finite_positive_normalized_of_upstream m hm (upstream_main m hm)

end Smale5




