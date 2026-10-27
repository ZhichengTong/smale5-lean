import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Range

/-!
Elementary reconstruction from distances, replacing the use of Witt's theorem
in manuscript lines 548–578. The field lemmas below establish finite choices of
offsets for a fixed nonzero gauge. They do not assert finiteness of the original
normalized-configuration fibre: the centre-of-mass and inverse-distance bridges
are separate obligations.
-/
namespace Smale5

section Field
variable {K : Type*} [Field K]

/-- The two distances to the first two bodies recover the sum of offsets. -/
theorem quadratic_offset_sum (a b t u v w : K)
    (hab : a * b = u) (hshift : (a - t) * (b - t) = v)
    (ht : t ^ 2 = w) (htne : t ≠ 0) :
    a + b = (u + w - v) / t := by
  have hlinear : t * (a + b) = u + w - v := by
    calc
      t * (a + b) = a * b + t ^ 2 - (a - t) * (b - t) := by ring
      _ = u + w - v := by rw [hab, ht, hshift]
  apply (eq_div_iff htne).2
  simpa only [mul_comm] using hlinear

/-- Each first offset satisfies a monic quadratic, and fixes the second one. -/
theorem quadratic_offset_recovery (a b t u v w : K)
    (hab : a * b = u) (hshift : (a - t) * (b - t) = v)
    (ht : t ^ 2 = w) (htne : t ≠ 0) :
    a ^ 2 - ((u + w - v) / t) * a + u = 0 ∧
      b = (u + w - v) / t - a := by
  have hsum := quadratic_offset_sum a b t u v w hab hshift ht htne
  constructor
  · rw [← hsum]
    calc
      a ^ 2 - (a + b) * a + u = u - a * b := by ring
      _ = 0 := by rw [hab, sub_self]
  · rw [← hsum]
    ring

/-- Relative to any one root, a monic quadratic has only two candidate roots. -/
theorem quadratic_root_eq_or (c u a x : K)
    (ha : a ^ 2 - c * a + u = 0)
    (hx : x ^ 2 - c * x + u = 0) :
    x = a ∨ x = c - a := by
  have hfactor : (x - a) * (x + a - c) = 0 := by
    calc
      (x - a) * (x + a - c) =
          (x ^ 2 - c * x + u) - (a ^ 2 - c * a + u) := by ring
      _ = 0 := by rw [hx, ha, sub_self]
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · exact Or.inr (eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hright))

/-- Finite quadratic root set, proved by factorization rather than a root oracle. -/
theorem finite_quadratic_roots (c u : K) :
    {x : K | x ^ 2 - c * x + u = 0}.Finite := by
  classical
  by_cases hexists : ∃ a : K, a ^ 2 - c * a + u = 0
  · obtain ⟨a, ha⟩ := hexists
    apply ((Set.finite_singleton (c - a)).insert a).subset
    intro x hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      quadratic_root_eq_or c u a x ha hx
  · apply (Set.finite_empty : (∅ : Set K).Finite).subset
    intro x hx
    exact False.elim (hexists ⟨x, hx⟩)

/-- In particular, the gauge has finitely many square-root choices. -/
theorem finite_square_roots (w : K) : {t : K | t ^ 2 = w}.Finite := by
  apply (finite_quadratic_roots (0 : K) (-w)).subset
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  simp [ht]

/-- Two fixed squared distances and a nonzero gauge allow finitely many offsets. -/
theorem finite_offset_pairs (t u v : K) (htne : t ≠ 0) :
    {q : K × K | q.1 * q.2 = u ∧ (q.1 - t) * (q.2 - t) = v}.Finite := by
  let c : K := (u + t ^ 2 - v) / t
  have hfinite := (finite_quadratic_roots c u).image (fun a : K => (a, c - a))
  apply hfinite.subset
  intro q hq
  obtain ⟨hquadratic, hb⟩ :=
    quadratic_offset_recovery q.1 q.2 t u v (t ^ 2) hq.1 hq.2 rfl htne
  refine ⟨q.1, hquadratic, ?_⟩
  exact Prod.ext rfl hb.symm

/-- Finitely many simultaneous offset choices for any finite number of bodies.
This is the fixed-gauge coordinate part of the fixed-distance fibre proof. -/
theorem finite_offset_families {Index : Type*} [Fintype Index]
    (t : K) (u v : Index → K) (htne : t ≠ 0) :
    {q : Index → K × K | ∀ i,
      (q i).1 * (q i).2 = u i ∧ ((q i).1 - t) * ((q i).2 - t) = v i}.Finite := by
  classical
  let Choice (i : Index) := {q : K × K //
    q.1 * q.2 = u i ∧ (q.1 - t) * (q.2 - t) = v i}
  let : ∀ i : Index, Fintype (Choice i) :=
    fun i => (finite_offset_pairs t (u i) (v i) htne).fintype
  have hfinite : (Set.range (fun q : ∀ i, Choice i => fun i => (q i).val)).Finite :=
    Set.finite_range _
  apply hfinite.subset
  intro q hq
  refine ⟨(fun i => ⟨q i, hq i⟩), ?_⟩
  rfl

/-- Finitely many simultaneous square-root choices over a finite index set. -/
theorem finite_square_root_families {Index : Type*} [Fintype Index]
    (w : Index → K) : {q : Index → K | ∀ i, q i ^ 2 = w i}.Finite := by
  classical
  let Choice (i : Index) := {x : K // x ^ 2 = w i}
  let : ∀ i : Index, Fintype (Choice i) :=
    fun i => (finite_square_roots (w i)).fintype
  have hfinite : (Set.range (fun q : ∀ i, Choice i => fun i => (q i).val)).Finite :=
    Set.finite_range _
  apply hfinite.subset
  intro q hq
  refine ⟨(fun i => ⟨q i, hq i⟩), ?_⟩
  rfl
end Field
end Smale5




