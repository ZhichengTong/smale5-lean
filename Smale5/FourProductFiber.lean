import Smale5.FiniteFiber

/-!
Fixed four-products have finite fibres on the normalized configuration space.
This replaces the Petersen determinant step and the curve-specific constancy
argument by finite algebra and the proved fixed-distance fibre theorem.
-/
namespace Smale5

section Field
variable {K : Type*} [Field K]

/-- Finiteness of fourth roots follows from two quadratic root problems. -/
theorem finite_fourth_roots (w : K) : {x : K | x ^ 4 = w}.Finite := by
  have hfinite : (⋃ a ∈ ({a : K | a ^ 2 = w} : Set K),
      {x : K | x ^ 2 = a}).Finite :=
    (finite_square_roots w).biUnion (fun a _ => finite_square_roots a)
  apply hfinite.subset
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨x ^ 2, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, rfl⟩
  simpa only [Set.mem_ofPred_eq, ← pow_mul] using hx

/-- Finiteness of eighth roots follows from three quadratic root problems. -/
theorem finite_eighth_roots (w : K) : {x : K | x ^ 8 = w}.Finite := by
  have hfinite : (⋃ a ∈ ({a : K | a ^ 2 = w} : Set K),
      {x : K | x ^ 4 = a}).Finite :=
    (finite_square_roots w).biUnion (fun a _ => finite_fourth_roots a)
  apply hfinite.subset
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨x ^ 4, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, rfl⟩
  simpa only [Set.mem_ofPred_eq, ← pow_mul] using hx

/-- A finite family of fixed eighth-power equations has finitely many solutions. -/
theorem finite_eighth_root_families {Index : Type*} [Fintype Index]
    (w : Index → K) : {q : Index → K | ∀ i, q i ^ 8 = w i}.Finite := by
  classical
  let Choice (i : Index) := {x : K // x ^ 8 = w i}
  let : ∀ i : Index, Fintype (Choice i) :=
    fun i => (finite_eighth_roots (w i)).fintype
  have hfinite : (Set.range (fun q : ∀ i, Choice i => fun i => (q i).val)).Finite :=
    Set.finite_range _
  apply hfinite.subset
  intro q hq
  refine ⟨(fun i => ⟨q i, hq i⟩), ?_⟩
  rfl
end Field

/-- The same fixed-distance theorem without a nonzero hypothesis: a zero
prescribed squared distance gives an empty fibre. -/
theorem finite_normalized_fixed_distances_any (m : Fin 5 → ℝ)
    (hm : PositiveMasses m) (s : Edge → ℂ) :
    {q : Configuration | IsNormalized m q ∧ ∀ e, squaredDistance q e = s e}.Finite := by
  classical
  by_cases hs : ∀ e, s e ≠ 0
  · exact finite_normalized_fixed_distances m hm s hs
  · push Not at hs
    obtain ⟨e, he⟩ := hs
    apply (Set.finite_empty : (∅ : Set Configuration).Finite).subset
    intro q hq
    exact False.elim (squaredDistance_ne_zero hq.1 e ((hq.2 e).trans he))

/-- Prescribing all ten four-products leaves finitely many normalized solutions.
No irreducibility, projective completion, or singular-diagram input is used. -/
theorem finite_normalized_fixed_fourProducts (m : Fin 5 → ℝ)
    (hm : PositiveMasses m) (p : Edge → ℂ) :
    {q : Configuration | IsNormalized m q ∧
      ∀ e, fourProduct (squaredDistance q) e = p e}.Finite := by
  classical
  by_cases hp : ∀ e, p e ≠ 0
  · have hpTotal : totalProduct p ≠ 0 := totalProduct_ne_zero p hp
    let W : Edge → ℂ := fun e => complementaryProduct p e ^ 4 / totalProduct p
    let distanceChoices : Set (Edge → ℂ) := {s | ∀ e, s e ^ 8 = W e}
    have hDistances : distanceChoices.Finite := finite_eighth_root_families W
    have hUnion : (⋃ s ∈ distanceChoices,
        {q : Configuration | IsNormalized m q ∧ ∀ e, squaredDistance q e = s e}).Finite :=
      hDistances.biUnion (fun s _ => finite_normalized_fixed_distances_any m hm s)
    apply hUnion.subset
    intro q hq
    apply Set.mem_iUnion.mpr
    refine ⟨squaredDistance q, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨?_, hq.1, fun _ => rfl⟩
    intro e
    have hrec := eighthPower_recovery (squaredDistance q) e
    have hfour : fourProduct (squaredDistance q) = p := funext hq.2
    rw [hfour] at hrec
    exact (eq_div_iff hpTotal).2 hrec
  · push Not at hp
    obtain ⟨e, he⟩ := hp
    apply (Set.finite_empty : (∅ : Set Configuration).Finite).subset
    intro q hq
    have hne := fourProduct_ne_zero (squaredDistance q) (squaredDistance_ne_zero hq.1) e
    exact False.elim (hne ((hq.2 e).trans he))

/-- On any infinite set of normalized solutions, at least one four-product
takes two distinct values. This implies the manuscript's curve statement. -/
theorem infinite_normalized_has_nonconstant_fourProduct (m : Fin 5 → ℝ)
    (hm : PositiveMasses m) (S : Set Configuration) (hinfinite : S.Infinite)
    (hnormalized : ∀ q ∈ S, IsNormalized m q) :
    ∃ e, ∃ q ∈ S, ∃ r ∈ S,
      fourProduct (squaredDistance q) e ≠ fourProduct (squaredDistance r) e := by
  classical
  by_contra hconstant
  push Not at hconstant
  obtain ⟨q₀, hq₀⟩ := hinfinite.nonempty
  have hfinite := finite_normalized_fixed_fourProducts m hm
    (fourProduct (squaredDistance q₀))
  apply hinfinite
  apply hfinite.subset
  intro q hq
  exact ⟨hnormalized q hq, fun e => hconstant e q hq q₀ hq₀⟩

end Smale5

