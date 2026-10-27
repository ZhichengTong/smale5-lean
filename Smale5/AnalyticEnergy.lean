import Smale5.ArchonVirial
import Smale5.TangentEnergy
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Basic

/-!
Actual real-parameter derivatives of the potential and inertia along paths of
normalized configurations, and constancy on closed real intervals.
-/

namespace Smale5

open scoped BigOperators Topology
open Set Filter

/-- Coordinate derivatives identify the derivative of a squared distance. -/
theorem path_squaredDistance_hasDerivAt
    (q : ℝ → Configuration) (t : ℝ) (v : TangentData)
    (hz : ∀ k, HasDerivAt (fun s => (q s).z k) (v.dz k) t)
    (hw : ∀ k, HasDerivAt (fun s => (q s).w k) (v.dw k) t)
    (e : Edge) :
    HasDerivAt (fun s => squaredDistance (q s) e)
      (distanceDifferential (q t) v e) t := by
  simpa only [squaredDistance, distanceDifferential, Pi.mul_apply, Pi.sub_apply] using
    ((hz e.right).fun_sub (hz e.left)).fun_mul
      ((hw e.right).fun_sub (hw e.left))

/-- Coordinate derivatives identify the derivative of the potential. -/
theorem path_potential_hasDerivAt
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (t : ℝ)
    (v : TangentData)
    (hd : ∀ e, HasDerivAt (fun s => (q s).delta e) (v.ddelta e) t) :
    HasDerivAt (fun s => potential m (q s))
      (potentialDifferential m v) t := by
  simpa only [potential, potentialDifferential] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (fun e _ => (hd e).const_mul
        ((m e.left : ℂ) * (m e.right : ℂ))))

/-- Coordinate derivatives identify the derivative of the inertia. -/
theorem path_inertia_hasDerivAt
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (t : ℝ)
    (v : TangentData)
    (hz : ∀ k, HasDerivAt (fun s => (q s).z k) (v.dz k) t)
    (hw : ∀ k, HasDerivAt (fun s => (q s).w k) (v.dw k) t) :
    HasDerivAt (fun s => inertia m (q s))
      (inertiaDifferential m (q t) v) t := by
  simpa only [inertia, inertiaDifferential, mul_assoc, Pi.mul_apply] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (fun k _ => ((hz k).mul (hw k)).const_mul (m k : ℂ)))

/-- Differentiating the actual locally valid distance constraints gives their
linearizations. -/
theorem path_linearizedDistanceConstraints
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (t : ℝ)
    (v : TangentData)
    (hn : ∀ᶠ s in 𝓝 t, IsNormalized m (q s))
    (hz : ∀ k, HasDerivAt (fun s => (q s).z k) (v.dz k) t)
    (hw : ∀ k, HasDerivAt (fun s => (q s).w k) (v.dw k) t)
    (hd : ∀ e, HasDerivAt (fun s => (q s).delta e) (v.ddelta e) t) :
    HasLinearizedDistanceConstraints (q t) v := by
  intro e
  have hp :
      HasDerivAt
        (fun s => (q s).delta e ^ 2 * squaredDistance (q s) e)
        (2 * (q t).delta e * v.ddelta e * squaredDistance (q t) e +
          (q t).delta e ^ 2 * distanceDifferential (q t) v e) t := by
    simpa using
      ((hd e).fun_pow 2).fun_mul
        (path_squaredDistance_hasDerivAt q t v hz hw e)
  have he :
      (fun s => (q s).delta e ^ 2 * squaredDistance (q s) e)
        =ᶠ[𝓝 t] (fun _ => (1 : ℂ)) := by
    filter_upwards [hn] with s hs
    exact hs.distance_constraint e
  have hc :
      HasDerivAt
        (fun s => (q s).delta e ^ 2 * squaredDistance (q s) e)
        0 t :=
    (hasDerivAt_const t (1 : ℂ)).congr_of_eventuallyEq he
  exact hp.unique hc

/-- Local normalization forces both actual energy derivatives to vanish.
Only coordinate derivatives and the actual normalization predicate are assumed. -/
theorem normalized_path_energy_zero_of_hasDerivAt
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (t : ℝ)
    (v : TangentData)
    (hn : ∀ᶠ s in 𝓝 t, IsNormalized m (q s))
    (hz : ∀ k, HasDerivAt (fun s => (q s).z k) (v.dz k) t)
    (hw : ∀ k, HasDerivAt (fun s => (q s).w k) (v.dw k) t)
    (hd : ∀ e, HasDerivAt (fun s => (q s).delta e) (v.ddelta e) t) :
    HasDerivAt (fun s => potential m (q s)) 0 t ∧
      HasDerivAt (fun s => inertia m (q s)) 0 t := by
  have hnt : IsNormalized m (q t) := hn.self_of_nhds
  have hu := path_potential_hasDerivAt m q t v hd
  have hi := path_inertia_hasDerivAt m q t v hz hw
  have he :
      (fun s => potential m (q s))
        =ᶠ[𝓝 t] (fun s => inertia m (q s)) := by
    filter_upwards [hn] with s hs
    exact normalized_potential_eq_inertia hs
  have heq :
      potentialDifferential m v = inertiaDifferential m (q t) v :=
    hu.unique (hi.congr_of_eventuallyEq he)
  have hlin :=
    path_linearizedDistanceConstraints m q t v hn hz hw hd
  obtain ⟨hu0, hi0⟩ :=
    energyDifferentials_zero_of_equal hnt v hlin heq
  exact ⟨hu.congr_deriv hu0, hi.congr_deriv hi0⟩

/-- Coordinate differentiability supplies the tangent data used by the local
derivative-zero theorem. -/
theorem normalized_path_energy_hasDerivAt_zero
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (t : ℝ)
    (hn : ∀ᶠ s in 𝓝 t, IsNormalized m (q s))
    (hz : ∀ k, DifferentiableAt ℝ (fun s => (q s).z k) t)
    (hw : ∀ k, DifferentiableAt ℝ (fun s => (q s).w k) t)
    (hd : ∀ e, DifferentiableAt ℝ (fun s => (q s).delta e) t) :
    HasDerivAt (fun s => potential m (q s)) 0 t ∧
      HasDerivAt (fun s => inertia m (q s)) 0 t := by
  let v : TangentData :=
    { dz := fun k => deriv (fun s => (q s).z k) t
      dw := fun k => deriv (fun s => (q s).w k) t
      ddelta := fun e => deriv (fun s => (q s).delta e) t }
  exact normalized_path_energy_zero_of_hasDerivAt m q t v hn
    (fun k => (hz k).hasDerivAt)
    (fun k => (hw k).hasDerivAt)
    (fun e => (hd e).hasDerivAt)

private theorem continuousOn_complex_sum
    {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℂ) (S : Set ℝ)
    (hA : ∀ i ∈ s, ContinuousOn (A i) S) :
    ContinuousOn (fun t => ∑ i ∈ s, A i t) S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) S)
  | @insert i s his ih =>
      have hi : ContinuousOn (A i) S :=
        hA i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, ContinuousOn (A j) S := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert his, Pi.add_apply] using hi.fun_add (ih hs)

/-- Coordinate continuity implies potential continuity. -/
theorem path_potential_continuousOn
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (S : Set ℝ)
    (hd : ∀ e, ContinuousOn (fun t => (q t).delta e) S) :
    ContinuousOn (fun t => potential m (q t)) S := by
  unfold potential
  exact continuousOn_complex_sum Finset.univ
    (fun e t => (m e.left : ℂ) * (m e.right : ℂ) * (q t).delta e) S
    (fun e _ => (hd e).const_mul
      ((m e.left : ℂ) * (m e.right : ℂ)))

/-- Coordinate continuity implies inertia continuity. -/
theorem path_inertia_continuousOn
    (m : Fin 5 → ℝ) (q : ℝ → Configuration) (S : Set ℝ)
    (hz : ∀ k, ContinuousOn (fun t => (q t).z k) S)
    (hw : ∀ k, ContinuousOn (fun t => (q t).w k) S) :
    ContinuousOn (fun t => inertia m (q t)) S := by
  unfold inertia
  exact continuousOn_complex_sum Finset.univ
    (fun k t => (m k : ℂ) * (q t).z k * (q t).w k) S
    (fun k _ => ((hz k).const_mul (m k : ℂ)).mul (hw k))

private theorem complex_const_on_Icc_of_hasDerivAt_zero
    (f : ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, f x = f y := by
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hcI : c ∈ Ioo a b := ⟨hac, hcb⟩
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
    intro t ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  have hderiv : (Ioo a b).EqOn (deriv f) 0 := by
    intro t ht
    exact (hd t ht).deriv
  have hconst : (Ioo a b).EqOn f (fun _ => f c) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hderiv ht hcI
  have hclosed :
      (closure (Ioo a b)).EqOn f (fun _ => f c) :=
    ContinuousWithinAt.eqOn_const_closure
      (fun t ht =>
        (hc t (by
          simpa only [closure_Ioo (ne_of_lt hab)] using ht)).mono
            Ioo_subset_Icc_self)
      hconst
  have hclosed' : (Icc a b).EqOn f (fun _ => f c) := by
    simpa only [closure_Ioo (ne_of_lt hab)] using hclosed
  intro x hx y hy
  exact (hclosed' hx).trans (hclosed' hy).symm

/-- On a nondegenerate closed interval, a coordinatewise continuous path of
actual normalized configurations with coordinate derivatives in the interior
has constant potential and constant inertia. -/
theorem normalized_path_energy_constant_Icc
    (m : Fin 5 → ℝ) (q : ℝ → Configuration)
    {a b : ℝ} (hab : a < b)
    (hn : ∀ t ∈ Icc a b, IsNormalized m (q t))
    (hz_cont : ∀ k, ContinuousOn (fun t => (q t).z k) (Icc a b))
    (hw_cont : ∀ k, ContinuousOn (fun t => (q t).w k) (Icc a b))
    (hd_cont : ∀ e, ContinuousOn (fun t => (q t).delta e) (Icc a b))
    (hz_diff : ∀ t ∈ Ioo a b, ∀ k,
      DifferentiableAt ℝ (fun s => (q s).z k) t)
    (hw_diff : ∀ t ∈ Ioo a b, ∀ k,
      DifferentiableAt ℝ (fun s => (q s).w k) t)
    (hd_diff : ∀ t ∈ Ioo a b, ∀ e,
      DifferentiableAt ℝ (fun s => (q s).delta e) t) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      potential m (q x) = potential m (q y) ∧
        inertia m (q x) = inertia m (q y) := by
  have hzero : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => potential m (q s)) 0 t ∧
        HasDerivAt (fun s => inertia m (q s)) 0 t := by
    intro t ht
    have hlocal : ∀ᶠ s in 𝓝 t, IsNormalized m (q s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hn s (Ioo_subset_Icc_self hs)
    exact normalized_path_energy_hasDerivAt_zero m q t hlocal
      (hz_diff t ht) (hw_diff t ht) (hd_diff t ht)
  have hu :=
    complex_const_on_Icc_of_hasDerivAt_zero
      (fun t => potential m (q t)) hab
      (path_potential_continuousOn m q (Icc a b) hd_cont)
      (fun t ht => (hzero t ht).1)
  have hi :=
    complex_const_on_Icc_of_hasDerivAt_zero
      (fun t => inertia m (q t)) hab
      (path_inertia_continuousOn m q (Icc a b) hz_cont hw_cont)
      (fun t ht => (hzero t ht).2)
  intro x hx y hy
  exact ⟨hu x hx y hy, hi x hx y hy⟩

end Smale5
