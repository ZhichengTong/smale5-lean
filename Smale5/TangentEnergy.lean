import Smale5.Configuration

/-!
Finite algebra for the differential of the energy in manuscript lines 465–488.
These are algebraic tangent equations and directional expressions. No calculus
identification, smoothness theorem, or constancy on an irreducible curve is
asserted here.
-/
namespace Smale5
open scoped BigOperators
open Edge

/-- Ambient directional coordinates for the twenty configuration coordinates. -/
structure TangentData where
  dz : Fin 5 → ℂ
  dw : Fin 5 → ℂ
  ddelta : Edge → ℂ

def TangentData.inversePair (v : TangentData) (i j : Fin 5) : ℂ :=
  match edgeFor i j with
  | some e => v.ddelta e
  | none => 0

/-- Formal directional derivative of a squared mutual distance. -/
def distanceDifferential (q : Configuration) (v : TangentData) (e : Edge) : ℂ :=
  (v.dz e.right - v.dz e.left) * (q.w e.right - q.w e.left) +
    (q.z e.right - q.z e.left) * (v.dw e.right - v.dw e.left)

def potentialDifferential (m : Fin 5 → ℝ) (v : TangentData) : ℂ :=
  ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) * v.ddelta e

def inertiaDifferential (m : Fin 5 → ℝ) (q : Configuration) (v : TangentData) : ℂ :=
  ∑ k : Fin 5, (m k : ℂ) * (v.dz k * q.w k + q.z k * v.dw k)

/-- Linearization of every equation delta² times squared distance equals one. -/
def HasLinearizedDistanceConstraints (q : Configuration) (v : TangentData) : Prop :=
  ∀ e, 2 * q.delta e * v.ddelta e * squaredDistance q e +
    q.delta e ^ 2 * distanceDifferential q v e = 0

/-- Linearization of the normalized z-force equations. This condition alone,
together with the distance linearizations, suffices for the derivative virial identity. -/
def HasLinearizedZBalance (m : Fin 5 → ℝ) (q : Configuration) (v : TangentData) : Prop :=
  ∀ k, v.dz k = ∑ l : Fin 5, (m l : ℂ) *
    (3 * q.inversePair k l ^ 2 * v.inversePair k l * (q.z k - q.z l) +
      q.inversePair k l ^ 3 * (v.dz k - v.dz l))

/-- Algebraic form of twice d(delta) plus delta³ d(squared distance) equals zero. -/
theorem linearized_distance_recovery {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData)
    (hd : HasLinearizedDistanceConstraints q v) (e : Edge) :
    2 * v.ddelta e + q.delta e ^ 3 * distanceDifferential q v e = 0 := by
  have hc := h.distance_constraint e
  have he := hd e
  linear_combination q.delta e * he - 2 * v.ddelta e * hc

/-- Pairing oriented forces in the directional inertia expression. -/
theorem tangent_pair_sum (m : Fin 5 → ℝ) (q : Configuration) (v : TangentData) :
    (∑ k : Fin 5, ∑ l : Fin 5,
      (m k : ℂ) * (m l : ℂ) * q.inversePair k l ^ 3 *
        (v.dz k * (q.w k - q.w l) + (q.z k - q.z l) * v.dw k)) =
    ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) *
      q.delta e ^ 3 * distanceDifferential q v e := by
  have huniv : (Finset.univ : Finset Edge) =
      {e12, e13, e14, e15, e23, e24, e25, e34, e35, e45} := rfl
  simp only [Fin.sum_univ_succ]
  rw [huniv]
  simp [Configuration.inversePair, edgeFor, distanceDifferential, Edge.left, Edge.right]
  ring

/-- The force equations express dI as a sum over derivatives of squared distances. -/
theorem normalized_inertiaDifferential_eq {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData) :
    inertiaDifferential m q v =
      ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) *
        q.delta e ^ 3 * distanceDifferential q v e := by
  calc
    inertiaDifferential m q v =
        ∑ k : Fin 5, ∑ l : Fin 5,
          (m k : ℂ) * (m l : ℂ) * q.inversePair k l ^ 3 *
            (v.dz k * (q.w k - q.w l) + (q.z k - q.z l) * v.dw k) := by
      unfold inertiaDifferential
      apply Finset.sum_congr rfl
      intro k hk
      conv_lhs => rw [h.w_balance k, h.z_balance k]
      simp only [mul_add, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := tangent_pair_sum m q v

/-- Every normalized solution is algebraically critical for 2U+I along all
ambient directions satisfying the linearized distance constraints. -/
theorem normalized_tangent_energy_critical {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData)
    (hd : HasLinearizedDistanceConstraints q v) :
    2 * potentialDifferential m v + inertiaDifferential m q v = 0 := by
  rw [normalized_inertiaDifferential_eq h v]
  unfold potentialDifferential
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e he
  calc
    2 * ((m e.left : ℂ) * (m e.right : ℂ) * v.ddelta e) +
        (m e.left : ℂ) * (m e.right : ℂ) * q.delta e ^ 3 * distanceDifferential q v e =
      (m e.left : ℂ) * (m e.right : ℂ) *
        (2 * v.ddelta e + q.delta e ^ 3 * distanceDifferential q v e) := by ring
    _ = 0 := by rw [linearized_distance_recovery h v hd e, mul_zero]

/-- An explicit derivative equality dU=dI, together with criticality, forces both zero. -/
theorem energyDifferentials_zero_of_equal {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData)
    (hd : HasLinearizedDistanceConstraints q v)
    (heq : potentialDifferential m v = inertiaDifferential m q v) :
    potentialDifferential m v = 0 ∧ inertiaDifferential m q v = 0 := by
  have hc := normalized_tangent_energy_critical h v hd
  have hu : potentialDifferential m v = 0 := by
    linear_combination (1 / 3 : ℂ) * hc + (1 / 3 : ℂ) * heq
  exact ⟨hu, heq.symm.trans hu⟩

/-- Differentiated pair identity, proved directly as a finite polynomial identity. -/
theorem linearized_virial_pair_sum (m : Fin 5 → ℝ) (q : Configuration) (v : TangentData) :
    (∑ k : Fin 5, ∑ l : Fin 5, (m k : ℂ) * (m l : ℂ) *
      (3 * q.inversePair k l ^ 2 * v.inversePair k l * (q.z k - q.z l) * q.w k +
        q.inversePair k l ^ 3 *
          ((v.dz k - v.dz l) * q.w k + (q.z k - q.z l) * v.dw k))) =
    ∑ e : Edge, (m e.left : ℂ) * (m e.right : ℂ) *
      (3 * q.delta e ^ 2 * v.ddelta e * squaredDistance q e +
        q.delta e ^ 3 * distanceDifferential q v e) := by
  have huniv : (Finset.univ : Finset Edge) =
      {e12, e13, e14, e15, e23, e24, e25, e34, e35, e45} := rfl
  simp only [Fin.sum_univ_succ]
  rw [huniv]
  simp [Configuration.inversePair, TangentData.inversePair, edgeFor,
    squaredDistance, distanceDifferential, Edge.left, Edge.right]
  ring

/-- The linearized z-force and distance equations imply the derivative identity dU=dI.
This is proved algebraically; it does not assume differentiation of a previous theorem. -/
theorem normalized_tangent_virial {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData)
    (hd : HasLinearizedDistanceConstraints q v) (hz : HasLinearizedZBalance m q v) :
    potentialDifferential m v = inertiaDifferential m q v := by
  have hi : inertiaDifferential m q v =
      ∑ k : Fin 5, ∑ l : Fin 5, (m k : ℂ) * (m l : ℂ) *
        (3 * q.inversePair k l ^ 2 * v.inversePair k l * (q.z k - q.z l) * q.w k +
          q.inversePair k l ^ 3 *
            ((v.dz k - v.dz l) * q.w k + (q.z k - q.z l) * v.dw k)) := by
    unfold inertiaDifferential
    apply Finset.sum_congr rfl
    intro k hk
    conv_lhs => rw [h.z_balance k, hz k]
    simp only [mul_add, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hi, linearized_virial_pair_sum]
  unfold potentialDifferential
  apply Finset.sum_congr rfl
  intro e he
  have hc := h.distance_constraint e
  have hd' := linearized_distance_recovery h v hd e
  linear_combination -(m e.left : ℂ) * (m e.right : ℂ) * hd' -
    3 * (m e.left : ℂ) * (m e.right : ℂ) * v.ddelta e * hc

/-- Local algebraic energy constancy: derivatives of U and I vanish on directions
satisfying the linearized normalized z-force and distance equations. -/
theorem normalized_tangent_energy_zero {m : Fin 5 → ℝ} {q : Configuration}
    (h : IsNormalized m q) (v : TangentData)
    (hd : HasLinearizedDistanceConstraints q v) (hz : HasLinearizedZBalance m q v) :
    potentialDifferential m v = 0 ∧ inertiaDifferential m q v = 0 :=
  energyDifferentials_zero_of_equal h v hd (normalized_tangent_virial h v hd hz)

end Smale5

