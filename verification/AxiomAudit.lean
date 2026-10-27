-- Generated audit. The main target is a proposition definition.
import Smale5.AnalyticEnergy
import Smale5.ArchonVirial
import Smale5.Balance
import Smale5.Configuration
import Smale5.Diagram3Elimination
import Smale5.Diagram3NormCertificate
import Smale5.Diagram7Inertia
import Smale5.Edges
import Smale5.FiniteFiber
import Smale5.FourProductFiber
import Smale5.Global
import Smale5.Orders
import Smale5.PairInertia
import Smale5.Positivity
import Smale5.PrincipalDivisor
import Smale5.Products
import Smale5.QuadraticRecovery
import Smale5.Symmetry
import Smale5.TangentEnergy
import Smale5.UpstreamBridge

#check Smale5.FiveBodyFiniteness
#print Smale5.FiveBodyFiniteness

#print axioms Smale5.path_squaredDistance_hasDerivAt
#print axioms Smale5.path_potential_hasDerivAt
#print axioms Smale5.path_inertia_hasDerivAt
#print axioms Smale5.path_linearizedDistanceConstraints
#print axioms Smale5.normalized_path_energy_zero_of_hasDerivAt
#print axioms Smale5.normalized_path_energy_hasDerivAt_zero
#print axioms Smale5.path_potential_continuousOn
#print axioms Smale5.path_inertia_continuousOn
#print axioms Smale5.normalized_path_energy_constant_Icc
#print axioms Smale5.virial_pair_sum
#print axioms Smale5.normalized_potential_eq_inertia
#print axioms Smale5.internal_force_sum_zero
#print axioms Smale5.centerOfMass_from_balance
#print axioms Smale5.normalized_centerOfMass_z
#print axioms Smale5.normalized_centerOfMass_w
#print axioms Smale5.Configuration.inversePair_symm
#print axioms Smale5.squaredDistance_ne_zero
#print axioms Smale5.inverseDistance_ne_zero
#print axioms Smale5.normalized_totalProduct_ne_zero
#print axioms Smale5.normalized_product_identity
#print axioms Smale5.Diagram3.elimination_identity
#print axioms Smale5.Diagram3.obstruction_of_two_equations
#print axioms Smale5.Diagram3.mass_elimination_identity
#print axioms Smale5.Diagram3.mass_obstruction_of_two_equations
#print axioms Smale5.Diagram3Norm.p66_factorization
#print axioms Smale5.Diagram3Norm.cleared_nine_root_norm
#print axioms Smale5.Diagram3Norm.cubic_norm_vanishes
#print axioms Smale5.Diagram3Norm.p66_negative_decomposition
#print axioms Smale5.Diagram3Norm.rational_nine_root_norm
#print axioms Smale5.Diagram3Norm.root_form_ne_zero
#print axioms Smale5.Diagram3Norm.p66_pos
#print axioms Smale5.Diagram3Norm.positive_norm_factor_ne_zero
#print axioms Smale5.Diagram3Norm.p66_ofReal
#print axioms Smale5.Diagram3Norm.positive_family_root_form_ne_zero
#print axioms Smale5.Diagram3Norm.p66_negative_pos
#print axioms Smale5.Diagram3Norm.negative_family_root_form_ne_zero
#print axioms Smale5.Diagram7.inertia_identity
#print axioms Smale5.Diagram7.normalized_forceResidualZ
#print axioms Smale5.Diagram7.normalized_forceResidualW
#print axioms Smale5.Diagram7.normalized_inertia_identity
#print axioms Smale5.Edge.left_ne_right
#print axioms Smale5.edgeFor_symm
#print axioms Smale5.edgeFor_self
#print axioms Smale5.normalized_gauge_square
#print axioms Smale5.normalized_offset_constraints
#print axioms Smale5.centered_offsets_injective
#print axioms Smale5.normalized_offsets_delta_injective
#print axioms Smale5.finite_normalized_fixed_distances
#print axioms Smale5.finite_fourth_roots
#print axioms Smale5.finite_eighth_roots
#print axioms Smale5.finite_eighth_root_families
#print axioms Smale5.finite_normalized_fixed_distances_any
#print axioms Smale5.finite_normalized_fixed_fourProducts
#print axioms Smale5.infinite_normalized_has_nonconstant_fourProduct
#print axioms Smale5.globalOrderContradiction
#print axioms Smale5.finite_of_order_reduction
#print axioms Smale5.sum_fourOrders
#print axioms Smale5.complementary_fourOrders
#print axioms Smale5.exists_negative_of_totalOrder_neg
#print axioms Smale5.exists_negative_fourOrder
#print axioms Smale5.diagram9_totalOrder
#print axioms Smale5.diagram9_totalOrder_pos
#print axioms Smale5.diagram9_unbounded_fourProducts
#print axioms Smale5.weighted_pair_distance_identity
#print axioms Smale5.mass_mul_inertia_of_centerOfMass_zero
#print axioms Smale5.normalized_mass_mul_inertia
#print axioms Smale5.inertia_eq_ofReal_realInertia
#print axioms Smale5.exists_nonzero_z
#print axioms Smale5.realInertia_pos
#print axioms Smale5.real_normalized_inertia_ne_zero
#print axioms Smale5.positive_inverse_distances_exclude_d3
#print axioms Smale5.exists_negative_of_sum_zero_of_positive
#print axioms Smale5.zero_has_pole_of_degree_zero
#print axioms Smale5.globalOrderContradiction_from_degreeZero
#print axioms Smale5.product_fourProducts
#print axioms Smale5.complementary_fourProducts
#print axioms Smale5.eighthPower_recovery
#print axioms Smale5.totalProduct_ne_zero
#print axioms Smale5.fourProduct_ne_zero
#print axioms Smale5.quadratic_offset_sum
#print axioms Smale5.quadratic_offset_recovery
#print axioms Smale5.quadratic_root_eq_or
#print axioms Smale5.finite_quadratic_roots
#print axioms Smale5.finite_square_roots
#print axioms Smale5.finite_offset_pairs
#print axioms Smale5.finite_offset_families
#print axioms Smale5.finite_square_root_families
#print axioms Smale5.IsNormalized.toForceDistanceSolution
#print axioms Smale5.inversePair_cStarScale
#print axioms Smale5.squaredDistance_cStarScale
#print axioms Smale5.IsForceDistanceSolution.cStarScale
#print axioms Smale5.gauge_cStarScale_iff
#print axioms Smale5.normalized_gauge_cStarScale_iff_square_one
#print axioms Smale5.IsNormalized.cStarScale_of_gauge
#print axioms Smale5.IsNormalized.cStarScale_of_square_one
#print axioms Smale5.potential_cStarScale
#print axioms Smale5.inertia_cStarScale
#print axioms Smale5.linearized_distance_recovery
#print axioms Smale5.tangent_pair_sum
#print axioms Smale5.normalized_inertiaDifferential_eq
#print axioms Smale5.normalized_tangent_energy_critical
#print axioms Smale5.energyDifferentials_zero_of_equal
#print axioms Smale5.linearized_virial_pair_sum
#print axioms Smale5.normalized_tangent_virial
#print axioms Smale5.normalized_tangent_energy_zero
#print axioms Smale5.normalized_collisionFree
#print axioms Smale5.real_squaredDistance_norm
#print axioms Smale5.positive_delta_inverse_norm
#print axioms Smale5.positive_inversePair_inverse_norm
#print axioms Smale5.positive_normalized_normEq
#print axioms Smale5.positive_normalized_isCC
#print axioms Smale5.Upstream.similar_symm
#print axioms Smale5.Upstream.similar_trans
#print axioms Smale5.Upstream.normEq_conj
#print axioms Smale5.Upstream.affine_rhs
#print axioms Smale5.Upstream.normEq_affine_scale_one
#print axioms Smale5.Upstream.normEq_similar_distances
#print axioms Smale5.positive_normalized_similar_squaredDistances
#print axioms Smale5.finite_positive_normalized_similar
#print axioms Smale5.finite_positive_normalized_of_upstream
#print axioms Smale5.fiveBodyFiniteness_of_upstream
