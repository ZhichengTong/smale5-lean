import Smale5.UpstreamBridge
import CC5Full.System

namespace Smale5
/-- The isolated adapter predicate is definitionally equal to the published one. -/
theorem upstream_main_interface_exact : Upstream.MainTheorem = CC5Full.MainTheorem := rfl

/-- No reinterpretation of the upstream theorem is required. -/
theorem target_from_actual_upstream_statement (h : CC5Full.MainTheorem) : FiveBodyFiniteness :=
  fiveBodyFiniteness_of_upstream h
end Smale5

#print axioms Smale5.upstream_main_interface_exact
#print axioms Smale5.target_from_actual_upstream_statement
