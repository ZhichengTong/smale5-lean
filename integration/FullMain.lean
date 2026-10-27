import Smale5.UpstreamBridge
import CC5Full.Core.Compose.Main

/-!
Final integration target, separate from the presently checked local library.
It applies Tomar's actual published unconditional theorem. It introduces no
axioms or finiteness assumptions. The complete upstream proof and its generated
certificate modules must be rebuilt in a compatible toolchain before this file
can be kernel checked. Source presence is not a successful build claim.
-/
namespace Smale5

theorem fiveBodyFiniteness_from_published_proof : FiveBodyFiniteness :=
  fiveBodyFiniteness_of_upstream CC5Full.Core.Compose.MainTheorem_holds

end Smale5

#print axioms Smale5.fiveBodyFiniteness_from_published_proof
