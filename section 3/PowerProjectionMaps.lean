import «section 3».NamedDefinableMaps
import Section4.CodeMaps
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]

def universalPowerProjection (P : Space L M) (S : Set M) {I J : Type} [Finite I] [Finite J]
    (f : J → I) : Map (DefSet.univ (P.power I) S) (DefSet.univ (P.power J) S) :=
  Map.ofCodes (DefSet.univ (P.power I) S) (fun x j => x (f j))
    (fun c z => c (f z.1, z.2)) (fun _ => Set.DefinableFun.proj L)
    (fun c j => c.property (f j)) (fun _ => rfl)

end DiamondIntegral.Section3
