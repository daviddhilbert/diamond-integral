import «section 3».DefinableBijections
import Section4.FiniteMaps
import Section4.MapCorestrict

/-! Equal actual carriers give the identity definable bijection, even
when their definability proofs or inherited auxiliary maps differ. -/

open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P : Space L M}

def DefinableBijection.ofCarrierEq {A B : DefSet P S} (h : A.carrier = B.carrier) :
    DefinableBijection A B where
  map := Map.inclusion h.le
  bijective := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun x : B => x.val) he)
    · intro b
      exact ⟨⟨b.val, h.ge b.property⟩, Subtype.ext rfl⟩

def DefinableBijection.ofEmpty {Q : Space L M} {A : DefSet P S} {B : DefSet Q S}
    (hA : A.carrier = ∅) (hB : B.carrier = ∅) : DefinableBijection A B where
  map := ((Map.empty P Q S).comp (DefinableBijection.ofCarrierEq hA).map).corestrict
    (fun a => False.elim (show False from (Set.notMem_empty a.val) (hA ▸ a.property)))
  bijective := by
    constructor
    · intro a
      exact False.elim (show False from (Set.notMem_empty a.val) (hA ▸ a.property))
    · intro b
      exact False.elim (show False from (Set.notMem_empty b.val) (hB ▸ b.property))

end DiamondIntegral.Section3
