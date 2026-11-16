import «section 6».ContinuousRVFamilyMaps
import «section 6».FullFocusGraphData

/-! Whole continuous RV-family graphs reconstruct actual full focus
data on the exact current active domain. Independence and leading-term
tests are the geometric checks retained by the parameter templates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def fullFocusGraphOfContinuousFamily
    (A : DefSet (rawMixedSpace (M := M) n r) S) (j : Fin n)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M)
    (hf : S.Definable LRV (rvVFGraph f)) (hCont : ∀ u,Continuous (f u))
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hTagged : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hInd : ∀ p q : focusActive A U,p.val.2=q.val.2 →
      (∀ i ≠ j,p.val.1 i=q.val.1 i) → f p.val.2 p.val.1 0=f q.val.2 q.val.1 0)
    (hRV : ∀ p : focusActive A U,rv M (f p.val.2 p.val.1 0)=rv M (p.val.1 j)) :
    FullFocusGraphData (G := G) A where
  coordinate := j
  activeTags := U
  map := rvFamilyMap (focusActive A U) f hf
  independent := hInd
  proper := hA
  doublyBounded := hAD
  tagged := hTagged
  continuous u := ((continuous_apply 0).comp (hCont u)).comp continuous_subtype_val
  leadingTerm := hRV

end DiamondIntegral.Section6
