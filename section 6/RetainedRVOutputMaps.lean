import «section 6».RVGrafting
import «section 6».RVRefinementCoveredBases

/-! Apply a full definable map while retaining the complete old RV
tuple as additional labels. This is the actual map used to port a base
homeomorphism through a full RV-label refinement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

def retainedRVOutputMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :
    Map A (DefSet.univ (rawMixedSpace (M := M) m (s+r)) S) := by
  let B' := toOrdinarySet hc B
  let D := DefSet.univ (rawMixedSpace (M := M) 0 r) S
  let D' := toOrdinarySet hc D
  let τ := rvProjection (Map.id A)
  exact fromOrdinaryMap hc (SpecialTransformations.Section5.Map.comp
    (SpecialTransformations.Section5.attachRVMap B' D')
    (SpecialTransformations.Section5.Map.pair (toOrdinaryMap hc f) (toOrdinaryMap hc τ)))

def retainedRVOutput (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :=
  (retainedRVOutputMap hc f).toImage

theorem retainedRVOutputMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) (p : A) :
    (retainedRVOutputMap hc f p).val=((f p).val.1,Fin.append (f p).val.2 p.val.2) := rfl

theorem retainedRVOutput_value (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) (p : A) :
    (retainedRVOutput hc f p).val=((f p).val.1,Fin.append (f p).val.2 p.val.2) := rfl

theorem retainedRVOutput_retained (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (p : A) (i : Fin r) : (retainedRVOutput hc f p).val.2 (Fin.natAdd s i)=p.val.2 i := by
  simp only [retainedRVOutput_value,Fin.append_right]

theorem retainedRVOutput_selected (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (p : A) : ((retainedRVOutput hc f p).val.1,(retainedRVOutput hc f p).val.2 ∘ Fin.castAdd r)=(f p).val := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [retainedRVOutput_value,Function.comp_apply,Fin.append_left]

end DiamondIntegral.Section6
