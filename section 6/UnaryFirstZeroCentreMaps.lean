import «section 6».UnaryFirstZeroStates
import «section 6».LabelConstantScalarValues
import «section 6».OrdinaryChainZeroEndpoints

/-! Pull the actual current focus back through the whole preparation.
Live commutation and zero persistence prove that this is an original
exceptional centre. The complete map is over the original base and is
constant on the retained RV-label fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ r s : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (tail : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.centripetal D) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.centripetal D) tail) hT)

def unrestrictedCentreMap (h00 : M ⊨ Axioms.ACVF00) :
    Map (focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) A₀ :=
  (Z.map.inverse (Z.chain.bijective h00)).comp
    ((Z.frame.wholeFocusData D hT.1.2).focusPointMap Z.pullback)

theorem unrestrictedCentreMap_point (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    Z.map (Z.unrestrictedCentreMap D tail hT h00 p)=
      (Z.frame.wholeFocusData D hT.1.2).focusPointMap Z.pullback p :=
  Map.apply_inverse Z.map (Z.chain.bijective h00) _

theorem unrestrictedCentreMap_live (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.map (Z.unrestrictedCentreMap D tail hT h00 p)).val.2 ∈ Z.frame.liveLabels.carrier := by
  have hMap := congrArg (fun a : Z.frame.current => a.val.2) (Z.unrestrictedCentreMap_point D tail hT h00 p)
  have hPoint := congrArg (fun a : Mixed M 1 Z.arity => a.2)
    ((Z.frame.wholeFocusData D hT.1.2).focusPointMap_value Z.pullback p)
  have hTags := hMap.trans hPoint
  exact hTags.symm ▸ Z.frame.activeTags_live D hT.1.2 p.property.2

theorem unrestrictedCentreMap_ordinary_zero (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (D.toFocusGeometry.eta (Z.ordinaryMap (Z.unrestrictedCentreMap D tail hT h00 p)).val).1 0=(0 : VF M) := by
  let a := Z.unrestrictedCentreMap D tail hT h00 p
  have hLive := Z.unrestrictedCentreMap_live D tail hT h00 p
  have hPoint : (Z.map a).val=(Z.frame.liveFocusPointMap D hT.1.2 Z.pullback p).val := by
    have h := congrArg (fun a : Z.frame.current => a.val) (Z.unrestrictedCentreMap_point D tail hT h00 p)
    exact h
  have hEq : (⟨(Z.map a).val,(Z.map a).property,hLive⟩ : Z.frame.liveFrame.source)=
      Z.frame.liveFocusPointMap D hT.1.2 Z.pullback p := Subtype.ext hPoint
  have hOrd : Z.ordinaryMap a=Z.frame.oldMap (Z.frame.liveFocusPointMap D hT.1.2 Z.pullback p) :=
    (Z.live_agrees a hLive).symm.trans (congrArg Z.frame.oldMap hEq)
  change (D.toFocusGeometry.eta (Z.ordinaryMap a).val).1 0=(0 : VF M)
  rw [hOrd]
  exact Z.frame.liveFocusPointMap_ordinary_zero D hT.1.2 Z.pullback p

theorem unrestrictedCentreMap_mem_centres (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.unrestrictedCentreMap D tail hT h00 p).val ∈ K.centres.carrier := by
  apply (Z.zero_cover _).mp
  exact ordinary_chain_fixes_zero tail _ (Z.unrestrictedCentreMap_ordinary_zero D tail hT h00 p)

def firstZeroCentreMap (h00 : M ⊨ Axioms.ACVF00) :
    Map (focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) K.centres :=
  (Z.unrestrictedCentreMap D tail hT h00).corestrict (Z.unrestrictedCentreMap_mem_centres D tail hT h00)

theorem firstZeroCentreMap_point (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    Z.map (K.centre (Z.firstZeroCentreMap D tail hT h00 p))=
      (Z.frame.wholeFocusData D hT.1.2).focusPointMap Z.pullback p := by
  have hOrig : K.centre (Z.firstZeroCentreMap D tail hT h00 p)=Z.unrestrictedCentreMap D tail hT h00 p :=
    Subtype.ext rfl
  rw [hOrig]
  exact Z.unrestrictedCentreMap_point D tail hT h00 p

theorem firstZeroCentreMap_same_labels (h00 : M ⊨ Axioms.ACVF00)
    (p q : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) (hTags : p.val.2=q.val.2) :
    Z.firstZeroCentreMap D tail hT h00 p=Z.firstZeroCentreMap D tail hT h00 q := by
  apply Subtype.ext
  have hPoint := (Z.frame.wholeFocusData D hT.1.2).focusPointMap_same_labels Z.pullback p q hTags
  have h := congrArg (Z.map.inverse (Z.chain.bijective h00)).toFun hPoint
  have hv := congrArg (fun a : A₀ => a.val) h
  exact hv

end DiamondIntegral.Section6.UnaryFirstZeroState
