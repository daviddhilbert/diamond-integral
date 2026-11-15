import «section 5».NativeSortedGroundTransfer
import «section 3».GammaGroundRVSemiring
import «section 4».Section3RVChartBridge

/-! Sorted parameter substitution keeps every native RV coordinate and
its finite label map literally unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

def sortedTransferRVVolume {k : ℕ} (U : GammaGroundRVObject hc B k) :
    GammaGroundMap (sortedTransferRVDomain H U.domain) (GammaGroundDefSet.univ hc C (rawRVSpace k)) :=
  (mapOfRaw (rawDomain U.domain) (H _ _ (rawDomain_definable U.domain)) (rawMap U.volume)
    (H _ _ (rawMap_definable U.volume)) (fun x hx i => (Section3RVChartBridge.chart U).coordinate_proper x hx i |>.1)).comp
      (sortedTransferRVRawBijection H U.domain).map

theorem sortedTransferRVVolume_value {k : ℕ} (U : GammaGroundRVObject hc B k)
    (u : sortedTransferRVDomain H U.domain) :
    (sortedTransferRVVolume H U u).val = (U.volume ⟨u.val,u.property⟩).val := by
  apply rvValues_injective
  exact rawMap_apply U.volume ⟨u.val,u.property⟩

def sortedTransferRVObject {k : ℕ} (U : GammaGroundRVObject hc B k) : GammaGroundRVObject hc C k where
  arity := U.arity
  domain := sortedTransferRVDomain H U.domain
  volume := sortedTransferRVVolume H U
  finite t := by
    let s : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k) := ⟨t.val,t.property⟩
    change {u | sortedTransferRVVolume H U u = t}.Finite
    apply (U.finite s).subset
    intro u hu
    apply Subtype.ext
    have he := congrArg Subtype.val hu
    exact (sortedTransferRVVolume_value H U u).symm.trans he
  nonzero u i := by
    have he := congrFun (sortedTransferRVVolume_value H U u) i
    exact he.symm ▸ U.nonzero ⟨u.val,u.property⟩ i

end DiamondIntegral.Section5
