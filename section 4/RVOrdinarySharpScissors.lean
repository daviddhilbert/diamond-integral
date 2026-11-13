import «section 4».RVOrdinaryRing
import «section 4».RVSharpScissors

/-! Ordinary RV classes of full Gamma preimages depend only on their
supports and satisfy the actual support scissor relation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinarySharpScissors
open RVMeasuredCharts RVSharpCharts RVOrdinaryRing GammaChartOperations GammaOrderLogic
open GammaRVChartPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sameSupportIso {B : Base (M := M)} {n : ℕ} (a b : GammaWeightedCharts.Chart B n)
    (h : a.support = b.support) : RVForgetScissors.UnderlyingIso (sharpChart a) (sharpChart b) := by
  apply RVForgetScissors.ofMap (sharpChart a) (sharpChart b) (fun u : Fin n → M => u)
  · exact identity_graph_definable B _ (sharpChart a).domain_definable
  · have hd : (sharpChart a).domain = (sharpChart b).domain := congrArg GammaRVChartPresentation.sharp h
    rw [hd]
    exact Set.bijOn_id _

theorem class_eq_of_support_eq {B : Base (M := M)} {n : ℕ}
    (a b : GammaWeightedCharts.Chart B n) (h : a.support = b.support) :
    objectClass (sharpChart a) = objectClass (sharpChart b) := objectClass_iso (sameSupportIso a b h)

theorem scissor_ofTotal (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinableMaps.MapDefinable B μ) :
    objectClass (sharpChart (ofTotal B n (I ∪ J) hU μ hμ)) +
      objectClass (sharpChart (ofTotal B n (I ∩ J) hN μ hμ)) =
      objectClass (sharpChart (ofTotal B n I hI μ hμ)) +
        objectClass (sharpChart (ofTotal B n J hJ μ hμ)) :=
  objectClass_scissor _ _ _ _ (RVForgetScissors.measured_scissor _ _ _ _
    (RVSharpScissors.sharp_scissor B n I J hI hJ hU hN μ hμ))

theorem empty_support {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (h : a.support = ∅) : objectClass (sharpChart a) = 0 := by
  apply objectClass_empty
  ext u
  change (Proper u ∧ codeValues u ∈ a.support) ↔ False
  rw [h]
  exact ⟨fun hu => hu.2.elim, fun hu => hu.elim⟩

end DiamondIntegral.Section4.RVOrdinarySharpScissors
