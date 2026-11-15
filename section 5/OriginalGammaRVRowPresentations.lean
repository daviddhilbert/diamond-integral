import «section 5».OriginalRVRowProducts
import «section 5».OriginalEulerRowValues
import «section 4».Section3GammaRVCodeBridge
import «section 3».RVUnitGammaCodeBijection

/-! A full original Gamma row schema is exactly the actual native RV
code lift of the Gamma set it represents, including all representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n a b : ℕ} {sp : Fin p → SortTag}

theorem originalGammaRVRow_raw
    (D : GammaDomainFormula B p n sp) (z : Fin p → M)
    (I : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ ((volumeGammaSpace hc).power (Fin n)))
    (hrep : gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z) I.carrier) :
    {v | Fin.append z v ∈ D.val} = rawDomain (gammaGroundGammaRVCodeLift I).domain := by
  rw [Section3GammaRVCodeBridge.rawDomain_codeLift]
  ext v
  exact (gammaDomainSyntax_realize hc B D z v).symm.trans (hrep v)

def originalGammaRVRowBijection
    (D : GammaDomainFormula B p n sp) (z : Fin p → M)
    (I : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ ((volumeGammaSpace hc).power (Fin n)))
    (hrep : gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z) I.carrier) :
    GammaGroundBijection (originalRVRowDomain hc D z) (gammaGroundGammaRVCodeLift I).domain :=
  gammaGroundBijectionOfRawDomainEq _ _ ((originalRVRowDomain_raw D z).trans (originalGammaRVRow_raw D z I hrep))

theorem originalDomainProduct_presents_rawProduct
    (F : GammaDomainFormula B p a sp) (G : GammaDomainFormula B p b sp) (z : Fin p → M)
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) b))
    (hF : {v | Fin.append z v ∈ F.val} = rawDomain A)
    (hG : {v | Fin.append z v ∈ G.val} = rawDomain C) :
    {w | Fin.append z w ∈ (originalDomainProduct F G).val} = rawDomain (gammaGroundRVProductDomain A C) := by
  ext w
  exact (originalDomainProduct_row F G z w).trans
    ((and_congr (Set.ext_iff.mp hF _) (Set.ext_iff.mp hG _)).trans (rawDomain_product A C w).symm)

end DiamondIntegral.Section5
