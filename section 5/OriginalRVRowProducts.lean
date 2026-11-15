import «section 5».OriginalRVRowObjects
import «section 5».OriginalDomainProducts
import «section 3».GammaGroundRVProductLaws

/-! Canonical original schema products are the literal native RV
cartesian products, with full raw-domain equality. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem rawDomain_product (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) (w : Fin (a+b) → M) :
    w ∈ rawDomain (gammaGroundRVProductDomain A C) ↔
      w ∘ Fin.castAdd b ∈ rawDomain A ∧ w ∘ Fin.natAdd a ∈ rawDomain C := by
  constructor
  · rintro ⟨u,⟨v,hv⟩,huw⟩
    have hraw : rvValues (Fin.append v.val.1 v.val.2) = w := by
      exact (congrArg rvValues hv).trans huw
    refine ⟨⟨v.val.1,v.property.1,?_⟩,⟨v.val.2,v.property.2,?_⟩⟩
    · funext j
      have hj := congrFun hraw (Fin.castAdd b j)
      simpa only [rvValues,Fin.append_left,Function.comp_def] using hj
    · funext j
      have hj := congrFun hraw (Fin.natAdd a j)
      simpa only [rvValues,Fin.append_right,Function.comp_def] using hj
  · rintro ⟨⟨x,hx,hex⟩,⟨y,hy,hey⟩⟩
    refine ⟨Fin.append x y,⟨⟨(x,y),hx,hy⟩,rfl⟩,?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [rvValues,Fin.append_left,Function.comp_def] using congrFun hex j
    · simpa only [rvValues,Fin.append_right,Function.comp_def] using congrFun hey j

theorem originalRVRowDomain_product_raw (F : GammaDomainFormula B p a sp) (G : GammaDomainFormula B p b sp)
    (z : Fin p → M) :
    rawDomain (originalRVRowDomain hc (originalDomainProduct F G) z) =
      rawDomain (gammaGroundRVProductDomain (originalRVRowDomain hc F z) (originalRVRowDomain hc G z)) := by
  ext w
  rw [rawDomain_product,originalRVRowDomain_raw,originalRVRowDomain_raw,originalRVRowDomain_raw]
  exact originalDomainProduct_row F G z w

def originalRVRowProductBijection (F : GammaDomainFormula B p a sp) (G : GammaDomainFormula B p b sp)
    (z : Fin p → M) :
    GammaGroundBijection (originalRVRowDomain hc (originalDomainProduct F G) z)
      (gammaGroundRVProductDomain (originalRVRowDomain hc F z) (originalRVRowDomain hc G z)) :=
  gammaGroundBijectionOfRawDomainEq _ _ (originalRVRowDomain_product_raw F G z)

end DiamondIntegral.Section5
