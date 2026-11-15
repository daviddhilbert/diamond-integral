import «section 5».OriginalPredicateSyntax
import «section 5».NativeSetBijections
import «section 4».Section3RVCodeBridge

/-! Every original RV-domain row realizes an actual native RV domain,
and every actual RV domain at a parameter has such a presentation. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

def originalRVRowDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p a sp) (z : Fin p → M) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a) :=
  ofRaw {v | Fin.append z v ∈ D.val} (gamma_tuple_parameter_specialize sp (fun _ => .rv) z D.property)

theorem originalRVRowDomain_raw (D : GammaDomainFormula B p a sp) (z : Fin p → M) :
    rawDomain (originalRVRowDomain hc D z) = {v | Fin.append z v ∈ D.val} :=
  rawDomain_ofRaw _ _

theorem original_rv_domain_at_parameter
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a)) :
    ∃ D : GammaDomainFormula B p a sp,
      {v | Fin.append z v ∈ D.val} = rawDomain A ∧
        Nonempty (GammaGroundBijection (originalRVRowDomain hc D z) A) := by
  obtain ⟨D,hD⟩ := promote_original_gamma_predicate hc B sp z hz (rawDomain A) (rawDomain_definable A)
  have hrow : {v | Fin.append z v ∈ D.val} = rawDomain A := by
    ext v
    exact (gammaDomainSyntax_realize hc B D z v).symm.trans (hD v)
  exact ⟨D,hrow,⟨gammaGroundBijectionOfRawDomainEq _ _ ((originalRVRowDomain_raw D z).trans hrow)⟩⟩

end DiamondIntegral.Section5
