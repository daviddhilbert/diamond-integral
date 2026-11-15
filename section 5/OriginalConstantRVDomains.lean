import «section 5».OriginalRVRowProducts
import «section 5».OriginalSortedPredicates
import «section 3».GammaGroundRealExtensions

/-! Literal original-ground RV domains give constant families over any
mixed parameter sort. Their rows are actual real-parameter extensions of
the same original domain, without any extra RV parameter or section. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

def originalConstantRVDomain (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (sp : Fin p → SortTag) :
    GammaDomainFormula B p a sp :=
  ⟨{w | w ∈ sortedUniverse (Fin.append sp (fun _ : Fin a => .rv)) ∧
    w ∘ Fin.natAdd p ∈ rawDomain D},
    (OriginalSortedPredicate.of_definable (rawDomain_definable D)).pullback (Fin.natAdd p)
      (fun i => (Fin.append_right sp (fun _ : Fin a => .rv) i).symm)⟩

theorem originalConstantRVDomain_row (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i)) (x : Fin a → M) :
    Fin.append z x ∈ (originalConstantRVDomain D sp).val ↔ x ∈ rawDomain D := by
  change (_ ∧ _) ↔ _
  have ht : Fin.append z x ∘ Fin.natAdd p = x := funext (fun i => Fin.append_right _ _ i)
  rw [ht]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_,hx⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hz j
    · simpa only [Fin.append_right] using (rawDomain_definable D).proper x hx j

def originalConstantRVRowBijection (D : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i)) :
    GammaGroundBijection (originalRVRowDomain hc (originalConstantRVDomain D sp) z)
      (D.monoReal Set.subset_union_left) :=
  gammaGroundBijectionOfRawDomainEq _ _ (by
    ext x
    rw [originalRVRowDomain_raw]
    exact originalConstantRVDomain_row D sp z hz x)

end DiamondIntegral.Section5
