import «section 5».NativeDomainPresentations
import «section 5».RESFormalExpressions
import «section 5».RESPositiveFamilies

/-! The old degree-filtered coproduct layout is presented structurally.
Its polynomial value is the finite sum of precisely the selected leaves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open RESFiniteWitness
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

def NativeDomainPresentationAt.retargetNative (z : Fin p → M)
    {U V : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k}
    (h : U = V) (P : NativeDomainPresentationAt B sp z U.obj.domain) :
    NativeDomainPresentationAt B sp z V.obj.domain where
  arity := P.arity
  expression := P.expression
  valid := P.valid
  bijection := by cases h; exact P.bijection

abbrev PresentedGradedRESObjectAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M) :=
  (U : GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩) × NativeDomainPresentationAt B sp z U.2.obj.domain

def presentedOldObjects {z : Fin p → M} (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    List (GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩) := L.map Sigma.fst

def presentedDegreeFormal {z : Fin p → M} (k : ℕ) (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    FreeCommRing (RESAtomSchema B p sp) :=
  (L.map (fun U => if U.1.1 = k then U.2.expression.formalValue else 0)).sum

theorem presented_degree_expression_exists (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) (k : ℕ) :
    ∃ P : NativeDomainPresentationAt B sp z
      (positiveFamilyAtDegree hc ⟨B.real ∪ Set.range z, B.gamma⟩ k (presentedOldObjects L)).obj.domain,
      P.expression.formalValue = presentedDegreeFormal k L := by
  induction L with
  | nil => exact ⟨NativeDomainPresentationAt.empty B sp z hz, rfl⟩
  | cons U L ih =>
    rcases U with ⟨⟨d, U⟩, P⟩
    obtain ⟨Q, hQ⟩ := ih
    by_cases h : d = k
    · subst k
      have hobj : positiveFamilyAtDegree hc ⟨B.real ∪ Set.range z, B.gamma⟩ d
          (presentedOldObjects (⟨⟨d, U⟩, P⟩ :: L)) =
          U.coprod (positiveFamilyAtDegree hc ⟨B.real ∪ Set.range z, B.gamma⟩ d (presentedOldObjects L)) := by
        simp [presentedOldObjects, positiveFamilyAtDegree]
      let T := NativeDomainPresentationAt.retargetNative z hobj.symm (P.sum z Q)
      refine ⟨T, ?_⟩
      change P.expression.formalValue + Q.expression.formalValue = _
      simpa [presentedDegreeFormal] using
        congrArg (fun x => P.expression.formalValue+x) hQ
    · have hobj : positiveFamilyAtDegree hc ⟨B.real ∪ Set.range z, B.gamma⟩ k
          (presentedOldObjects (⟨⟨d, U⟩, P⟩ :: L)) =
          positiveFamilyAtDegree hc ⟨B.real ∪ Set.range z, B.gamma⟩ k (presentedOldObjects L) := by
        simp only [presentedOldObjects, List.map_cons, positiveFamilyAtDegree, dif_neg h]
      let T := NativeDomainPresentationAt.retargetNative z hobj.symm Q
      refine ⟨T, ?_⟩
      change Q.expression.formalValue = _
      simpa only [presentedDegreeFormal, List.map_cons, List.sum_cons, if_neg h, zero_add] using hQ

end DiamondIntegral.Section5
