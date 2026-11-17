import «section 3».GammaRetainedContractionValues
import Integration7.GammaRVLabelCuts

/-! Restrictions retain the actual old-label form. Pure RV label cuts
have native containing-context presentations with their literal domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n d : ℕ}
namespace GammaRetainedMeasuredVFData
variable (U : GammaRetainedMeasuredVFData hc B (n+1))

def restrict (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier) : GammaRetainedMeasuredVFData hc B (n+1) where
  arity := U.arity
  domain := A
  finite x := (U.finite x).subset (fun _ h => hA h)
  labels := U.labels
  labels_mem p := U.labels_mem ⟨p.val,hA p.property⟩
  form := U.form

theorem restrict_toMeasured (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier) : (U.restrict A hA).toMeasured = U.toMeasured.restrict A hA := rfl

def labelCut (C : BaseContext M) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (ρ : Fin d → Fin U.arity) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable B R) :
    GammaRetainedMeasuredVFData hc B (n+1) :=
  let A := rvLabelCut (U.nativeSet C hNames) U.point_definable ρ R hR hNames
  let hA := gamma_rv_label_cut (U.nativeSet C hNames) U.point_definable ρ R hR
  U.restrict (Section5.nativeGammaPointDomain (carrier A) hA) (fun _ h => h.1)

theorem labelCut_carrier (C : BaseContext M) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (ρ : Fin d → Fin U.arity) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable B R) :
    (U.labelCut C hNames ρ R hR).domain.carrier =
      {p | p ∈ U.domain.carrier ∧ (Fin.elim0,p.2 ∘ ρ) ∈ R} := rfl

end GammaRetainedMeasuredVFData
end DiamondIntegral.Section3
