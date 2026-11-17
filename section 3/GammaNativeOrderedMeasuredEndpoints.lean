import «section 3».GammaNativeSelectedMeasuredHeads
import «section 3».GammaSelectedLiteralEndpointValues
import IntegrationSection6.OrderedSelectedVolume

/-! Interpret a specified native ordered contraction using the same
selected retained Gamma data as the checked measured-head induction.
This is a recursive construction from its actual preparation stages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeOrderedEndpoint
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (P : OrderedContractionProgram (C.base : Set M) A D) :
    ∀ (hP : GammaProgramDefinable B P) (hA : GammaSetDefinable B (carrier A))
    {k : ℕ} (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q),
      GammaSelectedRetainedData hc B 0 (orderedVolumeDegree n k) := by
  induction P with
  | zero A =>
    intro hP hA k ρ hfin Q hQ ω
    exact gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω
  | step T tail ih =>
    intro hP hA k ρ hfin Q hQ ω
    let H := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 ρ hfin Q hQ ω
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let E := H.next C.uncountable.le C.saturated hr
    exact ih hP.2.2 (gamma_headImage T.target hP.2.1) E.select E.finite E.labels
      (fun p => E.labels_mem ⟨p.val,p.property⟩) E.form

end DiamondIntegral.Section3
