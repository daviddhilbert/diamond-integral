import «section 3».GammaRelativeRetainedContractionValues
import Integration7.GammaRVGraphRefinementGeometry
import Integration7.VFVolumeBijections

/-! RV graph refinements preserve every retained original-Gamma form
and every specified contraction order. The argument is the actual
VF-fixed refinement map from the RV-density proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRVGraph_refinement_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n a d : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap B (carrier A) d)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction A σ) (W : StandardContraction (gammaRVGraphRefinement A P hNames) σ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC
        (gamma_rv_graph_refinement_target_gamma A P hNames)
        (gamma_rv_graph_refinement_finite_labels A hfin P hNames) W hW
        (gammaTotalRVCoordinateForm (Fin.castAdd d) ω)) := by
  let H := gammaRVGraphRefinement A P hNames
  let hH := gamma_rv_graph_refinement_target_gamma A P hNames
  let hfinH := gamma_rv_graph_refinement_finite_labels A hfin P hNames
  let f := SpecialTransformations.Section5.Map.toImage (gammaRVGraphRefinementMap A P hNames)
  let η := gammaTotalRVCoordinateForm (Fin.castAdd d) ω
  have hForm (p : A) : η ⟨(f p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩ := by
    apply congrArg ω
    apply Subtype.ext
    funext i
    exact Fin.append_left p.val.2 (P.toFun p) i
  have hJ := vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ n) (rawSpecialMap hc f) (fun _ => rfl)
  exact gammaRelative_retained_contraction_values C hBC hv hg δ hδ hδ1 hA hH hfin hfinH ω η f
    (gamma_rv_graph_refinement_bijective A P hNames) (gamma_rv_graph_refinement_map_gamma A P hNames)
    hForm hJ (gamma_rv_graph_refinement_unary_relative A P hNames (σ 0)) T W hT hW

end DiamondIntegral.Section3
