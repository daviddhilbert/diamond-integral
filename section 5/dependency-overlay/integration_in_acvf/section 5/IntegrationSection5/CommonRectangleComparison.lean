import IntegrationSection5.CommonRectangleSwap
import IntegrationSection5.CommonProductNComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def final_rectangle_profile_comparison (Z : CommonProductNComparison T δ hδ) :
    GammaRVIso G (Z.matching.leftRProfile Z.left) (Z.matching.rightRProfile Z.right) := by
  let Q := Z.matching
  let U := Q.leftRProfile Z.left
  let V := Q.rightRProfile Z.right
  let W := @SpecialTransformations.Section4.RVObject.reindexVolume M (@CanonicalStructure.normalize M sM)
    Q.unary.codes 2 2 V (Equiv.swap 0 1)
  let f : Map Q.leftRSource (rvObjectDomain W) := Map.comp (Q.rightRRawMap Z.right) Q.rectangleSwap
  have hKer (p q : Q.leftRSource) : Q.leftRRawMap Z.left p = Q.leftRRawMap Z.left q ↔ f p = f q := by
    change _ ↔ Q.rightRRawMap Z.right (Q.rectangleSwap p) = Q.rightRRawMap Z.right (Q.rectangleSwap q)
    rw [Q.leftRRawMap_kernel Z.left,Q.rightRRawMap_kernel Z.right,Q.rightRDMap_swap,Q.rightRDMap_swap,
      Q.rightREMap_swap,Q.rightREMap_swap]
    exact and_comm
  have hVol (p : Q.leftRSource) : (rvObjectVolume W (f p)).val = (rvObjectVolume U (Q.leftRRawMap Z.left p)).val := by
    change (rvObjectVolume V (Q.rightRRawMap Z.right (Q.rectangleSwap p))).val ∘ (Equiv.swap 0 1) = _
    rw [Q.rightRRawMap_volume Z.right,Q.leftRRawMap_volume Z.left,Q.rightRDMap_swap,Q.rightREMap_swap]
    funext i
    fin_cases i <;> rfl
  have hFG := (gammaLogicInput G).comp_graph Q.rectangleSwap_graph (Q.rightRRawMap_graph Z.right)
  have hFΓ : GammaGraphDefinable G (rvOutputGraph f) := by
    apply GammaGraphDefinable.congr hFG
    intro p q
    constructor
    · rintro ⟨w,⟨a,ha,hw⟩,b,hb,hq⟩
      have he : b = Q.rectangleSwap a := Subtype.ext (hb.trans hw.symm)
      subst b
      exact ⟨a,ha,hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨(Q.rectangleSwap a).val,⟨a,ha,rfl⟩,Q.rectangleSwap a,rfl,hq⟩
  let e := gammaRVIsoOfSurjectiveKernels U W (Q.leftRRawMap Z.left) (Q.leftRRawMap_surjective Z.left)
    f ((Q.rightRRawMap_surjective Z.right).comp Q.rectangleSwap_bijective.2) hKer hVol
    (Q.leftRRawMap_graph Z.left) hFΓ
  have hV : GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity V) | p.2 ∈ carrier (rvObjectDomain V)} :=
    gamma_rawOutput_target (Q.rightRRawMap Z.right) (Q.rightRRawMap_surjective Z.right) (Q.rightRRawMap_graph Z.right)
  exact e.trans (GammaRVIso.reindexVolume V (Equiv.swap 0 1) hV).symm

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
