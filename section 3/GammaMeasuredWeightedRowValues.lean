import «section 3».GammaMeasuredFullSchemaRows
import «section 3».GammaNativeCombinedWeights
import «section 3».GammaMeasuredCodeProducts
import Integration7.GammaWeightedVolumeGraphs

/-! Interpret an existing weighted-row tuple as the full measured Gamma
weight of its actual label. Every density representative gives that same
weight, so no choice of RV-valued density function is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaMeasured_weighted_row_value
    (z : Fin p → M) (U : GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ Set.univ (k+1))
    (hU : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain U))
    (F : GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) (k+1) sp)
    (hF : gammaSchemaRepresents U.toGamma F.object z)
    (hDensity : ∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔
      Fin.append x y ∈ gammaRVFormCodeRows ω)
    (x : Fin (rvObjectArity U.object.obj) → M)
    (w : Fin ((k+1)+1) → CanonicalRV.RVSort M)
    (hw : Fin.append (Fin.append z x) (rvValues w) ∈ weightedVolumeGraph F.toRVTemplate) :
    ∃ u : Section5.nativeRVGroundDomain (hc := hc) U,
      rvValues u.val = x ∧ (∀ i, (w i).val ≠ iRVZero) ∧
      Values.vrv (∏ i, w i) = gammaNativeCombinedWeight U ω u := by
  have hParts := (weightedVolumeGraph_parts F.toRVTemplate z x (rvValues w)).mp hw
  obtain ⟨a,ha,hv⟩ := (gammaRawObjectVolume_append_iff U.toGamma.toGammaRVObject _ _).mp
    ((hF.2 x (rvValues w ∘ Fin.castAdd 1)).mp hParts.1)
  let u := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm a
  have hu : rvValues u.val = x := ha
  have hVol : (Section5.nativeRVGroundVolume U u).val = (rvObjectVolume U.object.obj a).val := by
    rw [gammaNativeRVGroundVolume_value]
    congr 1
  have hHead : w ∘ Fin.castAdd 1 = (Section5.nativeRVGroundVolume U u).val := by
    apply rvValues_injective
    exact hv.symm.trans (congrArg rvValues hVol.symm)
  have hCode : rvValues w ∘ Fin.natAdd (k+1) ∈ (volumeGammaSpace hc).domain := by
    simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hParts.2
  let c : (volumeGammaSpace hc).domain := ⟨rvValues w ∘ Fin.natAdd (k+1),hCode⟩
  have hcValue : (volumeGammaSpace hc).decode c = (ω u).val := by
    have hd := (hDensity x c.val).mp hParts.2
    rw [← hu] at hd
    obtain ⟨v,hv,hω⟩ := (gammaRVFormCodeRows_mem ω u.val c).mp hd
    have hEq : v = u := Subtype.ext hv
    subst v
    exact hω.symm
  have hTuple : Fin.append (Section5.nativeRVGroundVolume U u).val (gammaVolumeCodeRV c) = w := by
    have hTail : gammaVolumeCodeRV c = w ∘ Fin.natAdd (k+1) := by
      funext i
      apply Subtype.ext
      rfl
    rw [hTail,← hHead]
    exact Fin.append_castAdd_natAdd
  refine ⟨u,hu,?_,?_⟩
  · rw [← hTuple]
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left,hVol]
      intro hz
      exact (gammaFullWeightAt_iff_nonzero U).mp hU a j
        (hz.trans (CanonicalStructure.sortZero_normalize .rv).symm)
    · rw [Fin.append_right]
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact c.property.2
  · rw [← hTuple]
    exact gammaMeasuredCodeProduct ω u (Section5.nativeRVGroundVolume U u).val c hcValue

end DiamondIntegral.Section3
