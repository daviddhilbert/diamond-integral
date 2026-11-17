import «section 3».GammaNativeVFSliceDensities
import «section 3».GammaMeasuredRawRowForms
import «section 3».GammaGroundRealExtensions

/-! Actual inclusions of full unary RV slice lifts into the native VF
lift with its frozen prefix. Precisely the frozen VF tuple is added to
the real parameters; the Gamma base is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

def universalMixedPrefixInsert (B : Base (M := M)) (x : Fin p → VF (M := M)) :
    Map (DefSet.univ (rawMixedSpace (M := M) 1 a) (B.real ∪ Set.range (vfValues x)))
      (DefSet.univ (rawMixedSpace (p+1) a) (B.real ∪ Set.range (vfValues x))) := by
  let f (q : Section2.Mixed M 1 a) : Section2.Mixed M (p+1) a := (Fin.append x q.1,q.2)
  let F (z : Fin 1 ⊕ Fin a → M) : Fin (p+1) ⊕ Fin a → M :=
    Sum.elim (Fin.append (vfValues x) (fun j => z (.inl j))) (fun j => z (.inr j))
  have hF : (B.real ∪ Set.range (vfValues x)).DefinableMap LRV F := by
    intro i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have hc : Set.DefinableFun LRV (B.real ∪ Set.range (vfValues x))
            (fun _ : Fin 1 ⊕ Fin a → M => vfValues x j) :=
          LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
        simpa only [F,Sum.elim_inl,Fin.append_left] using hc
      · have hp : Set.DefinableFun LRV (B.real ∪ Set.range (vfValues x))
            (fun z : Fin 1 ⊕ Fin a → M => z (.inl j)) := Set.DefinableFun.proj LRV
        simpa only [F,Sum.elim_inl,Fin.append_right] using hp
    | inr i => exact Set.DefinableFun.proj LRV
  have hcode (c : (rawMixedSpace (M := M) 1 a).domain) :
      mixedValues (f ((rawMixedSpace 1 a).decode c)) = F c.val := by
    funext i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [f,F,mixedValues,vfValues,Fin.append_left,Sum.elim_inl]
      · simpa only [f,F,mixedValues,vfValues,Fin.append_right,Sum.elim_inl] using congrFun (mixedValues_decode c) (.inl j)
    | inr i => exact congrFun (mixedValues_decode c) (.inr i)
  refine Map.ofCodes _ f F hF
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace 1 a).decode c))) ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode _).trans (hcode c).symm

variable (U : GammaObjectAt B Set.univ (p+1))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
variable (x : Fin p → VF (M := M)) (hF : (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity U.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowVolume (vfValues x)))

include hF in
theorem gammaNativeSliceRow_lift (q : Section2.Mixed M 1 (rvObjectArity U.object.obj)) :
    q ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier ↔
      (Fin.append x q.1,q.2) ∈ (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier :=
  (gammaNativeLift_membership (gammaUniversalObject P.toGamma) q).trans
    (((gammaNativeMeasuredVFSliceSchema U ω N).rawRow_volume (vfValues x) hF P q.2
      (@Section2.tupleRV M sM hM 1 q.1)).symm.trans (gammaNativeVFSliceSchema_lift U x q.1 q.2).symm)

def gammaNativeSliceRowInclusion :
    GammaGroundMap (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain
      ((gammaNativeUnitLift (hc := hc) U.toGamma).domain.monoReal Set.subset_union_left) :=
  GammaGroundMap.ofGlobal _ _ (universalMixedPrefixInsert B x)
    (fun q => (gammaNativeSliceRow_lift U ω N x hF P q.val).mp q.property)

theorem gammaNativeSliceRowInclusion_value
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    (gammaNativeSliceRowInclusion U ω N x hF P q).val = (Fin.append x q.val.1,q.val.2) := rfl

theorem gammaNativeSliceRowInclusion_injective : Function.Injective (gammaNativeSliceRowInclusion U ω N x hF P) := by
  intro q r h
  have he := congrArg Subtype.val h
  apply Subtype.ext
  have hRV : q.val.2 = r.val.2 :=
    congrArg (fun z : Section2.Mixed M (p+1) (rvObjectArity U.object.obj) => z.2) he
  refine Prod.ext (funext (fun j => ?_)) hRV
  have hj := congrArg (fun z : Section2.Mixed M (p+1) (rvObjectArity U.object.obj) => z.1 (Fin.natAdd p j)) he
  simpa only [gammaNativeSliceRowInclusion_value,Fin.append_right] using hj

end DiamondIntegral.Section3
