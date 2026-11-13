import «section 3».MeasuredRankLayerSourceMatching
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}
variable {L R : GammaGroundMeasuredTensorRankLayer hc B k m}
variable {F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain}
namespace GammaGroundMeasuredTensorRankLayerTwoSidedCover

def sourceUnion (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :=
  gammaGroundDefSetFiniteUnion Finset.univ (fun c : C.MatchedIndex => (C.sourceMap c).image)

def targetUnion (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :=
  gammaGroundDefSetFiniteUnion Finset.univ (fun c : C.MatchedIndex => (C.targetMap c).image)

def residualBijection (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :
    GammaGroundBijection (L.object.underlying.domain.sdiff C.sourceUnion) (R.object.underlying.domain.sdiff C.targetUnion) :=
  gammaGroundMatchedResidualBijection F (fun c => (C.data c).data.bijection) C.sourceMap C.targetMap
    (fun c u => (C.data c).data.agrees u)

/-- The residual map is the restriction of the actual ambient map. -/
theorem residualBijection_agrees (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (x : L.object.underlying.domain.sdiff C.sourceUnion) :
    (C.residualBijection.map x).val = (F.map ⟨x.val,x.property.1⟩).val := rfl

/-- The selected source images still cover every non-exceptional
maximal-rank source point. -/
theorem source_union_or_hyperplane (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (i : Fin L.topCount) (u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i)) :
    (L.unmeasured.topMap i u).val ∈ C.sourceUnion.carrier ∨
      ∃ h ∈ C.sourceHyperplanes i, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  rcases C.source_seed_cover i u with ⟨a,ha⟩ | hu
  · have hmem : (L.unmeasured.topMap i u).val ∈ ((L.unmeasured.topMap i).comp (C.seedMatch i a).source.inclusion).image.carrier := by
      let v : (C.seedMatch i a).source.source := ⟨u.val,ha⟩
      refine ⟨v,?_⟩
      exact congrArg (fun w : gammaGroundNativeProductDomain (L.residue i) (L.gamma i) => (L.unmeasured.topMap i w).val)
        (show (C.seedMatch i a).source.inclusion v = u from Subtype.ext (Prod.eta u.val))
    obtain ⟨c,_,v,hv⟩ := (C.gridMatching i).forget.original_source_covered a hmem
    exact Or.inl ⟨⟨i,c⟩,Finset.mem_univ _,v,hv⟩
  · exact Or.inr hu

/-- Selecting disjoint source cells also retains the complete inverse
generic cover. This supplies the target-side rank reduction. -/
theorem target_union_or_hyperplane (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F)
    (j : Fin R.topCount) (v : gammaGroundNativeProductDomain (R.residue j) (R.gamma j)) :
    (R.unmeasured.topMap j v).val ∈ C.targetUnion.carrier ∨
      ∃ h ∈ C.targetHyperplanes j, rvUnitTupleValues v.val.1 ∈ h.carrier := by
  rcases C.target_cover j v with ⟨i,e,he,hv⟩ | hv
  · let s : C.Seed i := ⟨j,e,he⟩
    let a := Fintype.equivFin (C.Seed i) s
    have ha : C.seed i a = s := (Fintype.equivFin (C.Seed i)).symm_apply_apply s
    have himage := congrArg (fun w : C.Seed i =>
      ((R.unmeasured.topMap w.1).comp w.2.val.target.inclusion).image.carrier) ha
    have hmem : (R.unmeasured.topMap j v).val ∈
        ((R.unmeasured.topMap (C.seedTarget i a)).comp (C.seedMatch i a).target.inclusion).image.carrier := by
      change (R.unmeasured.topMap j v).val ∈ ((R.unmeasured.topMap (C.seed i a).1).comp (C.seed i a).2.val.target.inclusion).image.carrier
      rw [himage]
      let w : e.target.source := ⟨v.val,hv⟩
      refine ⟨w,?_⟩
      exact congrArg (fun z : gammaGroundNativeProductDomain (R.residue j) (R.gamma j) => (R.unmeasured.topMap j z).val)
        (show e.target.inclusion w = v from Subtype.ext (Prod.eta v.val))
    obtain ⟨c,_,w,hw⟩ := (C.gridMatching i).forget.original_target_covered a hmem
    exact Or.inl ⟨⟨i,c⟩,Finset.mem_univ _,w,hw⟩
  · exact Or.inr hv
end GammaGroundMeasuredTensorRankLayerTwoSidedCover
end DiamondIntegral.Section3
