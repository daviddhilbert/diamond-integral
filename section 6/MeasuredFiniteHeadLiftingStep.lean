import «section 6».OriginalBaseAffineTailData
import «section 6».MeasuredRVLiftRepair

/-! The lower-rank lifting step with actual finite heads already first.
The entire bad-head-label domain is replaced by the smaller-rank
induction lift; all tail coefficients and the ambient map are built. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k m : ℕ}

theorem exists_measured_rv_lift_of_finite_headLift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : EverywhereMeasuredRVLift (measuredRVHeadIso hc e
      (productLeft (k+1) m) (productLeft (k+1) m) hU hV)) (j : Fin m)
    (hLower : ∀ (D : DefSet (rawRVSpace (M := M) U.object.arity) (S : Set M))
      (hD : D.carrier ⊆ U.object.domain.carrier), rvDim D < k+1 →
        Nonempty (EverywhereMeasuredRVLift (e.restrict D hD))) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  obtain ⟨T⟩ := exists_fullAffineTailData_vfGenerated h00 hc hκ hs hv S B hsmall e hU hV F
  obtain ⟨f,hf,hLabel,D,hD,hDim,hGood⟩ := exists_affineLift_small_head_jacobian_exception
    h00 hc hκ.le hs hsmall hΓ hv U V hU hV F.map F.bijective
    (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩)
    T.a T.b T.D T.c j T.a_nonzero T.b_nonzero T.a_rv T.b_rv T.head_det T.correction
  have hLabel' (p : rvLift U.object) : e.iso.hom.map.graph p.val.2 (f p).val.2 := by
    let x := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p
    obtain ⟨u,hu,hv⟩ := F.labels x
    exact ⟨u,hu,hv.trans (hLabel p).symm⟩
  let E := rvLift (U.object.restrict D hD)
  have hE : E.carrier ⊆ (rvLift U.object).carrier := fun _ h =>
    ((rvLift_restrict_mem_iff U.object D hD _).mp h).1
  have hCover : (badRVLiftLabels U.object E hE).carrier ⊆ D.carrier := by
    rintro t ⟨q,rfl⟩
    exact ((rvLift_restrict_mem_iff U.object D hD q.val).mp q.property).2
  let g := Classical.choice (hLower D hD hDim)
  apply exists_repaired_measured_rv_lift e f hf hLabel' E hE D hD hCover g
  intro p hp
  have hpD : p.val.2 ∉ D.carrier := by
    intro h
    exact hp ((rvLift_restrict_mem_iff U.object D hD p.val).mpr ⟨p.property,h⟩)
  obtain ⟨L,hL,hJ⟩ := hGood p hpD
  refine ⟨L,hL,?_⟩
  rw [hJ,liftLabelMap_target_of_graph e.iso.hom.map f hLabel' p]
  exact T.c_value (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p)

end DiamondIntegral.Section6
