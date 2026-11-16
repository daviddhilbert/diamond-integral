import «section 6».FusionBranchTags
import «section 6».TemplateComponentImages
import «section 6».CorePartitionImages

/-! The actual global centripetal step and regularization form a
literal synchronized chain, with exact full protected images and the
proper RV-pullback ambient required by the branch induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def sourcePiece (i : Fin k) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily R.parameter (P i))

theorem sourcePiece_subset (i : Fin k) : (R.sourcePiece i).carrier ⊆ C.carrier :=
  rvLabelPullback_subset C _ _

def protectedComponent (i : Fin k) : CentripetalData (G := G) (R.sourcePiece i) := (R.restrictions i).choose

theorem protectedComponent_compatible (i : Fin k) : ApertureRestrictionData R.component (R.protectedComponent i) :=
  (R.restrictions i).choose_spec

def stageTarget := (regularizeMap R.component.map.image).image

def stageMap : Map C R.stageTarget := (regularization R.component.map.image).comp R.component.bijection

theorem stageMap_value (p : C) : (R.stageMap p).val=regularize (R.component.point p.val) := rfl

def stagePiece (i : Fin k) := (R.stageMap.restrict (R.sourcePiece_subset i)).image

theorem stagePiece_local_image (i : Fin k) :
    R.stagePiece i=(regularizeMap (R.protectedComponent i).map.image).image := by
  apply defSet_eq_of_carrier_eq
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨(R.protectedComponent i).bijection p,?_⟩
    exact congrArg DiamondIntegral.Section6.regularize ((R.protectedComponent_compatible i).point p.val p.property)
  · rintro ⟨p,rfl⟩
    obtain ⟨a,ha⟩ := p.property
    refine ⟨a,?_⟩
    change regularize (R.component.point a.val)=regularize p.val
    exact congrArg DiamondIntegral.Section6.regularize
      (((R.protectedComponent_compatible i).point a.val a.property).symm.trans ha)

theorem stage_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    SynchronizedCentripetalChain (G := G) (Fin k) C R.stageTarget R.stageMap R.sourcePiece := by
  have hFirst : SynchronizedCentripetalChain (G := G) (Fin k) C R.component.map.image R.component.bijection
      R.sourcePiece := .centripetal C R.component R.sourcePiece R.sourcePiece_subset
        R.protectedComponent R.protectedComponent_compatible
  exact .comp R.sourcePiece R.sourcePiece_subset hFirst
    (.regularize _ (R.component.image_properInvariant h00 hc hκ hs hv) R.component.image_vfDoublyBounded
      _ (fun i z hz => by obtain ⟨a,ha⟩ := hz; exact ha ▸ (R.component.bijection.restrict (R.sourcePiece_subset i) a).property)
      (fun i => ((hFirst.atPiece i).literal_restriction h00 (R.sourcePiece_subset i)).target_properInvariant
        h00 hc hκ hs hv)
      (fun i => R.component.image_vfDoublyBounded.mono (fun z hz => by
        obtain ⟨a,ha⟩ := hz
        exact ha ▸ (R.component.bijection.restrict (R.sourcePiece_subset i) a).property)))

theorem stageTarget_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ProperInvariant S R.stageTarget.carrier :=
  regularization_properInvariant h00 hc hκ hs hv _ (R.component.image_properInvariant h00 hc hκ hs hv)
    R.component.image_vfDoublyBounded

theorem stageTarget_doublyBounded : VFDoublyBounded R.stageTarget.carrier :=
  regularized_vfDoublyBounded R.component.image_vfDoublyBounded

theorem stageTarget_rvPullback (h00 : M ⊨ Axioms.ACVF00) : IsRVPullback R.stageTarget.carrier :=
  R.component.regularized_image_rvPullback h00 R.context.pullback

theorem stageTarget_tagged : ∀ p ∈ R.stageTarget.carrier,∀ z ∈ R.stageTarget.carrier,
    p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
  change ∀ p ∈ (regularizeMap R.component.map.image).image.carrier,
    ∀ z ∈ (regularizeMap R.component.map.image).image.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1
  rw [regularization_carrier]
  exact regularized_tagged _

end DiamondIntegral.Section6.CentripetalFusionRepair
