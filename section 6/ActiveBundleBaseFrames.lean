import «section 6».ActiveBundleBaseReplacement
import «section 6».CoordinateStepFibres

/-! Dropping the active coordinate after its actual centripetal step
and regularization yields a full RV refinement of the unchanged base.
This keeps the base transformation available for later deferral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n r) S} {k : Fin r}

def activeBundleStepBase (D : CentripetalData (G := G) (rvCoordinateBundle B k)) :=
  (vfDropLast (regularizeMap D.map.image).image).image

theorem activeBundle_step_oldTags (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (p : rvCoordinateBundle B k) : coordinateStepOldTags (centripetalStepMap D p).val.2=p.val.2 := by
  funext i
  change (regularize (D.point p.val)).2 (Fin.natAdd (n+1) (Fin.natAdd 1 i))=p.val.2 i
  simp only [regularize,CentripetalData.point,Fin.append_right]

theorem activeBundle_step_base_recovery (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle B k) :
    (Fin.init (centripetalStepMap D p).val.1,coordinateStepOldTags (centripetalStepMap D p).val.2)=
      (Fin.init p.val.1,p.val.2) :=
  Prod.ext (activeBundle_point_base D hCoord p) (activeBundle_step_oldTags D p)

theorem activeBundleStepBase_old_subset (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (q : activeBundleStepBase D) :
    (q.val.1,coordinateStepOldTags q.val.2) ∈ B.carrier := by
  obtain ⟨z,hz⟩ := q.property
  obtain ⟨p,hp⟩ := centripetalStepMap_surjective D z
  have hBase : (Fin.init (centripetalStepMap D p).val.1,(centripetalStepMap D p).val.2)=q.val :=
    (congrArg (fun w : (regularizeMap D.map.image).image => (vfDropLast (regularizeMap D.map.image).image w).val) hp).trans hz
  have h := congrArg (fun w : Mixed M n ((n+1)+(1+r)) => (w.1,coordinateStepOldTags w.2)) hBase
  have he : (q.val.1,coordinateStepOldTags q.val.2)=(Fin.init p.val.1,p.val.2) :=
    h.symm.trans (activeBundle_step_base_recovery D hCoord p)
  exact he.symm ▸ p.property.1

theorem activeBundleStepBase_fibres (D : CentripetalData (G := G) (rvCoordinateBundle B k))
    (hCoord : D.coordinate=Fin.last n) (v : Fin ((n+1)+(1+r)) → RVInfinity M) :
    vfFibre (activeBundleStepBase D).carrier v=∅ ∨
      vfFibre (activeBundleStepBase D).carrier v=vfFibre B.carrier (coordinateStepOldTags v) := by
  by_cases hNE : (vfFibre (activeBundleStepBase D).carrier v).Nonempty
  · right
    obtain ⟨b,z,hz⟩ := hNE
    obtain ⟨p,hp⟩ := centripetalStepMap_surjective D z
    have hBase : (Fin.init (centripetalStepMap D p).val.1,(centripetalStepMap D p).val.2)=(b,v) :=
      (congrArg (fun w : (regularizeMap D.map.image).image => (vfDropLast (regularizeMap D.map.image).image w).val) hp).trans hz
    have hTags : (centripetalStepMap D p).val.2=v := congrArg Prod.snd hBase
    have hOld : p.val.2=coordinateStepOldTags v :=
      (activeBundle_step_oldTags D p).symm.trans (congrArg coordinateStepOldTags hTags)
    apply Set.Subset.antisymm
    · intro a ha
      exact activeBundleStepBase_old_subset D hCoord ⟨(a,v),ha⟩
    · intro a ha
      have hA : (a,p.val.2) ∈ B.carrier := hOld.symm ▸ ha
      obtain ⟨q,hQOld,hQBase,hQTags,hQLast⟩ := activeBundle_step_base_replacement D hCoord p a hA
      exact ⟨centripetalStepMap D q,Prod.ext hQBase (hQTags.trans hTags)⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNE)

def activeBundleBaseFrame
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    RVRefinementFrame B := by
  have hStep := regularization_properInvariant h00 hc hκ hs hv D.map.image
    (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
  have hDB := regularized_vfDoublyBounded D.image_vfDoublyBounded
  exact {
    arity := (n+1)+(1+r)
    base := activeBundleStepBase D
    labels := fun i => Fin.natAdd (n+1) (Fin.natAdd 1 i)
    proper := vfDropLast_image_properInvariant hStep
    doublyBounded := vfDropLast_image_doublyBounded hDB
    fibres := activeBundleStepBase_fibres D hCoord }

end DiamondIntegral.Section6
