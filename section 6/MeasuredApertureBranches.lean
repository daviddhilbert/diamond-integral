import «section 6».MeasuredSynchronizedCarrying
import «section 6».CoreGammaForms
import «section 6».SynchronizedApertureBranches

/-! Measured replacements on the actual retained core and released
annulus. Each lower-dimensional measured preparation lifts through the
full RV-disc coordinate, with its exact descended form, every literal
protected image and the common synchronized chain retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_synchronized_core_of_projected_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S} (D : CentripetalData (G := G) A)
    (hj : D.coordinate=Fin.last (n+1)) (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map D.coreProjection (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ q : D.coreRegularizedImage,η ((vfDropLast D.coreRegularizedImage).toImage q)=D.coreGammaForm h00 ω q)
    (F : MeasuredCoordinatePreparation (G := G) D.coreProjection (fun i => (E i).coreProjection)
      (fun i => (hRestr i).core_projection_subset h00) η)
    (hF : SynchronizedCentripetalChain (G := G) (Fin k) D.coreProjection F.target F.map
      (fun i => (E i).coreProjection)) :
    ∃ T : MeasuredCoordinatePreparation (G := G) D.coreRegularizedImage (fun i => (E i).coreRegularizedImage)
        (fun i => (hRestr i).core_image_subset h00) (D.coreGammaForm h00 ω),
      SynchronizedCentripetalChain (G := G) (Fin k) D.coreRegularizedImage T.target T.map
        (fun i => (E i).coreRegularizedImage) ∧
      ∀ p : D.coreRegularizedImage,(T.map p).val.1 (Fin.last (n+1))=p.val.1 (Fin.last (n+1)) := by
  apply measured_synchronized_preparation_carrying_coordinate h00 hc hκ hs hv
    (D.coreProjection_properInvariant h00 hc hκ hs hv) D.coreProjection_doublyBounded F hF
    (Fin.castAdd (1+r) (Fin.last (n+1))) D.coreRegularizedImage (fun i => (E i).coreRegularizedImage)
    (fun i => (hRestr i).core_image_subset h00) (D.coreRegularizedImage_bundle h00 hj)
    (fun i => (E i).coreRegularizedImage_bundle h00 ((hRestr i).coordinate.trans hj)) (D.coreGammaForm h00 ω)
  intro q
  exact (gammaFormExtension_at η ((vfDropLast D.coreRegularizedImage).toImage q)).trans
    (congrArg Subtype.val (hη q))

theorem measured_synchronized_released_annulus_of_projected_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S} (D : CentripetalData (G := G) A)
    (hj : D.coordinate=Fin.last (n+1)) (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (c : VF M) (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val}) (hval : vfValue D.coefficient ≤ vfValue c)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map (D.releasedProjection (D.refineCoefficient c hc0 hcdef hval))
      (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ q : D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval),
      η ((vfDropLast (D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval))).toImage q)=
        D.releasedGammaForm (D.refineCoefficient c hc0 hcdef hval) h00 ω q)
    (F : MeasuredCoordinatePreparation (G := G) (D.releasedProjection (D.refineCoefficient c hc0 hcdef hval))
      (fun i => (E i).releasedProjection ((E i).refineCoefficient c hc0 hcdef
        (by rw [(hRestr i).coefficient]; exact hval)))
      (fun i => (hRestr i).released_projection_subset h00 c hc0 hcdef hval) η)
    (hF : SynchronizedCentripetalChain (G := G) (Fin k)
      (D.releasedProjection (D.refineCoefficient c hc0 hcdef hval)) F.target F.map
      (fun i => (E i).releasedProjection ((E i).refineCoefficient c hc0 hcdef
        (by rw [(hRestr i).coefficient]; exact hval)))) :
    ∃ T : MeasuredCoordinatePreparation (G := G) (D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval))
        (fun i => (E i).releasedRegularizedImage ((E i).refineCoefficient c hc0 hcdef
          (by rw [(hRestr i).coefficient]; exact hval)))
        (fun i => (hRestr i).released_image_subset h00 c hc0 hcdef hval)
        (D.releasedGammaForm (D.refineCoefficient c hc0 hcdef hval) h00 ω),
      SynchronizedCentripetalChain (G := G) (Fin k)
        (D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval)) T.target T.map
        (fun i => (E i).releasedRegularizedImage ((E i).refineCoefficient c hc0 hcdef
          (by rw [(hRestr i).coefficient]; exact hval))) ∧
      ∀ p : D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval),
        (T.map p).val.1 (Fin.last (n+1))=p.val.1 (Fin.last (n+1)) := by
  let D' := D.refineCoefficient c hc0 hcdef hval
  let E' (i) := (E i).refineCoefficient c hc0 hcdef (by rw [(hRestr i).coefficient]; exact hval)
  apply measured_synchronized_preparation_carrying_coordinate h00 hc hκ hs hv
    (D.releasedProjection_properInvariant h00 hc linear hκ hs hv hsmall hΓ D') (D.releasedProjection_doublyBounded D')
    F hF (Fin.castAdd (1+r) (Fin.last (n+1))) (D.releasedRegularizedImage D')
    (fun i => (E i).releasedRegularizedImage (E' i))
    (fun i => (hRestr i).released_image_subset h00 c hc0 hcdef hval)
    (D.releasedRegularizedImage_bundle hj c hc0 hcdef hval)
    (fun i => (E i).releasedRegularizedImage_bundle ((hRestr i).coordinate.trans hj)
      c hc0 hcdef (by rw [(hRestr i).coefficient]; exact hval)) (D.releasedGammaForm D' h00 ω)
  intro q
  exact (gammaFormExtension_at η ((vfDropLast (D.releasedRegularizedImage D')).toImage q)).trans
    (congrArg Subtype.val (hη q))

end DiamondIntegral.Section6
