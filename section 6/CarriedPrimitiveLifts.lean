import «section 6».CarriedChainLifts

/-! Actual carried lifts of both primitive operations. The target is
the precise next bundle, including every regularization and branch tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}

theorem regularize_bundle_label_selection (p : Mixed M (n+1) s) (π : Fin r → Fin s) :
    (Fin.init (regularize p).1,
      (regularize p).2 ∘ (regularizedBundleLabels n s ∘ regularizedLabelSelection n π)) =
      regularize (Fin.init p.1,p.2 ∘ π) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [regularize,Function.comp_apply,regularizedBundleLabels,regularizedLabelSelection,
        Fin.addCases_left,Fin.append_left]
      rfl
    · simp only [regularize,Function.comp_apply,regularizedBundleLabels,regularizedLabelSelection,
        Fin.addCases_right,Fin.append_right]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CarriedChainLift.regularize
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A) :
    CarriedChainLift (G := G) X (regularization A) := by
  let Y := X.afterRegularization h00 hc hκ hs hv
  have hTarget : (regularizeMap X.bundle).image = Y.bundle :=
    (regularizedBundle_defSet_eq X.base X.freeLabel).symm
  let F := changeMapTarget (regularization X.bundle) hTarget
  refine ⟨Y,F,?_,?_,?_⟩
  · exact (SpecialCovariantChain.regularize X.bundle
      (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper)
      (rvCoordinateBundle_doublyBounded X.base X.freeLabel X.doublyBounded X.proper.rvBounded)).changeTarget
        hTarget (fun p => (changeMapTarget_value _ hTarget p).symm)
  · intro p
    rw [show (F p).val = (DiamondIntegral.Section6.regularize p.val) from changeMapTarget_value _ hTarget p]
    exact regularize_bundle_label_selection p.val X.labels
  · intro p
    rw [show (F p).val = DiamondIntegral.Section6.regularize p.val from changeMapTarget_value _ hTarget p]
    rfl

def CarriedChainLift.centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) : CarriedChainLift (G := G) X D.bijection := by
  let Y := X.afterCentripetal h00 hc hκ hs hv D
  let E := X.portComponent D
  have hW := rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper
  let H := E.carryCoordinate X.freeLabel hW
  have hTarget : H.map.image = Y.bundle := defSet_eq_of_carrier_eq (E.carryCoordinate_image X.freeLabel hW)
  let F := changeMapTarget H.bijection hTarget
  refine ⟨Y,F,?_,?_,?_⟩
  · exact (SpecialCovariantChain.centripetal X.bundle H).changeTarget
      hTarget (fun p => (changeMapTarget_value _ hTarget p).symm)
  · intro p
    rw [show (F p).val = H.point p.val from changeMapTarget_value _ hTarget p]
    change (Fin.init (H.point p.val).1,(H.point p.val).2 ∘ prefixLabelSelection X.labels) =
      D.point (X.oldPoint p).val
    rw [E.carryCoordinate_point X.freeLabel hW p.val p.property]
    simp only [Fin.init_snoc]
    exact D.refineLabels_point_commutes X.labels X.proper X.doublyBounded
      (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres
      (Fin.init p.val.1,p.val.2) p.property.1
  · intro p
    rw [show (F p).val = H.point p.val from changeMapTarget_value _ hTarget p]
    rw [E.carryCoordinate_point X.freeLabel hW p.val p.property]
    simp only [Fin.snoc_last]

end DiamondIntegral.Section6
