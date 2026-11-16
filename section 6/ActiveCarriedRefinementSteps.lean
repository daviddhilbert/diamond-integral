import «section 6».ActiveBundleCoordinateReplacement

/-! The actual active centripetal step returns a carried refinement of
the unchanged base, with a literal full-bundle map, proper homeomorphism
and bounded relatively unary chain. -/

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

def activeBundleCarriedFrame
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    CarriedRefinementFrame B := by
  let Y := activeBundleBaseFrame h00 hc hκ hs hv D hCoord
  exact ⟨Y.arity,Y.base,Y.labels,Fin.castAdd (1+r) (Fin.last n),Y.proper,Y.doublyBounded,Y.fibres⟩

theorem activeBundleStepTarget_eq
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    (regularizeMap D.map.image).image=(activeBundleCarriedFrame h00 hc hκ hs hv D hCoord).bundle :=
  defSet_eq_of_carrier_eq (activeBundle_step_full_bundle D hCoord)

def activeBundleStepRetarget
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    Map (rvCoordinateBundle B k) (activeBundleCarriedFrame h00 hc hκ hs hv D hCoord).bundle :=
  changeMapTarget (centripetalStepMap D) (activeBundleStepTarget_eq h00 hc hκ hs hv D hCoord)

theorem activeBundleStepRetarget_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) :
    (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p).val=(centripetalStepMap D p).val :=
  changeMapTarget_value _ _ p

theorem activeBundleStepRetarget_commutes
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) :
    (activeBundleCarriedFrame h00 hc hκ hs hv D hCoord).oldMap
      (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p)=bundleProjection B k p := by
  apply Subtype.ext
  change (Fin.init (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p).val.1,
    coordinateStepOldTags (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p).val.2)=(Fin.init p.val.1,p.val.2)
  rw [activeBundleStepRetarget_value]
  exact activeBundle_step_base_recovery D hCoord p

theorem activeBundleStepRetarget_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    ∃ F : RetainedUnaryHomeChain (G := G) S (activeBundleStepRetarget h00 hc hκ hs hv D hCoord)
      (fun i => Fin.natAdd (n+1) (Fin.natAdd 1 i)),F.DoublyBounded := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let A := rvCoordinateBundle B k
  let W := (regularizeMap D.map.image).image
  let Y := activeBundleCarriedFrame h00 hc hκ hs hv D hCoord
  have H : SpecialCovariantChain (G := G) A W (centripetalStepMap D) :=
    .comp (.centripetal A D) (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)
  have hHome := (H.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ).changeMapTarget
    (activeBundleStepTarget_eq h00 hc hκ hs hv D hCoord)
  obtain ⟨E,hEA,hDim,hUnit⟩ := H.unit_derivative_ae h00 hc hκ.le hs hsmall hv (Nat.zero_lt_succ n)
  let F : RetainedUnaryHomeChain (G := G) S (activeBundleStepRetarget h00 hc hκ hs hv D hCoord)
      (fun i => Fin.natAdd (n+1) (Fin.natAdd 1 i)) :=
    .unary (Fin.last n) hHome
      (by
        intro p i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hNe
          exact (hNe rfl).elim
        · intro _
          rw [activeBundleStepRetarget_value]
          exact congrFun (activeBundle_point_base D hCoord p) j)
      (fun p hInd => (hUnit p (not_mem_small_set_of_independent hc E hDim p.val hInd)).changeMapTarget _)
      (by
        intro p i
        rw [activeBundleStepRetarget_value]
        exact congrFun (activeBundle_step_oldTags D p) i)
  exact ⟨F,⟨D.sourceDoublyBounded,rvCoordinateBundle_doublyBounded Y.base Y.freeLabel Y.doublyBounded Y.proper.rvBounded⟩⟩

end DiamondIntegral.Section6
