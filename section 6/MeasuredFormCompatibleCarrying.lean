import «section 6».PreparedMeasuredProgramRealizations
import «section 6».FormCompatibleCarriedPreparation

/-! A synchronized measured preparation on a positive-dimensional
base lifts through a full retained-label VF disc. Its actual Gamma form,
all narrow maps and the common component chain are carried together;
the extra VF coordinate is fixed everywhere. -/

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

theorem measured_form_compatible_preparation_carrying_coordinate
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    {C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
    {η : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (T : MeasuredCoordinatePreparation (G := G) A C hCA η)
    (hT : FormCompatibleSynchronizedChain (G := G) (Fin k) A T.target T.map C η)
    (j : Fin r) (W : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S) (hPA : ∀ i,(P i).carrier ⊆ W.carrier)
    (hW : W.carrier=(rvCoordinateBundle A j).carrier)
    (hP : ∀ i,(P i).carrier=(rvCoordinateBundle (C i) j).carrier)
    (ω : Map W (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hDesc : ∀ p : W,gammaFormExtension η (Fin.init p.val.1,p.val.2)=(ω p).val) :
    ∃ U : MeasuredCoordinatePreparation (G := G) W P hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) W U.target U.map P ω ∧
        ∀ p : W,(U.map p).val.1 (Fin.last (n+1))=p.val.1 (Fin.last (n+1)) := by
  let X := CarriedRefinementFrame.identity A j hA hAD
  obtain ⟨F,hF⟩ := hT.carried_form_compatible_lift_exists h00 hc hκ hs hv X
  have hSelected (i) : X.selectedPiece (C i)=C i := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [X.mem_selectedPiece]
    change (p ∈ A.carrier ∧ (p.1,p.2 ∘ id) ∈ (C i).carrier) ↔ p ∈ (C i).carrier
    simpa only [Function.comp_id,Prod.mk.eta] using
      (show (p ∈ A.carrier ∧ p ∈ (C i).carrier) ↔ p ∈ (C i).carrier from
        ⟨fun h => h.2,fun hp => ⟨hCA i hp,hp⟩⟩)
  let g := F.lift.map.comp (Map.inclusion (fun _ hp => hW ▸ hp))
  have hSource : X.bundle=W := defSet_eq_of_carrier_eq hW.symm
  have hSourceForm (p : X.bundle) : ((η.comp X.oldMap) p).val=
      (ω ⟨p.val,hSource ▸ p.property⟩).val := by
    change (η (X.oldPoint p)).val=(ω ⟨p.val,hSource ▸ p.property⟩).val
    rw [← gammaFormExtension_at η (X.oldPoint p)]
    have hPoint : (X.oldPoint p).val=(Fin.init p.val.1,p.val.2) := by
      change (Fin.init p.val.1,p.val.2 ∘ id)=_
      rw [Function.comp_id]
    rw [hPoint]
    exact hDesc ⟨p.val,hSource ▸ p.property⟩
  have hCert : FormCompatibleSynchronizedChain (G := G) (Fin k) W F.lift.target.bundle g P ω :=
    (hF.changeSource hSource (fun _ => rfl) hSourceForm).changePieces (fun i =>
      defSet_eq_of_carrier_eq (by rw [hSelected i]; exact (hP i).symm))
  have hPrepared (i) : IsRVPullback (g.restrict (hPA i)).image.carrier := by
    have hPieceSource : (rvCoordinateBundle (X.selectedPiece (C i)) X.freeLabel).carrier=(P i).carrier := by
      rw [hSelected i]
      exact (hP i).symm
    have hImage := map_image_carrier_eq_of_source_eq
      (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i))) (g.restrict (hPA i)) hPieceSource (fun _ => rfl)
    rw [← hImage]
    exact F.lift.partition_image_pullback h00 (hT.toSynchronized.toChain.toSpecial.bijective h00).injective
      (C i) (hCA i) (T.pieces i).2
  let θ := T.form.comp F.lift.target.oldMap
  refine ⟨{
    arity := F.lift.target.arity
    target := F.lift.target.bundle
    map := g
    special := hCert.toSynchronized.toChain.toSpecial
    proper := rvCoordinateBundle_properInvariant h00 hc hκ hs hv F.lift.target.base F.lift.target.freeLabel F.lift.target.proper
    doublyBounded := rvCoordinateBundle_doublyBounded F.lift.target.base F.lift.target.freeLabel
      F.lift.target.doublyBounded F.lift.target.proper.rvBounded
    prepared := F.lift.target_pullback T.prepared
    tagged := F.lift.target.bundle_tagged T.tagged
    form := θ
    transport := ?_
    constant := F.lift.target.gamma_form_constant T.form T.constant
    pieces := fun i => ⟨(hCert.toSynchronized.atPiece i).literal_restriction h00 (hPA i),hPrepared i⟩ },
    hCert,fun p => F.lift.carried ⟨p.val,hW ▸ p.property⟩⟩
  intro p
  let pX : X.bundle := ⟨p.val,hW ▸ p.property⟩
  have ht := F.lift.gamma_form_transport η T.form T.transport pX
  have hAt := gammaFormExtension_at η (X.oldPoint pX)
  have hPoint : (X.oldPoint pX).val=(Fin.init p.val.1,p.val.2) := by
    change (Fin.init p.val.1,p.val.2 ∘ id)=_
    rw [Function.comp_id]
  rw [hPoint] at hAt
  exact ht.trans (hAt.symm.trans (hDesc p))

end DiamondIntegral.Section6
