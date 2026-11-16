import «section 6».OpenRVLabelGeometry
import «section 6».ShearContractionStages

/-! Construct an actual contraction stage from its shear geometry.
The source supplies the bounds; open nonzero labels construct the new
RV bounds, the leading label bounds the active VF coordinate, and the
generic derivative exception is derived from the actual shear charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}

theorem relative_target_doublyBounded_of_labels
    (f : Map A B) (hSurj : Function.Surjective f) (hAD : VFDoublyBounded A.carrier)
    (hR : RVSupportDoublyBounded B.carrier)
    (hRelative : ∀ p : A,∀ i : Fin n,(f p).val.1 i.castSucc=p.val.1 i.castSucc)
    (k : Fin s) (hLeading : ∀ p : A,rv M ((f p).val.1 (Fin.last n))=(f p).val.2 k) :
    VFDoublyBounded B.carrier := by
  obtain ⟨α,hα⟩ := hAD
  obtain ⟨β,hβ⟩ := hR
  have hLoA : ((max α β)⁻¹).val ≤ (α⁻¹).val := inv_le_inv' (le_max_left α β)
  have hLoB : ((max α β)⁻¹).val ≤ (β⁻¹).val := inv_le_inv' (le_max_right α β)
  refine ⟨max α β,?_⟩
  intro b hb i
  obtain ⟨p,hp⟩ := hSurj ⟨b,hb⟩
  have hValue : (f p).val=b := congrArg Subtype.val hp
  change ((max α β)⁻¹).val ≤ vfValue (b.1 i) ∧ vfValue (b.1 i) ≤ (max α β).val
  rw [← hValue]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hVal := congrArg Values.vrv (hLeading p)
    change vfValue ((f p).val.1 (Fin.last n))=Values.vrv ((f p).val.2 k) at hVal
    rw [hVal]
    have h := hβ (f p).val (f p).property k
    exact ⟨hLoB.trans h.1,h.2.trans (show β.val ≤ (max α β).val from le_max_right _ _)⟩
  · rw [hRelative p j]
    have h := hα p.val p.property j.castSucc
    exact ⟨hLoA.trans h.1,h.2.trans (show α.val ≤ (max α β).val from le_max_left _ _)⟩

def shear_contraction_stage_of_open_labels
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hBij : Function.Bijective f) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (hRelative : ∀ p : A,∀ i : Fin n,(f p).val.1 i.castSucc=p.val.1 i.castSucc)
    (hStable : SameLabelShearDisplacement f (Fin.last n))
    (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (k : Fin s)
    (hLeading : ∀ p : A,rv M ((f p).val.1 (Fin.last n))=(f p).val.2 k)
    (hNZ : ∀ p : A,∀ i,((f p).val.2 i).val ≠ iRVZero)
    (hBundle : B.carrier=(rvCoordinateBundle (vfDropLast B).image k).carrier)
    (hCont : ContinuousOnGraphFibres f)
    (hOpen : ∀ u v,IsOpen (graphFibreSource f u v))
    (hRange : ∀ u v,IsClopen (graphFibreRange f u v)) : ShearContractionStage (G := G) A := by
  have hR := target_rvBounded_of_open_nonzero_labels h00 hc linear hκ hs hv hsmall hΓ f hBij.surjective hA hOpen hNZ
  have hBD := relative_target_doublyBounded_of_labels f hBij.surjective hAD hR hRelative k hLeading
  have hB : ProperInvariant S B.carrier := by
    obtain ⟨α,hα⟩ := hBD
    apply (lemma_6_5 h00 hc hκ hs hv B.carrier B.definable
      ⟨α⁻¹,fun p hp i => (hα p hp i).1⟩ hR).mpr
    intro v
    rw [retained_target_fibre_eq_graphRange f hBij.surjective π hRetain v]
    exact hRange _ _
  have hHome := properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ f
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv f hA hB hCont hOpen hRange) hBij hCont
  exact shear_contraction_stage_of_bundle h00 hc linear hκ hs hv hsmall hΓ f hHome hBD hRelative hStable π hπ hRetain k hBundle

end DiamondIntegral.Section6
