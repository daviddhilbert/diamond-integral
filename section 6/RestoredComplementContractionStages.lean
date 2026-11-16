import «section 6».TranslationCoordinateBundles
import «section 6».StandardContractionStages

/-! An actual prepared map yields a contraction stage after its
complementary translations have been restored. The restoration map,
proper geometry, full coordinate-disc fibres and approved Jacobian
exception are all constructed here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem contraction_stage_of_restored_complement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {B : DefSet (rawMixedSpace (M := M) (n+1) s) S} {f : Map A B}
    (H : SpecialCovariantChain (G := G) A B f)
    (hAD : VFDoublyBounded A.carrier) (hBD : VFDoublyBounded B.carrier)
    (hBRP : IsRVPullback B.carrier) (k : Fin s)
    (hLeading : ∀ p ∈ B.carrier,rv M (p.1 (Fin.last n))=p.2 k)
    (δ : Map B (DefSet.univ (rawVFSpace (M := M) (n+1)) S))
    (hδ : ∀ p z : B,p.val.2=z.val.2 → δ p=δ z)
    (hZero : ∀ p : B,rvTranslationVector δ p (Fin.last n)=0)
    (hRestore : ∀ p : A,∀ i : Fin n,
      (f p).val.1 i.castSucc+rvTranslationVector δ (f p) i.castSucc=p.val.1 i.castSucc) :
    Nonempty (StandardContractionStage (G := G) A) := by
  obtain ⟨hHome,_,hJac⟩ := lemma_6_14 h00 hc linear hκ hs hv hsmall hΓ H
  have hB := hHome.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHome.bijective.surjective
  let C := (rvLabelTranslationMap δ).image
  let R := rvLabelTranslation δ
  have hCD : VFDoublyBounded C.carrier := by
    obtain ⟨α,hα⟩ := hAD
    obtain ⟨β,hβ⟩ := hBD
    have hloA : ((max α β)⁻¹).val ≤ (α⁻¹).val := inv_le_inv' (le_max_left α β)
    have hloB : ((max α β)⁻¹).val ≤ (β⁻¹).val := inv_le_inv' (le_max_right α β)
    have hhiA : α.val ≤ (max α β).val := le_max_left α β
    have hhiB : β.val ≤ (max α β).val := le_max_right α β
    refine ⟨max α β,?_⟩
    rintro q ⟨b,rfl⟩ i
    obtain ⟨p,hp⟩ := hHome.bijective.surjective b
    change ((max α β)⁻¹).val ≤ vfValue ((R b).val.1 i) ∧ vfValue ((R b).val.1 i) ≤ (max α β).val
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [rvLabelTranslation_last_fixed δ hZero]
      exact ⟨hloB.trans (hβ b.val b.property (Fin.last n)).1,(hβ b.val b.property (Fin.last n)).2.trans hhiB⟩
    · have hCoordinate : (R b).val.1 j.castSucc=p.val.1 j.castSucc := by
        have h := hRestore p j
        rw [hp] at h
        exact h
      rw [hCoordinate]
      exact ⟨hloA.trans (hα p.val p.property j.castSucc).1,(hα p.val p.property j.castSucc).2.trans hhiA⟩
  have hCBound : VFBounded C.carrier := by
    obtain ⟨γ,hγ⟩ := hCD
    exact ⟨γ⁻¹,fun p hp i => (hγ p hp i).1⟩
  have hC := rvLabelTranslation_image_proper δ hδ h00 hc hκ hs hv hB hCBound
  have hR := rvLabelTranslation_properHomeomorphism δ hδ h00 hc linear hκ hs hv hsmall hΓ hB hCBound
  obtain ⟨E,hEA,hDim,hUnit⟩ := hJac (Nat.zero_lt_succ n)
  obtain ⟨hrs,hRetain⟩ := H.retainsRV
  refine ⟨{
    arity := s
    target := C
    lift := R.comp f
    home := lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hHome hR
    proper := hC
    doublyBounded := hCD
    relative := hRestore
    oldLabels := rvTailIndex hrs
    oldLabels_injective := ?_
    retained := hRetain
    leading := k
    bundle := rvLabelTranslation_coordinate_bundle δ hδ hZero hBRP k hLeading
    exceptional := E
    exceptional_subset := hEA
    exceptional_dim := hDim
    unitDerivative := fun p hp => (rvLabelTranslation_unit_derivative δ hδ hB hv (f p)).comp (hUnit p hp) }⟩
  intro i j he
  apply Fin.ext
  have he' := congrArg Fin.val he
  change s-r+i.val=s-r+j.val at he'
  omega

end DiamondIntegral.Section6
