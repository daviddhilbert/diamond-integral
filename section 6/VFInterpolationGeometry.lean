import «section 6».VFCoordinateInterpolation
import «section 6».RVDisplacementGeometry

/-! Coordinate interpolation of a retained-label translation is an
actual proper homeomorphism. Its full graph fibres are translations of
the original label fibres, with exact source and target bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem vfInterpolation_retained (f : Map A B) (P : Fin n → Prop) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (p : A) (i : Fin r) :
    (vfInterpolation f P p).val.2 (π i)=p.val.2 i := by
  rw [vfInterpolation_value]
  exact hRetain p i

theorem vfInterpolation_rv_displacements (f : Map A B) (P : Fin n → Prop)
    (hD : ∀ i,RVCoordinateDisplacement f i) (i : Fin n) : RVCoordinateDisplacement (vfInterpolation f P) i := by
  intro p z he
  have hTags : (f p).val.2=(f z).val.2 := by simpa only [vfInterpolation_value] using he
  rw [vfInterpolation_value,vfInterpolation_value]
  by_cases hi : P i
  · simpa only [if_pos hi] using hD i p z hTags
  · simp only [if_neg hi,sub_self]

theorem vfInterpolation_graph_source (f : Map A B) (P : Fin n → Prop)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (vfInterpolation f P) u v=graphFibreSource f u v := by
  ext x
  constructor
  · rintro ⟨y,p,hp,hfp⟩
    have hTags := congrArg Prod.snd hfp
    rw [vfInterpolation_value] at hTags
    exact ⟨(f p).val.1,p,hp,Prod.ext rfl hTags⟩
  · rintro ⟨y,p,hp,hfp⟩
    refine ⟨(vfInterpolation f P p).val.1,p,hp,Prod.ext rfl ?_⟩
    rw [vfInterpolation_value]
    have hTags := congrArg Prod.snd hfp
    exact hTags

theorem vfInterpolation_image_fibre (f : Map A B) (P : Fin n → Prop) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (v : Fin s → RVInfinity M) :
    vfFibre (vfInterpolationMap f P).image.carrier v=
      graphFibreRange (vfInterpolation f P) (v ∘ π) v := by
  ext y
  constructor
  · rintro ⟨p,hp⟩
    have hTags : p.val.2=v ∘ π := by
      funext i
      exact (vfInterpolation_retained f P π hRetain p i).symm.trans
        (congrArg (fun w : Mixed M n s => w.2 (π i)) hp)
    exact ⟨p.val.1,p,Prod.ext rfl hTags,hp⟩
  · rintro ⟨x,p,hp,hfp⟩
    exact ⟨p,hfp⟩

theorem vfInterpolation_bijective (f : Map A B) (P : Fin n → Prop) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (hD : ∀ i,RVCoordinateDisplacement f i) : Function.Bijective (vfInterpolation f P) :=
  ⟨injective_of_rv_displacements _ π (vfInterpolation_retained f P π hRetain)
    (vfInterpolation_rv_displacements f P hD),map_toImage_surjective _⟩

theorem vfInterpolation_vfBounded (f : Map A B) (P : Fin n → Prop)
    (hA : VFBounded A.carrier) (hB : VFBounded B.carrier) : VFBounded (vfInterpolationMap f P).image.carrier := by
  obtain ⟨α,hα⟩ := hA
  obtain ⟨β,hβ⟩ := hB
  refine ⟨min α β,?_⟩
  rintro q ⟨p,rfl⟩ i
  change (min α β).val ≤ vfValue ((vfInterpolation f P p).val.1 i)
  rw [vfInterpolation_coordinate]
  by_cases hi : P i
  · rw [if_pos hi]
    exact (show (min α β).val ≤ β.val from min_le_right _ _).trans (hβ (f p).val (f p).property i)
  · rw [if_neg hi]
    exact (show (min α β).val ≤ α.val from min_le_left _ _).trans (hα p.val p.property i)

theorem vfInterpolation_doublyBounded (f : Map A B) (P : Fin n → Prop)
    (hA : VFDoublyBounded A.carrier) (hB : VFDoublyBounded B.carrier) :
    VFDoublyBounded (vfInterpolationMap f P).image.carrier := by
  obtain ⟨α,hα⟩ := hA
  obtain ⟨β,hβ⟩ := hB
  have hloA : ((max α β)⁻¹).val ≤ (α⁻¹).val := inv_le_inv' (le_max_left α β)
  have hloB : ((max α β)⁻¹).val ≤ (β⁻¹).val := inv_le_inv' (le_max_right α β)
  refine ⟨max α β,?_⟩
  rintro q ⟨p,rfl⟩ i
  change ((max α β)⁻¹).val ≤ vfValue ((vfInterpolation f P p).val.1 i) ∧
    vfValue ((vfInterpolation f P p).val.1 i) ≤ (max α β).val
  rw [vfInterpolation_coordinate]
  by_cases hi : P i
  · rw [if_pos hi]
    exact ⟨hloB.trans (hβ (f p).val (f p).property i).1,(hβ (f p).val (f p).property i).2.trans (le_max_right _ _)⟩
  · rw [if_neg hi]
    exact ⟨hloA.trans (hα p.val p.property i).1,(hα p.val p.property i).2.trans (le_max_left _ _)⟩

theorem vfInterpolation_rvBounded (f : Map A B) (P : Fin n → Prop) (hB : RVSupportDoublyBounded B.carrier) :
    RVSupportDoublyBounded (vfInterpolationMap f P).image.carrier := by
  obtain ⟨α,hα⟩ := hB
  refine ⟨α,?_⟩
  rintro q ⟨p,rfl⟩ i
  change (α⁻¹).val ≤ Values.vrv ((vfInterpolation f P p).val.2 i) ∧
    Values.vrv ((vfInterpolation f P p).val.2 i) ≤ α.val
  rw [vfInterpolation_value]
  exact hα (f p).val (f p).property i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfInterpolation_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hF : ProperCovariantHomeomorphism f) (P : Fin n → Prop) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (hD : ∀ i,RVCoordinateDisplacement f i) :
    ProperCovariantHomeomorphism (vfInterpolation f P) := by
  have hA := hF.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  have hSource (u v) : IsClopen (graphFibreSource (vfInterpolation f P) u v) := by
    rw [vfInterpolation_graph_source]
    obtain ⟨α,β,hα,hβ,hInv,hRange,hCov⟩ := hF.covariant.radii u v
    exact hInv.isClopen hv
  have hRange := graphFibreRange_clopen_of_rv_displacements hv (vfInterpolation f P)
    (vfInterpolation_rv_displacements f P hD) hSource
  have hTarget : ProperInvariant S (vfInterpolationMap f P).image.carrier := by
    apply (lemma_6_5 h00 hc hκ hs hv _ (vfInterpolationMap f P).image.definable
      (vfInterpolation_vfBounded f P hA.vfBounded hB.vfBounded) (vfInterpolation_rvBounded f P hB.rvBounded)).mpr
    intro v
    rw [vfInterpolation_image_fibre f P π hRetain]
    exact hRange _ _
  have hCont := continuous_of_rv_displacements (vfInterpolation f P) (vfInterpolation_rv_displacements f P hD)
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv _ hA hTarget hCont (fun u v => (hSource u v).isOpen) hRange)
    (vfInterpolation_bijective f P π hRetain hD) hCont

end DiamondIntegral.Section6
