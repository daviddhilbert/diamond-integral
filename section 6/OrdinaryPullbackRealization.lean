import «section 6».OrdinaryRealizationPullbacks

/-! An original-base proper ordinary restriction with a whole-disc
endpoint has an actual special-covariant RV-pullback realization. The
identity input frame is built, and its label-faithfulness is proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}

def originalOrdinaryFocusFrame (H : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hH : H.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hProper : ProperInvariant S H.carrier) (hDB : VFDoublyBounded H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ q ∈ H.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    OrdinaryUnaryFocusFrame hc A hA r where
  source := H
  oldMap := Map.inclusion hH
  labels := id
  point p := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  proper := hProper
  doublyBounded := hDB
  tagged := hTag

theorem originalOrdinaryFocusFrame_labelsFaithful
    (H : DefSet (rawMixedSpace (M := M) 1 r) S) (hH : H.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hProper : ProperInvariant S H.carrier) (hDB : VFDoublyBounded H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ q ∈ H.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    (originalOrdinaryFocusFrame (hc := hc) (hA := hA) H hH hProper hDB hTag).labelsFaithful := by
  intro p q hSame
  exact ((ordinary_sameRV_iff _ _).mp hSame).2

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_covariant_rvPullback_realization_of_ordinary_image
    (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (H : DefSet (rawMixedSpace (M := M) 1 r) S) (hH : H.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hProper : ProperInvariant S H.carrier) (hDB : VFDoublyBounded H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ q ∈ H.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hNo : ∀ p : H,p.val ∉ ordinaryChainZeroSources T)
    (hOld : IsRVPullback (ordinaryFrameEndpointImage
      (originalOrdinaryFocusFrame (hc := hc)
        (hA := SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT)
        H hH hProper hDB hTag) T)) :
    ∃ t : ℕ,∃ K : DefSet (rawMixedSpace (M := M) 1 t) S,∃ f : Map H K,
      SpecialCovariantChain (G := G) H K f ∧ ProperInvariant S K.carrier ∧
      VFDoublyBounded K.carrier ∧ IsRVPullback K.carrier ∧
      ∃ π : Fin s → Fin t,∀ p : H,(T.toMap ⟨p.val,hH p.property⟩).val=((f p).val.1,(f p).val.2 ∘ π) := by
  let X := originalOrdinaryFocusFrame (hc := hc)
    (hA := SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT)
    H hH hProper hDB hTag
  obtain ⟨F⟩ := exists_labelled_covariant_realization_off_ordinary_exceptions h00 linear hκ hs hv V hsmall
    hΓ hV hVS hSV hnt T hT r X hNo
  have hRP := F.target_rvPullback h00 (originalOrdinaryFocusFrame_labelsFaithful H hH hProper hDB hTag) hOld
  exact ⟨F.arity,F.targetFrame.source,F.map,F.special,F.targetFrame.proper,F.targetFrame.doublyBounded,hRP,
    F.targetFrame.labels,fun p => (F.commutes p).symm.trans (F.targetFrame.point (F.map p))⟩

end DiamondIntegral.Section6
