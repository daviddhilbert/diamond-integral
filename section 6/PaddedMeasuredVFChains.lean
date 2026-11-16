import «section 6».PaddedLiftDerivatives
import «section 6».MeasuredVFUnaryChainBounds

/-! Actual smaller-degree measured VF unary chains extend to the full
degree by carrying a unit-RV tail unchanged at every stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

def paddedEverywhereMeasuredRVLift {U V : MeasuredRVObject (M := M) S k}
    {e : MeasuredRVIso U V} (F : EverywhereMeasuredRVLift e) (m : ℕ) :
    EverywhereMeasuredRVLift (measuredRVPadOnesIso e m) where
  map := paddedRVLiftMap F.map m
  bijective := paddedRVLiftMap_bijective F.map F.bijective m
  labels p := F.labels (rvPadOnesLiftHeadMap U m p)
  measure p := by
    obtain ⟨L,hL,hJ⟩ := F.measure (rvPadOnesLiftHeadMap U m p)
    obtain ⟨D,hD,hDet⟩ := paddedRVLiftMap_derivative_and_det F.map m p hL
    exact ⟨D,hD,(congrArg vfValue hDet).trans hJ⟩

theorem paddedEverywhereMeasuredRVLift_unary {U V : MeasuredRVObject (M := M) S k}
    {e : MeasuredRVIso U V} (F : EverywhereMeasuredRVLift e) (m : ℕ)
    (i : Fin k) (hF : VFUnaryRelativeAt F.map i) :
    VFUnaryRelativeAt (paddedEverywhereMeasuredRVLift F m).map (productLeft k m i) := by
  intro p j hj
  obtain ⟨q,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective j
  cases q with
  | inl q =>
    change productTuple (F.map (rvPadOnesLiftHeadMap U m p)).val.1 (p.val.1 ∘ productRight k m) (productLeft k m q)=_
    rw [productTuple_left]
    exact hF (rvPadOnesLiftHeadMap U m p) q (fun he => hj (congrArg (productLeft k m) he))
  | inr q =>
    change productTuple (F.map (rvPadOnesLiftHeadMap U m p)).val.1 (p.val.1 ∘ productRight k m) (productRight k m q)=_
    rw [productTuple_right]
    rfl

def MeasuredVFUnaryLiftChain.padOnes {U V : MeasuredRVObject (M := M) S k} :
    MeasuredVFUnaryLiftChain S k U V → (m : ℕ) →
      MeasuredVFUnaryLiftChain S (k+m) (measuredRVPadOnes U m) (measuredRVPadOnes V m)
  | .identity U,m => .identity (measuredRVPadOnes U m)
  | .step i F hu T,m => .step (productLeft k m i) (paddedEverywhereMeasuredRVLift F m)
      (paddedEverywhereMeasuredRVLift_unary F m i hu) (T.padOnes m)

theorem MeasuredVFUnaryLiftChain.padOnes_map {U V : MeasuredRVObject (M := M) S k}
    (T : MeasuredVFUnaryLiftChain S k U V) (m : ℕ) (u : U.object.domain) :
    (T.padOnes m).iso.iso.hom.map u=T.iso.iso.hom.map u := by
  induction T with
  | identity U => rfl
  | step i F hu T ih => exact ih _

theorem MeasuredVFUnaryLiftChain.padOnes_doublyBounded {U V : MeasuredRVObject (M := M) S k}
    (T : MeasuredVFUnaryLiftChain S k U V) (m : ℕ) (h : T.doublyBounded) :
    (T.padOnes m).doublyBounded := by
  induction T with
  | identity U => exact measuredRVPadOnes_doublyBounded U m h
  | step i F hu T ih => exact ⟨measuredRVPadOnes_doublyBounded _ m h.1,ih h.2⟩

end DiamondIntegral.Section6
