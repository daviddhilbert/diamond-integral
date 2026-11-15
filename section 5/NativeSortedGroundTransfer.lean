import «section 5».NativeGammaPointBridge
import «section 5».RESGroundTransfer
import «section 3».GammaGroundCarrierBijections

/-! Changing the presentation of a parameter base through actual sorted
formula transfer retains literal native domains and complete bijection
graphs. These are parameter substitutions, not field extensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

def sortedTransferMixedDomain {n r : ℕ} (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    GammaGroundDefSet hc C (rawMixedSpace (M := M) n r) :=
  nativeGammaPointDomain D.carrier (H _ _ (nativeMixedDomain_definable D))

theorem sortedTransferMixedDomain_carrier {n r : ℕ}
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    (sortedTransferMixedDomain H D).carrier = D.carrier := rfl

def sortedTransferMixedBijection {n r m s : ℕ}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)} (f : GammaGroundBijection D E) :
    GammaGroundBijection (sortedTransferMixedDomain H D) (sortedTransferMixedDomain H E) :=
  nativeMixedBijectionOfSortedIso _ _ ⟨(nativeMixedSortedIso f).equiv,H _ _ (nativeMixedSortedIso f).graph⟩

def sortedTransferRVDomain {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundDefSet hc C (rawRVSpace (M := M) n) where
  carrier := D.carrier
  definable := gammaGroundDefinable_iff_rvBase.mpr (H _ _ (rawDomain_definable D))

def sortedTransferRVRawBijection {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundBijection (sortedTransferRVDomain H D)
      (ofRaw (hc := hc) (rawDomain D) (H _ _ (rawDomain_definable D))) :=
  GammaGroundBijection.ofCarrierEq (by
    ext x
    constructor
    · intro hx
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact rvValues_injective he ▸ hy)

def sortedTransferRVBijection {n m : ℕ}
    {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) m)} (f : GammaGroundBijection D E) :
    GammaGroundBijection (sortedTransferRVDomain H D) (sortedTransferRVDomain H E) :=
  (sortedTransferRVRawBijection H E).symm.comp
    ((bijectionOfRaw (rawDomain D) (rawDomain E) (H _ _ (rawDomain_definable D)) (H _ _ (rawDomain_definable E))
      (rawMap f.map) (H _ _ (rawMap_definable f.map)) (rawMap_bijective f.map f.bijective)).comp
        (sortedTransferRVRawBijection H D))

end DiamondIntegral.Section5
