import «section 3».GammaChainRetainedLabels
import «section 5».NativeGammaPointBridge
import «section 3».GammaGroundVolumeForms

/-! Original-ground special chains transport arbitrary Gamma forms.
Constancy on the original RV labels becomes constancy on final labels,
using explicit retained coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S n l}

def gammaNativeSpecialIso (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain) :
    GammaIso B (carrier A) (carrier D) :=
  ⟨T.equiv,GammaChainDefinable.graph (gammaLogicInput B) T.chain hT⟩

def gammaNativeSpecialBijection (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain) :
    GammaGroundBijection
      (Section5.nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT))
      (Section5.nativeGammaPointDomain (carrier D) (GammaChainDefinable.target B T.chain hT)) :=
  Section5.nativeGammaPointBijection _ _ (gammaNativeSpecialIso T hT)

theorem gammaNativeSpecialBijection_apply (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT)) :
    ((gammaNativeSpecialBijection T hT).map p).val = (T.toMap ⟨p.val,p.property⟩).val :=
  Section5.nativeGammaPointBijection_apply _ _ (gammaNativeSpecialIso T hT) p

theorem gammaNativeSpecialBijection_inverse (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier D) (GammaChainDefinable.target B T.chain hT)) :
    ((gammaNativeSpecialBijection T hT).symm.map p).val = (T.inverseMap ⟨p.val,p.property⟩).val :=
  Section5.nativeGammaPointBijection_symm_apply _ _ (gammaNativeSpecialIso T hT) p

def gammaSpecialTransportedForm (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (ω : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT))) :
    GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier D) (GammaChainDefinable.target B T.chain hT)) :=
  ω.comp (gammaNativeSpecialBijection T hT).symm.map

theorem gammaSpecialTransportedForm_labelconstant
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (ω : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT)))
    (hω : ∀ p q, p.val.2 = q.val.2 → ω p = ω q)
    (p q : Section5.nativeGammaPointDomain (carrier D) (GammaChainDefinable.target B T.chain hT))
    (hpq : p.val.2 = q.val.2) :
    gammaSpecialTransportedForm T hT ω p = gammaSpecialTransportedForm T hT ω q := by
  apply hω
  rw [gammaNativeSpecialBijection_inverse,gammaNativeSpecialBijection_inverse]
  rw [gammaSpecial_inverse_old_labels,gammaSpecial_inverse_old_labels,hpq]

end DiamondIntegral.Section3
