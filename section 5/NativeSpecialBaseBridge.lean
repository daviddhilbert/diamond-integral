import «section 5».NativeGammaPointBridge
import IntegrationSection6.GammaPreparedRowAgreements

/-! A genuine original-ground special preparation induces the native
base bijection, with its inverse parameter code exactly equal to the
parameter used by the prepared row-agreement theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p q l : ℕ} {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}

def nativeSpecialBaseIso (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain) :
    GammaIso B (carrier A) (carrier C) :=
  ⟨T.equiv,GammaChainDefinable.graph (gammaLogicInput B) T.chain hT⟩

def nativeSpecialBaseBijection (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain) :
    GammaGroundBijection
      (nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT))
      (nativeGammaPointDomain (carrier C) (GammaChainDefinable.target B T.chain hT)) :=
  nativeGammaPointBijection _ _ (nativeSpecialBaseIso T hT)

theorem nativeSpecialBaseBijection_inverse (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (c : nativeGammaPointDomain (hc := hc) (carrier C) (GammaChainDefinable.target B T.chain hT)) :
    ((nativeSpecialBaseBijection T hT).symm.map c).val = (T.inverseMap ⟨c.val,c.property⟩).val :=
  nativeGammaPointBijection_symm_apply _ _ (nativeSpecialBaseIso T hT) c

theorem nativeSpecialBaseBijection_parameter (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (c : nativeGammaPointDomain (hc := hc) (carrier C) (GammaChainDefinable.target B T.chain hT))
    (v : Fin q → CanonicalRV.RVSort M) :
    nativeMixedCode (((nativeSpecialBaseBijection T hT).symm.map c).val.1,v) =
      Fin.append (rawVFParameter (T.inverseMap ⟨c.val,c.property⟩).val) (rvValues v) := by
  rw [nativeSpecialBaseBijection_inverse]
  rfl

end DiamondIntegral.Section5
