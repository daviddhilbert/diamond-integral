import «section 4».Section3GammaChartBridge
import «section 4».Section3RVRelationBridge
import «section 3».GammaGroundCarrierBijections

/-! Every native Gamma code is exactly a proper raw RV tuple. These
are full preimages, and the original base is unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaRVCodeBridge
open GammaRVChartPresentation Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def rawCode {n : ℕ} {G : GammaGroundGammaPiece hc B n} (c : gammaGroundCodePreimage G) : Fin n → M :=
  fun i => c.val.val (i, (0 : Fin 1))

theorem rawCode_proper {n : ℕ} {G : GammaGroundGammaPiece hc B n} (c : gammaGroundCodePreimage G) :
    Proper (rawCode c) := c.val.property

theorem rawCode_value {n : ℕ} {G : GammaGroundGammaPiece hc B n} (c : gammaGroundCodePreimage G) :
    codeValues (rawCode c) = ((volumeGammaSpace hc).power (Fin n)).decode c.val := by
  funext i
  exact codeValue_raw ⟨⟨c.val.val (i, (0 : Fin 1)), (c.val.property i).1⟩, (c.val.property i).2⟩

theorem codeToRV_raw {n : ℕ} {G : GammaGroundGammaPiece hc B n} (c : gammaGroundCodePreimage G) :
    rvValues (gammaGroundGammaCodeToRV G c).val = rawCode c := rfl

theorem rawDomain_codeLift {n : ℕ} (G : GammaGroundGammaPiece hc B n) :
    rawDomain (gammaGroundGammaRVCodeLift G).domain = sharp G.carrier := by
  ext z
  constructor
  · rintro ⟨t, ⟨c, ht⟩, rfl⟩
    have hv : rvValues t = rawCode c := (congrArg rvValues ht).symm.trans (codeToRV_raw c)
    change Proper (rvValues t) ∧ codeValues (rvValues t) ∈ G.carrier
    rw [hv]
    exact ⟨rawCode_proper c, (rawCode_value c).symm ▸ c.property⟩
  · rintro ⟨hp, hz⟩
    let c0 : ((volumeGammaSpace hc).power (Fin n)).domain := ⟨fun ij => z ij.1, hp⟩
    have hd : ((volumeGammaSpace hc).power (Fin n)).decode c0 = codeValues z := by
      funext i
      exact (codeValue_raw ⟨⟨z i, (hp i).1⟩, (hp i).2⟩).symm
    let c : gammaGroundCodePreimage G := ⟨c0, by
      change ((volumeGammaSpace hc).power (Fin n)).decode c0 ∈ G.carrier
      rw [hd]
      exact hz⟩
    exact ⟨(gammaGroundGammaCodeToRV G c).val, ⟨c, rfl⟩, rfl⟩

theorem codeLift_carrier {n : ℕ} (G : GammaGroundGammaPiece hc B n) :
    (gammaGroundGammaRVCodeLift G).domain.carrier =
      (ofRaw (hc := hc) (sharp G.carrier) (GammaRVChartPresentation.sharp_definable _
        ((Section3GammaCodeBridge.native_iff _).mp G.definable))).carrier := by
  ext t
  constructor
  · intro ht
    have h : rvValues t ∈ rawDomain (gammaGroundGammaRVCodeLift G).domain := ⟨t, ht, rfl⟩
    exact (congrArg (fun D => rvValues t ∈ D) (rawDomain_codeLift G)).mp h
  · intro ht
    have h : rvValues t ∈ rawDomain (gammaGroundGammaRVCodeLift G).domain :=
      (congrArg (fun D => rvValues t ∈ D) (rawDomain_codeLift G)).mpr ht
    obtain ⟨u, hu, he⟩ := h
    exact rvValues_injective he ▸ hu

def codeBijection {n : ℕ} (G : GammaGroundGammaPiece hc B n) :
    GammaGroundBijection (gammaGroundCodePreimage G)
      (ofRaw (sharp G.carrier) (GammaRVChartPresentation.sharp_definable _
        ((Section3GammaCodeBridge.native_iff _).mp G.definable))) :=
  (GammaGroundBijection.ofCarrierEq (codeLift_carrier G)).comp (gammaGroundGammaRVCodeBijection G)

theorem codeBijection_value {n : ℕ} (G : GammaGroundGammaPiece hc B n) (c : gammaGroundCodePreimage G) :
    rvValues ((codeBijection G).map c).val = rawCode c := rfl

end DiamondIntegral.Section4.Section3GammaRVCodeBridge
