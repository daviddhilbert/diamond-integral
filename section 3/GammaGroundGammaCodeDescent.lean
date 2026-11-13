import «section 3».GammaGroundFamilyDescent
import «section 3».GammaGroundGammaVolumeCategories
/-! A bijection on full RV code families descends to a genuine Gamma
morphism when it preserves and reflects the decoding equivalence relation. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundGammaHom.ofCodeBijection {A B : GammaGroundGammaObject hc ground k}
    (F : GammaGroundFamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d ↔ B.decode (F.equiv c) = B.decode (F.equiv d)) : GammaGroundGammaHom A B where
  bijection := F.descend hF
  contraction := ⟨F, fun c => (gammaGroundFamilyDescendedMap_decode F (fun c d h => (hF c d).mp h) c).symm⟩

def gammaGroundMeasuredGammaHomOfCodes {A B : GammaGroundMeasuredGammaObject hc ground k}
    (F : GammaGroundFamilyBijection A.underlying.codeLift B.underlying.codeLift)
    (hF : ∀ c d, A.underlying.decode c = A.underlying.decode d ↔
      B.underlying.decode (F.equiv c) = B.underlying.decode (F.equiv d))
    (hW : ∀ c, A.combinedWeight (A.underlying.decode c) = B.combinedWeight (B.underlying.decode (F.equiv c))) :
    GammaGroundMeasuredGammaHom A B where
  underlying := GammaGroundGammaHom.ofCodeBijection F hF
  preserves a := by
    obtain ⟨c, rfl⟩ := A.underlying.decode_surjective a
    have he := gammaGroundFamilyDescendedMap_decode F (fun c d h => (hF c d).mp h) c
    change _ = B.combinedWeight (gammaGroundFamilyDescendedMap F (A.underlying.decode c))
    rw [he]
    exact hW c

end DiamondIntegral.Section3
