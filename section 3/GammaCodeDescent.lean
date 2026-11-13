import «section 3».FamilyDescent
import «section 3».GammaVolumeCategories

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def GammaHom.ofCodeBijection {A B : GammaObject hc S k}
    (F : FamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d ↔ B.decode (F.equiv c) = B.decode (F.equiv d)) : GammaHom A B where
  bijection := F.descend hF
  contraction := ⟨F, fun c => (familyDescendedMap_decode F (fun c d h => (hF c d).mp h) c).symm⟩

def measuredGammaHomOfCodes {A B : MeasuredGammaObject hc S k}
    (F : FamilyBijection A.underlying.codeLift B.underlying.codeLift)
    (hF : ∀ c d, A.underlying.decode c = A.underlying.decode d ↔
      B.underlying.decode (F.equiv c) = B.underlying.decode (F.equiv d))
    (hW : ∀ c, A.combinedWeight (A.underlying.decode c) = B.combinedWeight (B.underlying.decode (F.equiv c))) :
    MeasuredGammaHom A B where
  underlying := GammaHom.ofCodeBijection F hF
  preserves a := by
    obtain ⟨c, rfl⟩ := A.underlying.decode_surjective a
    have he := familyDescendedMap_decode F (fun c d h => (hF c d).mp h) c
    change _ = B.combinedWeight (familyDescendedMap F (A.underlying.decode c))
    rw [he]
    exact hW c

end DiamondIntegral.Section3
