import «section 3».GammaGroundRVFamilyDesc
import «section 3».GammaGroundRVFamilyRestrictions
/-! Descending a finite gammaGroundFamily of maps commutes with restricting its
pieces. The explicit tags are unchanged. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {n : ℕ}
variable {Q : Space LRV M}

theorem gammaGroundRVFamilyDesc_restrict (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) (B : GammaGroundDefSet hc ground Q)
    (f : ∀ i, GammaGroundMap (A.piece i) B) (X : Fin A.tags → GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier)
    (a : (GammaGroundFiniteFamily.rvRealization ⟨A.tags, X⟩)) :
    gammaGroundRVFamilyDesc ⟨A.tags, X⟩ B (fun i => (f i).comp (GammaGroundMap.inclusion (hX i))) a =
      gammaGroundRVFamilyDesc A B f (GammaGroundMap.inclusion (gammaGroundRVFamilyRealization_mono A.piece X hX) a) := by
  let P : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n) := ⟨A.tags, X⟩
  obtain ⟨b, rfl⟩ := P.rvEquiv.surjective a
  obtain ⟨i, b⟩ := b
  have he : GammaGroundMap.inclusion (gammaGroundRVFamilyRealization_mono A.piece X hX) (P.rvEncode ⟨i, b⟩) =
      A.rvEncode ⟨i, ⟨b.val, hX i b.property⟩⟩ := Subtype.ext rfl
  change gammaGroundRVFamilyDesc P B (fun j => (f j).comp (GammaGroundMap.inclusion (hX j)))
    (P.rvEncode (⟨i, b⟩ : P.Carrier)) =
    gammaGroundRVFamilyDesc A B f (GammaGroundMap.inclusion (gammaGroundRVFamilyRealization_mono A.piece X hX)
      (P.rvEncode (⟨i, b⟩ : P.Carrier)))
  rw [he, gammaGroundRVFamilyDesc_encode, gammaGroundRVFamilyDesc_encode]
  rfl

end DiamondIntegral.Section3
