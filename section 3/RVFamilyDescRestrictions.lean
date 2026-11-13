import «section 3».RVFamilyDesc
import «section 3».RVFamilyRestrictions

/-! Descending a finite family of maps commutes with restricting its
pieces. The explicit tags are unchanged. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {Q : Space LRV M}

theorem rvFamilyDesc_restrict (A : FiniteFamily (rawRVSpace (M := M) n) S) (B : DefSet Q S)
    (f : ∀ i, Map (A.piece i) B) (X : Fin A.tags → DefSet (rawRVSpace (M := M) n) S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier)
    (a : (FiniteFamily.rvRealization ⟨A.tags, X⟩)) :
    rvFamilyDesc ⟨A.tags, X⟩ B (fun i => (f i).comp (Map.inclusion (hX i))) a =
      rvFamilyDesc A B f (Map.inclusion (rvFamilyRealization_mono A.piece X hX) a) := by
  let P : FiniteFamily (rawRVSpace (M := M) n) S := ⟨A.tags, X⟩
  obtain ⟨b, rfl⟩ := P.rvEquiv.surjective a
  obtain ⟨i, b⟩ := b
  have he : Map.inclusion (rvFamilyRealization_mono A.piece X hX) (P.rvEncode ⟨i, b⟩) =
      A.rvEncode ⟨i, ⟨b.val, hX i b.property⟩⟩ := Subtype.ext rfl
  change rvFamilyDesc P B (fun j => (f j).comp (Map.inclusion (hX j)))
    (P.rvEncode (⟨i, b⟩ : P.Carrier)) =
    rvFamilyDesc A B f (Map.inclusion (rvFamilyRealization_mono A.piece X hX)
      (P.rvEncode (⟨i, b⟩ : P.Carrier)))
  rw [he, rvFamilyDesc_encode, rvFamilyDesc_encode]
  rfl

end DiamondIntegral.Section3
