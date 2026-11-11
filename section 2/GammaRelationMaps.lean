import «section 2».Conventions
import Section3.GammaBaseTools

/-!
# Definable real substitutions in genuine Gamma relations

Only the real arguments are substituted. Gamma inputs retain their complete
proper-code preimage and representative invariance. The explicit real base
of the substituting map records every named constant.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaRelationPreimageMap {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : GammaParameters.Relation S k n sn) (sm : Fin m → SortTag)
    (f : (Fin m → M) → Fin n → M)
    (hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ S f) :
    GammaParameters.Relation S k m sm where
  carrier := {p | (p.1, f p.2) ∈ Q.carrier ∧ p.2 ∈ GammaParameters.sortedUniverse sm}
  definable := by
    have hs := (definableOver_iff_normalized_raw S sm _).mp
      (GammaParameters.sortedUniverse_definable S sm)
    have hQ := Q.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hF : S.DefinableMap LRV (fun z : Fin k ⊕ Fin m → M =>
        Sum.elim (z ∘ Sum.inl) (f (z ∘ Sum.inr))) := by
      rintro (i | i)
      · exact Set.DefinableFun.proj LRV
      · exact (hf i).comp (fun _ => Set.DefinableFun.proj LRV)
    exact (hQ.preimage_map hF).inter (hs.1.preimage_comp Sum.inr)
  proper := fun p hp => ⟨(Q.proper _ hp.1).1, hp.2⟩
  invariant := fun t u he x => and_congr (Q.invariant t u he (f x)) Iff.rfl

theorem gammaRelationPreimageMap_fibre {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : GammaParameters.Relation S k n sn) (sm : Fin m → SortTag)
    (f : (Fin m → M) → Fin n → M)
    (hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ S f)
    (γ : Fin k → Gamma M) :
    (gammaRelationPreimageMap Q sm f hf).fibre γ =
      {x | f x ∈ Q.fibre γ ∧ x ∈ GammaParameters.sortedUniverse sm} := rfl

end DiamondIntegral.Section2
