import «section 3».NamedDefinableMaps
import Section4.CanonicalLift
import Section4.CodeMaps

/-! The actual coordinatewise rv map and the graph map used by the
object lift, definable over the original real parameter set. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem tupleRV_decode_code (k : ℕ) (c : (rawVFSpace (M := M) k).domain) :
    rvValues (tupleRV ((rawVFSpace k).decode c)) = fun i => iRv (c.val i) := by
  have h := Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace (M := M) k).domain_definable c
  funext i
  exact congrArg iRv (congrFun h i)

def universalTupleRVMap (S : Set M) (k : ℕ) :
    Map (DefSet.univ (rawVFSpace (M := M) k) S) (DefSet.univ (rawRVSpace k) S) := by
  let F (z : Fin k → M) : Fin k → M := fun i => iRv (z i)
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin k → M => ![z i]) from
        fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  have hdom (c : (rawVFSpace (M := M) k).domain) : F c.val ∈ (rawRVSpace k).domain :=
    ⟨tupleRV ((rawVFSpace k).decode c), tupleRV_decode_code k c⟩
  exact Map.ofCodes (DefSet.univ (rawVFSpace k) S) tupleRV F hF hdom (fun c =>
    rvValues_injective ((Space.ofEmbedding_decode rvValues rvValues_injective
      (rawRVSpace (M := M) k).domain_definable ⟨F c.val, hdom c⟩).trans (tupleRV_decode_code k c).symm))

def universalLiftGraphMap (S : Set M) (k n : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) k n) S)
      (DefSet.univ ((rawRVSpace n).prod (rawRVSpace k)) S) :=
  ((universalProductSnd (rawVFSpace k) (rawRVSpace n) S).pair
    ((universalTupleRVMap S k).comp (universalProductFst (rawVFSpace k) (rawRVSpace n) S))).toUniv

end DiamondIntegral.Section3
