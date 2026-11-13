import «section 3».RVUnitSpace
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def rvUnitTupleProductMap (S : Set M) (n m : ℕ) :
    Map (DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) S)
      (DefSet.univ (rawRVUnitSpace (n+m)) S) := by
  let F := fun z : Fin n ⊕ Fin m → M => z ∘ finSumFinEquiv.symm
  have hc (c : ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)).domain) :
      F c.val = rvUnitValues (Fin.append ((rawRVUnitSpace n).decode ⟨c.val ∘ Sum.inl,c.property.1⟩)
        ((rawRVUnitSpace m).decode ⟨c.val ∘ Sum.inr,c.property.2⟩)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [F,Function.comp_apply,finSumFinEquiv_symm_apply_castAdd,rvUnitValues,Fin.append_left] using
        (congrFun (rvUnitValues_decode (M := M) (n := n) ⟨c.val ∘ Sum.inl,c.property.1⟩) j).symm
    · simpa only [F,Function.comp_apply,finSumFinEquiv_symm_apply_natAdd,rvUnitValues,Fin.append_right] using
        (congrFun (rvUnitValues_decode (M := M) (n := m) ⟨c.val ∘ Sum.inr,c.property.2⟩) j).symm
  have hd (c : ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)).domain) :
      F c.val ∈ (rawRVUnitSpace (M := M) (n+m)).domain := ⟨_,(hc c).symm⟩
  refine Map.ofCodes _ (Fin.appendEquiv n m) F (fun _ => Set.DefinableFun.proj LRV) hd ?_
  intro c
  apply rvUnitValues_injective
  exact (rvUnitValues_decode _).trans (hc c)

theorem rvUnitTupleProductMap_bijective (S : Set M) : Function.Bijective (rvUnitTupleProductMap (M := M) S n m) := by
  constructor
  · intro a b hab
    exact Subtype.ext ((Fin.appendEquiv n m).injective (congrArg Subtype.val hab))
  · intro z
    refine ⟨⟨(Fin.appendEquiv n m).symm z.val,Set.mem_univ _⟩,?_⟩
    exact Subtype.ext ((Fin.appendEquiv n m).apply_symm_apply z.val)

def gammaGroundRVUnitTupleProductMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    GammaGroundMap T (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) (n+m))) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitTupleProductMap B.real n m) (fun _ => Set.mem_univ _)

theorem gammaGroundRVUnitTupleProductMap_injective {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    Function.Injective (gammaGroundRVUnitTupleProductMap T) := by
  intro a b hab
  exact Subtype.ext ((Fin.appendEquiv n m).injective (congrArg Subtype.val hab))

def gammaGroundRVUnitTupleProductBijection {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    GammaGroundBijection T (gammaGroundRVUnitTupleProductMap T).image :=
  ⟨(gammaGroundRVUnitTupleProductMap T).toImage,
    (gammaGroundRVUnitTupleProductMap T).toImage_bijective (gammaGroundRVUnitTupleProductMap_injective T)⟩
end DiamondIntegral.Section3
