import «section 3».RVUnitTupleProducts
import «section 3».RVUnitGammaMaps
import «section 3».GammaGroundMapComposition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- The full value graph of an actual RV map keeps every representative
of each output value, rather than retaining only the actual output point. -/
def gammaGroundRVUnitValueGraphProduct
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D) :
    GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) := by
  let Q := rawRVUnitSpace (M := M) n
  let R := rawRVUnitSpace (M := M) m
  let G := (volumeGammaSpace hc).power (Fin m)
  let v : GammaGroundMap D (GammaGroundDefSet.univ hc B G) :=
    GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real m) (fun _ => Set.mem_univ _)
  let g := v.comp f
  let h : Map (DefSet.univ (Q.prod R) B.real) (DefSet.univ (Q.prod G) B.real) :=
    ((universalProductFst Q R B.real).pair
      ((rvUnitGammaMap hc B.real m).comp (universalProductSnd Q R B.real))).toUniv
  refine ⟨{z | ∃ a : A, a.val = z.1 ∧ rvUnitTupleValues (f a).val = rvUnitTupleValues z.2},?_⟩
  exact g.graph_definable.preimage h

/-- Flattening the full value graph into the actual nonzero RV tuple
space preserves all source and target coordinates and every value code. -/
def gammaGroundRVUnitValueGraph
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+m)) :=
  (gammaGroundRVUnitTupleProductMap (gammaGroundRVUnitValueGraphProduct A D f)).image

theorem gammaGroundRVUnitValueGraph_append_mem_iff
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D)
    (u : Fin n → (CanonicalRV.RVSort M)ˣ) (v : Fin m → (CanonicalRV.RVSort M)ˣ) :
    Fin.append u v ∈ (gammaGroundRVUnitValueGraph A D f).carrier ↔
      ∃ a : A, a.val = u ∧ rvUnitTupleValues (f a).val = rvUnitTupleValues v := by
  constructor
  · rintro ⟨z,hz⟩
    have he : z.val = (u,v) := (Fin.appendEquiv n m).injective hz
    exact Eq.mp (congrArg
      (fun t => t ∈ (gammaGroundRVUnitValueGraphProduct A D f).carrier) he) z.property
  · intro h
    exact ⟨⟨(u,v),h⟩,rfl⟩

end DiamondIntegral.Section3
