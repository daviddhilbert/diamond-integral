import «section 3».RVUnitPresentationBridge
import «section 3».GammaGroundMapImages
import Section4.RVProduct
import Section4.MapProduct
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def rvUnitProductTuple (x : (Fin n → (CanonicalRV.RVSort M)ˣ) × (Fin m → (CanonicalRV.RVSort M)ˣ)) :
    Fin (n+m) → CanonicalRV.RVSort M :=
  Fin.append (fun i => (x.1 i : CanonicalRV.RVSort M)) (fun i => (x.2 i : CanonicalRV.RVSort M))

theorem rvUnitProductTuple_injective : Function.Injective (rvUnitProductTuple (M := M) (n := n) (m := m)) := by
  intro x y hxy
  apply Prod.ext
  · funext i
    apply Units.ext
    simpa only [rvUnitProductTuple,Fin.append_left] using congrFun hxy (Fin.castAdd m i)
  · funext i
    apply Units.ext
    simpa only [rvUnitProductTuple,Fin.append_right] using congrFun hxy (Fin.natAdd n i)

def rvUnitProductTupleMap (S : Set M) (n m : ℕ) :
    Map (DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) S)
      (DefSet.univ (rawRVSpace (n+m)) S) := by
  let X := DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) S
  let f := (rvUnitToRVMap (DefSet.univ (rawRVUnitSpace (M := M) n) S)).comp
    (Map.fst (rawRVUnitSpace n) (rawRVUnitSpace m) S X)
  let g := (rvUnitToRVMap (DefSet.univ (rawRVUnitSpace (M := M) m) S)).comp
    (Map.snd (rawRVUnitSpace n) (rawRVUnitSpace m) S X)
  exact (rvPack (DefSet.univ (rawRVSpace n) S) (DefSet.univ (rawRVSpace m) S)).comp (f.pair g)

theorem rvUnitProductTupleMap_values (S : Set M)
    (x : DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) S) :
    (rvUnitProductTupleMap S n m x).val = rvUnitProductTuple x.val := rfl

def gammaGroundRVUnitProductTupleMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B (rawRVSpace (n+m))) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitProductTupleMap B.real n m) (fun _ => Set.mem_univ _)

theorem gammaGroundRVUnitProductTupleMap_injective {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    Function.Injective (gammaGroundRVUnitProductTupleMap X) := by
  intro x y hxy
  apply Subtype.ext
  apply rvUnitProductTuple_injective
  exact congrArg (fun z : GammaGroundDefSet.univ hc B (rawRVSpace (n+m)) => z.val) hxy

def gammaGroundRVUnitProductTupleBijection {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m))) :
    GammaGroundBijection X (gammaGroundRVUnitProductTupleMap X).image :=
  ⟨(gammaGroundRVUnitProductTupleMap X).toImage,
    (gammaGroundRVUnitProductTupleMap X).toImage_bijective (gammaGroundRVUnitProductTupleMap_injective X)⟩
end DiamondIntegral.Section3
