import «section 3».GammaGroundRVUnitDomains
import «section 3».GammaGroundMapImages

/-! Initial-coordinate projection of actual nonzero RV tuples preserves
the original real/Gamma base and retains its exact image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def unitTupleInitMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) (n+1)) S) (DefSet.univ (rawRVUnitSpace n) S) := by
  have hcode (c : (rawRVUnitSpace (M := M) (n+1)).domain) :
      rvUnitValues (Fin.init ((rawRVUnitSpace (n+1)).decode c)) = Fin.init c.val := by
    funext i
    exact congrFun (rvUnitValues_decode c) i.castSucc
  have hdom (c : (rawRVUnitSpace (M := M) (n+1)).domain) :
      Fin.init c.val ∈ (rawRVUnitSpace (M := M) n).domain :=
    ⟨Fin.init ((rawRVUnitSpace (n+1)).decode c), hcode c⟩
  refine Map.ofCodes _ Fin.init Fin.init (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  exact rvUnitValues_injective ((rvUnitValues_decode _).trans (hcode c).symm)

def groundUnitTupleInitMap (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
  GammaGroundMap.ofGlobal X _ (unitTupleInitMap B.real n) (fun _ => Set.mem_univ _)

theorem groundUnitTupleInitMap_image (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))) :
    (groundUnitTupleInitMap X).image.carrier = Fin.init '' X.carrier := by
  ext t
  exact ⟨fun ⟨x, hx⟩ => ⟨x.val, x.property, hx⟩, fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩

end DiamondIntegral.Section5
