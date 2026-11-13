import «section 3».GammaGroundRVGenericValueImage
import «section 3».GammaGroundRVValueGraph
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n m : ℕ}

/-- An actual RV map determines a uniformly definable relation on its
source and target Gamma tuples by its residue-generic full value graph. -/
def gammaGroundRVGenericValueGraph
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+m))) :=
  gammaGroundRVGenericValueImage hs h00 B hsmall (gammaGroundRVUnitValueGraph A D f)

theorem gammaGroundRVGenericValueGraph_append_mem_iff
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D)
    (u : Fin n → (CanonicalRV.RVSort M)ˣ) (v : Fin m → (CanonicalRV.RVSort M)ˣ) :
    Fin.append (rvUnitTupleValues u) (rvUnitTupleValues v) ∈
        (gammaGroundRVGenericValueGraph hs h00 B hsmall A D f).carrier ↔
      rvUnitValues (Fin.append u v) ∈
        rvFullFibreGeneric (rvUnitValues '' (gammaGroundRVUnitValueGraph A D f).carrier) := by
  have he : rvUnitTupleValues (Fin.append u v) =
      Fin.append (rvUnitTupleValues u) (rvUnitTupleValues v) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rvUnitTupleValues,Fin.append_left]
    · simp only [rvUnitTupleValues,Fin.append_right]
  rw [← he]
  exact gammaGroundRVGenericValueImage_mem_iff hs h00 B hsmall _ _

end DiamondIntegral.Section3
