import «section 3».GammaGroundGenericFibreTests
import «section 3».GammaGroundFiniteCoverPartition
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
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

def gammaGroundRVUnitIntersection {ι : Type} [Finite ι]
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
  ⟨⋂ i, (A i).carrier,GammaGroundDefinable.iInter (fun i => (A i).definable)⟩

/-- Generic value images preserve all finite intersections, including
the empty intersection. This uses simultaneous actual fibre tests. -/
theorem gammaGroundRVGenericValueImage_iInter (hκ : Cardinal.aleph0 < κ)
    {ι : Type} [Finite ι] (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    (gammaGroundRVGenericValueImage hs h00 B hsmall (gammaGroundRVUnitIntersection B A)).carrier =
      ⋂ i, (gammaGroundRVGenericValueImage hs h00 B hsmall (A i)).carrier := by
  ext γ
  let F : Option ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
    fun o => o.elim (gammaGroundRVUnitIntersection B A) A
  obtain ⟨u,_,hF⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ F γ
  constructor
  · intro h
    apply Set.mem_iInter.mpr
    intro i
    exact (hF (some i)).mpr (Set.mem_iInter.mp ((hF none).mp h) i)
  · intro h
    apply (hF none).mpr
    apply Set.mem_iInter.mpr
    intro i
    exact (hF (some i)).mp (Set.mem_iInter.mp h i)

end DiamondIntegral.Section3
