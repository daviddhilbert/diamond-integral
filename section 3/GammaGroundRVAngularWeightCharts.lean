import «section 3».GammaGroundRVProductWeightRefinement
import «section 3».GammaGroundRVAngularProductMaps
import «section 3».GammaGroundRVFormChartAssembly
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaGroundRVAngularCell_weight_charts {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVFormProductChart hc B (rawRVUnitSpace (M := M) n)
        (fun x => f (rvUnitTupleValues x)),
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (C i).source.carrier) := by
  let K := Section2.zeroFaceChart (Set.range E.active)
  obtain ⟨N,R,G,Y,F,hR,_,hdis,hcov,hF⟩ :=
    gammaGroundRVAngularCell_product_maps hκ hs h00 hsmall hγsmall hΓ X E K
  apply gammaGroundRVFormProductCharts_assemble X Y hdis hcov
  intro i
  apply gammaGroundRVProduct_weight_refinement (Y i) (R i) (hR i) (G i) (F i)
    (fun z => f (E.valueReconstruction K z))
    (hf.comp (fun j z => E.valueReconstruction K z j) (E.valueReconstruction_definable K _))
    (fun x => f (rvUnitTupleValues x))
  intro a
  rw [hF i a]
  exact (congrArg f (E.valueReconstruction_coordinate K a.val)).symm
end DiamondIntegral.Section3
