import «section 3».RVGroundAngularPartition
import «section 3».GammaGroundRVUnitDomains
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

theorem gammaGroundRVUnit_angular_cells {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    ∃ N : ℕ, ∃ X : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      (∀ i, Nonempty (RVAngularCell (X i).carrier)) ∧
      (∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (X i).carrier) := by
  have hA := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  obtain ⟨N,W,hW,hE,hdis,hcov⟩ := gammaGround_finite_angular_partition hκ hs h00 hc B hsmall
    (rvUnitValues '' A.carrier) hA
  let X := fun i => gammaGroundRVUnitSetOfBase (hc := hc) (W i) (hW i)
  refine ⟨N,X,hE,fun i j hij => Set.disjoint_left.mpr (fun x hi hj => Set.disjoint_left.mp (hdis i j hij) hi hj),?_⟩
  intro x
  have he : rvUnitValues x ∈ rvUnitValues '' A.carrier ↔ x ∈ A.carrier :=
    ⟨fun ⟨y,hy,he⟩ => rvUnitValues_injective he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩
  exact he.symm.trans (hcov x)
end DiamondIntegral.Section3
