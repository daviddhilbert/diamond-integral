import «section 3».GammaGroundRVAngularWeightCharts
import «section 3».RVGroundAngularPartition
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

/-- A Gamma function of the original coordinate values has a finite
disjoint product decomposition whose weights live on the Gamma factors. -/
theorem gammaGroundRVUnit_value_weight_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVFormProductChart hc B (rawRVUnitSpace (M := M) n)
        (fun x => f (rvUnitTupleValues x)),
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (C i).source.carrier) := by
  have hA := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  obtain ⟨N,W,hW,hE,hdis,hcov⟩ := gammaGround_finite_angular_partition hκ hs h00 hc B hsmall
    (rvUnitValues '' A.carrier) hA
  let X := fun i => gammaGroundRVUnitSetOfBase (hc := hc) (W i) (hW i)
  have hXd : ∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier :=
    fun i j hij => Set.disjoint_left.mpr (fun x hi hj => Set.disjoint_left.mp (hdis i j hij) hi hj)
  have hXc : ∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (X i).carrier := by
    intro x
    have he : rvUnitValues x ∈ rvUnitValues '' A.carrier ↔ x ∈ A.carrier :=
      ⟨fun ⟨y,hy,he⟩ => rvUnitValues_injective he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩
    exact he.symm.trans (hcov x)
  apply gammaGroundRVFormProductCharts_assemble A X hXd hXc
  intro i
  exact gammaGroundRVAngularCell_weight_charts hκ hs h00 hsmall hγsmall hΓ (X i) (Classical.choice (hE i)) f hf
end DiamondIntegral.Section3
