import «section 6».RealTupleCodeSets
import «section 2».BoundaryCoordinates
import «section 3».IntegrationFinitaryPartition
import «section 3».RVDimensionBridge

/-! The actual RV boundary has a finite-to-one map to one fewer RV
coordinate. All former geometric inputs of the boundary theorem are
supplied by checked earlier-result adapters over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def vfRVBoundary (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawVFSpace (M := M) n) S) : DefSet (rawRVSpace (M := M) n) S := by
  let B := tupleRV M '' A.carrier ∩ tupleRV M '' A.carrierᶜ
  have hAv : DefinableOver S (fun _ : Fin n => .vf) (vfValues '' A.carrier) :=
    SpecialTransformations.Section3.raw_definableOver_sorted hc S _ _
    (vfDefSet_codeImage_definable A) (by rintro z ⟨a,ha,rfl⟩ j; exact (a j).property)
  have hB := (rawRVBoundary_definable hc S (vfValues '' A.carrier) hAv).raw_definable
  rw [rawRVBoundary_vfValues] at hB
  exact rvDefSetOfCodeImage B hB

theorem exists_vfRVBoundary_finite_map
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawVFSpace (M := M) (n+1)) S) :
    ∃ f : Map (vfRVBoundary hc A) (DefSet.univ (rawRVSpace (M := M) n) S), f.FiniteFibres := by
  have h := lemma_2_35_vf hc h00 hs S hsmall hΓ
    (DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs)
    DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput
    DiamondIntegral.Section3.integrationOpenDiscNamesImageInput A.carrier (vfDefSet_codeImage_definable A)
  have hDef := (rawRVBoundary_definable hc S (vfValues '' A.carrier)
    (SpecialTransformations.Section3.raw_definableOver_sorted hc S _ _
      (vfDefSet_codeImage_definable A) (by rintro z ⟨a,ha,rfl⟩ j; exact (a j).property)))
  rw [rawRVBoundary_vfValues] at hDef
  have hMap := (rvDimension_lt_succ_iff_finite_map hc S _ hDef).mp h
  exact (DiamondIntegral.Section3.rvFiniteMap_iff hc (vfRVBoundary hc A) n).mp hMap

end DiamondIntegral.Section6
