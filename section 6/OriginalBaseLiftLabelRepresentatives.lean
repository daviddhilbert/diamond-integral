import «section 6».OriginalBaseMeasuredRVLifting
import Section9.LiftLabelRepresentatives

/-! VF representatives of finite-head RV label functions over the
actual original VF-generated field base. Temporary definable closure
is eliminated from the complete graph of the representative map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem exists_liftLabelRepresentative_vfGenerated
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (S : LRV.Substructure M) (F : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (U : RVFiniteObject (M := M) (S : Set M) k)
    (τ : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (S : Set M)))
    (hτ : ∀ u, ((τ u).val 0).val ≠ iRVZero) :
    ∃ c : Map (rvLift U.obj) (DefSet.univ (rawVFSpace (M := M) 1) (S : Set M)),
      ∀ p, CanonicalRV.encodedRv ((c p).val 0) = (τ (liftLabelMap U.obj p)).val 0 := by
  let B := GammaParameters.closureBase (⟨(S : Set M),∅⟩ : ParameterBase M)
  have hST : (S : Set M) ⊆ B.real := (GammaParameters.subset_closureBase ⟨(S : Set M),∅⟩).1
  have hParams : ∀ b ∈ B.real, (S : Set M).Definable₁ LRV {b} := by
    rintro b ⟨σ,hb⟩
    exact ((GammaParameters.dcl_base_empty_iff (S : Set M) σ b).mp hb).raw_definable
  have hBsmall : Cardinal.mk B.real < κ := IntegrationInACVF.Section6.closureBase_real_small hκ
    ⟨(S : Set M),∅⟩ hsmall (by simpa using (Cardinal.zero_le Cardinal.aleph0).trans_lt hκ)
  let UB : RVFiniteObject (M := M) B.real k := ⟨extendRVObjectBase hST U.obj,U.property⟩
  obtain ⟨cB,hcB⟩ := exists_liftLabelRepresentative hc hκ.le hs h00 B hBsmall
    (F.gamma_closure_generated ∅) UB (extendMapBase hST τ) hτ
  let c : Map (rvLift U.obj) (DefSet.univ (rawVFSpace (M := M) 1) (S : Set M)) :=
    ⟨cB,definable_finite_index_parameter_descent _ cB.graph_definable hParams⟩
  exact ⟨c,hcB⟩

end DiamondIntegral.Section6
