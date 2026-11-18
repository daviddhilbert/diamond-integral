import «section 3».GammaMixedBinaryPartitionValues
import «section 3».GammaMixedEmptyContractionValues
import «section 3».GammaMeasuredRestrictionComposition
import «section 3».GammaMixedContractionValues

/-! Binary additivity for arbitrary mixed Gamma forms descends through
the actual VF-fixed retained presentation and its corresponding domain
predicates. No measure representative is added to the ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open scoped BigOperators
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMixed_finite_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {ι : Type} [DecidableEq ι] (I : Finset ι) :
    ∀ (U : GammaGroundMeasuredVFData hc B (n+1))
      (P : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
      (hP : ∀ i, (P i).carrier ⊆ U.domain.carrier)
      (hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i).carrier (P j).carrier)
      (hCover : ∀ p : U.domain, ∃ i ∈ I, p.val ∈ (P i).carrier),
    gammaMixedContractionValue C hBC hv hNames hGenerated U =
      ∑ i ∈ I, gammaMixedContractionValue C hBC hv hNames hGenerated (U.restrict (P i) (hP i)) := by
  induction I using Finset.induction_on with
  | empty =>
    intro U P hP hDisj hCover
    rw [Finset.sum_empty]
    apply gammaMixed_empty_contraction_value C hBC hv hNames hGenerated U
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,hi,_⟩ := hCover ⟨x,hx⟩
    exact Finset.notMem_empty i hi
  | @insert i I hi ih =>
    intro U P hP hDisj hCover
    let D := U.domain.sdiff (P i)
    let hD : D.carrier ⊆ U.domain.carrier := fun _ h => h.1
    let V := U.restrict D hD
    let Q := fun j => (P j).inter D
    have hQ : ∀ j, (Q j).carrier ⊆ V.domain.carrier := fun _ _ h => h.2
    have hSubset (j : ι) (hj : j ∈ I) : (P j).carrier ⊆ D.carrier := by
      intro x hx
      refine ⟨hP j hx,?_⟩
      intro hxi
      have hij : i ≠ j := by intro he; subst j; exact hi hj
      exact Set.disjoint_left.mp (hDisj i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj) hij) hxi hx
    have hQDisj : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (Q j).carrier (Q k).carrier := by
      intro j hj k hk hjk
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp (hDisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk) hx.1 hy.1
    have hQCover : ∀ p : V.domain, ∃ j ∈ I, p.val ∈ (Q j).carrier := by
      intro p
      obtain ⟨j,hj,hp⟩ := hCover ⟨p.val,p.property.1⟩
      have hji : j ≠ i := by intro he; subst j; exact p.property.2 hp
      exact ⟨j,(Finset.mem_insert.mp hj).resolve_left hji,⟨hp,p.property⟩⟩
    have hRest := ih V Q hQ hQDisj hQCover
    have hSum : (∑ j ∈ I, gammaMixedContractionValue C hBC hv hNames hGenerated (V.restrict (Q j) (hQ j))) =
        ∑ j ∈ I, gammaMixedContractionValue C hBC hv hNames hGenerated (U.restrict (P j) (hP j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply congrArg (gammaMixedContractionValue C hBC hv hNames hGenerated)
      apply gammaMeasuredVFRestriction_trans_eq U D hD (Q j) (hQ j) (P j) (hP j)
      ext x
      exact ⟨fun h => h.1,fun h => ⟨h,hSubset j hj h⟩⟩
    rw [Finset.sum_insert hi]
    have hBinary := gammaMixed_binary_partition_values C hBC hv hg hNames hGenerated δ hδ hδ1 U (P i) (hP i)
    exact hBinary.trans (congrArg (fun z => gammaMixedContractionValue C hBC hv hNames hGenerated
      (U.restrict (P i) (hP i)) + z) (hRest.trans hSum))

end DiamondIntegral.Section3
