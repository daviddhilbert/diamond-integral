import «section 3».GammaGroundVFSemiring
import «section 3».GammaGroundRVFinitePartitions
import «section 3».GammaGroundEmptyBijections

/-! Finite disjoint partitions of actual finite-RV-fibre VF domains give
literal finite sums in the native positive and semiring presentations.
This uses only actual same-ground scissors and bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {ι : Type}

theorem nativeFiniteVFClass_of_empty (U : GammaGroundFiniteVFObject hc B) (hU : U.domain.carrier = ∅) :
    gammaGroundFiniteVFClass U = 0 := by
  have h : U ≅ GammaGroundFiniteVFObject.empty hc B :=
    asIso (show U ⟶ GammaGroundFiniteVFObject.empty hc B from GammaGroundBijection.ofEmpty hU rfl)
  exact (gammaGroundFiniteVFClass_iso h).trans gammaGroundFiniteVFClass_empty

theorem nativeFiniteVFClass_partition (U : GammaGroundFiniteVFObject hc B)
    (A C : GammaGroundDefSet hc B (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hA : A.carrier ⊆ U.domain.carrier) (hC : C.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier C.carrier) (hcov : (A.union C).carrier = U.domain.carrier) :
    gammaGroundFiniteVFClass U = gammaGroundFiniteVFClass (U.restrict A hA) +
      gammaGroundFiniteVFClass (U.restrict C hC) := by
  have hrest : (U.domain.sdiff A).carrier = C.carrier := by
    ext x
    constructor
    · rintro ⟨hx,hn⟩
      have h := hcov.symm ▸ hx
      exact h.resolve_left hn
    · intro hx
      exact ⟨hC hx,fun ha => Set.disjoint_left.mp hd ha hx⟩
  have hi : U.restrict (U.domain.sdiff A) (fun _ h => h.1) ≅ U.restrict C hC :=
    asIso (show _ ⟶ _ from GammaGroundBijection.ofCarrierEq hrest)
  have h := gammaGroundFiniteVFClass_scissor U A hA
  rw [gammaGroundFiniteVFClass_iso hi] at h
  exact h.symm

theorem nativeFiniteVFClass_finiteUnion (U : GammaGroundFiniteVFObject hc B)
    (A : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hA : ∀ i,(A i).carrier ⊆ U.domain.carrier)
    (hd : ∀ i j,i ≠ j → Disjoint (A i).carrier (A j).carrier) (T : Finset ι) :
    gammaGroundFiniteVFClass (U.restrict (gammaGroundDefSetFiniteUnion T A)
      (by rintro x ⟨i,hi,hx⟩;exact hA i hx)) =
        ∑ i ∈ T,gammaGroundFiniteVFClass (U.restrict (A i) (hA i)) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : (U.restrict (gammaGroundDefSetFiniteUnion ∅ A)
        (by rintro x ⟨i,hi,hx⟩;exact hA i hx)).domain.carrier = ∅ := by
      ext x
      simp only [GammaGroundFiniteVFObject.restrict,gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,
        Finset.notMem_empty,false_and,exists_false,Set.mem_empty_iff_false]
    simpa only [Finset.sum_empty] using nativeFiniteVFClass_of_empty _ he
  | @insert i T hit ih =>
    let V := gammaGroundDefSetFiniteUnion T A
    let W := U.restrict (gammaGroundDefSetFiniteUnion (insert i T) A)
      (by rintro x ⟨j,hj,hx⟩;exact hA j hx)
    have hiW : (A i).carrier ⊆ W.domain.carrier := fun x hx => ⟨i,Finset.mem_insert_self i T,hx⟩
    have htW : V.carrier ⊆ W.domain.carrier := by
      rintro x ⟨j,hj,hx⟩
      exact ⟨j,Finset.mem_insert_of_mem hj,hx⟩
    have hdis : Disjoint (A i).carrier V.carrier := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨j,hj,hy⟩
      exact Set.disjoint_left.mp (hd i j (fun he => hit (he.symm ▸ hj))) hx hy
    have he : ((A i).union V).carrier = W.domain.carrier := by
      ext x
      change (x ∈ (A i).carrier ∨ ∃ j ∈ T,x ∈ (A j).carrier) ↔ ∃ j ∈ insert i T,x ∈ (A j).carrier
      simp only [Finset.mem_insert,exists_eq_or_imp]
    have hp := nativeFiniteVFClass_partition W (A i) V hiW htW hdis he
    have hiIso : W.restrict (A i) hiW ≅ U.restrict (A i) (hA i) :=
      asIso (show _ ⟶ _ from GammaGroundBijection.id (A i))
    have htIso : W.restrict V htW ≅ U.restrict V (by rintro x ⟨j,hj,hx⟩;exact hA j hx) :=
      asIso (show _ ⟶ _ from GammaGroundBijection.id V)
    rw [gammaGroundFiniteVFClass_iso hiIso,gammaGroundFiniteVFClass_iso htIso,ih] at hp
    simpa only [Finset.sum_insert hit] using hp

theorem nativeFiniteVFClass_finite_partition [Fintype ι] (U : GammaGroundFiniteVFObject hc B)
    (A : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hd : ∀ i j,i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x,x ∈ U.domain.carrier ↔ ∃ i,x ∈ (A i).carrier) :
    gammaGroundFiniteVFClass U = ∑ i,gammaGroundFiniteVFClass
      (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hA : ∀ i,(A i).carrier ⊆ U.domain.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  have he : U.domain.carrier = (gammaGroundDefSetFiniteUnion Finset.univ A).carrier := by
    ext x
    simpa only [gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,Finset.mem_univ,true_and] using hcov x
  have hi : U ≅ U.restrict (gammaGroundDefSetFiniteUnion Finset.univ A)
      (by rintro x ⟨i,hi,hx⟩;exact hA i hx) :=
    asIso (show _ ⟶ _ from GammaGroundBijection.ofCarrierEq he)
  rw [gammaGroundFiniteVFClass_iso hi,nativeFiniteVFClass_finiteUnion U A hA hd]

theorem nativeVFSemiringClass_finite_partition [Fintype ι] (U : GammaGroundFiniteVFObject hc B)
    (A : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hd : ∀ i j,i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x,x ∈ U.domain.carrier ↔ ∃ i,x ∈ (A i).carrier) :
    gammaGroundVFSemiringClass U = ∑ i,gammaGroundVFSemiringClass
      (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have h := congrArg (gammaGroundFiniteVFKPlusToSemiring (hc := hc) (ground := B))
    (nativeFiniteVFClass_finite_partition U A hd hcov)
  simpa only [map_sum,gammaGroundFiniteVFKPlusToSemiring_class] using h

end DiamondIntegral.Section5
