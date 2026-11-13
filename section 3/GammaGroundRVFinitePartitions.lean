import «section 3».GammaGroundRVEmptyClasses
import «section 3».GammaGroundRVProductScissors
import «section 3».GammaGroundFiniteUnions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P : Space LRV M} {ι : Type}

def gammaGroundDefSetFiniteUnion (T : Finset ι) (A : ι → GammaGroundDefSet hc B P) : GammaGroundDefSet hc B P := by
  refine ⟨{x | ∃ i ∈ T, x ∈ (A i).carrier},?_⟩
  apply (GammaGroundDefinable.iUnion (fun i : T => (A i.val).definable)).congr
  intro x
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,i.property,hi⟩,fun ⟨i,hi,hx⟩ => ⟨⟨i,hi⟩,hx⟩⟩

variable {k : ℕ}

theorem gammaGroundRVClass_finiteUnion (U : GammaGroundRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity))
    (hA : ∀ i, (A i).carrier ⊆ U.domain.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) (T : Finset ι) :
    gammaGroundRVClass (U.restrict (gammaGroundDefSetFiniteUnion T A)
      (by rintro x ⟨i,hi,hx⟩; exact hA i hx)) = ∑ i ∈ T, gammaGroundRVClass (U.restrict (A i) (hA i)) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : (U.restrict (gammaGroundDefSetFiniteUnion ∅ A)
        (by rintro x ⟨i,hi,hx⟩; exact hA i hx)).domain.carrier = ∅ := by
      ext x
      simp only [GammaGroundRVObject.restrict,gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,
        Finset.notMem_empty,false_and,exists_false,Set.mem_empty_iff_false]
    simpa only [Finset.sum_empty] using gammaGroundRVClass_of_empty _ he
  | @insert i T hit ih =>
    let V := gammaGroundDefSetFiniteUnion T A
    let W := U.restrict (gammaGroundDefSetFiniteUnion (insert i T) A)
      (by rintro x ⟨j,hj,hx⟩; exact hA j hx)
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
      change (x ∈ (A i).carrier ∨ ∃ j ∈ T, x ∈ (A j).carrier) ↔ ∃ j ∈ insert i T, x ∈ (A j).carrier
      simp only [Finset.mem_insert,exists_eq_or_imp]
    have hp := gammaGroundRVClass_partition W (A i) V hiW htW hdis he
    have hiIso : W.restrict (A i) hiW ≅ U.restrict (A i) (hA i) :=
      asIso (show _ ⟶ _ from GammaGroundBijection.id (A i))
    have htIso : W.restrict V htW ≅ U.restrict V (by rintro x ⟨j,hj,hx⟩; exact hA j hx) :=
      asIso (show _ ⟶ _ from GammaGroundBijection.id V)
    rw [gammaGroundRVClass_iso hiIso,gammaGroundRVClass_iso htIso,ih] at hp
    simpa only [Finset.sum_insert hit] using hp

theorem gammaGroundRVClass_finite_partition [Fintype ι]
    (U : GammaGroundRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ U.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundRVClass U = ∑ i, gammaGroundRVClass (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hA : ∀ i, (A i).carrier ⊆ U.domain.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  have he : U.domain.carrier = (gammaGroundDefSetFiniteUnion Finset.univ A).carrier := by
    ext x
    simpa only [gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,Finset.mem_univ,true_and] using hcov x
  have hi : U ≅ U.restrict (gammaGroundDefSetFiniteUnion Finset.univ A)
      (by rintro x ⟨i,hi,hx⟩; exact hA i hx) :=
    asIso (show _ ⟶ _ from GammaGroundBijection.ofCarrierEq he)
  rw [gammaGroundRVClass_iso hi,gammaGroundRVClass_finiteUnion U A hA hd]

theorem gammaGroundRVSemiringClass_finite_partition [Fintype ι]
    (U : GammaGroundRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ U.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundRVSemiringClass U = ∑ i, gammaGroundRVSemiringClass
      (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hh := congrArg (gammaGroundRVKPlusToSemiring (M := M) (hc := hc) (ground := B) (k := k))
    (gammaGroundRVClass_finite_partition U A hd hcov)
  simpa only [map_sum,gammaGroundRVKPlusToSemiring_class] using hh
end DiamondIntegral.Section3
