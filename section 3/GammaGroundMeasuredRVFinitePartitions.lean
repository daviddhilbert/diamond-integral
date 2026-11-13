import «section 3».GammaGroundRVFinitePartitions
import «section 3».GammaGroundMeasuredRVProductScissors
import «section 3».GammaGroundMeasuredRVSemiring
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

theorem gammaGroundMeasuredRVClass_of_empty {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (hU : U.underlying.domain.carrier = ∅) : gammaGroundMeasuredRVClass U = 0 := by
  let f : GammaGroundMeasuredRVHom U (GammaGroundMeasuredRVObject.empty hc B k) :=
    ⟨GammaGroundBijection.ofEmpty hU rfl,fun a => False.elim ((Set.eq_empty_iff_forall_notMem.mp hU) a.val a.property)⟩
  rw [gammaGroundMeasuredRVClass_iso (asIso f),gammaGroundMeasuredRVClass_empty]

theorem gammaGroundMeasuredRVSemiringClass_of_empty {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (hU : U.underlying.domain.carrier = ∅) : gammaGroundMeasuredRVSemiringClass U = 0 := by
  have hh := congrArg (gammaGroundMeasuredRVKPlusToSemiring (M := M) (hc := hc) (ground := B) (k := k))
    (gammaGroundMeasuredRVClass_of_empty U hU)
  simpa only [gammaGroundMeasuredRVKPlusToSemiring_class,map_zero] using hh

variable {k : ℕ}

theorem gammaGroundMeasuredRVClass_finiteUnion (U : GammaGroundMeasuredRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hA : ∀ i, (A i).carrier ⊆ U.underlying.domain.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) (T : Finset ι) :
    gammaGroundMeasuredRVClass (U.restrict (gammaGroundDefSetFiniteUnion T A)
      (by rintro x ⟨i,hi,hx⟩; exact hA i hx)) = ∑ i ∈ T, gammaGroundMeasuredRVClass (U.restrict (A i) (hA i)) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : (U.restrict (gammaGroundDefSetFiniteUnion ∅ A)
        (by rintro x ⟨i,hi,hx⟩; exact hA i hx)).underlying.domain.carrier = ∅ := by
      ext x
      simp only [GammaGroundMeasuredRVObject.restrict,GammaGroundRVObject.restrict,gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,
        Finset.notMem_empty,false_and,exists_false,Set.mem_empty_iff_false]
    simpa only [Finset.sum_empty] using gammaGroundMeasuredRVClass_of_empty _ he
  | @insert i T hit ih =>
    let V := gammaGroundDefSetFiniteUnion T A
    let W := U.restrict (gammaGroundDefSetFiniteUnion (insert i T) A)
      (by rintro x ⟨j,hj,hx⟩; exact hA j hx)
    have hiW : (A i).carrier ⊆ W.underlying.domain.carrier := fun x hx => ⟨i,Finset.mem_insert_self i T,hx⟩
    have htW : V.carrier ⊆ W.underlying.domain.carrier := by
      rintro x ⟨j,hj,hx⟩
      exact ⟨j,Finset.mem_insert_of_mem hj,hx⟩
    have hdis : Disjoint (A i).carrier V.carrier := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨j,hj,hy⟩
      exact Set.disjoint_left.mp (hd i j (fun he => hit (he.symm ▸ hj))) hx hy
    have he : ((A i).union V).carrier = W.underlying.domain.carrier := by
      ext x
      change (x ∈ (A i).carrier ∨ ∃ j ∈ T, x ∈ (A j).carrier) ↔ ∃ j ∈ insert i T, x ∈ (A j).carrier
      simp only [Finset.mem_insert,exists_eq_or_imp]
    have hp := gammaGroundMeasuredRVClass_partition W (A i) V hiW htW hdis he
    let fi : GammaGroundMeasuredRVHom (W.restrict (A i) hiW) (U.restrict (A i) (hA i)) :=
      {bijection := GammaGroundBijection.id (A i), preserves := fun _ => rfl}
    let ft : GammaGroundMeasuredRVHom (W.restrict V htW)
        (U.restrict V (by rintro x ⟨j,hj,hx⟩; exact hA j hx)) :=
      {bijection := GammaGroundBijection.id V, preserves := fun _ => rfl}
    have hiIso := asIso (show W.restrict (A i) hiW ⟶ U.restrict (A i) (hA i) from fi)
    have htIso := asIso (show W.restrict V htW ⟶ U.restrict V (by rintro x ⟨j,hj,hx⟩; exact hA j hx) from ft)
    rw [gammaGroundMeasuredRVClass_iso hiIso,gammaGroundMeasuredRVClass_iso htIso,ih] at hp
    simpa only [Finset.sum_insert hit] using hp

theorem gammaGroundMeasuredRVClass_finite_partition [Fintype ι]
    (U : GammaGroundMeasuredRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ U.underlying.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundMeasuredRVClass U = ∑ i, gammaGroundMeasuredRVClass (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hA : ∀ i, (A i).carrier ⊆ U.underlying.domain.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  have he : U.underlying.domain.carrier = (gammaGroundDefSetFiniteUnion Finset.univ A).carrier := by
    ext x
    simpa only [gammaGroundDefSetFiniteUnion,Set.mem_ofPred_eq,Finset.mem_univ,true_and] using hcov x
  let V := U.restrict (gammaGroundDefSetFiniteUnion Finset.univ A)
      (by rintro x ⟨i,hi,hx⟩; exact hA i hx)
  let f : GammaGroundMeasuredRVHom U V :=
    {bijection := GammaGroundBijection.ofCarrierEq he, preserves := fun _ => rfl}
  have hi : U ≅ V := asIso (show U ⟶ V from f)
  rw [gammaGroundMeasuredRVClass_iso hi,gammaGroundMeasuredRVClass_finiteUnion U A hA hd]

theorem gammaGroundMeasuredRVSemiringClass_finite_partition [Fintype ι]
    (U : GammaGroundMeasuredRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ U.underlying.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundMeasuredRVSemiringClass U = ∑ i, gammaGroundMeasuredRVSemiringClass
      (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hh := congrArg (gammaGroundMeasuredRVKPlusToSemiring (M := M) (hc := hc) (ground := B) (k := k))
    (gammaGroundMeasuredRVClass_finite_partition U A hd hcov)
  simpa only [map_sum,gammaGroundMeasuredRVKPlusToSemiring_class] using hh
end DiamondIntegral.Section3
