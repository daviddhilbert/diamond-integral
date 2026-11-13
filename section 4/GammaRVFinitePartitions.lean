import «section 4».GammaRVIdentityIso

/-! Finite disjoint partitions in the actual RV-lifted Gamma chart ring.
Tags are formal finite component labels and do not add Gamma coordinates
or change the object degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVFinitePartitions
open GammaWeightedCharts GammaChartOperations GammaRVChartPresentation GammaRVIdentityIso
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem class_disjoint_union (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hd : Disjoint I J) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (ofTotal B n (I ∪ J) (GammaQuantifierLogic.union_definable_base B I J hI hJ) μ hμ) =
      objectClass (ofTotal B n I hI μ hμ) + objectClass (ofTotal B n J hJ μ hμ) := by
  have he : objectClass (ofTotal B n (I ∩ J) (GammaRelationLogic.inter_definable_base B I J hI hJ) μ hμ) = 0 :=
    (class_eq_on_domain (ofTotal B n (I ∩ J) (GammaRelationLogic.inter_definable_base B I J hI hJ) μ hμ) (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ)
      (Set.disjoint_iff_inter_eq_empty.mp hd) (fun _ _ => rfl)).trans (class_empty B n μ hμ)
  have h := class_scissor B n I J hI hJ
    (GammaQuantifierLogic.union_definable_base B I J hI hJ)
    (GammaRelationLogic.inter_definable_base B I J hI hJ) μ hμ
  rwa [he, add_zero] at h

def support {ι : Type*} (s : Finset ι) {n : ℕ} (I : ι → Set (Fin n → Values.Gamma (M := M))) :
    Set (Fin n → Values.Gamma (M := M)) := ⋃ i ∈ s, I i

theorem support_definable {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i)) :
    GammaDefinable B (support s I) := by
  induction s using Finset.induction_on with
  | empty => simpa only [support, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] using GammaIntegerFamilies.empty_definable_base B n
  | @insert i s hi ih =>
    have he : support (insert i s) I = I i ∪ support s I := by ext x; simp [support]
    rw [he]
    exact GammaQuantifierLogic.union_definable_base B _ _ (hI i) ih

def unionChart {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : Chart B n :=
  ofTotal B n (support s I) (support_definable s I hI) μ hμ

theorem class_unionChart {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (unionChart s I hI μ hμ) = ∑ i ∈ s, objectClass (ofTotal B n (I i) (hI i) μ hμ) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : support (∅ : Finset ι) I = ∅ := by ext x; simp [support]
    have hc := class_eq_on_domain (unionChart (∅ : Finset ι) I hI μ hμ)
      (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ) he (fun _ _ => rfl)
    simpa only [Finset.sum_empty] using hc.trans (class_empty B n μ hμ)
  | @insert i s hi ih =>
    have hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j) :=
      fun i hi j hj hij => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hdis : Disjoint (I i) (support s I) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hy
      exact Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun he => hi (he ▸ hj))) hx hxj
    have he : support (insert i s) I = I i ∪ support s I := by ext x; simp [support]
    have hc := class_eq_on_domain (unionChart (insert i s) I hI μ hμ)
      (ofTotal B n (I i ∪ support s I) (GammaQuantifierLogic.union_definable_base B _ _ (hI i) (support_definable s I hI)) μ hμ)
      he (fun _ _ => rfl)
    rw [hc, class_disjoint_union B n _ _ (hI i) (support_definable s I hI) hdis μ hμ]
    change objectClass (ofTotal B n (I i) (hI i) μ hμ) + objectClass (unionChart s I hI μ hμ) = _
    rw [ih hp, Finset.sum_insert hi]

def restrict {B : Base (M := M)} {n : ℕ} (a : Chart B n)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) : Chart B n :=
  ofTotal B n I hI a.normalizedVolume a.normalizedVolume_definable

theorem class_partition {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ} (a : Chart B n)
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j)) (hc : support s I = a.support) :
    objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i)) := by
  have h := class_eq_on_domain a (unionChart s I hI a.normalizedVolume a.normalizedVolume_definable)
    hc.symm (fun z hz => (a.normalizedVolume_on z hz).symm)
  exact h.trans (class_unionChart s I hI hd a.normalizedVolume a.normalizedVolume_definable)

end DiamondIntegral.Section4.GammaRVFinitePartitions
