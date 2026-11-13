import «section 4».GammaRVFinitePartitions
import «section 4».GammaBoundedRVEmpty

/-! Finite partition additivity inside the intrinsic bounded Gamma ring.
Every restriction and finite union retains a proved domain bound; no
injectivity into the unbounded ring is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVPartitions
open GammaBoundedRVCharts GammaBoundedRVPresentation GammaBoundedProducts GammaOrderLogic GammaDefinableMaps
open GammaRVFinitePartitions (support support_definable)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem class_eq_on_domain {B : Base (M := M)} {n : ℕ} (a b : BoundedChart B n)
    (hs : a.support = b.support) (hv : ∀ z ∈ a.support, a.volume z = b.volume z) : objectClass a = objectClass b :=
  class_iso (GammaRVIdentityIso.sameDomainIso a.toChart b.toChart hs hv)

theorem class_disjoint_union (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hbI : DomainBounded I) (hbJ : DomainBounded J) (hd : Disjoint I J)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (ofTotal B n (I ∪ J) (GammaQuantifierLogic.union_definable_base B I J hI hJ) (hbI.union hbJ) μ hμ) =
      objectClass (ofTotal B n I hI hbI μ hμ) + objectClass (ofTotal B n J hJ hbJ μ hμ) := by
  let d := ofTotal B n (I ∩ J) (GammaRelationLogic.inter_definable_base B I J hI hJ)
    (hbI.subset Set.inter_subset_left) μ hμ
  have he : objectClass d = 0 := GammaBoundedRVEmpty.class_empty_support B d (Set.disjoint_iff_inter_eq_empty.mp hd)
  have h := class_scissor B n I J hI hJ hbI hbJ
    (GammaQuantifierLogic.union_definable_base B I J hI hJ)
    (GammaRelationLogic.inter_definable_base B I J hI hJ) μ hμ
  change _ + objectClass d = _ at h
  rwa [he, add_zero] at h

theorem support_bounded {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hbI : ∀ i, DomainBounded (I i)) : DomainBounded (support s I) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : support (∅ : Finset ι) I = ∅ := by ext x; simp [support]
    rw [he]
    exact DomainBounded.empty n
  | @insert i s hi ih =>
    have he : support (insert i s) I = I i ∪ support s I := by ext x; simp [support]
    rw [he]
    exact (hbI i).union ih

def unionChart {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i)) (hbI : ∀ i, DomainBounded (I i))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : BoundedChart B n :=
  ofTotal B n (support s I) (support_definable s I hI) (support_bounded s I hbI) μ hμ

theorem class_unionChart {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ}
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i)) (hbI : ∀ i, DomainBounded (I i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (unionChart s I hI hbI μ hμ) = ∑ i ∈ s, objectClass (ofTotal B n (I i) (hI i) (hbI i) μ hμ) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : support (∅ : Finset ι) I = ∅ := by ext x; simp [support]
    simpa only [Finset.sum_empty] using GammaBoundedRVEmpty.class_empty_support B (unionChart (∅ : Finset ι) I hI hbI μ hμ) he
  | @insert i s hi ih =>
    have hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j) :=
      fun i hi j hj hij => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hdis : Disjoint (I i) (support s I) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hy
      exact Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) (fun he => hi (he ▸ hj))) hx hxj
    have he : support (insert i s) I = I i ∪ support s I := by ext x; simp [support]
    have hc := class_eq_on_domain (unionChart (insert i s) I hI hbI μ hμ)
      (ofTotal B n (I i ∪ support s I) (GammaQuantifierLogic.union_definable_base B _ _ (hI i) (support_definable s I hI))
        ((hbI i).union (support_bounded s I hbI)) μ hμ) he (fun _ _ => rfl)
    rw [hc, class_disjoint_union B n _ _ (hI i) (support_definable s I hI) (hbI i) (support_bounded s I hbI) hdis μ hμ]
    change objectClass (ofTotal B n (I i) (hI i) (hbI i) μ hμ) + objectClass (unionChart s I hI hbI μ hμ) = _
    rw [ih hp, Finset.sum_insert hi]

def restrict {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I ⊆ a.support) : BoundedChart B n :=
  ofTotal B n I hI (a.domain_bounded.subset hi) a.toChart.normalizedVolume a.toChart.normalizedVolume_definable

theorem class_partition {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ} (a : BoundedChart B n)
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i)) (hi : ∀ i, I i ⊆ a.support)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j)) (hc : support s I = a.support) :
    objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i) (hi i)) := by
  let hbI := fun i => a.domain_bounded.subset (hi i)
  have h := class_eq_on_domain a (unionChart s I hI hbI a.toChart.normalizedVolume a.toChart.normalizedVolume_definable)
    hc.symm (fun z hz => (a.toChart.normalizedVolume_on z hz).symm)
  exact h.trans (class_unionChart s I hI hbI hd a.toChart.normalizedVolume a.toChart.normalizedVolume_definable)

end DiamondIntegral.Section4.GammaBoundedRVPartitions
