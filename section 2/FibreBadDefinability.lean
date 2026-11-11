import «section 2».VFPairClosure
import «section 2».FibreBadLocus

/-! The actual relative bad locus is definable over the original base.
Product-coordinate closure is transported through a proved homeomorphism. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem vfPairValues_injective : Function.Injective (vfPairValues (M := M) (n := n)) := by
  intro p q he
  exact Prod.ext (vfValues_injective (funext (fun i => congrFun he (.inl i))))
    (vfValues_injective (funext (fun i => congrFun he (.inr i))))

theorem vfPair_inter_definable {S : Set M}
    (A B : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hA : S.Definable LRV (vfPairValues '' A)) (hB : S.Definable LRV (vfPairValues '' B)) :
    S.Definable LRV (vfPairValues '' (A ∩ B)) := by
  convert hA.inter hB using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hq⟩,rfl⟩
    exact ⟨⟨p,hp,rfl⟩,p,hq,rfl⟩
  · rintro ⟨⟨p,hp,rfl⟩,q,hq,he⟩
    exact ⟨p,⟨hp,vfPairValues_injective he ▸ hq⟩,rfl⟩

theorem vfPair_sdiff_definable {S : Set M}
    (A B : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hA : S.Definable LRV (vfPairValues '' A)) (hB : S.Definable LRV (vfPairValues '' B)) :
    S.Definable LRV (vfPairValues '' (A \ B)) := by
  convert hA.inter hB.compl using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hno⟩,rfl⟩
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    rintro ⟨q,hq,he⟩
    exact hno (vfPairValues_injective he ▸ hq)
  · rintro ⟨⟨p,hp,rfl⟩,hno⟩
    exact ⟨p,⟨hp,fun hpB => hno ⟨p,hpB,rfl⟩⟩,rfl⟩

theorem vfPair_base_definable {S : Set M} (I : Set (Fin 1 → VF M))
    (hI : S.Definable LRV (vfValues '' I)) :
    S.Definable LRV (vfPairValues '' (I ×ˢ (Set.univ : Set (Fin n → VF M)))) := by
  have h := (hI.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin n)).inter
    ((vfRawUniverse_definable S n).preimage_comp Sum.inr)
  convert h using 1
  ext z
  constructor
  · rintro ⟨⟨a,x⟩,⟨ha,_⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,fun i => (x i).property⟩
  · rintro ⟨⟨a,ha,he⟩,hz⟩
    let x : Fin n → VF M := fun i => ⟨z (.inr i),hz i⟩
    refine ⟨(a,x),⟨ha,Set.mem_univ _⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => rfl

theorem vfPair_graph_eq (I : Set (Fin 1 → VF M))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ) :
    vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A}) = vfPairValues '' A := by
  ext z
  constructor
  · rintro ⟨a,ha,x,hx,he⟩
    exact ⟨(a,x),hx,he⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨p.1,(hAI hp).1,p.2,hp,he⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem relativeBadLocus_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A}))) :
    S.Definable LRV (vfPairValues '' relativeBadLocus (I ×ˢ Set.univ) A) := by
  have hAp : S.Definable LRV (vfPairValues '' A) := by
    rwa [vfPair_graph_eq I A hAI] at hA
  exact vfPair_inter_definable A _ hAp
    (vfPair_closure_definable hv _
      (vfPair_sdiff_definable (I ×ˢ Set.univ) A (vfPair_base_definable I hI) hAp))

theorem relativeBadLocus_graph_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A}))) :
    S.Definable LRV (vfCorrespondenceGraph I
      (fun a => {x | (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A})) := by
  rw [vfPair_graph_eq I _ (fun p hp => hAI hp.1)]
  exact relativeBadLocus_definable hv I hI A hAI hA

end DiamondIntegral.Section2
