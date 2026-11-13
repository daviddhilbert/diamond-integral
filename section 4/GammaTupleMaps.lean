import «section 4».GammaBijectiveRelations
import «section 4».GammaDefinableMaps

/-! Graphs and images of actual finite Gamma tuple maps from their
coordinate graphs. All output RV codes are retained by the injective
coordinate projection; no representative section is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTupleMaps
open GammaOrderLogic GammaDefinableMaps GammaBijectiveRelations FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem graph_definable (B : Base (M := M)) {n m : ℕ}
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hT : ∀ i, MapDefinable B (fun z => T z i)) : GammaDefinable B (graphOn I T) := by
  let π (i : Fin n) : Fin (m + 1) → Fin (n + m) :=
    Fin.cases (tailIndex n m i) (headIndex n m)
  have hi := GammaRelationLogic.preimage_definable_base B _ hI (headIndex n m)
  have ht := GammaQuantifierLogic.finite_iInter_definable_base B
    (fun i : Fin n => {w | w ∘ π i ∈ {z | z 0 = T (fun j => z j.succ) i}})
    (fun i => GammaRelationLogic.preimage_definable_base B _ (hT i) (π i))
  have h := GammaRelationLogic.inter_definable_base B _ _ hi ht
  convert h using 1
  ext w
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  change (w ∘ headIndex n m ∈ I ∧ T (w ∘ headIndex n m) = w ∘ tailIndex n m) ↔
    w ∘ headIndex n m ∈ I ∧ ∀ i, w ∘ π i ∈ {z | z 0 = T (fun j => z j.succ) i}
  apply and_congr_right
  intro _
  constructor
  · intro he i
    exact (congrFun he i).symm
  · intro he
    exact funext (fun i => (he i).symm)

theorem image_definable (B : Base (M := M)) {n m : ℕ}
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hT : ∀ i, MapDefinable B (fun z => T z i)) : GammaDefinable B (T '' I) := by
  have h := GammaQuantifierLogic.image_definable_base B _ (graph_definable B I hI T hT)
    (tailIndex n m) (tailIndex_injective n m)
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨join n m x (T x), (graphOn_join I T x (T x)).mpr ⟨hx, rfl⟩,
      funext (join_tail n m x (T x))⟩
  · rintro ⟨w, ⟨hw, he⟩, hy⟩
    exact ⟨w ∘ headIndex n m, hw, he.trans hy⟩

theorem preimage_definable (B : Base (M := M)) {n m : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaDefinable B P)
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hT : ∀ i, MapDefinable B (fun z => T z i)) : GammaDefinable B (T ⁻¹' P) := by
  have hg := graph_definable B Set.univ (GammaIntegerFamilies.univ_definable_base B m) T hT
  have hp := GammaRelationLogic.preimage_definable_base B _ hP (tailIndex n m)
  have h := GammaQuantifierLogic.image_definable_base B _
    (GammaRelationLogic.inter_definable_base B _ _ hg hp) (headIndex n m) (headIndex_injective n m)
  convert h using 1
  ext x
  constructor
  · intro hx
    have hh : join n m x (T x) ∘ tailIndex n m = T x := funext (join_tail n m x (T x))
    refine ⟨join n m x (T x), ⟨(graphOn_join Set.univ T x (T x)).mpr ⟨Set.mem_univ _, rfl⟩, ?_⟩,
      funext (join_head n m x (T x))⟩
    change join n m x (T x) ∘ tailIndex n m ∈ P
    rw [hh]
    exact hx
  · rintro ⟨w, ⟨⟨_, he⟩, hp⟩, hx⟩
    change T x ∈ P
    rw [← hx, he]
    exact hp

theorem compose_definable (B : Base (M := M)) {n m : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hT : ∀ i, MapDefinable B (fun z => T z i)) : MapDefinable B (fun z => f (T z)) := by
  let U : (Fin (m + 1) → Values.Gamma (M := M)) → (Fin (n + 1) → Values.Gamma (M := M)) :=
    fun z => Fin.cons (z 0) (T (Fin.tail z))
  have hU (i : Fin (n + 1)) : MapDefinable B (fun z => U z i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact projection_definable B 0
    · exact reindex_definable B _ (hT j) Fin.succ
  exact preimage_definable B _ hf U hU

end DiamondIntegral.Section4.GammaTupleMaps
