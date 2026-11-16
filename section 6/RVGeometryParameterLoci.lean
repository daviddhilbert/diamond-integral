import «section 6».GraphUniversalParameterLoci
import «section 6».ParameterRelationImages

/-! RV saturation of the final sets and the tagged-source condition
are first-order parameter tests on complete mixed-domain families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

def rawMixedRVEqual (n r : ℕ) : Set ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r) → M) :=
  {z | (∀ i : Fin n,iRv (z (.inl (.inl i)))=iRv (z (.inr (.inl i)))) ∧
    ∀ j : Fin r,z (.inl (.inr j))=z (.inr (.inr j))}

theorem rawMixedRVEqual_definable (S : Set M) (n r : ℕ) : S.Definable LRV (rawMixedRVEqual (M := M) n r) := by
  let Z := (Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r)
  have hVF (i : Fin n) : S.Definable LRV {z : Z → M | iRv (z (.inl (.inl i)))=iRv (z (.inr (.inl i)))} :=
    (rv_scalarCode_definable (Set.DefinableFun.proj LRV)).ofPred_eq
      (rv_scalarCode_definable (Set.DefinableFun.proj LRV))
  have hRV (j : Fin r) : S.Definable LRV {z : Z → M | z (.inl (.inr j))=z (.inr (.inr j))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  convert (Set.definable_iInter_of_finite hVF).inter (Set.definable_iInter_of_finite hRV) using 1
  ext z
  simp only [rawMixedRVEqual,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  rfl

theorem rawMixedRVEqual_at (p q : Mixed M n r) :
    Sum.elim (mixedValues p) (mixedValues q) ∈ rawMixedRVEqual n r ↔
      tupleRV M p.1=tupleRV M q.1 ∧ p.2=q.2 := by
  constructor
  · rintro ⟨hVF,hRV⟩
    exact ⟨funext (fun i => Subtype.ext (hVF i)),funext (fun j => Subtype.ext (hRV j))⟩
  · rintro ⟨hVF,hRV⟩
    exact ⟨fun i => congrArg Subtype.val (congrFun hVF i),fun j => congrArg (fun u => (u j).val) hRV⟩

def rvPullbackCodeCondition (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) :
    Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r)) → M) :=
  {z | (fun i => z (.inr (.inr i))) ∈ (rawMixedSpace (M := M) n r).domain →
    z ∘ Sum.inr ∈ rawMixedRVEqual n r →
      Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inr i))) ∈ R}

theorem rvPullbackCodeCondition_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvPullbackCodeCondition R) := by
  let Z := ι ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r))
  have hDom := ((rawMixedSpace (M := M) n r).definable_domain S).preimage_comp
    (fun i : Fin n ⊕ Fin r => (Sum.inr (Sum.inr i) : Z))
  have hEq := (rawMixedRVEqual_definable S n r).preimage_comp
    (Sum.inr : (Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r) → Z)
  have hCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inr i)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  convert hDom.compl.union (hEq.compl.union (hR.preimage_map hCode)) using 1
  ext z
  change (_ → _ → _) ↔ ¬ _ ∨ ¬ _ ∨ _
  exact ⟨fun h => by
    by_cases hd : (fun i => z (.inr (.inr i))) ∈ (rawMixedSpace (M := M) n r).domain
    · by_cases he : z ∘ Sum.inr ∈ rawMixedRVEqual n r
      · exact Or.inr (Or.inr (h hd he))
      · exact Or.inr (Or.inl he)
    · exact Or.inl hd,
    fun h hd he => by rcases h with h | h | h; exact False.elim (h hd); exact False.elim (h he); exact h⟩

def rvPullbackParameterLocus (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) : Set (ι → M) :=
  graphUniversalParameterLocus R (rvPullbackCodeCondition R)

theorem rvPullbackParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvPullbackParameterLocus R) :=
  graphUniversalParameterLocus_definable _ _ hR (rvPullbackCodeCondition_definable R hR)

end DiamondIntegral.Section6
