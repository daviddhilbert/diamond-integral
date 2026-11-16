import «section 6».BinaryCorePreparation

/-! The full original-base graph of a fixed-radius focus congruence
relation. Both VF blocks and their shared RV labels are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}

def mixedPairIndex (n r : ℕ) (block : Fin n → Fin (n+n)) :
    Fin n ⊕ Fin r → Fin (n+n) ⊕ Fin r := Sum.map block id

theorem mixedValues_mem_preimage_iff (C : DefSet (rawMixedSpace (M := M) n r) S)
    (p : Mixed M n r) : mixedValues p ∈ (rawMixedSpace n r).preimage C.carrier ↔ p ∈ C.carrier := by
  exact ⟨fun ⟨_,h⟩ => by simpa only [decode_mixedValues] using h,
    fun h => ⟨mixedValues_mem_domain p,by simpa only [decode_mixedValues] using h⟩⟩

def focusCongruenceRelation (f : Map A B) (γ : Gamma M) : Set (Mixed M (n+n) r) :=
  {p | firstVFBlock p ∈ A.carrier ∧ secondVFBlock p ∈ A.carrier ∧
    Congruent (fun _ : Fin 1 => γ) (totalFocusFibre f p.2 (firstVFBlock p).1)
      (totalFocusFibre f p.2 (secondVFBlock p).1)}

theorem focusCongruenceRelation_definable (f : Map A B) (γ : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    (rawMixedSpace (M := M) (n+n) r).Definable S (focusCongruenceRelation f γ) := by
  let first := mixedPairIndex n r (Fin.castAdd n)
  let second := mixedPairIndex n r (Fin.natAdd n)
  let outputs (z : Fin (n+n) ⊕ Fin r → M) : Fin 1 ⊕ Fin 1 → M :=
    Sum.elim (fun _ => scalarCodeExtension f (z ∘ first))
      (fun _ => scalarCodeExtension f (z ∘ second))
  have hFirst : S.DefinableFun LRV (fun z : Fin (n+n) ⊕ Fin r → M => scalarCodeExtension f (z ∘ first)) :=
    (scalarCodeExtension_definable f).comp (fun _ => Set.DefinableFun.proj LRV)
  have hSecond : S.DefinableFun LRV (fun z : Fin (n+n) ⊕ Fin r → M => scalarCodeExtension f (z ∘ second)) :=
    (scalarCodeExtension_definable f).comp (fun _ => Set.DefinableFun.proj LRV)
  have hOutputs : S.DefinableMap LRV outputs := by
    rintro (i | i)
    · exact hFirst
    · exact hSecond
  have hCong := (named_scalar_congruence_definable (m := 1) γ hγ).preimage_map hOutputs
  have h := (A.definable.preimage_comp first).inter ((A.definable.preimage_comp second).inter hCong)
  convert mixedValues_preimage_definable _ h using 1
  ext p
  have h₁ : mixedValues p ∘ first = mixedValues (firstVFBlock p) := by funext i; cases i <;> rfl
  have h₂ : mixedValues p ∘ second = mixedValues (secondVFBlock p) := by funext i; cases i <;> rfl
  have hOut : outputs (mixedValues p) = Sum.elim
      (vfValues (totalFocusFibre f p.2 (firstVFBlock p).1))
      (vfValues (totalFocusFibre f p.2 (secondVFBlock p).1)) := by
    funext i
    cases i <;> simp only [outputs,h₁,h₂,Sum.elim_inl,Sum.elim_inr] <;> rfl
  change (firstVFBlock p ∈ A.carrier ∧ secondVFBlock p ∈ A.carrier ∧ _) ↔
    (mixedValues p ∘ first ∈ (rawMixedSpace n r).preimage A.carrier ∧
      mixedValues p ∘ second ∈ (rawMixedSpace n r).preimage A.carrier ∧
      outputs (mixedValues p) ∈ rawVFRelation (Congruent (fun _ : Fin 1 => γ)))
  rw [h₁,h₂,hOut,mixedValues_mem_preimage_iff,mixedValues_mem_preimage_iff,rawVFRelation_at]

end DiamondIntegral.Section6
