import «section 6».CoordinateFibreTemplates

/-! Reassemble a complete parameter family as an actual mixed domain
with the VF parameter retained as its first coordinate. Taking coordinate
fibres recovers exactly the original specialized family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def uncurryMixedCodeIndex : Fin 1 ⊕ (Fin n ⊕ Fin r) → Fin (n+1) ⊕ Fin r :=
  Sum.elim (fun _ => .inl 0) (Sum.elim (fun i => .inl i.succ) Sum.inr)

theorem uncurryMixedCodes_at (x : Mixed M (n+1) r) :
    mixedValues x ∘ uncurryMixedCodeIndex=
      Sum.elim (fun _ : Fin 1 => (x.1 0).val) (mixedValues (Fin.tail x.1,x.2)) := by
  funext i
  rcases i with i | (i | i) <;> rfl

def MixedSetParameterTemplate.uncurry (T : MixedSetParameterTemplate (M := M) S 1 n r) :
    DefSet (rawMixedSpace (M := M) (n+1) r) S := by
  let P := rawMixedSpace (M := M) (n+1) r
  refine ⟨{x | mixedValues x ∘ uncurryMixedCodeIndex ∈ T.graph},?_⟩
  change S.Definable LRV (P.preimage _)
  convert (P.definable_domain S).inter (T.definable.preimage_comp uncurryMixedCodeIndex) using 1
  ext z
  constructor
  · rintro ⟨hz,hzT⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∘ uncurryMixedCodeIndex ∈ T.graph at hzT
    rw [mixedValues_decode] at hzT
    exact ⟨hz,hzT⟩
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∘ uncurryMixedCodeIndex ∈ T.graph
    rw [mixedValues_decode]
    exact hzT

theorem MixedSetParameterTemplate.mem_uncurry_iff
    (T : MixedSetParameterTemplate (M := M) S 1 n r) (x : Mixed M (n+1) r) :
    x ∈ T.uncurry.carrier ↔
      (Fin.tail x.1,x.2) ∈ (T.fibre (fun _ => (x.1 0).val)).carrier := by
  change mixedValues x ∘ uncurryMixedCodeIndex ∈ T.graph ↔ _
  rw [uncurryMixedCodes_at]
  rfl

theorem MixedSetParameterTemplate.headFibre_uncurry
    (T : MixedSetParameterTemplate (M := M) S 1 n r) (a : VF M) :
    (headFibreTemplate T.uncurry).fibre (fun _ => a.val)=T.fibre (fun _ => a.val) := by
  apply defSet_eq_of_carrier_eq
  ext x
  rw [mem_headFibreTemplate_iff,T.mem_uncurry_iff]
  simp only [Fin.cons_zero,Fin.tail_cons]
  rfl

theorem uncurry_headFibreTemplate (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    (headFibreTemplate A).uncurry=A := by
  apply defSet_eq_of_carrier_eq
  ext x
  rw [MixedSetParameterTemplate.mem_uncurry_iff,mem_headFibreTemplate_iff]
  have h : Fin.cons (x.1 0) (Fin.tail x.1)=x.1 := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [h]
  rfl

end DiamondIntegral.Section6
