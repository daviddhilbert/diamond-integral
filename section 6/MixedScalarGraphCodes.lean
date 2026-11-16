import «section 6».UnaryGraphFibreDiscImages
import «section 6».PairedDiscImageGraphs

/-! Uniform scalar graph codes retaining both old RV tuples. This
complete original-base relation supplies the first-order predicate for
paired mixed cores while their centers and offsets vary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def unaryMixedScalarIndex (r s : ℕ) : ((Fin 1 ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin s)) → (Fin (r+s) ⊕ Fin 2) :=
  Sum.elim (Sum.elim (fun _ => .inr 0) (fun j => .inl (Fin.castAdd s j)))
    (Sum.elim (fun _ => .inr 1) (fun k => .inl (Fin.natAdd r k)))

def unaryMixedScalarGraph (f : Map A B) : Set (Fin (r+s) ⊕ Fin 2 → M) :=
  {z | z ∘ unaryMixedScalarIndex r s ∈ (rawMixedSpace (M := M) 1 r).relation (rawMixedSpace 1 s) f.graph}

theorem unaryMixedScalarGraph_definable (f : Map A B) : S.Definable LRV (unaryMixedScalarGraph f) :=
  f.graph_definable.preimage_comp (unaryMixedScalarIndex r s)

theorem unaryMixedScalarGraph_at (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (a b : VF M) :
    Sum.elim (rvValues (Fin.append u v)) ![a.val,b.val] ∈ unaryMixedScalarGraph f ↔
      ∃ p : A,p.val=((fun _ : Fin 1 => a),u) ∧ (f p).val=((fun _ : Fin 1 => b),v) := by
  let p : Mixed M 1 r := (fun _ => a,u)
  let q : Mixed M 1 s := (fun _ => b,v)
  have hShuffle : Sum.elim (rvValues (Fin.append u v)) ![a.val,b.val] ∘ unaryMixedScalarIndex r s=
      Sum.elim (mixedValues p) (mixedValues q) := by
    funext i
    rcases i with (i | j) | (i | k)
    · fin_cases i
      rfl
    · simp only [unaryMixedScalarIndex,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,
        rvValues,Fin.append_left,mixedValues,p]
    · fin_cases i
      rfl
    · simp only [unaryMixedScalarIndex,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,
        rvValues,Fin.append_right,mixedValues,q]
  change _ ∘ unaryMixedScalarIndex r s ∈ (rawMixedSpace (M := M) 1 r).relation (rawMixedSpace 1 s) f.graph ↔ _
  rw [hShuffle]
  have h := (rawMixedSpace (M := M) 1 r).relation_decode (rawMixedSpace (M := M) 1 s) f.graph
    ⟨mixedValues p,mixedValues_mem_domain p⟩ ⟨mixedValues q,mixedValues_mem_domain q⟩
  simpa only [decode_mixedValues,Map.graph] using h

end DiamondIntegral.Section6
