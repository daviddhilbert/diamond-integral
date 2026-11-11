import «section 2».ProductClosedGraph
import «section 2».DefinableVFInverse

/-! The two affine presentations of the fibre graph in Proposition 2.55.
The target chart coordinate is first in the tail tuple, followed by the
original tail input. The reciprocal chart excludes its zero coordinate
before closure, since the original map has finite VF output. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def affineFibreGraph (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (a : Fin 1 → VF M) : Set (Fin (n+1) → VF M) :=
  {z | (a,Fin.tail z) ∈ A ∧ (fun _ : Fin 1 => z 0) = f (a,Fin.tail z)}

def reciprocalFibreGraph (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (a : Fin 1 → VF M) : Set (Fin (n+1) → VF M) :=
  {z | (a,Fin.tail z) ∈ A ∧ z 0 ≠ 0 ∧ (fun _ : Fin 1 => (z 0)⁻¹) = f (a,Fin.tail z)}

theorem affineFibreGraph_definable {S : Set M}
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hAI : A ⊆ I ×ˢ Set.univ)
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f)) :
    S.Definable LRV (vfCorrespondenceGraph I (affineFibreGraph A f)) := by
  let π : (Fin 1 ⊕ Fin n) ⊕ Fin 1 → Fin 1 ⊕ Fin (n+1) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Fin.succ)) (fun _ => .inr 0)
  have h := hf.preimage_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,y,⟨hy,hfy⟩,rfl⟩
    refine ⟨(a,Fin.tail y),hy,?_⟩
    rw [← hfy]
    funext i
    cases i with
    | inl i => cases i <;> rfl
    | inr i => rfl
  · rintro ⟨p,hp,he⟩
    let y : Fin (n+1) → VF M := Fin.cons (f p 0) p.2
    refine ⟨p.1,(hAI hp).1,y,⟨hp,?_⟩,?_⟩
    · funext i
      fin_cases i
      rfl
    · funext i
      cases i with
      | inl i => exact congrFun he (.inl (.inl i))
      | inr i =>
        refine Fin.cases (congrFun he (.inr 0)) (fun j => congrFun he (.inl (.inr j))) i

theorem reciprocalFibreGraph_definable {S : Set M}
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hAI : A ⊆ I ×ˢ Set.univ)
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f)) :
    S.Definable LRV (vfCorrespondenceGraph I (reciprocalFibreGraph A f)) := by
  let τ (z : Fin 1 ⊕ Fin (n+1) → M) : (Fin 1 ⊕ Fin n) ⊕ Fin 1 → M :=
    Sum.elim (Sum.elim (z ∘ Sum.inl) (fun i => z (.inr i.succ)))
      (fun _ => rawVFInverse (z (.inr 0)))
  have hτ : S.DefinableMap LRV τ := by
    rintro ((i | i) | i)
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
    · exact rawVFInverse_definable S (Sum.inr 0 : Fin 1 ⊕ Fin (n+1))
  have hvf := ((definableAt_sort S .vf).raw_definable).preimage_comp
    (fun _ : Fin 1 => (Sum.inr 0 : Fin 1 ⊕ Fin (n+1)))
  have hz : S.DefinableFun LRV (fun _ : Fin 1 ⊕ Fin (n+1) → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hne := ((Set.DefinableFun.proj LRV (i := (Sum.inr 0 : Fin 1 ⊕ Fin (n+1)))).ofPred_eq hz).compl
  have h := (hf.preimage_map hτ).inter (hvf.inter hne)
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,y,⟨hy,hy0,hfy⟩,rfl⟩
    refine ⟨⟨(a,Fin.tail y),hy,?_⟩,(y 0).property,fun he => hy0 (Subtype.ext he)⟩
    rw [← hfy]
    funext i
    cases i with
    | inl i => cases i <;> rfl
    | inr i => exact (rawVFInverse_vf (y 0)).symm
  · rintro ⟨⟨p,hp,he⟩,hyVF,hyNZ⟩
    let b : VF M := ⟨z (.inr 0),hyVF⟩
    have hb0 : b ≠ 0 := fun h => hyNZ (congrArg Subtype.val h)
    let y : Fin (n+1) → VF M := Fin.cons b p.2
    have hfy : (fun _ : Fin 1 => b⁻¹) = f p := by
      funext i
      apply Subtype.ext
      exact (rawVFInverse_vf b).symm.trans (congrFun he (.inr i)).symm
    refine ⟨p.1,(hAI hp).1,y,⟨hp,hb0,hfy⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he (.inl (.inl i))
    | inr i =>
      refine Fin.cases rfl (fun j => congrFun he (.inl (.inr j))) i

end DiamondIntegral.Section2
