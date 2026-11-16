import «section 6».UncurriedMixedTemplates
import «section 6».ScalarCodeExtension

/-! Reassemble a mixed family whose parameter is an actual definable
function on a unary mixed base. The old parameter may depend on the
retained RV labels after unary preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

def unaryFamilyBasePoint (p : Mixed M (n+1) (r+s)) : Mixed M 1 r :=
  (fun _ => p.1 0,p.2 ∘ Fin.castAdd s)

def unaryFamilyBaseCodes (z : Fin (n+1) ⊕ Fin (r+s) → M) : Fin 1 ⊕ Fin r → M :=
  Sum.elim (fun _ => z (.inl 0)) (fun i => z (.inr (Fin.castAdd s i)))

theorem unaryFamilyBaseCodes_definable :
    S.DefinableMap LRV (unaryFamilyBaseCodes (M := M) (n := n) (r := r) (s := s)) := by
  rintro (i | i) <;> exact Set.DefinableFun.proj LRV

theorem unaryFamilyBasePoint_values (p : Mixed M (n+1) (r+s)) :
    mixedValues (unaryFamilyBasePoint p)=unaryFamilyBaseCodes (mixedValues p) := by
  funext i
  cases i <;> rfl

def unaryFamilyBaseMap (S : Set M) (n r s : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S)
      (DefSet.univ (rawMixedSpace (M := M) 1 r) S) := by
  let P := rawMixedSpace (M := M) (n+1) (r+s)
  let Q := rawMixedSpace (M := M) 1 r
  have hCode (c : P.domain) : mixedValues (unaryFamilyBasePoint (P.decode c))=
      unaryFamilyBaseCodes c.val := by
    rw [unaryFamilyBasePoint_values,mixedValues_decode]
  have hDom (c : P.domain) : unaryFamilyBaseCodes c.val ∈ Q.domain := by
    rw [← hCode c]
    exact mixedValues_mem_domain _
  exact Map.ofCodes _ unaryFamilyBasePoint unaryFamilyBaseCodes unaryFamilyBaseCodes_definable hDom
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (hCode c).symm))

def unaryFamilyParameterPoint {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Mixed M (n+1) (r+s)) :
    Mixed M (n+1) s :=
  (Fin.cons ⟨scalarCodeExtension η (mixedValues (unaryFamilyBasePoint p)),
    scalarCodeExtension_isVF η _⟩ (Fin.tail p.1),p.2 ∘ Fin.natAdd r)

def unaryFamilyParameterCodes {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (z : Fin (n+1) ⊕ Fin (r+s) → M) : Fin (n+1) ⊕ Fin s → M :=
  Sum.elim (Fin.cons (scalarCodeExtension η (unaryFamilyBaseCodes z)) (fun i => z (.inl i.succ)))
    (fun i => z (.inr (Fin.natAdd r i)))

theorem unaryFamilyParameterCodes_definable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    S.DefinableMap LRV (unaryFamilyParameterCodes (n := n) (s := s) η) := by
  rintro (i | i)
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact (scalarCodeExtension_definable η).comp unaryFamilyBaseCodes_definable
    · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV

theorem unaryFamilyParameterPoint_values {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Mixed M (n+1) (r+s)) :
    mixedValues (unaryFamilyParameterPoint η p)=unaryFamilyParameterCodes η (mixedValues p) := by
  funext i
  rcases i with i | i
  · refine Fin.cases ?_ (fun j => ?_) i
    · change scalarCodeExtension η (mixedValues (unaryFamilyBasePoint p))=_
      rw [unaryFamilyBasePoint_values]
      rfl
    · rfl
  · rfl

def unaryFamilyParameterMap {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (n s : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S)
      (DefSet.univ (rawMixedSpace (M := M) (n+1) s) S) := by
  let P := rawMixedSpace (M := M) (n+1) (r+s)
  let Q := rawMixedSpace (M := M) (n+1) s
  have hCode (c : P.domain) : mixedValues (unaryFamilyParameterPoint η (P.decode c))=
      unaryFamilyParameterCodes η c.val := by
    rw [unaryFamilyParameterPoint_values,mixedValues_decode]
  have hDom (c : P.domain) : unaryFamilyParameterCodes η c.val ∈ Q.domain := by
    rw [← hCode c]
    exact mixedValues_mem_domain _
  exact Map.ofCodes _ (unaryFamilyParameterPoint η) (unaryFamilyParameterCodes η)
    (unaryFamilyParameterCodes_definable η) hDom
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (hCode c).symm))

theorem unaryFamilyParameterPoint_at {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Mixed M (n+1) (r+s))
    (b : B) (hb : unaryFamilyBasePoint p=b.val) :
    unaryFamilyParameterPoint η p=(Fin.cons ((η b).val 0) (Fin.tail p.1),p.2 ∘ Fin.natAdd r) := by
  have hValue : (⟨scalarCodeExtension η (mixedValues (unaryFamilyBasePoint p)),
      scalarCodeExtension_isVF η _⟩ : VF M)=(η b).val 0 := by
    apply Subtype.ext
    rw [hb]
    exact scalarCodeExtension_at η b
  exact congrArg (fun x : VF M => (Fin.cons x (Fin.tail p.1),p.2 ∘ Fin.natAdd r)) hValue

end DiamondIntegral.Section6
