import «section 6».FiniteRVJacobianLifts

/-! Actual definable RV tuple assembly. These
maps operate on full real-code graphs and preserve the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvTupleConsMap (S : Set M) (n : ℕ) :
    Map ((DefSet.univ (rawRVSpace (M := M) 1) S).prod (DefSet.univ (rawRVSpace (M := M) n) S))
      (DefSet.univ (rawRVSpace (M := M) (n+1)) S) := by
  let P := (rawRVSpace (M := M) 1).prod (rawRVSpace n)
  let Q := rawRVSpace (M := M) (n+1)
  let σ : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.cases (.inl 0) (fun i => .inr i)
  let F (z : Fin 1 ⊕ Fin n → M) : Fin (n+1) → M := z ∘ σ
  let f (p : P.Carrier) : Fin (n+1) → RVInfinity M := Fin.cons (p.1 (0 : Fin 1)) p.2
  have hcode (c : P.domain) : rvValues (f (P.decode c)) = F c.val := by
    have ha := rvValues_decode (⟨c.val ∘ Sum.inl,c.property.1⟩ : (rawRVSpace (M := M) 1).domain)
    have hb := rvValues_decode (⟨c.val ∘ Sum.inr,c.property.2⟩ : (rawRVSpace (M := M) n).domain)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun ha (0 : Fin 1)
    · exact congrFun hb j
  have hdom (c : P.domain) : F c.val ∈ Q.domain := ⟨f (P.decode c),hcode c⟩
  refine (Map.ofCodes (DefSet.univ P S) f F (fun _ => Set.DefinableFun.proj LRV) hdom ?_).restrict
    (fun _ _ => Set.mem_univ _)
  intro c
  exact rvValues_injective ((rvValues_decode ⟨F c.val,hdom c⟩).trans (hcode c).symm)

def rvTupleAssembleMap {P : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    (A : DefSet P S) : (n : ℕ) → (Fin n → Map A (DefSet.univ (rawRVSpace (M := M) 1) S)) →
      Map A (DefSet.univ (rawRVSpace (M := M) n) S)
  | 0,_ => Map.ofCodes A (fun _ => Fin.elim0) (fun _ => Fin.elim0)
      (fun i => i.elim0) (fun _ => ⟨Fin.elim0,Subsingleton.elim _ _⟩)
      (fun _ => funext (fun i => i.elim0))
  | n+1,F => (rvTupleConsMap S n).comp ((F 0).pair (rvTupleAssembleMap A n (fun i => F i.succ)))

theorem rvTupleAssembleMap_value {P : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    (A : DefSet P S) (n : ℕ) (F : Fin n → Map A (DefSet.univ (rawRVSpace (M := M) 1) S)) (a : A) :
    (rvTupleAssembleMap A n F a).val = fun i => (F i a).val 0 := by
  induction n with
  | zero => exact funext (fun i => i.elim0)
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun j => F j.succ)) j


end DiamondIntegral.Section6
