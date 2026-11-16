import «section 6».UnaryRVJacobianLifting

/-! Actual definable coordinate selection and VF tuple assembly. These
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

def rvTupleSelectMap (S : Set M) {n m : ℕ} (σ : Fin m → Fin n) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (rawRVSpace (M := M) m) S) := by
  let P := rawRVSpace (M := M) n
  let Q := rawRVSpace (M := M) m
  let F (z : Fin n → M) : Fin m → M := z ∘ σ
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    refine ⟨P.decode c ∘ σ,?_⟩
    exact congrArg (fun z => z ∘ σ) (rvValues_decode c)
  refine Map.ofCodes (DefSet.univ P S) (fun t => t ∘ σ) F
    (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode ⟨F c.val,hdom c⟩).trans
    (congrArg (fun z => z ∘ σ) (rvValues_decode c)).symm

def vfTupleSelectMap (S : Set M) {n m : ℕ} (σ : Fin m → Fin n) :
    Map (DefSet.univ (rawVFSpace (M := M) n) S) (DefSet.univ (rawVFSpace (M := M) m) S) := by
  let P := rawVFSpace (M := M) n
  let Q := rawVFSpace (M := M) m
  let F (z : Fin n → M) : Fin m → M := z ∘ σ
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    refine ⟨P.decode c ∘ σ,?_⟩
    exact congrArg (fun z => z ∘ σ) (vfValues_decode c)
  refine Map.ofCodes (DefSet.univ P S) (fun t => t ∘ σ) F
    (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply vfValues_injective
  exact (vfValues_decode ⟨F c.val,hdom c⟩).trans
    (congrArg (fun z => z ∘ σ) (vfValues_decode c)).symm

def vfTupleConsMap (S : Set M) (n : ℕ) :
    Map ((DefSet.univ (rawVFSpace (M := M) 1) S).prod (DefSet.univ (rawVFSpace (M := M) n) S))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) S) := by
  let P := (rawVFSpace (M := M) 1).prod (rawVFSpace n)
  let Q := rawVFSpace (M := M) (n+1)
  let σ : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.cases (.inl 0) (fun i => .inr i)
  let F (z : Fin 1 ⊕ Fin n → M) : Fin (n+1) → M := z ∘ σ
  let f (p : P.Carrier) : Fin (n+1) → VF M := Fin.cons (p.1 (0 : Fin 1)) p.2
  have hcode (c : P.domain) : vfValues (f (P.decode c)) = F c.val := by
    have ha := vfValues_decode (⟨c.val ∘ Sum.inl,c.property.1⟩ : (rawVFSpace (M := M) 1).domain)
    have hb := vfValues_decode (⟨c.val ∘ Sum.inr,c.property.2⟩ : (rawVFSpace (M := M) n).domain)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun ha (0 : Fin 1)
    · exact congrFun hb j
  have hdom (c : P.domain) : F c.val ∈ Q.domain := ⟨f (P.decode c),hcode c⟩
  refine (Map.ofCodes (DefSet.univ P S) f F (fun _ => Set.DefinableFun.proj LRV) hdom ?_).restrict
    (fun _ _ => Set.mem_univ _)
  intro c
  exact vfValues_injective ((vfValues_decode ⟨F c.val,hdom c⟩).trans (hcode c).symm)

def vfTupleAssembleMap {P : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    (A : DefSet P S) : (n : ℕ) → (Fin n → Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) →
      Map A (DefSet.univ (rawVFSpace (M := M) n) S)
  | 0,_ => Map.ofCodes A (fun _ => Fin.elim0) (fun _ => Fin.elim0)
      (fun i => i.elim0) (fun _ => ⟨Fin.elim0,Subsingleton.elim _ _⟩)
      (fun _ => funext (fun i => i.elim0))
  | n+1,F => (vfTupleConsMap S n).comp ((F 0).pair (vfTupleAssembleMap A n (fun i => F i.succ)))

theorem vfTupleAssembleMap_value {P : SpecialTransformations.DefinableGeometry.Space LRV M} {S : Set M}
    (A : DefSet P S) (n : ℕ) (F : Fin n → Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (a : A) :
    (vfTupleAssembleMap A n F a).val = fun i => (F i a).val 0 := by
  induction n with
  | zero => exact funext (fun i => i.elim0)
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun j => F j.succ)) j

end DiamondIntegral.Section6
