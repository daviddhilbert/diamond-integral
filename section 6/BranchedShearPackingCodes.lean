import «section 6».BranchedShearLabelPacking

/-! The common output packing has an original-base definable validity
predicate. Decoding is pure coordinate selection, so whole local graph
formulas can be pulled back without introducing any new parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}

theorem rawRVOne_constant_definable {ι : Type} : S.DefinableFun LRV (fun _ : ι → M => iRVOne) :=
  (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvOne)).comp
    (show S.DefinableMap LRV (fun _ : ι → M => (Fin.elim0 : Fin 0 → M)) from fun i => i.elim0)

def packedBranchLocalIndex (r : ℕ) (arity : Fin k → ℕ) (i : Fin k) :
    Fin (r+arity i) → Fin (r+packedBranchArity r arity) :=
  Fin.addCases (Fin.castAdd (packedBranchArity r arity)) (fun j => Fin.natAdd r (packedBranchSlot r arity i j))

theorem packedBranchLocalIndex_at (arity : Fin k → ℕ) (i : Fin k)
    (w : Fin (r+packedBranchArity r arity) → RVInfinity M) :
    w ∘ packedBranchLocalIndex r arity i=
      Fin.append (w ∘ Fin.castAdd (packedBranchArity r arity)) (packedBranchDecode arity i (w ∘ Fin.natAdd r)) := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
    simp only [Function.comp_apply,packedBranchLocalIndex,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right,packedBranchDecode]

def packedBranchEncodeCode (r : ℕ) (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (z : Fin (r+arity i) → M) : Fin (packedBranchArity r arity) → M := fun j =>
  match (packedBranchEquiv r arity).symm j with
  | .inl l => z (Fin.castAdd (arity i) l)
  | .inr (.inl _) => z (Fin.natAdd r (leading i))
  | .inr (.inr ⟨b,l⟩) => if h : b=i then z (Fin.natAdd r (Fin.cast (congrArg arity h) l)) else iRVOne

theorem packedBranchEncodeCode_definable (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k) :
    S.DefinableMap LRV (packedBranchEncodeCode (M := M) r arity leading i) := by
  intro j
  unfold packedBranchEncodeCode
  split
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · split
    · exact Set.DefinableFun.proj LRV
    · exact rawRVOne_constant_definable

theorem packedBranchEncodeCode_at (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M) :
    packedBranchEncodeCode r arity leading i (rvValues (Fin.append u v))=
      rvValues (packedBranchEncode arity leading i u v) := by
  funext j
  rcases he : (packedBranchEquiv r arity).symm j with l | (l | ⟨b,l⟩)
  · simp only [packedBranchEncodeCode,packedBranchEncode,rvValues,he,Fin.append_left]
  · simp only [packedBranchEncodeCode,packedBranchEncode,rvValues,he,Fin.append_right]
  · by_cases h : b=i
    · simp [packedBranchEncodeCode,packedBranchEncode,rvValues,he,h]
    · simp [packedBranchEncodeCode,packedBranchEncode,rvValues,he,h,RVOperations.one_val]

def packedBranchValidCode (r : ℕ) (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k) :
    Set (Fin (r+packedBranchArity r arity) → M) :=
  {z | ∀ j,z (Fin.natAdd r j)=packedBranchEncodeCode r arity leading i (z ∘ packedBranchLocalIndex r arity i) j}

theorem packedBranchValidCode_definable (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k) :
    S.Definable LRV (packedBranchValidCode (M := M) r arity leading i) := by
  have hEncode : S.DefinableMap LRV (fun z : Fin (r+packedBranchArity r arity) → M =>
      packedBranchEncodeCode r arity leading i (z ∘ packedBranchLocalIndex r arity i)) := by
    intro j
    exact (packedBranchEncodeCode_definable arity leading i j).comp (fun _ => Set.DefinableFun.proj LRV)
  have hEach (j) : S.Definable LRV {z : Fin (r+packedBranchArity r arity) → M |
      z (Fin.natAdd r j)=packedBranchEncodeCode r arity leading i (z ∘ packedBranchLocalIndex r arity i) j} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (hEncode j)
  convert Set.definable_iInter_of_finite hEach using 1
  ext z
  simp only [packedBranchValidCode,Set.mem_setOf_eq,Set.mem_iInter]

theorem packedBranchValidCode_at (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (w : Fin (r+packedBranchArity r arity) → RVInfinity M) :
    rvValues w ∈ packedBranchValidCode r arity leading i ↔
      w ∘ Fin.natAdd r=packedBranchEncode arity leading i
        (w ∘ Fin.castAdd (packedBranchArity r arity)) (packedBranchDecode arity i (w ∘ Fin.natAdd r)) := by
  have hCode : rvValues w ∘ packedBranchLocalIndex r arity i=
      rvValues (Fin.append (w ∘ Fin.castAdd (packedBranchArity r arity))
        (packedBranchDecode arity i (w ∘ Fin.natAdd r))) := by
    rw [← packedBranchLocalIndex_at arity i w]
    rfl
  change (∀ j,(w (Fin.natAdd r j)).val=_ ) ↔ _
  rw [hCode,packedBranchEncodeCode_at]
  constructor
  · intro h
    funext j
    exact Subtype.ext (h j)
  · intro h j
    exact congrArg Subtype.val (congrFun h j)

end DiamondIntegral.Section6
