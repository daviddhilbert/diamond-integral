import «section 6».InteralgebraicTuplePivots

/-! Algebraic closure under coordinate permutations and adjoining one
retained RV coordinate. These identities allow induction on the actual
number of changing coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev rvTupleClosure (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n : ℕ} (a : Fin n → RVInfinity M) :=
  (rvAlgebraicMatroid hc hex S).closure (Set.range a)

theorem rvTupleClosure_reindex (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n : ℕ}
    (a : Fin n → RVInfinity M) (e : Equiv.Perm (Fin n)) :
    rvTupleClosure hc hex S (a ∘ e) = rvTupleClosure hc hex S a := by
  apply congrArg (rvAlgebraicMatroid hc hex S).closure
  apply Set.ext
  intro x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨e i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨e.symm i,congrArg a (e.apply_symm_apply i)⟩

theorem rvTupleClosure_snoc (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n : ℕ}
    (a : Fin n → RVInfinity M) (c : RVInfinity M) :
    rvTupleClosure hc hex S (Fin.snoc a c) = rvTupleClosure hc hex (insert c.val S) a := by
  rw [rvTupleClosure,rvTupleClosure,rvAlgebraicMatroid_closure,rvAlgebraicMatroid_closure]
  ext x
  change AlgebraicAt (S ∪ rvParameterNames (Set.range (Fin.snoc a c))) .rv x.val ↔
    AlgebraicAt (insert c.val S ∪ rvParameterNames (Set.range a)) .rv x.val
  rw [rvParameterNames_range,rvParameterNames_range]
  have hValues : rvValues (Fin.snoc a c) = Fin.snoc (rvValues a) c.val := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [rvValues,Fin.snoc_last]
    · simp only [rvValues,Fin.snoc_castSucc]
  rw [hValues,Fin.range_snoc,Set.union_insert,Set.insert_union]

def finPermFixLast {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (e i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (e.symm i).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc,e.symm_apply_apply]
  right_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc,e.apply_symm_apply]

theorem snoc_comp_finPermFixLast {E : Type*} {n : ℕ} (a : Fin n → E) (c : E)
    (e : Equiv.Perm (Fin n)) : Fin.snoc a c ∘ finPermFixLast e = Fin.snoc (a ∘ e) c := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply,finPermFixLast,Equiv.coe_fn_mk,Fin.lastCases_last,Fin.snoc_last]
  · simp only [Function.comp_apply,finPermFixLast,Equiv.coe_fn_mk,Fin.lastCases_castSucc,Fin.snoc_castSucc]

theorem comp_snoc {E F : Type*} {n : ℕ} (f : E → F) (a : Fin n → E) (c : E) :
    f ∘ Fin.snoc a c = Fin.snoc (f ∘ a) (f c) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Function.comp_apply,Fin.snoc_last,Fin.snoc_castSucc]

end DiamondIntegral.Section6
