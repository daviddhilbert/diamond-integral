import «section 6».SpecialGammaTransport

/-! All proper RV codes of a Gamma form as one actual mixed definable
set. The code is an additional retained RV coordinate, not a selected
representative or a newly named parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def gammaCodeLocus (A : DefSet (rawMixedSpace (M := M) n r) S) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    DefSet (rawMixedSpace (M := M) n (r+1)) S := by
  let C : Set (Mixed M n (r+1)) := {p | (p.1,Fin.tail p.2) ∈ A.carrier ∧
    GammaParameters.NonzeroRV (p.2 0).val ∧
    GammaParameters.codeValue (p.2 0).val = ω (p.1,Fin.tail p.2)}
  let idx : (Fin n ⊕ Fin r) ⊕ Fin 1 → Fin n ⊕ Fin (r+1) :=
    Sum.elim (Sum.elim Sum.inl (fun j => .inr j.succ)) (fun _ => .inr 0)
  refine ⟨C,?_⟩
  apply (mixed_definable_iff_values_image S C).mpr
  convert (sumMixedGammaGraph_definable A.carrier ω hω).preimage_comp idx using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hNZ,hΓ⟩,rfl⟩
    refine ⟨hNZ,(p.1,Fin.tail p.2),hp,?_,hΓ⟩
    funext i
    cases i <;> rfl
  · rintro ⟨hNZ,a,ha,hac,hΓ⟩
    let t : RVInfinity M := ⟨z (.inr 0),hNZ.1⟩
    let p : Mixed M n (r+1) := (a.1,Fin.cons t a.2)
    have hp : p ∈ C := by
      dsimp only [p,C]
      simpa only [Set.mem_setOf_eq,Fin.tail_cons,Fin.cons_zero] using (show a ∈ A.carrier ∧
        GammaParameters.NonzeroRV t.val ∧ GammaParameters.codeValue t.val = ω a from ⟨ha,hNZ,hΓ⟩)
    refine ⟨p,hp,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun hac (.inl i)
    | inr i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun hac (.inr j)

theorem gammaCodeLocus_at (A : DefSet (rawMixedSpace (M := M) n r) S) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A.carrier ω)) (x : Fin n → VF M)
    (u : Fin r → RVInfinity M) (t : RVInfinity M) :
    (x,Fin.cons t u) ∈ (gammaCodeLocus A ω hω).carrier ↔ (x,u) ∈ A.carrier ∧
      GammaParameters.NonzeroRV t.val ∧ GammaParameters.codeValue t.val = ω (x,u) := by
  let w : Fin (r+1) → RVInfinity M := Fin.cons t u
  change ((x,Fin.tail w) ∈ A.carrier ∧ GammaParameters.NonzeroRV (w 0).val ∧
    GammaParameters.codeValue (w 0).val = ω (x,Fin.tail w)) ↔ _
  simp only [w,Fin.tail_cons,Fin.cons_zero]

end DiamondIntegral.Section6
