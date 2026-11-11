import «section 2».DiscTupleLogic

/-!
# Existential quantification with actual disc parameters

Projecting real output coordinates keeps every disc-name coordinate. The
full relation remains invariant under all centre/radius presentations.
This supplies quantifiers for the atomic-disc induction without naming
centres as ground parameters.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private def discProjectionIndex (n : ℕ) {m l : ℕ} (π : Fin l → Fin m) :
    Fin (n+l) → Fin (n+m) :=
  Fin.addCases (Fin.castAdd m) (fun j => Fin.natAdd n (π j))

private def projectedDiscRealRelation {S : Set M} {k n m l : ℕ}
    {sn : Fin m → SortTag}
    (Q : GammaParameters.Relation S k (n+m) (Fin.append (fun _ : Fin n => .vf) sn))
    (π : Fin l → Fin m) :
    GammaParameters.Relation S k (n+l) (Fin.append (fun _ : Fin n => .vf) (sn ∘ π)) where
  carrier := (Q.imageReal (discProjectionIndex n π)).carrier
  definable := (Q.imageReal (discProjectionIndex n π)).definable
  proper := by
    intro p hp
    obtain ⟨ht, hs⟩ := (Q.imageReal (discProjectionIndex n π)).proper p hp
    refine ⟨ht, fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Function.comp_apply, discProjectionIndex, Fin.addCases_left,
        Fin.append_left] using hs (Fin.castAdd l j)
    · simpa only [Function.comp_apply, discProjectionIndex, Fin.addCases_right,
        Fin.append_right] using hs (Fin.natAdd n j)
  invariant := (Q.imageReal (discProjectionIndex n π)).invariant

private theorem projectedDiscRealRelation_mem {S : Set M} {k n m l : ℕ}
    {sn : Fin m → SortTag}
    (Q : GammaParameters.Relation S k (n+m) (Fin.append (fun _ : Fin n => .vf) sn))
    (π : Fin l → Fin m) (γ : Fin k → Gamma M) (a : Fin n → VF M) (x : Fin l → M) :
    Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
        (projectedDiscRealRelation Q π).fibre γ ↔
      ∃ y : Fin m → M, Fin.append (SpecialTransformations.Section4.vfValues a) y ∈
        Q.fibre γ ∧ y ∘ π = x := by
  change (∃ w : Fin (n+m) → M, w ∈ Q.fibre γ ∧
      w ∘ discProjectionIndex n π = Fin.append (SpecialTransformations.Section4.vfValues a) x) ↔ _
  constructor
  · rintro ⟨w, hw, he⟩
    let y := w ∘ Fin.natAdd n
    have hwe : Fin.append (SpecialTransformations.Section4.vfValues a) y = w := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have hj := congrFun he (Fin.castAdd l j)
        simpa only [Function.comp_apply, discProjectionIndex, Fin.addCases_left,
          Fin.append_left] using hj.symm
      · simp only [Fin.append_right, y, Function.comp_apply]
    refine ⟨y, hwe.symm ▸ hw, ?_⟩
    funext j
    have hj := congrFun he (Fin.natAdd n j)
    simpa only [y, Function.comp_apply, discProjectionIndex, Fin.addCases_right,
      Fin.append_right] using hj
  · rintro ⟨y, hy, he⟩
    refine ⟨Fin.append (SpecialTransformations.Section4.vfValues a) y, hy, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply, discProjectionIndex, Fin.addCases_left, Fin.append_left]
    · simpa only [Function.comp_apply, discProjectionIndex, Fin.addCases_right,
        Fin.append_right] using congrFun he j

/-- Quantify real outputs, leaving the entire actual disc tuple unchanged. -/
def FiniteDiscTupleRelation.imageReal {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (π : Fin l → Fin m) :
    FiniteDiscTupleRelation B closed (sn ∘ π) where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := projectedDiscRealRelation R.relation π
  invariant := by
    intro a a' δ δ' he x
    rw [projectedDiscRealRelation_mem, projectedDiscRealRelation_mem]
    exact exists_congr (fun y => and_congr (R.invariant a a' δ δ' he y) Iff.rfl)

theorem FiniteDiscTupleRelation.imageReal_fibre {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (π : Fin l → Fin m)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    (R.imageReal π).fibre a δ = (fun y => y ∘ π) '' R.fibre a δ := by
  ext x
  exact projectedDiscRealRelation_mem R.relation π _ a x

theorem DefinableOverFiniteDiscNames.image_real {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A) (π : Fin l → Fin m) :
    DefinableOverFiniteDiscNames B closed a δ (sn ∘ π) ((fun y => y ∘ π) '' A) := by
  obtain ⟨R, rfl⟩ := hA
  exact ⟨R.imageReal π, R.imageReal_fibre π a δ⟩

end DiamondIntegral.Section2
