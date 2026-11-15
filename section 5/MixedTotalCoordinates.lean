import IntegrationSection6.GammaSortedTotalBijections

/-! Literal total-family coordinates can be grouped into their VF and RV
blocks by one explicit permutation. Both old RV parameter coordinates and
all fibre labels remain present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

def mixedTotalPermutationFun (p q n r : ℕ) : Fin ((p+q)+(n+r)) → Fin ((p+n)+(q+r)) :=
  Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd (q+r) (Fin.castAdd n i)) (fun i => Fin.natAdd (p+n) (Fin.castAdd r i)))
    (Fin.addCases (fun i => Fin.castAdd (q+r) (Fin.natAdd p i)) (fun i => Fin.natAdd (p+n) (Fin.natAdd q i)))

theorem mixedTotalPermutationFun_left_inverse (p q n r : ℕ) :
    Function.LeftInverse (mixedTotalPermutationFun p n q r) (mixedTotalPermutationFun p q n r) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp only [mixedTotalPermutationFun,Fin.addCases_left,Fin.addCases_right]

def mixedTotalPermutation (p q n r : ℕ) : Fin ((p+q)+(n+r)) ≃ Fin ((p+n)+(q+r)) where
  toFun := mixedTotalPermutationFun p q n r
  invFun := mixedTotalPermutationFun p n q r
  left_inv := mixedTotalPermutationFun_left_inverse p q n r
  right_inv := mixedTotalPermutationFun_left_inverse p n q r

theorem mixedTotalPermutation_append {α : Type*} {p q n r : ℕ}
    (z : Fin p → α) (t : Fin q → α) (x : Fin n → α) (u : Fin r → α) :
    Fin.append (Fin.append z t) (Fin.append x u) ∘ (mixedTotalPermutation p q n r).symm =
      Fin.append (Fin.append z x) (Fin.append t u) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp only [mixedTotalPermutation,mixedTotalPermutationFun,Function.comp_apply,Equiv.coe_fn_symm_mk,
        Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag} {sa : Fin a → SortTag}

theorem originalSortedRowTotal_definable {X : Set (Fin p → M)} {D : Set (Fin (p+a) → M)}
    (hX : DefinableOverBase B sp X) (hD : DefinableOverBase B (Fin.append sp sa) D) :
    DefinableOverBase B (Fin.append sp sa) (rawRowTotal X D) := by
  have h := hD.inter (hX.preimage_real (Fin.append sp sa) (Fin.castAdd a))
  convert h using 1
  ext w
  change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact ⟨fun h => ⟨h.2,h.1,hD.proper w h.2⟩,fun h => ⟨h.2.1,h.1⟩⟩

end DiamondIntegral.Section5
