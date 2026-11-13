import «section 4».FiniteFamilyBijections

/-! Changing only the proofs of finite component supports preserves
the actual tags, partial component maps and source/target pieces. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FiniteFamilyDomainCongruence
open FiniteFamilyBijections
variable {ι κ X Y : Type*} {A A' : ι → Set X} {D D' : κ → Set Y}

def congr (h : ∀ i, A i = A' i) : Domain A ≃ Domain A' where
  toFun a := ⟨a.val, (Set.ext_iff.mp (h a.val.1) a.val.2).mp a.property⟩
  invFun a := ⟨a.val, (Set.ext_iff.mp (h a.val.1) a.val.2).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def transport (hA : ∀ i, A i = A' i) (hD : ∀ j, D j = D' j) (F : Domain A ≃ Domain D) :
    Domain A' ≃ Domain D' :=
  (congr hA).symm.trans (F.trans (congr hD))

theorem sourcePiece_eq (hA : ∀ i, A i = A' i) (hD : ∀ j, D j = D' j) (F : Domain A ≃ Domain D)
    (i : ι) (j : κ) : sourcePiece (transport hA hD F) i j = sourcePiece F i j := by
  ext x
  exact ⟨fun ⟨hx, hj⟩ => ⟨(Set.ext_iff.mp (hA i) x).mpr hx, hj⟩,
    fun ⟨hx, hj⟩ => ⟨(Set.ext_iff.mp (hA i) x).mp hx, hj⟩⟩

theorem pieceMap_eq (hA : ∀ i, A i = A' i) (hD : ∀ j, D j = D' j) (F : Domain A ≃ Domain D)
    (default : Y) (i : ι) : pieceMap (transport hA hD F) default i = pieceMap F default i := by
  funext x
  by_cases hx : x ∈ A i
  · rw [pieceMap_on (transport hA hD F) default i x ((Set.ext_iff.mp (hA i) x).mp hx), pieceMap_on F default i x hx]
    rfl
  · have hx' : x ∉ A' i := fun h => hx ((Set.ext_iff.mp (hA i) x).mpr h)
    simp only [pieceMap, dite_eq_right hx, dite_eq_right hx']

end DiamondIntegral.Section4.FiniteFamilyDomainCongruence
