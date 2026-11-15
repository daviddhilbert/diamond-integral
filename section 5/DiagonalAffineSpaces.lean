import «section 5».DiagonalLineIdeals

/-! The character ideal in the actual constructible ring is exactly the
ideal of finite diagonal linear-action relations, also after multiplication
by every equivariant object. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
open Classical FirstOrder FirstOrder.Language
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem affineSpace_append {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) :
    affineSpace (Fin.append q r) = product (affineSpace q) (affineSpace r) := by
  have he : (Set.univ : Set (Fin (n + m) → ℂ)) = tupleProductSet Set.univ Set.univ := by
    ext x
    exact iff_of_true (Set.mem_univ _) ⟨Set.mem_univ _, Set.mem_univ _⟩
  change Object.mk (n + m) _ _ _ _ = Object.mk (n + m) _ _ _ _
  congr 1

theorem affineSpace_class (n : ℕ) (q : Fin n → ℚ) :
    objectClass (affineSpace q) = ∏ i, objectClass (affineLine (q i)) := by
  induction n with
  | zero =>
    have he : affineSpace q = unit := by
      have hw : q = Fin.elim0 := funext (fun i => Fin.elim0 i)
      change Object.mk 0 _ _ _ _ = Object.mk 0 _ _ _ _
      congr 1
    rw [he, objectClass_unit]
    simp
  | succ n ih =>
    let a : Fin n → ℚ := fun i => q (Fin.castSucc i)
    let b : Fin 1 → ℚ := fun _ => q (Fin.last n)
    have hq : Fin.append a b = q := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        rfl
      · fin_cases j
        simp only [Fin.append_right]
        rfl
    have he : affineSpace q = product (affineSpace a) (affineLine (q (Fin.last n))) := by
      exact (congrArg affineSpace hq.symm).trans (affineSpace_append a b)
    rw [he, objectClass_product, ih a]
    exact (Fin.prod_univ_castSucc (fun i => objectClass (affineLine (q i)))).symm

def linearActionRelations : Set Ring :=
  {x | ∃ X : Object, ∃ n : ℕ, ∃ q : Fin n → ℚ,
    x = objectClass (product X (affineSpace q)) - objectClass (product X (affineSpace (fun _ : Fin n => (0 : ℚ))))}

def linearActionIdeal : Ideal Ring := Ideal.span linearActionRelations

theorem linearActionIdeal_eq_lineIdeal : linearActionIdeal = lineIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨X, n, q, rfl⟩
    rw [objectClass_product, objectClass_product, affineSpace_class, affineSpace_class]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_sub]
    exact arbitrary_product_linear_relation_mem X n q
  · apply Ideal.span_le.mpr
    rintro x ⟨q, rfl⟩
    change objectClass (affineLine q) - objectClass (affineLine 0) ∈ linearActionIdeal
    have he : objectClass (affineLine q) - objectClass (affineLine 0) =
        objectClass (product unit (affineSpace (fun _ : Fin 1 => q))) -
          objectClass (product unit (affineSpace (fun _ : Fin 1 => (0 : ℚ)))) := by
      rw [objectClass_product, objectClass_product, objectClass_unit, one_mul, one_mul]
      rfl
    rw [he]
    exact Ideal.subset_span ⟨unit, 1, (fun _ => q), rfl⟩

end DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
