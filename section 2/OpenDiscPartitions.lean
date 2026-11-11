import «section 2».FiniteLimits

/-!
# Open-disc partitions and the two bounds in Lemma 2.53

The pure VF partition uses the actual finite Gamma radius at each point.
A bounded source gives a lower bound directly. For the upper-bound
argument, a correspondence whose partition values escape with the input
valuation cannot have a nonempty minimal affine limit inside the source.
The definable finite-choice construction is not assumed to be proved here.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def IsOpenDiscPartition (A : Set (Fin n → VF M)) (p : (Fin n → VF M) → Gamma M) : Prop :=
  ∀ a ∈ A, ∀ x ∈ A, x ∈ vfBall a (p a) → p x = p a

theorem IsOpenDiscPartition.constant_of_lt_bound
    {A : Set (Fin n → VF M)} {p : (Fin n → VF M) → Gamma M}
    (hp : IsOpenDiscPartition A p) (η : Gamma M)
    (hbound : ∀ x ∈ A, ∀ i, η.val ≤ vfValue (x i))
    {a : Fin n → VF M} (ha : a ∈ A) (hpa : p a < η) :
    ∀ x ∈ A, p x = p a := by
  intro x hx
  apply hp a ha x hx
  intro i
  have hle : η.val ≤ vfValue (x i - a i) :=
    (le_min (hbound x hx i) (hbound a ha i)).trans (vfValue_min_le_sub (x i) (a i))
  exact (show (p a).val < η.val from hpa).trans_le hle

theorem IsOpenDiscPartition.bddBelow
    {A : Set (Fin n → VF M)} {p : (Fin n → VF M) → Gamma M}
    (hp : IsOpenDiscPartition A p)
    (hbound : ∃ η : Gamma M, ∀ x ∈ A, ∀ i, η.val ≤ vfValue (x i)) :
    BddBelow (p '' A) := by
  classical
  obtain ⟨η, hη⟩ := hbound
  by_cases hlow : ∃ a ∈ A, p a < η
  · obtain ⟨a, ha, hpa⟩ := hlow
    refine ⟨p a, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hp.constant_of_lt_bound η hη ha hpa x hx).ge
  · refine ⟨η, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_not_gt (fun h => hlow ⟨x, hx, h⟩)

/-- The contradiction in the upper-bound proof. This statement needs
neither a definable choice nor finiteness once a minimal limit in A exists. -/
theorem IsOpenDiscPartition.no_escape_limit
    {A : Set (Fin n → VF M)} {p : (Fin n → VF M) → Gamma M}
    (hp : IsOpenDiscPartition A p)
    (D : Set (Fin 1 → VF M)) (F : (Fin 1 → VF M) → Set (Fin n → VF M))
    (L : Set (Fin n → VF M)) (hL : HasMinimalLimitSet D 0 F L) (hLA : L ⊆ A)
    (hvalues : ∀ c ∈ D, F c ⊆ A)
    (hescape : ∀ c ∈ D, ∀ x ∈ F c, vfValue (c 0) < (p x).val) : L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨c, hc, hnear, x, hx, hxe⟩ := hL.frequently_hits he (p e) (p e)
  have heA : e ∈ A := hLA he
  have hpx : p x = p e := hp e heA x (hvalues c hc.1 hx) hxe
  have hsmall : (p e).val < vfValue (c 0) := by
    have h := hnear 0
    change (p e).val < vfValue (c 0 - 0) at h
    simpa only [sub_zero] using h
  have hlarge := hescape c hc.1 x hx
  rw [hpx] at hlarge
  exact (lt_irrefl _ (hsmall.trans hlarge))

end DiamondIntegral.Section2
