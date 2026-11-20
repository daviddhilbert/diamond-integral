import «section 7».BalancedPiece
import «section 7».Lemma723Two

/-! Lemma 7.21 on the balanced piece, and Lemma 7.23 for `n = 2` (on the 7.14
and 7.20 inputs).

The balanced piece of `A*` has standard contractions in the orders `21` and
`12` with equal classes (`balancedOrders`, from `BalancedPiece.cls_balanced_orders`
in both orientations of the Lemma 7.20 contraction). This discharges the
hypothesis of `Lemma723Two.lemma_7_23_two`, which gives Lemma 7.23 for `n = 2`
(`lemma_7_23_n2`): any two standard contractions of an object of `μVF^◇[2]` in
the two orders have `μIsp^db`-related head-start-`0` classes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma723TwoFinal
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.LabelPieces DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section7.ProductKinds DiamondIntegral.Section7.BalancedKinds
open DiamondIntegral.Section7.BalancedPiece DiamondIntegral.Section7.Lemma723Two
open DiamondIntegral.Section7.PieceCombination DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.TwoCellInput
open DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem perm_two (e : Equiv.Perm (Fin 2)) : e = 1 ∨ e = Equiv.swap 0 1 := by
  revert e
  decide

theorem carrier_one {S : Set M} {r : ℕ} (W : DefSet (rawMixedSpace (M := M) 2 r) S) :
    (reindexedVFSet W (Equiv.swap 0 1)).carrier =
      (reindexedVFSet (reindexedVFSet W 1) (Equiv.swap 0 1)).carrier := by
  ext p
  rw [mem_reindexedVFSet, mem_reindexedVFSet, mem_reindexedVFSet]
  rfl

theorem carrier_swap {S : Set M} {r : ℕ} (W : DefSet (rawMixedSpace (M := M) 2 r) S) :
    (reindexedVFSet W 1).carrier =
      (reindexedVFSet (reindexedVFSet W (Equiv.swap 0 1)) (Equiv.swap 0 1)).carrier := by
  ext p
  rw [mem_reindexedVFSet, mem_reindexedVFSet, mem_reindexedVFSet]
  have he : (p.1 ∘ ⇑(Equiv.swap (0 : Fin 2) 1).symm) ∘ ⇑(Equiv.swap (0 : Fin 2) 1).symm =
      p.1 ∘ ⇑(1 : Equiv.Perm (Fin 2)).symm := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_self]
    rfl
  change ((p.1 ∘ ⇑(1 : Equiv.Perm (Fin 2)).symm), p.2) ∈ W.carrier ↔
    (((p.1 ∘ ⇑(Equiv.swap (0 : Fin 2) 1).symm) ∘ ⇑(Equiv.swap (0 : Fin 2) 1).symm), p.2) ∈ W.carrier
  rw [he]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include V hV hVT hTV hnt in
/-- **Lemma 7.21 on the balanced piece of `A*`.** -/
theorem balancedOrders : BalancedOrders (G := G) h00 hc hκ hs hv hsmall hΓ := by
  intro A' hω e F Dt
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (balPiece h00 hc hκ hs hv hsmall hΓ A' hω F Dt).carrier (balPiece h00 hc hκ hs hv hsmall hΓ A' hω F Dt).proper
  rcases perm_two e with rfl | rfl
  · obtain ⟨G₁, G₂, h⟩ := cls_balanced_orders (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A' hω F Dt D
      (Equiv.swap 0 1) (carrier_one D.map.image)
    exact ⟨G₁, G₂, ispRel_of_eq (h _ _)⟩
  · obtain ⟨G₁, G₂, h⟩ := cls_balanced_orders (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A' hω F Dt D
      1 (carrier_swap D.map.image)
    exact ⟨G₂, G₁, ispRel_of_eq (h _ _).symm⟩

include V hV hVT hTV hnt in
/-- **Lemma 7.23 (`contraction:perm:pair:isp`) for `n = 2`**, on the 7.14 and
7.20 inputs: standard contractions of an object of `μVF^◇[2]` in the two orders
have `μIsp^db`-related head-start-`0` classes. -/
theorem lemma_7_23_n2 (h714 : Lemma714 M G) (h720 : Lemma720 M G) (A : VFObject (M := M) (T : Set M) 2)
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form 1)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) :=
  lemma_7_23_two h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 h720
    (balancedOrders h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ) A F₁ F₂

end DiamondIntegral.Section7.Lemma723TwoFinal
