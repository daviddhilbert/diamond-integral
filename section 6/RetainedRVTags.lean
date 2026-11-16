import «section 6».UnaryFieldBase

/-! Every actual special covariant chain retains every original RV tag
as a suffix. The statement tracks the changing RV arities through finite
composition and supplies the label condition for standard contractions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

def rvTailIndex {r s : ℕ} (h : r ≤ s) (i : Fin r) : Fin s := ⟨s-r+i.val,by omega⟩

theorem rvTailIndex_self {r : ℕ} (i : Fin r) : rvTailIndex le_rfl i = i := by
  apply Fin.ext
  simp only [rvTailIndex,Nat.sub_self,Nat.zero_add]

theorem rvTailIndex_comp {r s t : ℕ} (h : r ≤ s) (k : s ≤ t) (i : Fin r) :
    rvTailIndex k (rvTailIndex h i) = rvTailIndex (h.trans k) i := by
  apply Fin.ext
  simp only [rvTailIndex]
  omega

theorem append_rvTailIndex {X : Type*} {n r : ℕ} (a : Fin n → X) (b : Fin r → X)
    (h : r ≤ n+r) (i : Fin r) : Fin.append a b (rvTailIndex h i) = b i := by
  have he : rvTailIndex h i = Fin.natAdd n i := by
    apply Fin.ext
    change (n+r)-r+i.val = n+i.val
    omega
  rw [he,Fin.append_right]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SpecialCovariantChain.retainsRV
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (H : SpecialCovariantChain (G := G) A B f) :
    ∃ h : r ≤ s, ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i) = p.val.2 i := by
  induction H with
  | identity A hA => exact ⟨le_rfl,fun p i => by rw [rvTailIndex_self]; rfl⟩
  | regularize A hA hD =>
      exact ⟨by omega,fun p i => append_rvTailIndex _ _ _ i⟩
  | centripetal A D =>
      refine ⟨by omega,?_⟩
      intro p i
      change Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core p.val)) p.val.2 (rvTailIndex _ i) = p.val.2 i
      exact append_rvTailIndex _ _ _ i
  | zeroCentered A D =>
      refine ⟨by omega,?_⟩
      intro p i
      change Fin.append (fun j => branchTag (M := M) (D.core p.val j)) p.val.2 (rvTailIndex _ i) = p.val.2 i
      exact append_rvTailIndex _ _ _ i
  | @comp r s t A B C f g hf hg ihf ihg =>
      obtain ⟨hrs,hfRV⟩ := ihf
      obtain ⟨hst,hgRV⟩ := ihg
      refine ⟨hrs.trans hst,fun p i => ?_⟩
      change (g (f p)).val.2 (rvTailIndex (hrs.trans hst) i) = p.val.2 i
      rw [← rvTailIndex_comp hrs hst i]
      exact (hgRV (f p) (rvTailIndex hrs i)).trans (hfRV p i)

end DiamondIntegral.Section6
