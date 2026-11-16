import «section 6».RVRefinementFrames

/-! A tagged ambient and an RV-pullback source with a label projection
give exact old-or-empty fibres from inclusion alone. This identifies
the actual transported ambient as a refinement of a joint family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem tagged_pullback_label_fibres
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : DefSet (rawMixedSpace (M := M) n s) S) (π : Fin r → Fin s)
    (hC : IsRVPullback C.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hSub : ∀ p ∈ C.carrier,(p.1,p.2 ∘ π) ∈ A.carrier) (u : Fin s → RVInfinity M) :
    vfFibre C.carrier u=∅ ∨ vfFibre C.carrier u=vfFibre A.carrier (u ∘ π) := by
  by_cases hEmpty : (vfFibre C.carrier u).Nonempty
  · obtain ⟨a,ha⟩ := hEmpty
    right
    apply Set.Subset.antisymm
    · intro x hx
      exact hSub (x,u) hx
    · intro x hx
      exact rvPullback_mem_of_sameRV hC ha
        (hTag (a,u ∘ π) (hSub (a,u) ha) (x,u ∘ π) hx rfl) rfl
  · left
    exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hEmpty ⟨x,hx⟩)

def RVRefinementFrame.of_tagged_pullback
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : DefSet (rawMixedSpace (M := M) n s) S) (π : Fin r → Fin s)
    (hC : ProperInvariant S C.carrier) (hCD : VFDoublyBounded C.carrier) (hCRV : IsRVPullback C.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hSub : ∀ p ∈ C.carrier,(p.1,p.2 ∘ π) ∈ A.carrier) : RVRefinementFrame A :=
  ⟨s,C,π,hC,hCD,tagged_pullback_label_fibres A C π hCRV hTag hSub⟩

end DiamondIntegral.Section6
