import «section 6».RVGraftingHomeomorphism

/-! The zero-VF-target proper covariance criterion. Open label fibers on
a proper invariant source and doubly bounded label image suffice. The
ambient target RV space is not assumed globally doubly bounded. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r q : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properCovariant_RV_labels_of_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hA : ProperInvariant S A.carrier)
    (himage : RVSupportDoublyBounded (mixedMapRange τ))
    (hopen : ∀ u v, IsOpen (graphFibreSource τ u v)) : ProperCovariant τ := by
  refine ⟨hA.vfBounded,⟨1,fun _ _ i => i.elim0⟩,hA.rvBounded,himage,fun u v => ?_⟩
  have hD := graphFibreSource_isClopen hv τ hA hopen u v
  have hb : ∃ γ : Gamma M, ∀ x ∈ graphFibreSource τ u v, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := hA.vfBounded
    exact ⟨γ,fun x hx i => hγ (x,u) (graphFibreSource_subset τ u v hx) i⟩
  obtain ⟨α,hα,hInv⟩ := clopen_has_named_invariant_radius h00 hc hκ hs hv
    _ (graphFibreSource_definable τ u v) hD hb
  refine ⟨fun _ => α,Fin.elim0,fun _ => hα,fun i => i.elim0,hInv,?_,?_⟩
  · intro a b hab
    have he : a = b := Subsingleton.elim _ _
    rw [he]
  · intro a ha b hb hab i
    exact i.elim0

end DiamondIntegral.Section6
