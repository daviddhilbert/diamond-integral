import «section 6».ClopenCriterion
import «section 6».CentripetalPullbackPreservation

/-! A definable doubly bounded RV-pullback with bounded RV support is
proper invariant. An arbitrary geometric bound proves clopenness;
the checked clopen criterion supplies the required original-base names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem doublyBounded_rvPullback_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hAD : VFDoublyBounded A.carrier)
    (hRV : RVSupportDoublyBounded A.carrier) (hA : IsRVPullback A.carrier) :
    ProperInvariant S A.carrier := by
  obtain ⟨γ,hγ⟩ := hAD
  apply (lemma_6_5 h00 hc hκ hs hv A.carrier A.definable
    ⟨γ⁻¹,fun x hx i => (hγ x hx i).1⟩ hRV).mpr
  intro u
  have hInv : AlphaInvariant (fun _ : Fin n => γ) (vfFibre A.carrier u) := by
    have step (x y : Fin n → VF M) (hxy : Congruent (fun _ => γ) x y)
        (hx : x ∈ vfFibre A.carrier u) : y ∈ vfFibre A.carrier u := by
      change (y,u) ∈ A.carrier
      apply rvPullback_mem_of_sameRV (p := (x,u)) (q := (y,u)) hA hx _ rfl
      funext i
      exact (rv_eq_of_close_at_radius γ (hγ (x,u) hx i).2 (hxy.symm i)).symm
    exact fun x y hxy => ⟨step x y hxy,step y x hxy.symm⟩
  exact hInv.isClopen hv

end DiamondIntegral.Section6
