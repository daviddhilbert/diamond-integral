import «section 6».FiniteDefSetIntersections
import Section4.FiniteCover

/-! Genuine saturation extracts a finite cover by actual definable
presented sets, retaining the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M}

theorem exists_finite_presented_subcover {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) {P : Space LRV M} (A : DefSet P S)
    {I : Type} (C : I → DefSet P S) (hCover : ∀ u : A, ∃ i, u.val ∈ (C i).carrier) :
    ∃ n : ℕ, ∃ f : Fin n → I, ∀ u : A, ∃ j, u.val ∈ (C (f j)).carrier := by
  let U (i : I) := P.preimage (C i).carrier
  have hCov : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz,ha⟩
    obtain ⟨i,hi⟩ := hCover ⟨P.decode ⟨z,hz⟩,ha⟩
    exact ⟨U i,⟨i,rfl⟩,hz,hi⟩
  obtain ⟨J,hJ,hSub,hCovJ⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨i,rfl⟩; exact (C i).definable) hCov
  letI : Fintype J := hJ.fintype
  let e := (Fintype.equivFin J).symm
  choose i hi using fun j : J => hSub j.property
  let f (k : Fin (Fintype.card J)) := i (e k)
  refine ⟨_,f,fun u => ?_⟩
  obtain ⟨z,hzu⟩ := P.onto u.val
  have hza : z.val ∈ P.preimage A.carrier := ⟨z.property,hzu.symm ▸ u.property⟩
  obtain ⟨c,hc,hzc⟩ := hCovJ z.val hza
  obtain ⟨k,hk⟩ := e.surjective (⟨c,hc⟩ : J)
  have hci : U (f k) = c := (hi (e k)).trans (congrArg Subtype.val hk)
  refine ⟨k,?_⟩
  have hzC : z.val ∈ P.preimage (C (f k)).carrier := by
    change z.val ∈ U (f k)
    rw [hci]
    exact hzc
  have hmem := (P.preimage_decode (C (f k)).carrier z).mp hzC
  rwa [hzu] at hmem

end DiamondIntegral.Section6
