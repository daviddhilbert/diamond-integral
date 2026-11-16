import «section 6».ParametricHittingSets
import Section3.DefinableMeans
import Section3.MeanInBalls
import Section4.UniformFinite

/-! Means of arbitrary definable finite VF fibers are definable over
the original base: genuine small-parameter saturation supplies the
uniform cardinal bound. Nonempty means stay in their prescribed RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

theorem finiteMean_definable (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (F : (Fin n → M) → Finset (VF M))
    (hF : RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation F)) :
    S.DefinableFun LRV (fun a => (Barycentre.mean (F a)).val) := by
  have hFinite (a : Fin n → M) : {x | (a,x) ∈ Barycentre.finiteFibreRelation F}.Finite :=
    (F a).finite_toSet.image Subtype.val
  obtain ⟨N,hN⟩ := uniform_finite_fibre_bound hs S hsmall
    (Barycentre.finiteFibreRelation F) hF hFinite
  apply Barycentre.mean_definable h00 S F hF N
  intro a
  have he : {x | (a,x) ∈ Barycentre.finiteFibreRelation F} = Subtype.val '' (F a : Set (VF M)) := rfl
  have hb := hN a
  rw [he,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset] at hb
  exact hb

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finiteMean_sameRV (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : Finset (VF M)) (hne : F.Nonempty) (t : RVInfinity M)
    (hR : ∀ x ∈ F, rv M x = t) : rv M (Barycentre.mean F) = t := by
  obtain ⟨a,ha⟩ := hne
  by_cases ha0 : a = 0
  · have haZero : rv M a = CanonicalRV.encodedRv (0 : VF M) := congrArg (rv M) ha0
    have hx0 (x : VF M) (hx : x ∈ F) : x = 0 := by
      apply CanonicalRV.encodedRv_zero_iff x |>.mp
      exact (congrArg Subtype.val ((hR x hx).trans ((hR a ha).symm.trans haZero))).trans
        ((CanonicalRV.encodedRv_zero_iff (0 : VF M)).mpr rfl)
    have he : F = {0} := by
      ext x
      constructor
      · intro hx
        exact Finset.mem_singleton.mpr (hx0 x hx)
      · intro hx
        rw [Finset.mem_singleton] at hx
        exact hx ▸ (ha0 ▸ ha)
    have hm : Barycentre.mean F = 0 := by simp [he,Barycentre.mean]
    exact (congrArg (rv M) (hm.trans ha0.symm)).trans (hR a ha)
  · let ρ := Balls.openRadius (Valued.v a) ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr ha0)
    have hBall := Balls.rvFibre_eq_openDisc Valued.v hv a ha0
    have hAll (x : VF M) (hx : x ∈ F) : x ∈ Balls.openDisc Valued.v a ρ := by
      rw [← hBall]
      exact congrArg Subtype.val ((hR x hx).trans (hR a ha).symm)
    have hm := Barycentre.mean_mem_openDisc Valued.v hv h00 F ⟨a,ha⟩ a ρ hAll
    rw [← hBall] at hm
    change iRv (Barycentre.mean F).val = iRv a.val at hm
    exact (show rv M (Barycentre.mean F) = rv M a from Subtype.ext hm).trans (hR a ha)

end DiamondIntegral.Section6
