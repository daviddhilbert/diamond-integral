import «section 6».VFInterpolationGeometry

/-! Transitions between actual coordinate interpolations retain their
RV labels. Changing one interpolation choice changes only that VF
coordinate, with unit total derivative on every point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def vfInterpolationTransition (f : Map A B) (P Q : Fin n → Prop)
    (hP : Function.Bijective (vfInterpolation f P)) :=
  (vfInterpolation f Q).comp ((vfInterpolation f P).inverse hP)

theorem vfInterpolationTransition_at (f : Map A B) (P Q : Fin n → Prop)
    (hP : Function.Bijective (vfInterpolation f P)) (p : A) :
    vfInterpolationTransition f P Q hP (vfInterpolation f P p)=vfInterpolation f Q p := by
  change vfInterpolation f Q ((vfInterpolation f P).inverse hP (vfInterpolation f P p))=_
  rw [Map.inverse_apply]

theorem vfInterpolationTransition_retained (f : Map A B) (P Q : Fin n → Prop)
    (hP : Function.Bijective (vfInterpolation f P)) (p : (vfInterpolationMap f P).image) (i : Fin s) :
    (vfInterpolationTransition f P Q hP p).val.2 i=p.val.2 i := by
  obtain ⟨a,rfl⟩ := hP.surjective p
  rw [vfInterpolationTransition_at,vfInterpolation_value,vfInterpolation_value]

theorem vfInterpolationTransition_relative (f : Map A B) (P Q : Fin n → Prop)
    (hP : Function.Bijective (vfInterpolation f P)) (j : Fin n) (hAgree : ∀ i,i ≠ j → (P i ↔ Q i))
    (p : (vfInterpolationMap f P).image) (i : Fin n) (hi : i ≠ j) :
    (vfInterpolationTransition f P Q hP p).val.1 i=p.val.1 i := by
  obtain ⟨a,rfl⟩ := hP.surjective p
  rw [vfInterpolationTransition_at,vfInterpolation_coordinate,vfInterpolation_coordinate,propext (hAgree i hi)]

theorem vfInterpolationTransition_rv_displacements (f : Map A B) (P Q : Fin n → Prop)
    (hP : Function.Bijective (vfInterpolation f P)) (hD : ∀ i,RVCoordinateDisplacement f i)
    (i : Fin n) : RVCoordinateDisplacement (vfInterpolationTransition f P Q hP) i := by
  intro p z he
  obtain ⟨a,rfl⟩ := hP.surjective p
  obtain ⟨b,rfl⟩ := hP.surjective z
  rw [vfInterpolationTransition_at,vfInterpolationTransition_at,vfInterpolation_value,vfInterpolation_value] at he
  rw [vfInterpolationTransition_at,vfInterpolationTransition_at,vfInterpolation_value,vfInterpolation_value,
    vfInterpolation_value,vfInterpolation_value]
  have hd := hD i a b he
  by_cases hPi : P i <;> by_cases hQi : Q i
  · simp only [if_pos hPi,if_pos hQi,sub_self]
  · simpa only [if_pos hPi,if_neg hQi,neg_sub] using congrArg (fun x : VF M => -x) hd
  · simpa only [if_neg hPi,if_pos hQi] using hd
  · simp only [if_neg hPi,if_neg hQi,sub_self]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem inverse_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (h : ProperCovariantHomeomorphism f) : ProperCovariantHomeomorphism (f.inverse h.bijective) := by
  have hInv : Function.Bijective (f.inverse h.bijective) := by
    constructor
    · intro p z he
      have hEq := congrArg f he
      simpa only [Map.apply_inverse] using hEq
    · intro p
      exact ⟨f p,Map.inverse_apply f h.bijective p⟩
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _
    h.inverseCovariant hInv h.inverseContinuous

theorem vfInterpolationTransition_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hF : ProperCovariantHomeomorphism f) (P Q : Fin n → Prop) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (hD : ∀ i,RVCoordinateDisplacement f i) :
    ProperCovariantHomeomorphism (vfInterpolationTransition f P Q (vfInterpolation_bijective f P π hRetain hD)) := by
  have hP := vfInterpolation_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF P π hRetain hD
  have hQ := vfInterpolation_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF Q π hRetain hD
  exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (inverse_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ _ hP) hQ

end DiamondIntegral.Section6
