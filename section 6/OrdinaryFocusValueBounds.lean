import «section 6».OriginalBaseOrdinaryFocus
import «section 6».FiniteFocusImages

/-! A unary ordinary focus has finite VF image over the original base.
Consequently it is inactive at every sufficiently small nonzero VF point,
uniformly in all its old RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OriginalBaseOrdinaryFocus
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)

theorem scalarImage_finite (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    (scalarFocusImage (scalarMap D hc hA hD)).Finite := by
  apply scalarFocusImage_finite hc hs hsmall
  intro p q hTags
  rw [scalarMap_value,scalarMap_value]
  exact center_same_labels D p.val q.val p.property q.property hTags

theorem inactive_near_zero (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ p : A,p.val.1 0 ≠ (0 : VF M) → η.val < vfValue (p.val.1 0) → p.val ∉ D.locus := by
  let C := scalarFocusImage (scalarMap D hc hA hD)
  let value (a : VF M) : Gamma M := if ha : a ≠ 0 then finiteValue a ha else 1
  obtain ⟨b,hb⟩ := ((scalarImage_finite D hc hs hsmall hA hD).image value).bddAbove
  refine ⟨max b 1,le_max_right _ _,fun p hp0 hpSmall hpActive => ?_⟩
  have hRV := center_leading_term D p.val ⟨p.property,hpActive⟩
  have hc0 : D.center p.val ≠ 0 := by
    intro he
    have hz : rv M (p.val.1 0)=rv M (0 : VF M) := hRV.symm.trans (congrArg (rv M) he)
    exact hp0 ((SpecialTransformations.Section5.rv_eq_zero_iff _).mp hz)
  have hcMem : D.center p.val ∈ C := ⟨⟨p.val,p.property,hpActive⟩,rfl⟩
  have hBound : finiteValue (D.center p.val) hc0 ≤ max b 1 := by
    have hh := hb (Set.mem_image_of_mem value hcMem)
    exact (show finiteValue (D.center p.val) hc0 ≤ b by simpa only [value,dif_pos hc0] using hh).trans (le_max_left _ _)
  have hEq : vfValue (D.center p.val)=vfValue (p.val.1 0) := congrArg Values.vrv hRV
  have hBound' : vfValue (D.center p.val) ≤ (max b 1).val := hBound
  exact (not_lt_of_ge (hEq ▸ hBound')) hpSmall

end DiamondIntegral.Section6.OriginalBaseOrdinaryFocus
