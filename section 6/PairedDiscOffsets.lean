import «section 6».PairedDiscValueLaw
import «section 6».UnaryApertureGeometry

/-! Actual offsets for paired cores. The target offset is evaluated
from the map on the source boundary. Translating from the corresponding
absent boundary focus sends each entire core onto a nonzero RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem centered_disc_boundary_focus_absent (a d : VF M) (hd : d ≠ 0) :
    a-d ∉ centeredGammaDisc a (finiteValue d hd) := by
  intro h
  have hh := (mem_centeredGammaDisc a (a-d) (finiteValue d hd)).mp h
  have he : (a-d)-a = -d := by abel
  rw [he] at hh
  change vfValue d < Values.vfValueHom (-d) at hh
  rw [vfValue_neg,valueHom_eq_value] at hh
  exact lt_irrefl _ hh

theorem centered_disc_boundary_translation_image (a d : VF M) (hd : d ≠ 0) :
    (fun x : VF M => x-(a-d)) '' centeredGammaDisc a (finiteValue d hd) =
      {y | rv M y=rv M d} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply (rv_eq_iff_value_close hd).mpr
    have he : x-(a-d)-d=x-a := by abel
    rw [he]
    exact (mem_centeredGammaDisc a x (finiteValue d hd)).mp hx
  · intro hy
    refine ⟨y+(a-d),?_,add_sub_cancel_right _ _⟩
    apply (mem_centeredGammaDisc a _ (finiteValue d hd)).mpr
    have he : y+(a-d)-a=y-d := by abel
    rw [he]
    exact (rv_eq_iff_value_close hd).mp hy

theorem centered_disc_boundary_focus_leading_term (a d : VF M) (ha : a ≠ 0)
    (hsmall : vfValue a < vfValue d) : rv M (a-d)=rv M a := by
  apply (rv_eq_iff_value_close ha).mpr
  have he : (a-d)-a = -d := by abel
  rw [he]
  change vfValue a < Values.vfValueHom (-d)
  rw [vfValue_neg,valueHom_eq_value]
  exact hsmall

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_bijection_paired_disc_offsets
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A B : Set (VF M)) (hA : IsOpen A) (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) (hCont : ContinuousOn f A)
    (hBound : ∃ η : Gamma M,∀ y ∈ B,η.val ≤ vfValue y) (a : VF M) (ha : a ∈ A)
    (α β : Gamma M) :
    ∃ η : Gamma M,∀ (d : VF M) (hd : d ≠ 0),η.val < vfValue d →
      a+d ∈ A ∧ ∃ he : f (a+d)-f a ≠ 0,
        α ≤ finiteValue d hd ∧ β ≤ finiteValue (f (a+d)-f a) he ∧
        centeredGammaDisc a (finiteValue d hd) ⊆ A ∧
        centeredGammaDisc (f a) (finiteValue (f (a+d)-f a) he) ⊆ B ∧
        f '' centeredGammaDisc a (finiteValue d hd)=
          centeredGammaDisc (f a) (finiteValue (f (a+d)-f a) he) := by
  obtain ⟨ρ,γ₀,hLaw,hDiscs⟩ := continuous_bijection_paired_centered_discs_with_value_law
    hc hκ hs hsmall hv A B hA f hbij hGraph hCont hBound a ha
  refine ⟨max γ₀ (max α (ρ.symm β)),fun d hd hηd => ?_⟩
  have hηd' : max γ₀ (max α (ρ.symm β)) < finiteValue d hd := hηd
  have hγd : γ₀ < finiteValue d hd := (le_max_left _ _).trans_lt hηd'
  have hPunctured : a+d ∈ puncturedGammaDisc a γ₀ := by
    refine ⟨?_,?_⟩
    · intro he
      exact hd (add_left_cancel (show a+d=a+0 by simpa only [add_zero] using he))
    · have hγdVal : γ₀.val < vfValue d := hγd
      simpa only [add_sub_cancel_left] using hγdVal
  obtain ⟨hne,heq⟩ := hLaw (a+d) hPunctured
  have he : f (a+d)-f a ≠ 0 := sub_ne_zero.mpr hne
  have heq' : finiteValue (f (a+d)-f a) he=ρ (finiteValue d hd) := by
    simpa only [add_sub_cancel_left] using heq
  obtain ⟨hSource,hTarget,hImage⟩ := hDiscs (finiteValue d hd) hγd.le
  have hα : α ≤ finiteValue d hd := (le_max_left _ _).trans ((le_max_right _ _).trans hηd'.le)
  have hβ : β ≤ finiteValue (f (a+d)-f a) he := by
    rw [heq']
    have hh := ρ.monotone ((le_max_right _ _).trans ((le_max_right _ _).trans hηd'.le))
    simpa only [ρ.apply_symm_apply] using hh
  have hpA : a+d ∈ A := (hDiscs γ₀ le_rfl).1 (Or.inr hPunctured)
  refine ⟨hpA,he,hα,hβ,hSource,?_,?_⟩
  · simpa only [heq'] using hTarget
  · simpa only [heq'] using hImage

end DiamondIntegral.Section6
