import «section 4».RVZeroDegreeRetraction

/-! The actual measured RES inclusion is a ring equivalence in degree
zero, for both the full and bounded RV chart presentations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R : Type*} [CommRing R]

def zeroSubring (c : Coaction R) : Subring R := by
  letI := c.grading
  exact {
    carrier := c.piece 0
    zero_mem' := (c.piece 0).zero_mem
    add_mem' := (c.piece 0).add_mem
    neg_mem' := (c.piece 0).neg_mem
    one_mem' := SetLike.one_mem_graded c.piece
    mul_mem' := fun hx hy => SetLike.mul_mem_graded hx hy }

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction

namespace DiamondIntegral.Section4.RVZeroDegreeEquivalences
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resZero (B : Base (M := M)) : Subring (RESChartRing.Ring B) :=
  (RESGrading.gradingCoaction B).zeroSubring

def fullZero (B : Base (M := M)) : Subring (RVChartRing.Ring B) :=
  (RVGrading.gradingCoaction B).zeroSubring

def boundedZero (B : Base (M := M)) : Subring (RVBoundedRing.Ring B) :=
  (RVBoundedGrading.gradingCoaction B).zeroSubring

def fullMap (B : Base (M := M)) : resZero B →+* fullZero B :=
  ((RVChartMaps.ofRES B).comp (resZero B).subtype).codRestrict (fullZero B)
    (fun x => RVChartMaps.ofRES_mem B x.property)

theorem fullMap_bijective (B : Base (M := M)) : Function.Bijective (fullMap B) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact RVZeroDegreeRetraction.full_injective_on_degree_zero B x.property y.property (congrArg Subtype.val h)
  · intro x
    obtain ⟨r, hr, hrx⟩ := RVZeroDegreeRES.full_degree_zero_surjective B x.val x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩

def fullEquiv (B : Base (M := M)) : resZero B ≃+* fullZero B :=
  RingEquiv.ofBijective (fullMap B) (fullMap_bijective B)

theorem fullEquiv_apply (B : Base (M := M)) (x : resZero B) :
    (fullEquiv B x).val = RVChartMaps.ofRES B x.val := rfl

theorem fullEquiv_symm_apply (B : Base (M := M)) (x : fullZero B) :
    ((fullEquiv B).symm x).val = RVZeroDegreeRetraction.full B x.val := by
  have h := congrArg Subtype.val ((fullEquiv B).apply_symm_apply x)
  exact (RVZeroDegreeRetraction.full_left_inverse B ((fullEquiv B).symm x).property).symm.trans
    (congrArg (RVZeroDegreeRetraction.full B) h)

def boundedMap (B : Base (M := M)) : resZero B →+* boundedZero B :=
  ((RVBoundedMaps.ofRES B).comp (resZero B).subtype).codRestrict (boundedZero B)
    (fun x => RVBoundedMaps.ofRES_mem B x.property)

theorem boundedMap_bijective (B : Base (M := M)) : Function.Bijective (boundedMap B) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact RVZeroDegreeRetraction.bounded_injective_on_degree_zero B x.property y.property (congrArg Subtype.val h)
  · intro x
    obtain ⟨r, hr, hrx⟩ := RVZeroDegreeRES.bounded_degree_zero_surjective B x.val x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩

def boundedEquiv (B : Base (M := M)) : resZero B ≃+* boundedZero B :=
  RingEquiv.ofBijective (boundedMap B) (boundedMap_bijective B)

theorem boundedEquiv_apply (B : Base (M := M)) (x : resZero B) :
    (boundedEquiv B x).val = RVBoundedMaps.ofRES B x.val := rfl

theorem boundedEquiv_symm_apply (B : Base (M := M)) (x : boundedZero B) :
    ((boundedEquiv B).symm x).val = RVZeroDegreeRetraction.bounded B x.val := by
  have h := congrArg Subtype.val ((boundedEquiv B).apply_symm_apply x)
  exact (RVZeroDegreeRetraction.bounded_left_inverse B ((boundedEquiv B).symm x).property).symm.trans
    (congrArg (RVZeroDegreeRetraction.bounded B) h)

end DiamondIntegral.Section4.RVZeroDegreeEquivalences
