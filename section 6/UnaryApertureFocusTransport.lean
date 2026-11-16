import «section 6».UnaryApertureTransport

/-! Moving a focus inside its old RV disc, while retaining the boundary
leading term, leaves each entire aperture-branch image unchanged. This
transports an actual output point and its core branch across base fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unaryAperture_branch_image (a b : VF M) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : vfValue a ≤ vfValue b) (core : Bool) :
    unaryApertureValue a b '' {x | rv M x=rv M a ∧ unaryApertureCore a b x=core}=
      UnaryApertureImage a b (finiteValue b hb) core := by
  cases core
  · ext y
    constructor
    · rintro ⟨x,⟨hx,hCore⟩,rfl⟩
      have hCut : vfValue (x-a) ≤ vfValue b := le_of_not_gt (of_decide_eq_false hCore)
      have hValue : unaryApertureValue a b x=x-a := by
        simp only [unaryApertureValue,hCore,Bool.false_eq_true,ite_false,add_zero]
      change vfValue a < vfValue (unaryApertureValue a b x) ∧ vfValue (unaryApertureValue a b x) ≤ vfValue b
      rw [hValue]
      exact ⟨(rv_eq_iff_value_close ha).mp hx,hCut⟩
    · intro hy
      obtain ⟨x,⟨hx,hCut⟩,hValue⟩ := (Set.ext_iff.mp (unary_noncore_image a ha (finiteValue b hb)) y).mpr hy
      have hCore : unaryApertureCore a b x=false := decide_eq_false (not_lt.mpr hCut)
      exact ⟨x,⟨hx,hCore⟩,by simpa only [unaryApertureValue,hCore,Bool.false_eq_true,ite_false,add_zero] using hValue⟩
  · ext y
    constructor
    · rintro ⟨x,⟨hx,hCore⟩,rfl⟩
      have hCut : vfValue b < vfValue (x-a) := of_decide_eq_true hCore
      change rv M (unaryApertureValue a b x)=rv M b
      apply (rv_eq_iff_value_close hb).mpr
      simpa only [unaryApertureValue,hCore,ite_true,add_sub_cancel_right] using hCut
    · intro hy
      obtain ⟨x,⟨hx,hCut⟩,hValue⟩ := (Set.ext_iff.mp (unary_core_image a b ha hb hab) y).mpr hy
      have hCore : unaryApertureCore a b x=true := decide_eq_true hCut
      exact ⟨x,⟨hx,hCore⟩,by simpa only [unaryApertureValue,hCore,ite_true] using hValue⟩

theorem unaryApertureImage_eq_of_sameRV (a b a' b' : VF M) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hA : rv M a=rv M a') (hB : rv M b=rv M b') (core : Bool) :
    UnaryApertureImage a b (finiteValue b hb) core=UnaryApertureImage a' b' (finiteValue b' hb') core := by
  have hVA : vfValue a=vfValue a' := congrArg Values.vrv hA
  have hVB : vfValue b=vfValue b' := congrArg Values.vrv hB
  ext y
  cases core <;> simp only [UnaryApertureImage,Bool.false_eq_true,ite_false,ite_true,Set.mem_setOf_eq]
  · change (vfValue a < vfValue y ∧ vfValue y ≤ vfValue b) ↔ (vfValue a' < vfValue y ∧ vfValue y ≤ vfValue b')
    rw [hVA,hVB]
  · rw [hB]

theorem unaryAperture_transport_focus (a b a' b' x : VF M)
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (hab : vfValue a ≤ vfValue b) (hab' : vfValue a' ≤ vfValue b')
    (hA : rv M a=rv M a') (hB : rv M b=rv M b') (hx : rv M x=rv M a) :
    ∃ z : VF M,rv M z=rv M a' ∧ unaryApertureCore a' b' z=unaryApertureCore a b x ∧
      unaryApertureValue a' b' z=unaryApertureValue a b x := by
  let core := unaryApertureCore a b x
  have hy : unaryApertureValue a b x ∈ UnaryApertureImage a b (finiteValue b hb) core := by
    rw [← unaryAperture_branch_image a b ha hb hab core]
    exact ⟨x,⟨hx,rfl⟩,rfl⟩
  rw [unaryApertureImage_eq_of_sameRV a b a' b' hb hb' hA hB core] at hy
  rw [← unaryAperture_branch_image a' b' ha' hb' hab' core] at hy
  obtain ⟨z,⟨hz,hCore⟩,hValue⟩ := hy
  exact ⟨z,hz,hCore,hValue⟩

end DiamondIntegral.Section6
