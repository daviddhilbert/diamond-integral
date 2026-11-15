import «section 2».Bases
import ValuedModelMap

/-! The RV image of an actual VF subfield is closed under every RV
function in the paper's language. No algebraic closure is taken. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV ValuedModelMap
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (F : Subfield (VFType (M := M)))

def vfFieldRVImage : Set (RVSort M) := encodedRv '' (F : Set (VFType (M := M)))

theorem vfFieldRVImage_zero : zeroRV ∈ vfFieldRVImage F := ⟨0,F.zero_mem,encodedRv_zero⟩
theorem vfFieldRVImage_one : oneRV ∈ vfFieldRVImage F := ⟨1,F.one_mem,encodedRv_one⟩
theorem vfFieldRVImage_mul {a b : RVSort M} (ha : a ∈ vfFieldRVImage F) (hb : b ∈ vfFieldRVImage F) :
    mulRV a b ∈ vfFieldRVImage F := by
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  exact ⟨x*y,F.mul_mem hx hy,encodedRv_mul x y⟩

theorem vfFieldRVImage_add {a b : RVSort M} (ha : a ∈ vfFieldRVImage F) (hb : b ∈ vfFieldRVImage F) :
    addK a b ∈ vfFieldRVImage F := by
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  by_cases hKx : inK (encodedRv x)
  · by_cases hKy : inK (encodedRv y)
    · rcases hKx with hux | hzx
      · rcases hKy with huy | hzy
        · rw [addK_units x y hux huy]
          split_ifs
          · exact ⟨x+y,F.add_mem hx hy,rfl⟩
          · exact vfFieldRVImage_zero F
        · rw [hzy,addK_zero _ (Or.inl hux)]
          exact ⟨x,hx,rfl⟩
      · rw [hzx,zero_addK _ hKy]
        exact ⟨y,hy,rfl⟩
    · rw [addK_junk _ _ (Or.inr hKy)]
      exact vfFieldRVImage_zero F
  · rw [addK_junk _ _ (Or.inl hKx)]
    exact vfFieldRVImage_zero F

theorem vfFieldRVImage_neg {a : RVSort M} (ha : a ∈ vfFieldRVImage F) :
    negK a ∈ vfFieldRVImage F := by
  obtain ⟨x,hx,rfl⟩ := ha
  by_cases hKx : inK (encodedRv x)
  · rcases hKx with hux | hzx
    · rw [negK_units x hux]
      exact ⟨-x,F.neg_mem hx,rfl⟩
    · rw [hzx,negK_zero]
      exact vfFieldRVImage_zero F
  · rw [negK_junk _ hKx]
    exact vfFieldRVImage_zero F

end DiamondIntegral.Section5
