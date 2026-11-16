import «section 6».UnaryActiveLabelFiniteness
import «section 6».UnaryApertureFocusTransport

/-! Exact full-disc replacement for an actual unary centripetal
component on an RV-pullback. For each active old label the noncore
image is the entire bounded annulus, and the core image is the entire
RV disc at coefficient times focus. The cutoff varies with the old
disc through that focus. No constant absolute radius is substituted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace CentripetalData

variable {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unary_branch_disc_image (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) (p : A) (hu : p.val.2 ∈ D.activeTags.carrier) (flag : Bool) :
    (fun q : Mixed M 1 r => (D.point q).1 0) ''
      {q | q ∈ A.carrier ∧ q.2 = p.val.2 ∧ D.core q = flag} =
        UnaryApertureImage (D.extendedFocus p.val) (D.coefficient * D.extendedFocus p.val)
          (finiteValue (D.coefficient * D.extendedFocus p.val)
            (mul_ne_zero D.coefficient_nonzero (D.focus_nonzero p.property hu))) flag := by
  let a := D.extendedFocus p.val
  let b := D.coefficient*a
  have ha : a ≠ 0 := D.focus_nonzero p.property hu
  have hb : b ≠ 0 := mul_ne_zero D.coefficient_nonzero ha
  have hab : vfValue a ≤ vfValue b := by
    change vfValue a ≤ Values.vfValueHom (D.coefficient*a)
    rw [map_mul,valueHom_eq_value,valueHom_eq_value]
    simpa only [one_mul] using mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue a))
  have hcoord : D.coordinate = 0 := Subsingleton.elim _ _
  have hFocus (q : Mixed M 1 r) (hq : q ∈ A.carrier) (hTags : q.2 = p.val.2) :
      D.extendedFocus q = a := D.extendedFocus_same_other hq p.property hTags
        (fun i hi => False.elim (hi (Subsingleton.elim _ _)))
  have hPoint (q : Mixed M 1 r) (hq : q ∈ A.carrier) (hTags : q.2 = p.val.2) :
      (D.point q).1 0 = unaryApertureValue a b (q.1 0) := by
    simp only [point,hcoord,Function.update_self,unaryApertureValue,unaryApertureCore,
      core,hFocus q hq hTags,b]
  have hCore (q : Mixed M 1 r) (hq : q ∈ A.carrier) (hTags : q.2 = p.val.2) :
      D.core q = unaryApertureCore a b (q.1 0) := by
    simp only [core,hcoord,hFocus q hq hTags,unaryApertureCore,b]
  rw [← unaryAperture_branch_image a b ha hb hab flag]
  ext y
  constructor
  · rintro ⟨q,⟨hq,hTags,hFlag⟩,he⟩
    have hqActive : q.2 ∈ D.activeTags.carrier := hTags ▸ hu
    have hRV : rv M (q.1 0) = rv M a := by
      have h := D.focusRV q hq hqActive
      rw [← D.extendedFocus_active hq hqActive,hcoord,hFocus q hq hTags] at h
      exact h.symm
    exact ⟨q.1 0,⟨hRV,(hCore q hq hTags).symm.trans hFlag⟩,
      (hPoint q hq hTags).symm.trans he⟩
  · rintro ⟨x,⟨hRV,hFlag⟩,he⟩
    let q : Mixed M 1 r := (fun _ => x,p.val.2)
    have hq : q ∈ A.carrier := by
      apply rvPullback_mem_of_sameRV (q := q) hA p.property _ rfl
      funext i
      fin_cases i
      have hpRV := D.focusRV p.val p.property hu
      rw [← D.extendedFocus_active p.property hu,hcoord] at hpRV
      exact hpRV.symm.trans hRV.symm
    exact ⟨q,⟨hq,rfl,(hCore q hq rfl).trans hFlag⟩,(hPoint q hq rfl).trans he⟩

end CentripetalData
end DiamondIntegral.Section6
