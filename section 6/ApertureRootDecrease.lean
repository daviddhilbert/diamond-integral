import «section 6».ApertureCore
import Section5.RootConstruction

/-! The noncore branch of unary finite-aperture centering strictly
reduces the number of remaining roots after regularization. The finite
cutoff excludes zero, so the induction cannot stall at a singleton. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def noncoreRootChild (F : Finset (VF M)) (ρ : Gamma M) (t : RVInfinity M) : Finset (VF M) :=
  (F.filter (fun y => vfValue (y-Barycentre.mean F) ≤ ρ.val ∧
    rv M (y-Barycentre.mean F) = t)).image (fun y => y-Barycentre.mean F)

theorem noncoreRootChild_nonzero (F : Finset (VF M)) (ρ : Gamma M) (t : RVInfinity M)
    {x : VF M} (hx : x ∈ noncoreRootChild F ρ t) : x ≠ 0 := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hbound := (Finset.mem_filter.mp hy).2.1
  intro he
  rw [he,value_zero] at hbound
  exact ρ.property (le_antisymm (Values.le_infinity _) hbound)

theorem noncoreRootChild_card_lt (h00 : M ⊨ Axioms.ACVF00)
    (F : Finset (VF M)) (ρ : Gamma M) (t : RVInfinity M)
    (hne : (noncoreRootChild F ρ t).Nonempty) :
    (noncoreRootChild F ρ t).card < F.card := by
  obtain ⟨x,hx⟩ := hne
  have hx0 := noncoreRootChild_nonzero F ρ t hx
  obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
  have hyF := (Finset.mem_filter.mp hy).1
  have htwo : 2 ≤ F.card := by
    by_contra hsmall
    have hcard : F.card ≤ 1 := by omega
    have he : F = {y} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hyF,fun z hz => (Finset.card_le_one_iff.mp hcard) hz hyF⟩
    have hm : Barycentre.mean F = y := by simp [he,Barycentre.mean]
    exact hx0 (by rw [← hyx,hm,sub_self])
  have hsub : noncoreRootChild F ρ t ⊆
      (F.filter (fun y => rv M (y-Barycentre.mean F) = t)).image (fun y => y-Barycentre.mean F) := by
    rintro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hb).1,(Finset.mem_filter.mp hb).2.2⟩,rfl⟩
  have hfilter : (F.filter (fun y => rv M (y-Barycentre.mean F) = t)).card < F.card := by
    have he : F.filter (fun y => rv M (y-Barycentre.mean F) = t) =
        F.filter (fun y => iRv (y-Barycentre.mean F).val = t.val) := by
      ext y
      simp only [Finset.mem_filter,Subtype.ext_iff]
      rfl
    rw [he]
    exact Barycentre.fibre_card_lt h00 F htwo t.val
  exact ((Finset.card_le_card hsub).trans Finset.card_image_le).trans_lt hfilter

theorem noncoreRootChild_bound (h00 : M ⊨ Axioms.ACVF00)
    (F : Finset (VF M)) (ρ : Gamma M) (t : RVInfinity M) (d : ℕ)
    (hF : F.card ≤ d+1) (U : Finset (VF M)) (hU : U ⊆ noncoreRootChild F ρ t) : U.card ≤ d := by
  by_cases hne : U.Nonempty
  · have hchild : (noncoreRootChild F ρ t).Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,hU hx⟩
    have hlt := noncoreRootChild_card_lt h00 F ρ t hchild
    have hle := Finset.card_le_card hU
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    exact Nat.zero_le _

end DiamondIntegral.Section6
