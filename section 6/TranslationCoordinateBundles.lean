import «section 6».RVLabelTranslationHomeomorphisms
import «section 6».CoordinateBundleCriterion

/-! Undoing translations in the complementary coordinates preserves
the full RV-disc fibres in the coordinate about to be contracted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable (δ : Map B (DefSet.univ (rawVFSpace (M := M) (n+1)) S))
variable (hδ : ∀ p z : B,p.val.2=z.val.2 → δ p=δ z)
variable (hZero : ∀ p : B,rvTranslationVector δ p (Fin.last n)=0)

include hZero in
theorem rvLabelTranslation_last_fixed (p : B) :
    (rvLabelTranslation δ p).val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
  rw [rvLabelTranslation_value]
  change p.val.1 (Fin.last n)+rvTranslationVector δ p (Fin.last n)=p.val.1 (Fin.last n)
  rw [hZero,add_zero]

include hδ hZero in
theorem rvLabelTranslation_coordinate_bundle
    (hB : IsRVPullback B.carrier) (k : Fin r)
    (hLeading : ∀ p ∈ B.carrier,rv M (p.1 (Fin.last n))=p.2 k) :
    (rvLabelTranslationMap δ).image.carrier=
      (rvCoordinateBundle (vfDropLast (rvLabelTranslationMap δ).image).image k).carrier := by
  apply coordinate_bundle_of_replacement
  · rintro p ⟨b,hb⟩
    have hEq : (rvLabelTranslation δ b).val=p := hb
    rw [← hEq,rvLabelTranslation_last_fixed δ hZero]
    exact hLeading b.val b.property
  · rintro p ⟨b,hb⟩ d hd
    have hEq : (rvLabelTranslation δ b).val=p := hb
    have hRV : rv M d=rv M (b.val.1 (Fin.last n)) := by
      rw [← hEq,rvLabelTranslation_last_fixed δ hZero] at hd
      exact hd
    let b' : B := ⟨(Function.update b.val.1 (Fin.last n) d,b.val.2),by
      apply rvPullback_mem_of_sameRV (q := (Function.update b.val.1 (Fin.last n) d,b.val.2)) hB b.property _ rfl
      funext i
      by_cases hi : i=Fin.last n
      · subst i
        change rv M (b.val.1 (Fin.last n))=rv M (Function.update b.val.1 (Fin.last n) d (Fin.last n))
        rw [Function.update_self]
        exact hRV.symm
      · change rv M (b.val.1 i)=rv M (Function.update b.val.1 (Fin.last n) d i)
        rw [Function.update_of_ne hi]⟩
    have hShift : rvTranslationVector δ b'=rvTranslationVector δ b := congrArg Subtype.val (hδ b' b rfl)
    refine ⟨b',?_⟩
    change (rvTranslationHead b'+rvTranslationVector δ b',b'.val.2)=
      (Function.update p.1 (Fin.last n) d,p.2)
    rw [hShift]
    apply Prod.ext
    · funext i
      by_cases hi : i=Fin.last n
      · subst i
        simp only [Pi.add_apply,rvTranslationHead,b',Function.update_self,hZero,add_zero]
      · have h := congrArg (fun w : Mixed M (n+1) r => w.1 i) hEq
        change b.val.1 i+rvTranslationVector δ b i=p.1 i at h
        simpa only [Pi.add_apply,rvTranslationHead,b',Function.update_of_ne hi] using h
    · have hTags := congrArg (fun w : Mixed M (n+1) r => w.2) hEq
      exact hTags

end DiamondIntegral.Section6
