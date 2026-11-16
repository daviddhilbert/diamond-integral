import «section 6».RVIsomorphismFactorizations

/-! Full real code images and actual VF/RV tuple presentations have
the same original-base definability. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rawVF_preimage_eq_codeImage (A : Set (Fin n → VF M)) :
    (rawVFSpace (M := M) n).preimage A = vfValues '' A := by
  ext z
  constructor
  · rintro ⟨hz,ha⟩
    exact ⟨(rawVFSpace (M := M) n).decode ⟨z,hz⟩,ha,vfValues_decode _⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,by simpa only [decode_vfValues] using ha⟩

theorem vfDefSet_codeImage_definable (A : DefSet (rawVFSpace (M := M) n) S) :
    S.Definable LRV (vfValues '' A.carrier) := by
  rw [← rawVF_preimage_eq_codeImage]
  exact A.definable

theorem rawRV_preimage_eq_codeImage (A : Set (Fin n → RVInfinity M)) :
    (rawRVSpace (M := M) n).preimage A = rvValues '' A := by
  ext z
  constructor
  · rintro ⟨hz,ha⟩
    exact ⟨(rawRVSpace (M := M) n).decode ⟨z,hz⟩,ha,rvValues_decode _⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,by simpa only [decode_rvValues] using ha⟩

def rvDefSetOfCodeImage (A : Set (Fin n → RVInfinity M)) (hA : S.Definable LRV (rvValues '' A)) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := A
  definable := by
    change S.Definable LRV ((rawRVSpace (M := M) n).preimage A)
    rwa [rawRV_preimage_eq_codeImage]

end DiamondIntegral.Section6
