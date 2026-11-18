import «section 3».GammaGroundEqualizers
import «section 3».GammaGroundRVPackPairs
import «section 5».Completed18GroundCodeGraphs

/-! Equality of arbitrary Gamma forms is an original-ground definable RV
constraint. Its real-code presentation chooses no RV representative of a
Gamma density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4.Section3RVCodeBridge
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b : ℕ}
variable (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
variable (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)

def gammaRVFormEqualizer :=
  (ω.comp (GammaGroundMap.prodFst A D)).equalizer (π.comp (GammaGroundMap.prodSnd A D))

def gammaRVFormConstraintDomain :=
  ((gammaGroundRVPack A D).restrict
    ((ω.comp (GammaGroundMap.prodFst A D)).equalizer_subset (π.comp (GammaGroundMap.prodSnd A D)))).image

def gammaRVFormRawConstraint : Set (Fin (a+b) → M) :=
  rawDomain (gammaRVFormConstraintDomain A D ω π)

theorem gammaRVFormRawConstraint_definable :
    DefinableOverBase B (fun _ => .rv) (gammaRVFormRawConstraint A D ω π) :=
  rawDomain_definable (gammaRVFormConstraintDomain A D ω π)

theorem gammaRVFormConstraintDomain_mem (r : Fin a → CanonicalRV.RVSort M) (s : Fin b → CanonicalRV.RVSort M) :
    Fin.append r s ∈ (gammaRVFormConstraintDomain A D ω π).carrier ↔
      ∃ u : A, ∃ v : D, u.val = r ∧ v.val = s ∧ ω u = π v := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨z,hz,hw⟩ := x.property
    have he : Fin.append z.val.1 z.val.2 = Fin.append r s := by
      change Fin.append x.val.1 x.val.2 = _ at hx
      exact (congrArg (fun q => Fin.append q.1 q.2) hz).trans hx
    have hp := @rvAppend_injective M _ a b z.val (r,s) he
    refine ⟨⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩,congrArg Prod.fst hp,congrArg Prod.snd hp,?_⟩
    exact Subtype.ext hw
  · rintro ⟨u,v,hu,hv,hw⟩
    let z : A.prod D := ⟨(u.val,v.val),u.property,v.property⟩
    let x : gammaRVFormEqualizer A D ω π := ⟨z.val,z,rfl,congrArg Subtype.val hw⟩
    refine ⟨x,?_⟩
    change Fin.append u.val v.val = Fin.append r s
    rw [hu,hv]

theorem gammaRVFormRawConstraint_labels_mem
    (r : Fin a → CanonicalRV.RVSort M) (s : Fin b → CanonicalRV.RVSort M) :
    Fin.append (rvValues r) (rvValues s) ∈ gammaRVFormRawConstraint A D ω π ↔
      ∃ u : A, ∃ v : D, u.val = r ∧ v.val = s ∧ ω u = π v := by
  have hcode : rvValues (Fin.append r s) = Fin.append (rvValues r) (rvValues s) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [rvValues,Fin.append_left,Fin.append_right]
  change (∃ t ∈ (gammaRVFormConstraintDomain A D ω π).carrier,
    rvValues t = Fin.append (rvValues r) (rvValues s)) ↔ _
  constructor
  · rintro ⟨t,ht,hc⟩
    have he : t = Fin.append r s := rvValues_injective (hc.trans hcode.symm)
    exact (gammaRVFormConstraintDomain_mem A D ω π r s).mp (he ▸ ht)
  · intro h
    exact ⟨Fin.append r s,(gammaRVFormConstraintDomain_mem A D ω π r s).mpr h,hcode⟩

theorem gammaRVFormRawConstraint_mem (u : A) (v : D) :
    Fin.append (rvValues u.val) (rvValues v.val) ∈ gammaRVFormRawConstraint A D ω π ↔ ω u = π v := by
  have hcode : rvValues (Fin.append u.val v.val) = Fin.append (rvValues u.val) (rvValues v.val) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [rvValues,Fin.append_left,Fin.append_right]
  change (∃ t ∈ (gammaRVFormConstraintDomain A D ω π).carrier,
    rvValues t = Fin.append (rvValues u.val) (rvValues v.val)) ↔ _
  constructor
  · rintro ⟨t,ht,hc⟩
    have he : t = Fin.append u.val v.val := rvValues_injective (hc.trans hcode.symm)
    obtain ⟨u',v',hu,hv,hw⟩ := (gammaRVFormConstraintDomain_mem A D ω π u.val v.val).mp (he ▸ ht)
    have hu' : u' = u := Subtype.ext hu
    have hv' : v' = v := Subtype.ext hv
    simpa only [hu',hv'] using hw
  · intro hw
    exact ⟨Fin.append u.val v.val,(gammaRVFormConstraintDomain_mem A D ω π u.val v.val).mpr ⟨u,v,rfl,rfl,hw⟩,hcode⟩

end DiamondIntegral.Section3
