import «section 3».GammaGroundFamilyBranchSources
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {A : GammaGroundFiniteFamily hc B P} {D : GammaGroundFiniteFamily hc B Q}

/-- Each complete family branch is an actual definable partial-domain
map with its actual target piece. -/
def GammaGroundFamilyMap.branchMap (F : GammaGroundFamilyMap A D) (i : Fin A.tags) (j : Fin D.tags) :
    GammaGroundMap (F.branchSource i j) (D.piece j) := by
  let g := (F.valueMap i).restrict (F.branchSource_subset i j)
  apply g.corestrict
  intro x
  obtain ⟨a,ha,b,hf⟩ := (F.mem_branchSource i j x.val).mp x.property
  have hx : (⟨x.val,F.branchSource_subset i j x.property⟩ : A.piece i) = a := Subtype.ext ha.symm
  have hv : (g x).val = b.val := by
    change (F.toFun ⟨i,⟨x.val,F.branchSource_subset i j x.property⟩⟩).2.val = b.val
    rw [hx]
    exact congrArg (fun t : D.Carrier => t.2.val) hf
  exact hv.symm ▸ b.property

@[simp] theorem GammaGroundFamilyMap.branchMap_value (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) (x : F.branchSource i j) :
    (F.branchMap i j x).val =
      (F.toFun ⟨i,⟨x.val,F.branchSource_subset i j x.property⟩⟩).2.val := rfl

theorem GammaGroundFamilyMap.branchMap_point (F : GammaGroundFamilyMap A D)
    (i : Fin A.tags) (j : Fin D.tags) (a : A.piece i) (b : D.piece j)
    (hf : F.toFun ⟨i,a⟩ = ⟨j,b⟩) :
    ∃ ha : a.val ∈ (F.branchSource i j).carrier, F.branchMap i j ⟨a.val,ha⟩ = b := by
  have ha := (F.mem_branchSource i j a.val).mpr ⟨a,rfl,b,hf⟩
  refine ⟨ha,Subtype.ext ?_⟩
  exact congrArg (fun t : D.Carrier => t.2.val) hf

theorem GammaGroundFamilyMap.branchMap_injective (F : GammaGroundFamilyMap A D)
    (hF : Function.Injective F.toFun) (i : Fin A.tags) (j : Fin D.tags) :
    Function.Injective (F.branchMap i j) := by
  intro x y hxy
  obtain ⟨a,ha,b,hfa⟩ := (F.mem_branchSource i j x.val).mp x.property
  obtain ⟨c,hc,d,hfc⟩ := (F.mem_branchSource i j y.val).mp y.property
  obtain ⟨ha',hab⟩ := F.branchMap_point i j a b hfa
  obtain ⟨hc',hcd⟩ := F.branchMap_point i j c d hfc
  have hax : (⟨a.val,ha'⟩ : F.branchSource i j) = x := Subtype.ext ha
  have hcy : (⟨c.val,hc'⟩ : F.branchSource i j) = y := Subtype.ext hc
  have hbd : b = d := hab.symm.trans
    ((congrArg (F.branchMap i j) hax).trans (hxy.trans
      ((congrArg (F.branchMap i j) hcy).symm.trans hcd)))
  have hac : a = c := by
    have hs := hF (hfa.trans ((congrArg (Sigma.mk j) hbd).trans hfc.symm))
    change (⟨i,a⟩ : Σ i, A.piece i) = ⟨i,c⟩ at hs
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hs
  exact Subtype.ext (ha.symm.trans ((congrArg Subtype.val hac).trans hc))

end DiamondIntegral.Section3
