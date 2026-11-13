import «section 3».GammaGroundRVFamilyMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}
variable {A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n)}
variable {D : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) m)}

def GammaGroundFiniteFamily.rvPieceEncode (A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n))
    (i : Fin A.tags) : GammaGroundMap (A.piece i) A.rvRealization :=
  (gammaGroundRVFamilyTagMap i (A.piece i)).corestrict (fun a => ⟨i,a,rfl⟩)

/-- An arbitrary bijection of actual tagged RV realizations reflects to
a same-ground family bijection, including every branch of its graph. -/
def gammaGroundRVFamilyBijectionOfRealization
    (F : GammaGroundBijection A.rvRealization D.rvRealization) : GammaGroundFamilyBijection A D where
  equiv := (A.rvEquiv.trans (Equiv.ofBijective F.map F.bijective)).trans D.rvEquiv.symm
  definable i j := by
    have hd := (((A.rvPieceEncode i).relation_definable.comp F.map.relation_definable).comp
      (D.rvPieceEncode j).relation_definable.symm)
    apply hd.congr
    intro x y
    constructor
    · rintro ⟨w,⟨v,⟨a,ha,hav⟩,⟨v',hvv,hfw⟩⟩,⟨b,hb,hbw⟩⟩
      have hv : v' = A.rvEncode ⟨i,a⟩ := Subtype.ext (hvv.trans hav.symm)
      have hw : F.map (A.rvEncode ⟨i,a⟩) = D.rvEncode ⟨j,b⟩ :=
        Subtype.ext ((congrArg (fun v => (F.map v).val) hv).symm.trans (hfw.trans hbw.symm))
      refine ⟨a,b,ha,hb,?_⟩
      change D.rvEquiv.symm (F.map (A.rvEncode ⟨i,a⟩)) = ⟨j,b⟩
      rw [hw]
      exact D.rvEquiv.symm_apply_apply ⟨j,b⟩
    · rintro ⟨a,b,ha,hb,he⟩
      have hw : F.map (A.rvEncode ⟨i,a⟩) = D.rvEncode ⟨j,b⟩ :=
        by
          change D.rvEquiv.symm (F.map (A.rvEncode ⟨i,a⟩)) = ⟨j,b⟩ at he
          exact (D.rvEquiv.apply_symm_apply _).symm.trans (congrArg D.rvEquiv he)
      exact ⟨(D.rvEncode ⟨j,b⟩).val,
        ⟨(A.rvEncode ⟨i,a⟩).val,⟨a,ha,rfl⟩,A.rvEncode ⟨i,a⟩,rfl,congrArg Subtype.val hw⟩,
        b,hb,rfl⟩
end DiamondIntegral.Section3
