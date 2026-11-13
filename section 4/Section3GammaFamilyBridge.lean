import «section 4».Section3GammaMapBridge
import «section 4».FiniteFamilyBijections
import «section 3».GammaGroundFamilyBranchMaps

/-! Native finite Gamma families keep their actual tags and complete
branch graphs when converted to the chart finite-family convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaFamilyBridge
open GammaOrderLogic FiniteFamilyBijections Section3GammaCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def familyEquiv {n : ℕ} (A : GammaGroundGammaObject hc B n) :
    A.Carrier ≃ Domain (fun i => (A.piece i).carrier) where
  toFun a := ⟨(a.1, a.2.val), a.2.property⟩
  invFun a := ⟨a.val.1, ⟨a.val.2, a.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def equiv {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A D) :
    Domain (fun i => (A.piece i).carrier) ≃ Domain (fun j => (D.piece j).carrier) :=
  (familyEquiv A).symm.trans (F.equiv.trans (familyEquiv D))

theorem sourcePiece_eq {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A D) (i : Fin A.tags) (j : Fin D.tags) :
    sourcePiece (equiv F) i j = (F.toFamilyMap.branchSource i j).carrier := by
  ext x
  constructor
  · rintro ⟨hx, hj⟩
    exact (F.toFamilyMap.mem_branchSource_iff_tag i j ⟨x, hx⟩).mpr hj
  · intro hx
    have ha := F.toFamilyMap.branchSource_subset i j hx
    exact ⟨ha, (F.toFamilyMap.mem_branchSource_iff_tag i j ⟨x, ha⟩).mp hx⟩

theorem sourcePiece_definable {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A D) (i : Fin A.tags) (j : Fin D.tags) :
    GammaDefinable B (sourcePiece (equiv F) i j) := by
  rw [sourcePiece_eq]
  exact (native_iff _).mp (F.toFamilyMap.branchSource i j).definable

theorem pieceMap_branch {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A D) (i : Fin A.tags) (j : Fin D.tags)
    (x : Fin n → Values.Gamma (M := M)) (hx : x ∈ sourcePiece (equiv F) i j) :
    pieceMap (equiv F) (fun _ => (1 : Values.Gamma (M := M))) i x = Section3GammaMapBridge.map (F.toFamilyMap.branchMap i j) x := by
  have ha := sourcePiece_subset (equiv F) i j hx
  have hs : x ∈ (F.toFamilyMap.branchSource i j).carrier := (sourcePiece_eq F i j) ▸ hx
  rw [pieceMap_on (equiv F) (fun _ => (1 : Values.Gamma (M := M))) i x ha,
    Section3GammaMapBridge.map_apply (F.toFamilyMap.branchMap i j) ⟨x, hs⟩]
  rfl

theorem graph_definable {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A D) (i : Fin A.tags) (j : Fin D.tags) :
    GammaDefinable B (GammaBijectiveRelations.graphOn (sourcePiece (equiv F) i j)
      (pieceMap (equiv F) (fun _ => (1 : Values.Gamma (M := M))) i)) := by
  have h := Section3GammaMapBridge.map_definable (F.toFamilyMap.branchMap i j)
  have he : GammaBijectiveRelations.graphOn (sourcePiece (equiv F) i j) (pieceMap (equiv F) (fun _ => (1 : Values.Gamma (M := M))) i) =
      GammaBijectiveRelations.graphOn (F.toFamilyMap.branchSource i j).carrier
        (Section3GammaMapBridge.map (F.toFamilyMap.branchMap i j)) := by
    ext z
    change (_ ∈ sourcePiece (equiv F) i j ∧ pieceMap (equiv F) (fun _ => (1 : Values.Gamma (M := M))) i _ = _) ↔
      (_ ∈ (F.toFamilyMap.branchSource i j).carrier ∧ Section3GammaMapBridge.map (F.toFamilyMap.branchMap i j) _ = _)
    constructor
    · rintro ⟨hz, hF⟩
      exact ⟨(sourcePiece_eq F i j) ▸ hz, (pieceMap_branch F i j _ hz).symm.trans hF⟩
    · rintro ⟨hz, hF⟩
      have hs : _ ∈ sourcePiece (equiv F) i j := (sourcePiece_eq F i j).symm ▸ hz
      exact ⟨hs, (pieceMap_branch F i j _ hs).trans hF⟩
  exact (congrArg (GammaDefinable B) he).mpr h

end DiamondIntegral.Section4.Section3GammaFamilyBridge
