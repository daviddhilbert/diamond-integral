import «section 3».GammaGroundGammaCodeProductIsomorphisms
import «section 3».GammaCodeProductUnits
/-! The zero-coordinate Gamma singleton is the actual full-code product
unit, including its definable unique code map. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundGammaUnitCode (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    (GammaGroundGammaObject.unit (M := M) hc ground).codeLift.Carrier :=
  ⟨(0 : Fin 1), ⟨gammaEmptyCode hc, Set.mem_univ _⟩⟩

def gammaGroundGammaToUnitPieceMap (A : GammaGroundGammaCodeObject hc ground) (i : Fin A.obj.tags) :
    GammaGroundMap (A.obj.codeLift.piece i) ((GammaGroundGammaObject.unit hc ground).codeLift.piece (0 : Fin 1)) :=
  GammaGroundMap.ofGlobal _ _
    (Map.ofCodes (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin A.degree))) ground.real)
      (fun _ => gammaEmptyCode hc) (fun _ p => p.1.elim0)
      (fun p => p.1.elim0) (fun _ i => i.elim0)
      (fun _ => Subtype.ext (funext (fun p => p.1.elim0))))
    (fun _ => Set.mem_univ _)

def gammaGroundGammaCodeToUnit (A : GammaGroundGammaCodeObject hc ground) : A ⟶ GammaGroundGammaCodeObject.unit hc ground where
  map := {
    toFun := fun _ => gammaGroundGammaUnitCode hc ground
    definable := gammaGroundFamilyTaggedMap_definable A.obj.codeLift (GammaGroundGammaObject.unit hc ground).codeLift
      (fun _ => (0 : Fin 1)) (gammaGroundGammaToUnitPieceMap A) }
  respects := fun _ _ _ => rfl

theorem gammaGroundGammaUnitCodes_subsingleton : Subsingleton (GammaGroundGammaObject.unit (M := M) hc ground).codeLift.Carrier :=
  ⟨fun a b => gammaGroundFamilyCarrier_ext _
    (Subsingleton.elim (show Fin 1 from a.1) (show Fin 1 from b.1))
    (Subtype.ext (funext (fun p => p.1.elim0)))⟩

theorem gammaGroundGammaCodeUnit_hom_ext {A : GammaGroundGammaCodeObject hc ground}
    (f g : A ⟶ GammaGroundGammaCodeObject.unit hc ground) : f = g := by
  apply GammaGroundGammaCodeMap.ext
  apply GammaGroundFamilyMap.ext
  funext c
  exact gammaGroundGammaUnitCodes_subsingleton.elim _ _

def gammaGroundGammaCodeProductRightUnitIso (A : GammaGroundGammaCodeObject hc ground) : A.product (GammaGroundGammaCodeObject.unit hc ground) ≅ A where
  hom := gammaGroundGammaCodeProductFst A (GammaGroundGammaCodeObject.unit hc ground)
  inv := gammaGroundGammaCodeProductPair (𝟙 A) (gammaGroundGammaCodeToUnit A)
  hom_inv_id := by
    apply gammaGroundGammaCodeProduct_hom_ext
    · simp only [Category.assoc, gammaGroundGammaCodeProductPair_fst, Category.comp_id, Category.id_comp]
    · exact gammaGroundGammaCodeUnit_hom_ext _ _
  inv_hom_id := gammaGroundGammaCodeProductPair_fst _ _

end DiamondIntegral.Section3
