import «section 3».GammaCodeProductIsomorphisms

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

def gammaEmptyCode (hc : CanonicalStructure.IsCanonical (M := M)) :
    (codeSpace ((volumeGammaSpace hc).power (Fin 0))).Carrier :=
  ⟨fun p => p.1.elim0, fun i : Fin 0 => i.elim0⟩

def gammaUnitCode (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    (GammaObject.unit (M := M) hc S).codeLift.Carrier :=
  ⟨(0 : Fin 1), ⟨gammaEmptyCode hc, Set.mem_univ _⟩⟩

def gammaToUnitPieceMap (A : GammaCodeObject hc S) (i : Fin A.obj.tags) :
    Map (A.obj.codeLift.piece i) ((GammaObject.unit hc S).codeLift.piece (0 : Fin 1)) := by
  let F : Map (A.obj.codeLift.piece i) (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin 0))) S) :=
    Map.ofCodes _ (fun _ => gammaEmptyCode hc) (fun _ p => p.1.elim0)
      (fun p => p.1.elim0) (fun _ i => i.elim0) (fun _ => Subtype.ext (funext (fun p => p.1.elim0)))
  exact F.corestrict (fun _ => Set.mem_univ _)

def gammaCodeToUnit (A : GammaCodeObject hc S) : A ⟶ GammaCodeObject.unit hc S where
  map := {
    toFun := fun _ => gammaUnitCode hc S
    definable := familyTaggedMap_definable A.obj.codeLift (GammaObject.unit hc S).codeLift
      (fun _ => (0 : Fin 1)) (gammaToUnitPieceMap A) }
  respects := fun _ _ _ => rfl

theorem gammaUnitCodes_subsingleton : Subsingleton (GammaObject.unit (M := M) hc S).codeLift.Carrier :=
  ⟨fun a b => familyCarrier_ext _
    (Subsingleton.elim (show Fin 1 from a.1) (show Fin 1 from b.1))
    (Subtype.ext (funext (fun p => p.1.elim0)))⟩

theorem gammaCodeUnit_hom_ext {A : GammaCodeObject hc S}
    (f g : A ⟶ GammaCodeObject.unit hc S) : f = g := by
  apply GammaCodeMap.ext
  apply FamilyMap.ext
  funext c
  exact gammaUnitCodes_subsingleton.elim _ _

def gammaCodeProductRightUnitIso (A : GammaCodeObject hc S) : A.product (GammaCodeObject.unit hc S) ≅ A where
  hom := gammaCodeProductFst A (GammaCodeObject.unit hc S)
  inv := gammaCodeProductPair (𝟙 A) (gammaCodeToUnit A)
  hom_inv_id := by
    apply gammaCodeProduct_hom_ext
    · simp only [Category.assoc, gammaCodeProductPair_fst, Category.comp_id, Category.id_comp]
    · exact gammaCodeUnit_hom_ext _ _
  inv_hom_id := gammaCodeProductPair_fst _ _

end DiamondIntegral.Section3
