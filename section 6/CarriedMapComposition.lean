import «section 6».ContractionMapTransports

/-! Carrying a fixed labelled VF disc commutes with actual map
composition and identity. These are equalities of full definable maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}

theorem carryLastMap_identity (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    carryLastMap (Map.id A) k k (fun _ => rfl)=Map.id (rvCoordinateBundle A k) := by
  apply Map.ext
  intro p
  apply Subtype.ext
  change (carryLastMap (Map.id A) k k (fun _ => rfl) p).val=p.val
  rw [carryLastMap_value]
  change (Fin.snoc (Fin.init p.val.1) (p.val.1 (Fin.last n)),p.val.2)=p.val
  rw [Fin.snoc_init_self]
  rfl

theorem carryLastMap_composition
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S}
    (f : Map A B) (g : Map B C) (k : Fin r) (l : Fin s) (m : Fin t)
    (hF : ∀ p : A,(f p).val.2 l=p.val.2 k) (hG : ∀ p : B,(g p).val.2 m=p.val.2 l) :
    carryLastMap (g.comp f) k m (fun p => (hG (f p)).trans (hF p))=
      (carryLastMap g l m hG).comp (carryLastMap f k l hF) := by
  apply Map.ext
  intro p
  apply Subtype.ext
  change (carryLastMap (g.comp f) k m (fun p => (hG (f p)).trans (hF p)) p).val=
    (carryLastMap g l m hG (carryLastMap f k l hF p)).val
  rw [carryLastMap_value,carryLastMap_value,carryLastMap_base,carryLastMap_fixed]
  rfl

end DiamondIntegral.Section6
