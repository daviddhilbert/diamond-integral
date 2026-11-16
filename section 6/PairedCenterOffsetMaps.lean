import «section 6».LabelledCenterCores

/-! The target center family and its offset map are transported through
the original bijection, retaining their complete original-base graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable (f : Map A B) (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)

def matchedCenterImage : DefSet (rawMixedSpace (M := M) 1 s) S := (f.restrict hEA).image

def matchedCenterMap : Map E (matchedCenterImage f E hEA) := (f.restrict hEA).toImage

theorem matchedCenterImage_subset : (matchedCenterImage f E hEA).carrier ⊆ B.carrier := by
  rintro q ⟨p,hp⟩
  exact hp ▸ (f ⟨p.val,hEA p.property⟩).property

theorem matchedCenterMap_bijective (hf : Function.Injective f) : Function.Bijective (matchedCenterMap f E hEA) :=
  restrict_toImage_bijective f hf hEA

theorem matchedCenterMap_value (p : E) : (matchedCenterMap f E hEA p).val=(f ⟨p.val,hEA p.property⟩).val := rfl

def matchedTargetOffsetMap (hf : Function.Injective f)
    (e : Map E (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map (matchedCenterImage f E hEA) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  e.comp ((matchedCenterMap f E hEA).inverse (matchedCenterMap_bijective f E hEA hf))

theorem matchedTargetOffsetMap_at (hf : Function.Injective f)
    (e : Map E (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : E) :
    matchedTargetOffsetMap f E hEA hf e (matchedCenterMap f E hEA p)=e p := by
  change e ((matchedCenterMap f E hEA).inverse _ (matchedCenterMap f E hEA p))=e p
  rw [Map.inverse_apply]

theorem matchedTargetOffsetMap_nonzero (hf : Function.Injective f)
    (e : Map E (DefSet.univ (rawVFSpace (M := M) 1) S)) (he : ∀ p : E,(e p).val 0 ≠ 0)
    (q : matchedCenterImage f E hEA) : (matchedTargetOffsetMap f E hEA hf e q).val 0 ≠ 0 :=
  he ((matchedCenterMap f E hEA).inverse (matchedCenterMap_bijective f E hEA hf) q)

end DiamondIntegral.Section6
