import «section 3».GammaGroundMapPreimages

/-! Actual native maps pull a finite target partition back to a finite
original-ground partition of their source. No target points or additional
parameters are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {Q R : Space LRV M} {A : GammaGroundDefSet hc B Q} {C : GammaGroundDefSet hc B R}

theorem nativeMap_preimage_disjoint (f : GammaGroundMap A C)
    (D E : GammaGroundDefSet hc B R) (hd : Disjoint D.carrier E.carrier) :
    Disjoint (f.preimage D).carrier (f.preimage E).carrier := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hD⟩ ⟨b,hb,hE⟩
  have he : b = a := Subtype.ext (hb.trans ha.symm)
  rw [he] at hE
  exact Set.disjoint_left.mp hd hD hE

theorem nativeMap_preimage_cover (f : GammaGroundMap A C) {ι : Type}
    (D : ι → GammaGroundDefSet hc B R)
    (hcov : ∀ y,y ∈ C.carrier ↔ ∃ i,y ∈ (D i).carrier) (x : Q.Carrier) :
    x ∈ A.carrier ↔ ∃ i,x ∈ (f.preimage (D i)).carrier := by
  constructor
  · intro hx
    let a : A := ⟨x,hx⟩
    obtain ⟨i,hi⟩ := (hcov (f a).val).mp (f a).property
    exact ⟨i,a,rfl,hi⟩
  · rintro ⟨i,hi⟩
    exact f.preimage_subset (D i) hi

theorem nativeMap_preimage_partition (f : GammaGroundMap A C) {ι : Type}
    (D : ι → GammaGroundDefSet hc B R)
    (hd : ∀ i j,i ≠ j → Disjoint (D i).carrier (D j).carrier)
    (hcov : ∀ y,y ∈ C.carrier ↔ ∃ i,y ∈ (D i).carrier) :
    (∀ i j,i ≠ j → Disjoint (f.preimage (D i)).carrier (f.preimage (D j)).carrier) ∧
      ∀ x,x ∈ A.carrier ↔ ∃ i,x ∈ (f.preimage (D i)).carrier :=
  ⟨fun i j hij => nativeMap_preimage_disjoint f (D i) (D j) (hd i j hij),nativeMap_preimage_cover f D hcov⟩

end DiamondIntegral.Section5
