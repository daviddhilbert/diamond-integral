import «section 3».GammaGroundRVUnitDomains
import Section3.GammaProjection
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def rvUnitRawCoordinateImage (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (i : Fin n) : Set M :=
  (fun z => z i) '' (rvUnitValues '' A)

theorem gammaGroundRVUnitCoordinate_definable (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (i : Fin n) :
    DefinableAtBase B .rv (rvUnitRawCoordinateImage A.carrier i) := by
  have hA := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  have hh := hA.image_real (fun _ : Fin 1 => i)
  have he : {z : Fin 1 → M | z 0 ∈ rvUnitRawCoordinateImage A.carrier i} =
      (fun x : Fin n → M => x ∘ (fun _ : Fin 1 => i)) '' (rvUnitValues '' A.carrier) := by
    ext z
    change (∃ a ∈ rvUnitValues '' A.carrier, a i = z 0) ↔
      ∃ a ∈ rvUnitValues '' A.carrier, (fun _ : Fin 1 => a i) = z
    exact ⟨fun ⟨a,ha,he⟩ => ⟨a,ha,funext (fun j => by have hj : j = (0 : Fin 1) := Subsingleton.elim _ _; subst j; exact he)⟩,
      fun ⟨a,ha,he⟩ => ⟨a,ha,congrFun he 0⟩⟩
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ rvUnitRawCoordinateImage A.carrier i}
  rw [he]
  exact hh

theorem rvUnitRawCoordinateImage_finite_values (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hA : (rvUnitTupleValues '' A).Finite) (i : Fin n) :
    (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ rvUnitRawCoordinateImage A i}).Finite := by
  apply (hA.image (fun γ => (γ i).val)).subset
  rintro v ⟨t,⟨a,⟨x,hx,rfl⟩,he⟩,rfl⟩
  refine ⟨rvUnitTupleValues x,⟨x,hx,rfl⟩,?_⟩
  change Values.vrv (x i).val = Values.vrv t
  exact congrArg Values.vrv (Subtype.ext he)
end DiamondIntegral.Section3
