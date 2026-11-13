import «section 3».RVUnitPresentationBridge
import «section 3».RVAngularQuotient
import «section 3».IntegrationGammaParameters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvUnitDomain_preimage (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    (rawRVUnitSpace n).preimage X.carrier = rvUnitValues '' X.carrier := by
  ext z
  constructor
  · rintro ⟨hz,hx⟩
    exact ⟨(rawRVUnitSpace n).decode ⟨z,hz⟩,hx,rvUnitValues_decode _⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Set.mem_range_self x,by rwa [decode_rvUnitValues]⟩

theorem rvUnitDomain_raw_definable (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    S.Definable LRV (rvUnitValues '' X.carrier) := by
  rw [← rvUnitDomain_preimage]
  exact X.definable

theorem rvUnitDomain_native_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    DefinableOver S (fun _ => .rv) (rvUnitValues '' X.carrier) := by
  apply (definableOver_iff_normalized_raw S (fun _ => .rv) _).mpr
  constructor
  · rw [canonical_normalize_eq hc]
    exact rvUnitDomain_raw_definable X
  · rintro z ⟨x,hx,rfl⟩ i
    exact (x i).val.property

def rvUnitCoordinateDomain (X : DefSet (rawRVUnitSpace (M := M) n) S) (i : Fin n) : Set M :=
  (fun z => z i) '' (rvUnitValues '' X.carrier)

theorem rvUnitCoordinateDomain_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (i : Fin n) :
    DefinableAt S .rv (rvUnitCoordinateDomain X i) := by
  apply (definableAt_iff_normalized_raw S .rv _).mpr
  constructor
  · rw [canonical_normalize_eq hc]
    have hh := (rvUnitDomain_raw_definable X).image_comp (fun _ : Fin 1 => i)
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ rvUnitCoordinateDomain X i}
    convert hh using 1
    ext z
    change (∃ a ∈ rvUnitValues '' X.carrier, a i = z 0) ↔
      ∃ a ∈ rvUnitValues '' X.carrier, (fun _ : Fin 1 => a i) = z
    exact ⟨fun ⟨a,ha,he⟩ => ⟨a,ha,funext (fun j => by have hj : j = (0 : Fin 1) := Subsingleton.elim _ _; subst j; exact he)⟩,
      fun ⟨a,ha,he⟩ => ⟨a,ha,congrFun he 0⟩⟩
  · rintro z ⟨a,⟨x,hx,rfl⟩,rfl⟩
    exact (x i).val.property

theorem rvUnitCoordinateDomain_finite_values (X : DefSet (rawRVUnitSpace (M := M) n) S)
    (hX : (rvUnitTupleValues '' X.carrier).Finite) (i : Fin n) :
    (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ rvUnitCoordinateDomain X i}).Finite := by
  apply (hX.image (fun γ => (γ i).val)).subset
  rintro v ⟨t,⟨a,⟨x,hx,rfl⟩,he⟩,rfl⟩
  refine ⟨rvUnitTupleValues x,⟨x,hx,rfl⟩,?_⟩
  change Values.vrv (x i).val = Values.vrv t
  exact congrArg Values.vrv (Subtype.ext he)
end DiamondIntegral.Section3
