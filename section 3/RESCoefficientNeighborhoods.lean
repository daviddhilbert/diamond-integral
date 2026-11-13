import «section 3».GammaGroundPointUniformization
import «section 3».GammaGroundRVFiniteValueFibres
import «section 3».GammaGroundMapPreimages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Values of coordinatewise definable RV-unit points are definable
Gamma points, proved by the actual singleton image under the value map. -/
theorem gammaGroundRVUnitTuple_point_values_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (c : Fin m → (CanonicalRV.RVSort M)ˣ)
    (hcdef : ∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) :
    ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues c j) := by
  let D : GammaGroundDefSet hc B (rawRVUnitSpace m) :=
    ⟨{c},gammaGroundRVUnitTuple_point_definable c hcdef⟩
  let v := GammaGroundMap.ofGlobal D (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
    (rvUnitGammaMap hc B.real m) (fun _ => Set.mem_univ _)
  have he : v.image.carrier = {rvUnitTupleValues c} := by
    ext γ
    constructor
    · rintro ⟨a,ha⟩
      have ha0 : a.val = c := a.property
      change rvUnitTupleValues a.val = γ at ha
      exact ha.symm.trans (congrArg rvUnitTupleValues ha0)
    · intro hγ
      have hγ0 : γ = rvUnitTupleValues c := hγ
      exact ⟨⟨c,rfl⟩,hγ0.symm⟩
  have hfin : v.image.carrier.Finite := he.symm ▸ Set.finite_singleton _
  have hmem : rvUnitTupleValues c ∈ v.image.carrier := he.symm ▸ Set.mem_singleton _
  exact gammaGroundGamma_finite_tuple_point_definable v.image hfin (rvUnitTupleValues c) hmem

/-- A coefficient over B(r), with r in a finite-value-support RES domain,
uniformizes over B on a definable subset through r with constant value
and original-ground definable value coordinates. -/
theorem gammaGroundRES_coefficient_constant_value_neighborhood {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (r : R)
    (c : Fin m → (CanonicalRV.RVSort M)ˣ)
    (hcdef : ∀ j, DefinableClosureAtBase (adjoinRVUnitTuple B r.val) .rv (rvUnitValues c j)) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n)) (_hsub : A.carrier ⊆ R.carrier)
      (hr : r.val ∈ A.carrier)
      (f : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m))),
      (f ⟨r.val,hr⟩).val = c ∧
      (∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues c j)) ∧
      (∀ a : A, rvUnitTupleValues (f a).val = rvUnitTupleValues c) := by
  have hδC := gammaGroundRVUnitTuple_point_values_definable (hc := hc) c hcdef
  have hδ : ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues c j) := fun j =>
    (gammaGroundRVUnit_residue_gamma_closure_iff hκ hs h00 hsmall R hR r _).mp (hδC j)
  obtain ⟨D,hrD,f,hfc⟩ := gammaGroundRVUnitCoefficient_function r.val c hcdef
  let V := gammaGroundRVUnitValueFibre (GammaGroundDefSet.univ hc B (rawRVUnitSpace m))
    (rvUnitTupleValues c) hδ
  let E := f.preimage V
  let A := R.inter E
  have hsub : A.carrier ⊆ R.carrier := fun _ h => h.1
  have hAD : A.carrier ⊆ D.carrier := fun _ h => f.preimage_subset V h.2
  have hrA : r.val ∈ A.carrier := by
    refine ⟨r.property,⟨⟨r.val,hrD⟩,rfl,?_⟩⟩
    exact ⟨Set.mem_univ _,congrArg rvUnitTupleValues hfc⟩
  refine ⟨A,hsub,hrA,f.restrict hAD,hfc,hδ,?_⟩
  intro a
  obtain ⟨b,hba,hbV⟩ := a.property.2
  have he : (⟨a.val,hAD a.property⟩ : D) = b := Subtype.ext hba.symm
  change rvUnitTupleValues (f ⟨a.val,hAD a.property⟩).val = rvUnitTupleValues c
  rw [he]
  exact hbV.2
end DiamondIntegral.Section3
