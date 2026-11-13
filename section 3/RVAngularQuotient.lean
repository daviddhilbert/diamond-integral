import «section 3».RVAngularCell
import «section 3».MixedValueQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rvUnitTupleValues {m : ℕ} (t : Fin m → (CanonicalRV.RVSort M)ˣ) : Fin m → Values.Gamma (M := M) :=
  fun i => rvUnitValueHom (t i)

namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def coordinateEquiv (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (Fin n → (CanonicalRV.RVSort M)ˣ) ≃
      (Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) × (Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :=
  (integerMonomialBasisEquiv E.basis).toEquiv.trans (coordinateProductChart K)

def coordinateImage (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) := coordinateEquiv E K '' A

theorem coordinateImage_fibre_invariant (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (s : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) (t u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ)
    (hst : (s,t) ∈ E.coordinateImage K) (htu : rvUnitTupleValues t = rvUnitTupleValues u) :
    (s,u) ∈ E.coordinateImage K := by
  obtain ⟨x,hx,hEx⟩ := hst
  let y := (E.coordinateEquiv K).symm (s,u)
  have hEy : E.coordinateEquiv K y = (s,u) := (E.coordinateEquiv K).apply_symm_apply _
  have hactive : ∀ i, integerMonomialBasisEquiv E.basis x (E.active i) = integerMonomialBasisEquiv E.basis y (E.active i) := by
    intro i
    obtain ⟨j,hj⟩ := coordinateProductChart_fixed_cover K (E.active i) (Set.mem_range_self i)
    rw [hj]
    exact (congrArg (fun z => z.1 j) hEx).trans (congrArg (fun z => z.1 j) hEy).symm
  have hfree : ∀ j, j ∉ Set.range E.active →
      rvUnitValueHom (integerMonomialBasisEquiv E.basis x j) = rvUnitValueHom (integerMonomialBasisEquiv E.basis y j) := by
    intro j hj
    obtain ⟨i,rfl⟩ := coordinateProductChart_free_cover K j hj
    have hhx := congrArg (fun z => z.2 i) hEx
    have hhy := congrArg (fun z => z.2 i) hEy
    change integerMonomialBasisEquiv E.basis x (K.freeIndex i) = t i at hhx
    change integerMonomialBasisEquiv E.basis y (K.freeIndex i) = u i at hhy
    rw [hhx,hhy]
    exact congrFun htu i
  exact ⟨y,E.invariant x hx y hactive hfree,hEy⟩

theorem full_value_preimage (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    mixedValueProjection rvUnitTupleValues ⁻¹' mixedValueQuotient rvUnitTupleValues (E.coordinateImage K) = E.coordinateImage K :=
  mixedValueQuotient_full_preimage rvUnitTupleValues _ (E.coordinateImage_fibre_invariant K)

theorem residue_tuple_values_finite (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ((fun x => fun i : Fin K.zeroArity => rvUnitValueHom (integerMonomialBasisEquiv E.basis x (K.zeroIndex i))) '' A).Finite := by
  have hv : ∀ i : Fin E.residueArity,
      ((fun x => rvUnitValueHom (integerMonomialBasisEquiv E.basis x (E.active i))) '' A).Finite := by
    intro i
    apply (E.finite_values.image (fun γ => γ i)).subset
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨_,⟨x,hx,rfl⟩,rfl⟩
  have hzero : ∀ i : Fin K.zeroArity,
      ((fun x => rvUnitValueHom (integerMonomialBasisEquiv E.basis x (K.zeroIndex i))) '' A).Finite := by
    intro i
    obtain ⟨j,hj⟩ := K.zero_mem i
    change E.active j = K.zeroIndex i at hj
    rw [← hj]
    exact hv j
  apply (Set.Finite.pi' hzero).subset
  rintro _ ⟨x,hx,rfl⟩ i
  exact ⟨x,hx,rfl⟩
end RVAngularCell
end DiamondIntegral.Section3
