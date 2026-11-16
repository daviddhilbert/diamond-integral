import «section 6».CarriedMapDerivatives

/-! A small exceptional set remains small when its coordinate disc is
carried along. The actual exceptional bundle is definable over the same
base and retains the precise pointwise derivative condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem not_mem_small_set_of_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) n r) S)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n)
    (p : Mixed M n r) (hInd : AlgebraicIndependent (vfParameterField S) p.1) : p ∉ E.carrier := by
  intro hp
  have hRank : vfTupleTrdeg S p.1=(n : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) p.1).mpr hInd
  have hLe := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) E ⟨p,hp⟩
  rw [hRank] at hLe
  have hn : n ≤ vfDim (rawRVSpace (M := M) 1) E := by exact_mod_cast hLe
  exact (not_lt_of_ge hn) hDim

theorem carried_exception_dim_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (E : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n) :
    vfDim (rawRVSpace (M := M) 1) (rvCoordinateBundle E k) < n+1 := by
  apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) (Nat.zero_lt_succ n)
  intro p hInd
  have hHead : AlgebraicIndependent (vfParameterField S) (Fin.init p.val.1) :=
    hInd.comp Fin.castSucc (Fin.castSucc_injective n)
  exact not_mem_small_set_of_independent hc E hDim (Fin.init p.val.1,p.val.2) hHead p.property.1

theorem carryLastMap_unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hA : ProperInvariant S A.carrier) (k : Fin r) (l : Fin s)
    (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hEA : E.carrier ⊆ A.carrier)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n)
    (hUnit : ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p) :
    (rvCoordinateBundle E k).carrier ⊆ (rvCoordinateBundle A k).carrier ∧
      vfDim (rawRVSpace (M := M) 1) (rvCoordinateBundle E k) < n+1 ∧
      ∀ p : rvCoordinateBundle A k,p.val ∉ (rvCoordinateBundle E k).carrier →
        HasMixedUnitDerivativeAt (carryLastMap f k l hLabels) p := by
  refine ⟨fun _ hp => ⟨hEA hp.1,hp.2⟩,carried_exception_dim_lt hc hs hsmall E k hDim,?_⟩
  intro p hp
  apply carryLastMap_unit_derivative h00 hc hκ hs hv f hA k l hLabels p
  apply hUnit
  intro hMem
  exact hp ⟨hMem,p.property.2⟩

end DiamondIntegral.Section6
