import «section 3».RVGlobalFreeValues
import «section 3».MixedValueQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (D : LiteralDNF I R (Fin n)) (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (p : RVDNFGlobalPattern D) {q : ℕ}
    (F : Module.Basis.SmithNormalForm (Submodule.span ℤ (rvDNFPatternCharacters D a r p)) (Fin n) q)
    (K : Section2.ZeroFaceChart (Set.range F.f))

def rvPatternCoordinateEquiv : (Fin n → (CanonicalRV.RVSort M)ˣ) ≃
    (Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) × (Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :=
  (integerMonomialBasisEquiv F.bM).toEquiv.trans (coordinateProductChart K)

def rvPatternCoordinateImage := rvPatternCoordinateEquiv D a r p F K '' rvDNFPatternCell D a r p

def rvPatternFreeValueMap (t : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :
    Fin K.freeArity → Values.Gamma (M := M) := fun i => rvUnitValueHom (t i)

theorem rvPatternCoordinateImage_fibre_invariant
    (s : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ)
    (t u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ)
    (hst : (s,t) ∈ rvPatternCoordinateImage D a r p F K)
    (htu : rvPatternFreeValueMap D a r p F K t = rvPatternFreeValueMap D a r p F K u) :
    (s,u) ∈ rvPatternCoordinateImage D a r p F K := by
  obtain ⟨x,hx,hEx⟩ := hst
  let E := rvPatternCoordinateEquiv D a r p F K
  let y := E.symm (s,u)
  have hEy : E y = (s,u) := E.apply_symm_apply _
  have hactive : ∀ i, integerMonomialBasisEquiv F.bM x (K.zeroIndex i) =
      integerMonomialBasisEquiv F.bM y (K.zeroIndex i) := by
    intro i
    have hhx := congrArg (fun z => z.1 i) hEx
    have hhy := congrArg (fun z => z.1 i) hEy
    exact hhx.trans hhy.symm
  have hfree : ∀ i, rvUnitValueHom (integerMonomialBasisEquiv F.bM x (K.freeIndex i)) =
      rvUnitValueHom (integerMonomialBasisEquiv F.bM y (K.freeIndex i)) := by
    intro i
    have hhx := congrArg (fun z => z.2 i) hEx
    have hhy := congrArg (fun z => z.2 i) hEy
    change integerMonomialBasisEquiv F.bM x (K.freeIndex i) = t i at hhx
    change integerMonomialBasisEquiv F.bM y (K.freeIndex i) = u i at hhy
    rw [hhx,hhy]
    exact congrFun htu i
  exact ⟨y,rvDNFPatternCell_chart_invariant D a r p F K x y hx hactive hfree,hEy⟩

theorem rvPatternCoordinateImage_full_value_preimage :
    mixedValueProjection (rvPatternFreeValueMap D a r p F K) ⁻¹'
      mixedValueQuotient (rvPatternFreeValueMap D a r p F K) (rvPatternCoordinateImage D a r p F K) =
        rvPatternCoordinateImage D a r p F K :=
  mixedValueQuotient_full_preimage (rvPatternFreeValueMap D a r p F K) _ (rvPatternCoordinateImage_fibre_invariant D a r p F K)

/-- The residue tuple of the mixed quotient has finite actual Gamma
support. The free coordinates remain full value fibres. -/
theorem rvPattern_residue_tuple_values_finite :
    ((fun x => fun i : Fin K.zeroArity => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (K.zeroIndex i))) ''
      rvDNFPatternCell D a r p).Finite := by
  have hv : ∀ i : Fin q,
      ((fun x => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (F.f i))) '' rvDNFPatternCell D a r p).Finite :=
    smith_basis_coordinate_values_finite _ _ F
      (characterValueImage_span_finite _ _ _ (rvDNFPatternCharacters_value_finite D a r p))
  have hzero : ∀ i : Fin K.zeroArity,
      ((fun x => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (K.zeroIndex i))) '' rvDNFPatternCell D a r p).Finite := by
    intro i
    obtain ⟨j,hj⟩ := K.zero_mem i
    change F.f j = K.zeroIndex i at hj
    rw [← hj]
    exact hv j
  apply (Set.Finite.pi' hzero).subset
  rintro _ ⟨x,hx,rfl⟩ i
  exact ⟨x,hx,rfl⟩
end DiamondIntegral.Section3
