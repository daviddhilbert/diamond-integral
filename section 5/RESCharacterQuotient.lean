import «section 5».RESFibreComparison

/-! The actual native RES fibre ideal corresponds exactly to the
character-line ideal. Rational value names are proved definable from
original-language value-pattern sets, without naming any Kummer root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance resCharacterQuotientStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem rationalGamma_definable (q : ℚ) :
    GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround (rationalGamma q) := by
  apply (GammaOrderLogic.unary_definable_iff originalPuiseuxGround {rationalGamma q}).mp
  let A := patternSet (fun _ : Fin 1 => (q : WithTop ℚ))
  let D : GammaGroundDefSet canonicalInterpret_isCanonical originalPuiseuxGround (rawRVSpace (M := Carrier) 1) :=
    GammaGroundDefSet.ofReal A
  have hD := D.definable.toRVBase
  change GammaParameters.DefinableOverBase originalPuiseuxGround (fun _ : Fin 1 => .rv)
    {z | GammaParameters.Proper z ∧ GammaParameters.codeValue (z 0) = rationalGamma q}
  have he : rvValues '' A.carrier =
      {z : Fin 1 → Carrier | GammaParameters.Proper z ∧ GammaParameters.codeValue (z 0) = rationalGamma q} := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hv := (patternSet_mem_iff (fun _ : Fin 1 => (q : WithTop ℚ)) r).mp hr
      have hz (i : Fin 1) : (r i).val ≠ iRVZero := by
        intro hi
        have hn := (rv_normal_eq_none_iff (r i)).mpr hi
        have hh := congrFun hv i
        simp only [hn, value, WithTop.top_ne_coe] at hh
      let c : GammaParameters.Code (M := Carrier) := ⟨r 0, hz 0⟩
      have hg : GammaParameters.value c = rationalGamma q := by
        apply Subtype.ext
        apply (gammaRational_vrv_iff (rationalGamma q) (r 0)).mpr
        simpa only [gammaRational_rationalGamma] using congrFun hv 0
      exact ⟨(fun i => ⟨(r i).property, hz i⟩), (GammaParameters.codeValue_raw c).trans hg⟩
    · rintro ⟨hz, hv⟩
      let r : Fin 1 → CanonicalRV.RVSort Carrier := fun i => ⟨z i, (hz i).1⟩
      let c : GammaParameters.Code (M := Carrier) := ⟨r 0, (hz 0).2⟩
      have hg : GammaParameters.value c = rationalGamma q := (GammaParameters.codeValue_raw c).symm.trans hv
      have hm : r ∈ A.carrier := by
        apply (patternSet_mem_iff (fun _ : Fin 1 => (q : WithTop ℚ)) r).mpr
        funext i
        have h := (gammaRational_vrv_iff (rationalGamma q) (r 0)).mp (congrArg Subtype.val hg)
        rw [gammaRational_rationalGamma] at h
        exact (congrArg (fun j => value (taggedRVEquiv (r j))) (Subsingleton.elim i 0)).trans h
      exact ⟨r, hm, rfl⟩
  exact he ▸ hD

theorem fibreIdeal_image_eq_lineIdeal :
    Ideal.map rawRESComparison.toRingHom (RESDimensionFreeReduction.fibreIdeal originalPuiseuxGround) =
      DiagonalConstructible.lineIdeal := by
  apply le_antisymm fibreIdeal_image_le_lineIdeal
  apply Ideal.span_le.mpr
  rintro x ⟨q, rfl⟩
  let α := rationalGamma q
  let hα := rationalGamma_definable q
  let a := RESFibreObjects.fibre originalPuiseuxGround α 1 hα (GammaGroupNames.one_definable_base originalPuiseuxGround)
  have h : RESOrdinaryRing.objectClass a - RESOrdinaryRing.objectClass (RESFibreObjects.torus originalPuiseuxGround) ∈
      RESOrdinaryReduction.fibreIdeal originalPuiseuxGround := Ideal.subset_span ⟨α, hα, rfl⟩
  have h' := Ideal.mem_map_of_mem (RESDimensionFreeRing.quotient originalPuiseuxGround) h
  have h'' := Ideal.mem_map_of_mem rawRESComparison.toRingHom h'
  change rawRESComparison (RESDimensionFreeRing.objectClass a -
    RESDimensionFreeRing.objectClass (RESFibreObjects.torus originalPuiseuxGround)) ∈ _ at h''
  rw [rawRESComparison_fibre_difference, gammaRational_rationalGamma] at h''
  exact h''

def reducedDiagonalRing := DiagonalConstructible.Ring ⧸ DiagonalConstructible.lineIdeal
  deriving CommRing

def residueCharacterComparison : RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* reducedDiagonalRing :=
  Ideal.quotientEquiv (RESDimensionFreeReduction.fibreIdeal originalPuiseuxGround)
    DiagonalConstructible.lineIdeal rawRESComparison fibreIdeal_image_eq_lineIdeal.symm

theorem residueCharacterComparison_mk (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    residueCharacterComparison (RESDimensionFreeReduction.quotient originalPuiseuxGround x) =
      Ideal.Quotient.mk DiagonalConstructible.lineIdeal (rawRESComparison x) := rfl

end DiamondIntegral.Section5.PuiseuxOriginal
