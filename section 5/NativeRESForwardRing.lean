import «section 5».NativeRESForwardAdditive
import «section 5».RESForwardProducts

/-! The forward comparison on the actual native graded RES semiring
and its ring completion. All multiplicative laws are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance nativeRESForwardRingStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem nativeForwardValue_unit :
    nativeForwardValue (GammaGroundRESObject.unit canonicalInterpret_isCanonical originalPuiseuxGround) = 1 := by
  let A : DefSet (rawRVSpace (M := Carrier) 0) {c | baseCarrier c} := DefSet.univ _ _
  let U := GammaGroundRESObject.unit canonicalInterpret_isCanonical originalPuiseuxGround
  have hs : actualValuePatterns A ⊆ (↑({Fin.elim0} : Finset (Fin 0 → WithTop ℚ)) : Set _) := by
    rintro p ⟨u, rfl⟩
    exact Finset.mem_singleton.mpr (funext (fun i => Fin.elim0 i))
  have he : valuePatternObject A Fin.elim0 = DiagonalConstructible.unit := by
    have hw : valuePatternWeights (Fin.elim0 : Fin 0 → WithTop ℚ) = Fin.elim0 := funext (fun i => Fin.elim0 i)
    have hd : rationalFramedSet (valuePatternWeights (Fin.elim0 : Fin 0 → WithTop ℚ))
        (patternPiece A Fin.elim0) = Set.univ := by
      ext x
      constructor
      · intro _; exact Set.mem_univ _
      · intro _
        exact (patternPiece_mem_iff A Fin.elim0 _).mpr ⟨Set.mem_univ _, funext (fun i => Fin.elim0 i)⟩
    change DiagonalConstructible.Object.mk 0 _ _ _ _ = DiagonalConstructible.Object.mk 0 _ _ _ _
    congr 1
  have hv := forwardRESValue_eq_sum A (originalDomain_finite_values canonicalInterpret_isCanonical U) {Fin.elim0} hs
  change forwardRESValue A _ = 1
  rw [hv, Finset.sum_singleton]
  change DiagonalConstructible.objectClass (valuePatternObject A Fin.elim0) = 1
  rw [he, DiagonalConstructible.objectClass_unit]

theorem nativeForwardValue_product {k l : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k)
    (V : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround l) :
    nativeForwardValue (U.product V) = nativeForwardValue U * nativeForwardValue V := by
  let A := originalDomain canonicalInterpret_isCanonical U
  let B := originalDomain canonicalInterpret_isCanonical V
  have he : (originalDomain canonicalInterpret_isCanonical (U.product V)).carrier =
      (resSetProduct canonicalInterpret_isCanonical A B (originalDomain_finite_values _ U)
        (originalDomain_finite_values _ V)).carrier := rfl
  exact (forwardRESValue_congr _ _ _ _ he).trans (forwardRESValue_product A B _ _)

theorem nativeForwardPositive_one : nativeForwardPositive 1 = 1 := by
  change nativeForwardPositive (gammaGroundRESDirectSumClass
    (GammaGroundRESObject.unit canonicalInterpret_isCanonical originalPuiseuxGround)) = 1
  rw [nativeForwardPositive_class, nativeForwardValue_unit]

theorem nativeForwardPositive_mul
    (a b : GammaGroundRESDirectSum canonicalInterpret_isCanonical originalPuiseuxGround) :
    nativeForwardPositive (a * b) = nativeForwardPositive a * nativeForwardPositive b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of k a =>
    obtain ⟨U, rfl⟩ := gammaGroundRESClass_surjective a
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of l b =>
      obtain ⟨V, rfl⟩ := gammaGroundRESClass_surjective b
      change nativeForwardPositive (gammaGroundRESDirectSumClass U * gammaGroundRESDirectSumClass V) =
        nativeForwardPositive (gammaGroundRESDirectSumClass U) * nativeForwardPositive (gammaGroundRESDirectSumClass V)
      rw [← gammaGroundRESDirectSumClass_product, nativeForwardPositive_class, nativeForwardPositive_class,
        nativeForwardPositive_class, nativeForwardValue_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def nativeForwardPositiveRing :
    GammaGroundRESDirectSum canonicalInterpret_isCanonical originalPuiseuxGround →+* DiagonalConstructible.Ring where
  __ := nativeForwardPositive
  map_one' := nativeForwardPositive_one
  map_mul' := nativeForwardPositive_mul

def nativeForwardOrdinary : Section3RESClassCuts.OrdinaryRing canonicalInterpret_isCanonical originalPuiseuxGround →+*
    DiagonalConstructible.Ring := Algebra.GrothendieckAddGroup.liftRingHom nativeForwardPositiveRing

theorem nativeForwardOrdinary_class {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) :
    nativeForwardOrdinary (Section3RESClassCuts.ordinaryClass U) = nativeForwardValue U := by
  rw [nativeForwardOrdinary, Section3RESClassCuts.ordinaryClass,
    Algebra.GrothendieckAddGroup.liftRingHom_apply_of]
  exact nativeForwardPositive_class U

end DiamondIntegral.Section5.PuiseuxOriginal
