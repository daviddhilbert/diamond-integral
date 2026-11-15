import «section 5».Completed18RVOperations

/-! The exact positive RV semiring dictionary, before imposing the
special congruence. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def completed18RVDirectSumAddEquiv : GammaGroundRVDirectSum hc B ≃+
    GammaNonzeroGradedAt (B := B) (S := Set.univ) where
  toFun := DirectSum.map (fun k => (completed18RVClassAddEquiv (hc := hc) (B := B) (k := k)).toAddMonoidHom)
  invFun := DirectSum.map (fun k => (completed18RVClassAddEquiv (hc := hc) (B := B) (k := k)).symm.toAddMonoidHom)
  left_inv x := by
    apply DFinsupp.ext
    intro k
    exact (completed18RVClassAddEquiv (hc := hc) (B := B) (k := k)).symm_apply_apply (x k)
  right_inv x := by
    apply DFinsupp.ext
    intro k
    exact (completed18RVClassAddEquiv (hc := hc) (B := B) (k := k)).apply_symm_apply (x k)
  map_add' := (DirectSum.map (fun k => (completed18RVClassAddEquiv (hc := hc) (B := B) (k := k)).toAddMonoidHom)).map_add

theorem completed18RVDirectSumAddEquiv_of (k : ℕ) (x : GammaGroundRVKPlus hc B k) :
    completed18RVDirectSumAddEquiv (DirectSum.of (GammaGroundRVKPlus hc B) k x)=
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) k (groundRVClassNative x) :=
  DirectSum.map_of _ _ _

theorem groundRVClassNative_unit :
    groundRVClassNative (gammaGroundRVClass (GammaGroundRVObject.unit hc B)) =
      (GradedMonoid.GOne.one : GammaNonzeroClassesAt (B := B) (S := Set.univ) 0) := by
  rw [groundRVClassNative_class]
  apply Subtype.ext
  apply gammaIsoClassAt_iso
  apply groundRVAtToNativeIso _ (gammaUnitAt (B := B) (Set.subset_univ _))
    (fun u => Nat.eq_zero_of_le_zero (@rvWeight_le_arity M
      (@CanonicalStructure.normalize M sM) 0
      (@RVObject.value M (@CanonicalStructure.normalize M sM) Set.univ 0
        (gammaUnitAt (B := B) (Set.subset_univ _)).object.obj u)))
  apply GammaGroundBijection.ofCarrierEq
  rw [nativeRVGroundDomain_carrier]
  rfl

theorem completed18RVDirectSumAddEquiv_one :
    completed18RVDirectSumAddEquiv (hc := hc) (B := B) 1 = 1 := by
  change completed18RVDirectSumAddEquiv (DirectSum.of (GammaGroundRVKPlus hc B) 0
    (gammaGroundRVClass (GammaGroundRVObject.unit hc B)))=1
  rw [completed18RVDirectSumAddEquiv_of,groundRVClassNative_unit]
  rfl

theorem completed18RVDirectSumAddEquiv_mul (x y : GammaGroundRVDirectSum hc B) :
    completed18RVDirectSumAddEquiv (x*y)=
      completed18RVDirectSumAddEquiv x*completed18RVDirectSumAddEquiv y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul,map_zero]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero,map_zero]
    | of j b =>
      rw [DirectSum.of_mul_of,completed18RVDirectSumAddEquiv_of,
        completed18RVDirectSumAddEquiv_of,completed18RVDirectSumAddEquiv_of,DirectSum.of_mul_of]
      exact congrArg (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) (i+j))
        (groundRVClassNative_mul a b)
    | add y z hy hz => simp only [mul_add,map_add,hy,hz]
  | add x z hx hz => simp only [add_mul,map_add,hx,hz]

def completed18RVDirectSumEquiv : GammaGroundRVDirectSum hc B ≃+*
    GammaNonzeroGradedAt (B := B) (S := Set.univ) where
  __ := completed18RVDirectSumAddEquiv
  map_mul' := completed18RVDirectSumAddEquiv_mul

def completed18RVPositiveEquiv : GammaGroundRVPositiveSemiring hc B ≃+*
    GammaNonzeroGradedAt (B := B) (S := Set.univ) :=
  gammaGroundRVSemiringEquivDirectSum.trans completed18RVDirectSumEquiv

theorem completed18RVPositiveEquiv_class {k : ℕ} (U : GammaGroundRVObject hc B k) :
    completed18RVPositiveEquiv (gammaGroundRVSemiringClass U)=
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) k
        (gammaNonzeroClassAt (groundRVAt U) (groundRVAt_full U)) := by
  change completed18RVDirectSumAddEquiv (gammaGroundRVPresentationToDirectSum (gammaGroundRVSemiringClass U))=_
  rw [gammaGroundRVPresentationToDirectSum_class]
  exact (completed18RVDirectSumAddEquiv_of k _).trans
    (congrArg (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) k) (groundRVClassNative_class U))

end DiamondIntegral.Section5
