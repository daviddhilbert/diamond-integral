import «section 5».CanonicalRESObjects
import «section 4».Section3RESRingEquivalences
import «section 4».RESDimensionFreeRing

/-! Actual ungraded RES classes forget auxiliary finite label maps through
proved original-base bijections, including between different degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def nativeUngradedClass (hc : CanonicalStructure.IsCanonical (M := M))
    {B : GammaParameters.Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k) :
    RESDimensionFreeRing.Ring B :=
  RESDimensionFreeRing.objectClass (Section3RVChartBridge.chartRES U)

def nativeUngradedHom (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) : Section3RESClassCuts.OrdinaryRing hc B →+*
      RESDimensionFreeRing.Ring B :=
  (RESDimensionFreeRing.quotient B).comp (Section3RESRingEquivalences.ordinary hc B).symm.toRingHom

theorem nativeUngradedHom_class (hc : CanonicalStructure.IsCanonical (M := M))
    {B : GammaParameters.Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k) :
    nativeUngradedHom hc B (Section3RESClassCuts.ordinaryClass U) = nativeUngradedClass hc U := by
  change RESDimensionFreeRing.quotient B
    ((Section3RESRingEquivalences.ordinary hc B).symm (Section3RESClassCuts.ordinaryClass U)) = _
  rw [Section3RESRingEquivalences.ordinary_symm_class]
  rfl

theorem nativeUngradedClass_product (hc : CanonicalStructure.IsCanonical (M := M))
    {B : GammaParameters.Base (M := M)} {k l : ℕ}
    (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) :
    nativeUngradedClass hc (U.product V) = nativeUngradedClass hc U * nativeUngradedClass hc V := by
  rw [← nativeUngradedHom_class, ← nativeUngradedHom_class, ← nativeUngradedHom_class, ← map_mul]
  apply congrArg (nativeUngradedHom hc B)
  simp only [Section3RESClassCuts.ordinaryClass, gammaGroundRESDirectSumClass_product]
  exact Algebra.GrothendieckAddGroup.ofRingHom.map_mul _ _

theorem nativeUngradedClass_cut (hc : CanonicalStructure.IsCanonical (M := M))
    {B : GammaParameters.Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) :
    nativeUngradedClass hc (U.restrict X hX) +
      nativeUngradedClass hc (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) =
        nativeUngradedClass hc U := by
  rw [← nativeUngradedHom_class, ← nativeUngradedHom_class, ← nativeUngradedHom_class, ← map_add]
  exact congrArg (nativeUngradedHom hc B) (Section3RESClassCuts.ordinary_cut U X hX)

theorem nativeUngradedClass_empty (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (k : ℕ) :
    nativeUngradedClass hc (GammaGroundRESObject.empty hc B k) = 0 := by
  rw [← nativeUngradedHom_class, Section3RESClassCuts.ordinary_empty, map_zero]

theorem nativeUngradedClass_unit (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) :
    nativeUngradedClass hc (GammaGroundRESObject.unit hc B) = 1 := by
  rw [← nativeUngradedHom_class]
  exact (nativeUngradedHom hc B).map_one

theorem nativeUngradedClass_bijection (hc : CanonicalStructure.IsCanonical (M := M))
    {B : GammaParameters.Base (M := M)} {k l : ℕ}
    (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l)
    (f : GammaGroundBijection U.obj.domain V.obj.domain) :
    nativeUngradedClass hc U = nativeUngradedClass hc V := by
  apply RESDimensionFreeRing.objectClass_iso
  exact RVUnderlyingIsomorphisms.ofMap _ _ (Section3RVCodeBridge.rawMap f.map)
    (Section3RVCodeBridge.rawMap_definable f.map)
    (Section3RVCodeBridge.rawMap_bijective f.map f.bijective)

def resSetClass (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    RESDimensionFreeRing.Ring (EmptyGammaGround.base S) :=
  nativeUngradedClass hc (nativeRESObjectOfSet hc A hA)

theorem resSetClass_bijection (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n m : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (B : DefSet (rawRVSpace (M := M) m) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (f : DefinableBijection A B) : resSetClass hc A hA = resSetClass hc B hB :=
  nativeUngradedClass_bijection hc _ _ (EmptyGammaGround.bijectionFromReal hc f)

theorem resSetClass_originalDomain (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {k : ℕ} (U : GammaGroundRESObject hc (EmptyGammaGround.base S) k) :
    resSetClass hc (originalDomain hc U) (originalDomain_finite_values hc U) =
      nativeUngradedClass hc U := by
  apply nativeUngradedClass_bijection
  exact GammaGroundBijection.id U.obj.domain

theorem resSetClass_congr (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ}
    (A B : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (he : A.carrier = B.carrier) : resSetClass hc A hA = resSetClass hc B hB := by
  have hab : A = B := by cases A; cases B; cases he; rfl
  subst B
  rfl

end DiamondIntegral.Section5
