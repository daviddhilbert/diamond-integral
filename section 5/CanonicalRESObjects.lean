import «section 3».RVDimensionBridge
import «section 3».GammaGroundRVCategories
import «section 5».EmptyGammaGround
import «section 5».DescendedFiniteValues

/-! Every finite-value original RV set is the literal domain of an actual
RES object. The finite label map replaces zero by one, without changing
the domain, its parameters, or its morphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvObjectOfSet {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    DiamondIntegral.Section3.RVObject S n where
  arity := n
  domain := A
  volume := cleanRVMap A
  finite := cleanRVMap_finite A
  nonzero a i := cleanRV_nonzero a.val i

def resObjectOfSet {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) : RESObject S n :=
  ⟨rvObjectOfSet A, by
    change ((fun t i => Values.vrv (t i)) '' A.carrier).Finite
    have he : ((fun t i => Values.vrv (t i)) '' A.carrier) =
        Set.range (fun u : A => fun i => Values.vrv (u.val i)) := by
      ext p
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, hr⟩, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨r.val, r.property, rfl⟩
    rw [he]
    exact hA⟩

def nativeRESObjectOfSet (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    GammaGroundRESObject hc (EmptyGammaGround.base S) n :=
  ⟨GammaGroundRVObject.ofReal (rvObjectOfSet A), (resObjectOfSet A hA).property⟩

def originalDomain (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k : ℕ}
    (U : GammaGroundRESObject hc (EmptyGammaGround.base S) k) :
    DefSet (rawRVSpace (M := M) U.obj.arity) S := EmptyGammaGround.toReal hc U.obj.domain

theorem originalDomain_finite_values (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {k : ℕ} (U : GammaGroundRESObject hc (EmptyGammaGround.base S) k) :
    (Set.range (fun u : originalDomain hc U => fun i => Values.vrv (u.val i))).Finite := by
  have he : Set.range (fun u : originalDomain hc U => fun i => Values.vrv (u.val i)) =
      ((fun t i => Values.vrv (t i)) '' U.obj.domain.carrier) := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [he]
  exact U.property

def originalDomainBijection (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {k : ℕ} {U V : GammaGroundRESObject hc (EmptyGammaGround.base S) k}
    (f : GammaGroundBijection U.obj.domain V.obj.domain) :
    DefinableBijection (originalDomain hc U) (originalDomain hc V) :=
  EmptyGammaGround.bijectionToReal hc f

namespace PuiseuxOriginal
local instance canonicalRESObjectsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def descendedRESObject {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    GammaGroundRESObject canonicalInterpret_isCanonical
      (EmptyGammaGround.base {c | baseCarrier c}) n :=
  nativeRESObjectOfSet canonicalInterpret_isCanonical (descendedOriginalSet N a X hX)
    (descendedOriginalSet_native_finite_values N a X hX)

theorem descendedRESObject_domain {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    originalDomain canonicalInterpret_isCanonical (descendedRESObject N a X hX) =
      descendedOriginalSet N a X hX := rfl

end PuiseuxOriginal
end DiamondIntegral.Section5
