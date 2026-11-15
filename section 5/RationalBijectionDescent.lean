import «section 5».RationalFrameComparison
import «section 5».NativeRESClasses

/-! An arbitrary equivariant constructible bijection descends to a
same-base original-language bijection and equality of actual RES classes.
The two objects may have different denominators, arities, and degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance rationalBijectionDescentStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def rationalObjectBijection {X Y : DiagonalConstructible.Object} (f : DiagonalConstructible.Iso X Y) :
    DefinableBijection (rationalDescendedSet X.weights X.domain X.definable)
      (rationalDescendedSet Y.weights Y.domain Y.definable) := by
  let F := rationalFraming (Fin.append X.weights Y.weights)
  let a : Fin X.arity → ℤ := fun i => F.weights (Fin.castAdd Y.arity i)
  let b : Fin Y.arity → ℤ := fun i => F.weights (Fin.natAdd X.arity i)
  have hq : ∀ i, X.weights i = (a i : ℚ) / (F.level : ℕ) := by
    intro i
    simpa only [Fin.append_left] using F.equation (Fin.castAdd Y.arity i)
  have hr : ∀ i, Y.weights i = (b i : ℚ) / (F.level : ℕ) := by
    intro i
    simpa only [Fin.append_right] using F.equation (Fin.natAdd X.arity i)
  have hiX : FiniteInvariant F.level a X.domain := (rationalInvariant_iff_finite _ _ _).mp
    (by simpa only [← funext hq] using X.invariant)
  have hiY : FiniteInvariant F.level b Y.domain := (rationalInvariant_iff_finite _ _ _).mp
    (by simpa only [← funext hr] using Y.invariant)
  have hab : (Fin.append X.weights Y.weights) =
      fun i => ((Fin.append a b i : ℤ) : ℚ) / (F.level : ℕ) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hq j
    · simpa only [Fin.append_right] using hr j
  have hiG : FiniteInvariant F.level (Fin.append a b)
      (framedEquivGraph X.domain Y.domain f.equiv) :=
    (rationalInvariant_iff_finite _ _ _).mp (by simpa only [← hab] using f.graph_invariant)
  have extD {n : ℕ} (A B : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
      (h : A.carrier = B.carrier) : A = B := by
    cases A
    cases B
    cases h
    rfl
  have hx : rationalDescendedSet X.weights X.domain X.definable =
      descendedOriginalSet F.level a X.domain X.definable := by
    apply extD
    exact rationalDescendedSet_eq_finite _ _ _ hq _ _ X.invariant
  have hy : rationalDescendedSet Y.weights Y.domain Y.definable =
      descendedOriginalSet F.level b Y.domain Y.definable := by
    apply extD
    exact rationalDescendedSet_eq_finite _ _ _ hr _ _ Y.invariant
  rw [hx, hy]
  exact originalDescendedBijection F.level a b X.domain Y.domain X.definable Y.definable
    hiX hiY f.equiv f.graph_definable hiG

def diagonalRESClass (X : DiagonalConstructible.Object) :
    RESDimensionFreeRing.Ring (EmptyGammaGround.base {c | baseCarrier c}) :=
  resSetClass canonicalInterpret_isCanonical (rationalDescendedSet X.weights X.domain X.definable)
    (rationalDescendedSet_finite_values _ _ _)

theorem diagonalRESClass_iso {X Y : DiagonalConstructible.Object} (f : DiagonalConstructible.Iso X Y) :
    diagonalRESClass X = diagonalRESClass Y :=
  resSetClass_bijection canonicalInterpret_isCanonical _ _ _ _ (rationalObjectBijection f)

end DiamondIntegral.Section5.PuiseuxOriginal
