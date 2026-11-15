import «section 5».DiagonalConstructibleRing
import «section 5».CanonicalRESObjects
import «section 5».OriginalBijectionDescent

/-! Denominator-independent framing and descent on actual original RV
sets. These constructions retain all zero coordinates and the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance rationalFrameComparisonStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

structure RationalFraming {n : ℕ} (q : Fin n → ℚ) where
  level : ℕ+
  weights : Fin n → ℤ
  equation : ∀ i, q i = (weights i : ℚ) / (level : ℕ)

theorem rationalFraming_nonempty {n : ℕ} (q : Fin n → ℚ) : Nonempty (RationalFraming q) := by
  obtain ⟨N, a, h⟩ := rational_tuple_common_level n q
  exact ⟨⟨N, a, h⟩⟩

def rationalFraming {n : ℕ} (q : Fin n → ℚ) : RationalFraming q :=
  Classical.choice (rationalFraming_nonempty q)

def rationalFrame {n : ℕ} (q : Fin n → ℚ) (x : Fin n → ℂ) :
    Fin n → CanonicalRV.RVSort Carrier := fun i => rvTag (linePoint (q i) (x i))

theorem rationalFrame_common_level {n : ℕ} (q : Fin n → ℚ) (N : ℕ+) (a : Fin n → ℤ)
    (hq : ∀ i, q i = (a i : ℚ) / (N : ℕ)) (x : Fin n → ℂ) :
    rationalFrame q x = fun i => rvTag (finiteFrame N a x i) := by
  funext i
  rw [rationalFrame, hq i]
  rfl

theorem rationalFrame_injective {n : ℕ} (q : Fin n → ℚ) : Function.Injective (rationalFrame q) := by
  intro x y h
  funext i
  have he : linePoint (q i) (x i) = linePoint (q i) (y i) :=
    congrArg taggedRVEquiv (congrFun h i)
  simpa only [lineCoefficient_point] using congrArg lineCoefficient he

def rationalFramedSet {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) : Set (Fin n → ℂ) :=
  {x | rationalFrame q x ∈ A.carrier}

theorem rationalFramedSet_eq_finite {n : ℕ} (q : Fin n → ℚ) (N : ℕ+) (a : Fin n → ℤ)
    (hq : ∀ i, q i = (a i : ℚ) / (N : ℕ))
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) :
    rationalFramedSet q A = framedRVSet N a A := by
  ext x
  change rationalFrame q x ∈ A.carrier ↔ _
  rw [rationalFrame_common_level q N a hq]
  rfl

def framedObject {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) : DiagonalConstructible.Object where
  arity := n
  weights := q
  domain := rationalFramedSet q A
  definable := by
    rw [rationalFramedSet_eq_finite q (rationalFraming q).level (rationalFraming q).weights
      (rationalFraming q).equation]
    exact framedRVSet_pure_definable _ _ A
  invariant := by
    have he := funext (rationalFraming q).equation
    rw [he, rationalFramedSet_eq_finite _ (rationalFraming q).level (rationalFraming q).weights
      (fun _ => rfl), rationalInvariant_iff_finite]
    exact framedRVSet_finiteInvariant _ _ A

def rationalDescendedSet {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} :=
  descendedOriginalSet (rationalFraming q).level (rationalFraming q).weights X hX

theorem finiteDescent_mem_image {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hiX : FiniteInvariant N a X) (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (descendedOriginalSet N a X hX).carrier ↔
      ∃ x ∈ X, (fun i => rvTag (finiteFrame N a x i)) = r := by
  let v : Fin n → RV := fun i => taggedRVEquiv (r i)
  have hr : (fun i => rvTag (v i)) = r :=
    funext (fun i => taggedRVEquiv.symm_apply_apply (r i))
  have hm := descendedOriginalSet_normalized_mem N a X hX v
  rw [hr, descendSet_eq_image N a X hiX] at hm
  rw [hm]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, (congrArg (fun z => fun i => rvTag (z i)) he).trans hr⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, funext (fun i => congrArg taggedRVEquiv (congrFun he i))⟩

theorem rationalDescent_mem_image {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X)
    (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (rationalDescendedSet q X hX).carrier ↔ ∃ x ∈ X, rationalFrame q x = r := by
  have hi : FiniteInvariant (rationalFraming q).level (rationalFraming q).weights X := by
    apply (rationalInvariant_iff_finite _ _ X).mp
    rwa [← funext (rationalFraming q).equation]
  rw [rationalDescendedSet, finiteDescent_mem_image _ _ X hX hi]
  exact exists_congr (fun x => and_congr Iff.rfl
    (Iff.of_eq (congrArg (fun z => z = r)
      (rationalFrame_common_level q _ _ (rationalFraming q).equation x).symm)))

theorem rationalDescendedSet_eq_finite {n : ℕ} (q : Fin n → ℚ) (N : ℕ+) (a : Fin n → ℤ)
    (hq : ∀ i, q i = (a i : ℚ) / (N : ℕ)) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X) :
    (rationalDescendedSet q X hX).carrier = (descendedOriginalSet N a X hX).carrier := by
  have hi : FiniteInvariant N a X := (rationalInvariant_iff_finite N a X).mp
    (by rwa [← funext hq])
  ext r
  rw [rationalDescent_mem_image q X hX hiX, finiteDescent_mem_image N a X hX hi]
  exact exists_congr (fun x => and_congr Iff.rfl
    (Iff.of_eq (congrArg (fun z => z = r) (rationalFrame_common_level q N a hq x))))

theorem rationalDescendedSet_finite_values {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    (Set.range (fun u : rationalDescendedSet q X hX => fun i => Values.vrv (u.val i))).Finite :=
  descendedOriginalSet_native_finite_values _ _ X hX

def descendedObject (X : DiagonalConstructible.Object) :
    GammaGroundRESObject canonicalInterpret_isCanonical (EmptyGammaGround.base {c | baseCarrier c}) X.arity :=
  nativeRESObjectOfSet canonicalInterpret_isCanonical (rationalDescendedSet X.weights X.domain X.definable)
    (rationalDescendedSet_finite_values X.weights X.domain X.definable)

theorem rational_framed_descent (X : DiagonalConstructible.Object) :
    rationalFramedSet X.weights (rationalDescendedSet X.weights X.domain X.definable) = X.domain := by
  ext x
  rw [show x ∈ rationalFramedSet X.weights (rationalDescendedSet X.weights X.domain X.definable) ↔
    rationalFrame X.weights x ∈ (rationalDescendedSet X.weights X.domain X.definable).carrier from Iff.rfl,
    rationalDescent_mem_image X.weights X.domain X.definable X.invariant]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (rationalFrame_injective X.weights he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end DiamondIntegral.Section5.PuiseuxOriginal
