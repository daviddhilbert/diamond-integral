import «section 6».DiamondGrothendieck
import Section4.EmptyMaps

/-! Empty objects of `μVF^◇[n]`.

A map out of an empty definable set is a proper covariant homeomorphism onto an
empty set, so any two objects with empty carrier are isomorphic (in every degree,
including zero). Hence every object with empty carrier has class
zero in `K_+ μVF^◇[n]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondEmpty
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properCovariant_of_empty (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (hA : A.carrier = ∅) : ProperCovariant f := by
  have hE : IsEmpty A := ⟨fun p => hA.le p.property⟩
  refine ⟨⟨1, fun _ hp => False.elim (hA.le hp)⟩, ⟨1, fun _ ⟨p, _⟩ => isEmptyElim p⟩,
    ⟨1, fun _ hp => False.elim (hA.le hp)⟩, ⟨1, fun _ ⟨p, _⟩ => isEmptyElim p⟩, fun u v => ?_⟩
  have named : ∀ {k : ℕ}, NamedGammaTuple (graphFibreBase S u v) (fun _ : Fin k => (1 : Gamma M)) :=
    fun _ => (gamma_one_named (S := S) hc).mono (fun _ hx => Or.inl (Or.inl hx))
  exact ⟨fun _ => 1, fun _ => 1, named, named,
    fun _ _ _ => ⟨fun ⟨_, p, _⟩ => isEmptyElim p, fun ⟨_, p, _⟩ => isEmptyElim p⟩,
    fun _ _ _ => ⟨fun ⟨_, p, _⟩ => isEmptyElim p, fun ⟨_, p, _⟩ => isEmptyElim p⟩,
    fun _ ⟨_, p, _⟩ => isEmptyElim p⟩

theorem continuous_of_empty {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (hA : A.carrier = ∅) :
    ContinuousOnGraphFibres (G := G) f := by
  intro u v
  have h : graphFibreSource f u v = ∅ :=
    Set.eq_empty_of_forall_notMem (fun _ ⟨_, p, _⟩ => hA.le p.property)
  rw [h]
  exact continuousOn_empty _

theorem homeo_of_empty (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (hA : A.carrier = ∅) (hB : B.carrier = ∅) :
    ProperCovariantHomeomorphism (G := G) f :=
  ⟨Map.bijective_of_empty f hA hB, properCovariant_of_empty hc f hA, continuous_of_empty f hA,
    properCovariant_of_empty hc _ hB, continuous_of_empty _ hB⟩

/-- The morphism between two objects with empty carriers. -/
def emptyMorphism (hc : CanonicalStructure.IsCanonical (M := M)) {A B : VFObject (M := M) S n}
    (hA : A.carrier.carrier = ∅) (hB : B.carrier.carrier = ∅) : Morphism G A B where
  map := Map.fromEmpty hA B.carrier
  bijective := Map.bijective_of_empty _ hA hB
  chain := ObjectFactorization.step ⟨homeo_of_empty hc _ hA hB, (by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr ⟨⟨0, h⟩, ⟨0, h⟩, fun p => False.elim (hA.le p.property)⟩),
    ⟨DefSet.empty _ S, Set.empty_subset _, Or.inr rfl, fun p _ => False.elim (hA.le p.property)⟩⟩
  bad := DefSet.empty _ S
  bad_subset := Set.empty_subset _
  bad_small := Or.inr rfl
  measure p _ := False.elim (hA.le p.property)

theorem isomorphic_empty (hc : CanonicalStructure.IsCanonical (M := M)) {A : VFObject (M := M) S n}
    (hA : A.carrier.carrier = ∅) : Isomorphic G A (emptyObject hc n) :=
  ⟨emptyMorphism hc hA rfl⟩

/-- Every object with empty carrier has class zero. -/
theorem vfClass_of_empty (hc : CanonicalStructure.IsCanonical (M := M)) {A : VFObject (M := M) S n}
    (hA : A.carrier.carrier = ∅) : vfClass G hc A = 0 :=
  (vfClass_iso hc (isomorphic_empty hc hA)).trans (vfClass_empty hc)

end DiamondIntegral.Section6.DiamondEmpty
