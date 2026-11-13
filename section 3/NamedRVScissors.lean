import «section 3».NamedRVCategories
import «section 3».Grothendieck
import «section 3».RVScissors

/-! Genuine fixed-degree scissors over an actual imaginary name. The
real-code comparison preserves every inherited cut and actual bijection. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Space LRV M} {p : P.Carrier} {S : Set M} {k : ℕ}

def NamedRVObject.empty (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) : NamedRVObject P p S k where
  arity := 0
  domain := NamedDefSet.empty P p (rawRVSpace 0) S
  volume := NamedMap.ofReal (Map.empty (rawRVSpace 0) (rawRVSpace k) S)
  finite t := Set.finite_empty.subset (fun a _ => False.elim a.property)
  nonzero a := False.elim a.property

def NamedRVObject.restrict (U : NamedRVObject P p S k)
    (X : NamedDefSet P p (rawRVSpace (M := M) U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) : NamedRVObject P p S k where
  arity := U.arity
  domain := X
  volume := U.volume.restrict hX
  finite := U.finite.comp (NamedMap.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun y : U.domain => y.val) he)))
  nonzero a := U.nonzero (NamedMap.inclusion hX a)

def namedRVScissor (A B D E : NamedRVObject P p S k) : Prop :=
  ∃ U : NamedRVObject P p S k,
    ∃ X : NamedDefSet P p (rawRVSpace (M := M) U.arity) S,
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = NamedRVObject.empty P p S k

def namedRVPresentation (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) :
    ScissorPresentation (NamedRVObject P p S k) where
  iso A B := Nonempty (A ≅ B)
  empty := NamedRVObject.empty P p S k
  scissor := namedRVScissor

abbrev NamedRVKPlus (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) := KPlus (namedRVPresentation P p S k)

def namedRVClass (U : NamedRVObject P p S k) : NamedRVKPlus P p S k := positiveClass (namedRVPresentation P p S k) U

@[simp] theorem namedRVClass_empty : namedRVClass (NamedRVObject.empty P p S k) = 0 :=
  positiveClass_empty (namedRVPresentation P p S k)

theorem namedRVClass_iso {U V : NamedRVObject P p S k} (e : U ≅ V) : namedRVClass U = namedRVClass V :=
  positiveClass_iso (namedRVPresentation P p S k) ⟨e⟩

theorem namedRVClass_scissor (U : NamedRVObject P p S k)
    (X : NamedDefSet P p (rawRVSpace (M := M) U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) :
    namedRVClass (U.restrict X hX) + namedRVClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = namedRVClass U := by
  have h := positiveClass_scissor (namedRVPresentation P p S k) ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change namedRVClass _ + namedRVClass _ = namedRVClass _ + namedRVClass _ at h
  simpa only [namedRVClass_empty, add_zero] using h

end DiamondIntegral.Section3
