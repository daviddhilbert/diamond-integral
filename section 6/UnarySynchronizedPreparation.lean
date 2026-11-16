import «section 6».PreparedSynchronizedFamilies
import «section 6».ProtectedUnaryContextPreparation

/-! The actual unary base case for the strong dimension-induction
invariant. Every protected restriction retains the ambient coordinate,
coefficient and focus compatibility throughout the finite sequence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def unarySelfPreparationContext (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) :
    UnaryPreparationContext A (0 : Fin 1) where
  arity := r
  source := A
  labels := id
  projection := Map.id A
  projection_value p := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl
  proper := hA
  doublyBounded := hAD
  pullback := hARV
  tagged := hTag

theorem unary_synchronized_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier) :
    Nonempty (PreparedSynchronizedFamily (G := G) A P hPA) := by
  let X := unarySelfPreparationContext A hA hAD hARV hTag
  let Q : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S := fun i => i.elim0
  obtain ⟨s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,hLift⟩ := unary_preparation_protecting_ambient_pieces
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD hARV hTag P hPA hP X Q
    (fun i => i.elim0) (fun i => i.elim0)
  exact ⟨⟨s,B,f,hChain,hB,hBD,hBRV,fun i => (hPieces i).2⟩⟩

end DiamondIntegral.Section6
