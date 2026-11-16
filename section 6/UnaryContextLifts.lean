import «section 6».UnaryContextComponentCompatibility
import «section 6».SynchronizedFocusSteps
import «section 6».SimultaneousChainTransport

/-! A common unary base change and its ambient lift. The certificate
retains every protected full piece and fixes every inactive VF coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s t m : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryContextLift
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    {i : Fin m} (X : UnaryPreparationContext A i) (f : Map A B)
    (P : I → DefSet (rawMixedSpace (M := M) m X.arity) S) where
  target : UnaryPreparationContext B i
  map : Map X.source target.source
  chain : SynchronizedCentripetalChain (G := G) I X.source target.source map P
  commutes : ∀ p : X.source,target.projection (map p)=f (X.projection p)
  fixed : ∀ p : X.source,∀ j ≠ i,(map p).val.1 j=p.val.1 j
  retainedLabels : Fin X.arity → Fin target.arity
  retained : ∀ p : X.source,∀ j,(map p).val.2 (retainedLabels j)=p.val.2 j

namespace UnaryContextLift
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {C : DefSet (rawMixedSpace (M := M) 1 t) S} {i : Fin m}
variable {X : UnaryPreparationContext A i} {f : Map A B} {g : Map B C}
variable {P : I → DefSet (rawMixedSpace (M := M) m X.arity) S}

theorem image_subset (F : UnaryContextLift (G := G) X f P)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (j : I) :
    (F.map.restrict (hPX j)).image.carrier ⊆ F.target.source.carrier := by
  rintro q ⟨p,hp⟩
  exact hp ▸ (F.map ⟨p.val,hPX j p.property⟩).property

def identity (X : UnaryPreparationContext A i)
    (P : I → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (hP : ∀ j,ProperInvariant S (P j).carrier) :
    UnaryContextLift (G := G) X (Map.id A) P where
  target := X
  map := Map.id X.source
  chain := .identity X.source X.proper P hPX hP
  commutes _ := rfl
  fixed _ _ _ := rfl
  retainedLabels := id
  retained _ _ := rfl

def comp (F : UnaryContextLift (G := G) X f P)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier)
    (H : UnaryContextLift (G := G) F.target g (fun j => (F.map.restrict (hPX j)).image)) :
    UnaryContextLift (G := G) X (g.comp f) P where
  target := H.target
  map := H.map.comp F.map
  chain := .comp P hPX F.chain H.chain
  commutes p := (H.commutes (F.map p)).trans (congrArg g (F.commutes p))
  fixed p j hj := (H.fixed (F.map p) j hj).trans (F.fixed p j hj)
  retainedLabels := H.retainedLabels ∘ F.retainedLabels
  retained p j := (H.retained (F.map p) (F.retainedLabels j)).trans (F.retained p j)

theorem image_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : UnaryContextLift (G := G) X f P) (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (j : I) :
    ProperInvariant S (F.map.restrict (hPX j)).image.carrier := by
  have h := ((F.chain.atPiece j).literal_restriction h00 (hPX j)).properHomeomorphism
    h00 hc linear hκ hs hv hsmall hΓ
  exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective

end UnaryContextLift
end DiamondIntegral.Section6
