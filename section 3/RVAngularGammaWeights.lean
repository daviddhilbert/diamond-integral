import «section 3».RVAngularValueReconstruction
import «section 3».FullGammaFunctionComposition
import «section 3».GammaGroundFiniteValuePoints
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem FullGammaFunction.freezeLeft {α β : Type} [Finite α] [Finite β]
    {f : (α ⊕ β → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : α → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    FullGammaFunction (integrationGammaBase B) (fun γ : β → Values.Gamma (M := M) => f (Sum.elim δ γ)) := by
  apply hf.comp (fun i γ => Sum.elim δ γ i)
  intro i
  cases i with
  | inl i => exact FullGammaFunction.constant (δ i) (integrationGammaDefinable (hδ i))
  | inr i => exact FullGammaFunction.proj _ i

namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def gammaWeight (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (δ : Fin K.zeroArity → Values.Gamma (M := M))
    (γ : Fin K.freeArity → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  f (E.valueReconstruction K (Sum.elim δ γ))

theorem gammaWeight_definable (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    {f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin K.zeroArity → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    FullGammaFunction (integrationGammaBase B) (E.gammaWeight K f δ) := by
  exact (hf.comp (fun i z => E.valueReconstruction K z i)
    (E.valueReconstruction_definable K _)).freezeLeft δ hδ

theorem gammaWeight_coordinate (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    E.gammaWeight K f (rvUnitTupleValues (E.coordinateEquiv K x).1)
      (rvUnitTupleValues (E.coordinateEquiv K x).2) = f (rvUnitTupleValues x) :=
  congrArg f (E.valueReconstruction_coordinate K x)
end RVAngularCell
end DiamondIntegral.Section3
