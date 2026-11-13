import «section 3».MeasuredTensorLocalMatches
import «section 3».MeasuredNativeLocalCongruence
import «section 3».MonomialTensorLocalMatches
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}

theorem gammaGroundMeasuredMonomialPatch_tensor_congruence
    (X Y : GammaGroundRESUnitChart hc B r)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (f : GammaGroundMap T D) (g : GammaGroundMap T Y.native)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (E : GammaGroundRVProductMonomialPatch X.native T D Y.native f g)
    (u v : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : FullGammaFunction (integrationGammaBase B) u) (hv : FullGammaFunction (integrationGammaBase B) v)
    (hw : ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E.gamma.carrier →
      u γ = v (fun i => E.value i * integerMonomialMap E.matrix γ i)) :
    gammaGroundMeasuredCoefficientCongruence
      (gammaGroundMeasuredRESDirectSumClass (X.restrict E.residue E.residue_subset).measured
        ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight E.gamma u hu))
      (gammaGroundMeasuredRESDirectSumClass (Y.restrict E.residueMap.image E.residueMap_image_subset).measured
        ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight E.targetGamma v hv)) := by
  exact (X.restrict E.residue E.residue_subset).measured_local_monomial_congruence Y
    E.residueMap (E.residueMap_injective hjoint) E.residueMap_image_subset E.gamma E.matrix E.unimodular
      E.coefficient E.value E.value_definable E.coefficient_values u v hu hv hw

variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

def gammaGroundMeasuredMonomialPatchBoxMatch
    (F : GammaGroundBijection U0 V0)
    (X Y : GammaGroundRESUnitChart hc B r) (G H : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)) (g : GammaGroundMap T Y.native)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (hgraph : ∀ a : T, t ⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ = F.map (s ⟨a.val,hT a.property⟩))
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g)
    (u v : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : FullGammaFunction (integrationGammaBase B) u) (hv : FullGammaFunction (integrationGammaBase B) v)
    (hw : ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E.gamma.carrier →
      u γ = v (fun i => E.value i * integerMonomialMap E.matrix γ i)) :
    GammaGroundMeasuredTensorBoxMatch F X G s u hu Y H t v hv (E.sourceBox hT) (E.targetBox hjoint) where
  data := gammaGroundMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E
  congruence := gammaGroundMeasuredMonomialPatch_tensor_congruence X Y T (gammaGroundRVUnitGammaPreimage H)
    f g hjoint E u v hu hv hw

/-- Source and target cuts of a compatible weighted monomial patch keep
the full measured congruence required by disjoint source selection. -/
def gammaGroundMeasuredMonomialPatchLocalMatch
    (F : GammaGroundBijection U0 V0)
    (X Y : GammaGroundRESUnitChart hc B r) (G H : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)) (g : GammaGroundMap T Y.native)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (hgraph : ∀ a : T, t ⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ = F.map (s ⟨a.val,hT a.property⟩))
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g)
    (u v : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : FullGammaFunction (integrationGammaBase B) u) (hv : FullGammaFunction (integrationGammaBase B) v)
    (hw : ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E.gamma.carrier →
      u γ = v (fun i => E.value i * integerMonomialMap E.matrix γ i)) :
    GammaGroundMeasuredTensorLocalMatch F X G s u hu Y H t v hv where
  source := E.sourceBox hT
  target := E.targetBox hjoint
  data := gammaGroundMeasuredMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E u v hu hv hw
  sourceCuts := by
    intro L hA hG hneA hneG
    let E' := E.restrict L.residue hA hneA L.gamma hG hneG
    have he : E'.sourceBox hT = L := GammaGroundTensorBox.ext rfl rfl
    have hw' : ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E'.gamma.carrier →
        u γ = v (fun i => E'.value i * integerMonomialMap E'.matrix γ i) :=
      fun γ hγ => hw γ (hG hγ)
    have hd := gammaGroundMeasuredMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E' u v hu hv hw'
    exact ⟨E'.targetBox hjoint,⟨he ▸ hd⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    let E' := E.restrictTarget R.residue hA hneA R.gamma hG hneG
    have he : E'.targetBox hjoint = R := GammaGroundTensorBox.ext
      (E.restrictTarget_residue_image R.residue hA hneA R.gamma hG hneG)
      (E.restrictTarget_gamma_image R.residue hA hneA R.gamma hG hneG)
    have hw' : ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E'.gamma.carrier →
        u γ = v (fun i => E'.value i * integerMonomialMap E'.matrix γ i) :=
      fun γ hγ => hw γ hγ.1
    have hd := gammaGroundMeasuredMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E' u v hu hv hw'
    exact ⟨E'.sourceBox hT,⟨he ▸ hd⟩⟩
end DiamondIntegral.Section3
