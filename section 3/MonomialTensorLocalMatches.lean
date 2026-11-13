import «section 3».TensorLocalMatches
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
namespace GammaGroundRVProductMonomialPatch

def sourceBox {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B m}
    {T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity))}
    {f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)} {g : GammaGroundMap T Y.native}
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier) : GammaGroundTensorBox X G :=
  ⟨E.residue,E.residue_subset,E.gamma,E.gamma_subset G (fun a => (hT a.property).1)⟩

def targetBox {X Y : GammaGroundRESUnitChart hc B r} {H : GammaGroundGammaPiece hc B m}
    {T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity))}
    {f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)} {g : GammaGroundMap T Y.native}
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) : GammaGroundTensorBox Y H :=
  ⟨E.residueMap.image,E.residueMap_image_subset,E.targetGamma,E.targetGamma_subset hjoint H (fun u => u.property)⟩
end GammaGroundRVProductMonomialPatch

variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- A genuine monomial patch is a positive product match inside the
actual global RV graph. -/
def gammaGroundMonomialPatchBoxMatch
    (F : GammaGroundBijection U0 V0)
    (X Y : GammaGroundRESUnitChart hc B r) (G H : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)) (g : GammaGroundMap T Y.native)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (hgraph : ∀ a : T, t ⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ =
      F.map (s ⟨a.val,hT a.property⟩))
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g) :
    GammaGroundTensorBoxMatch F X G s Y H t (E.sourceBox hT) (E.targetBox hjoint) where
  bijection := E.bijection hjoint
  congruence := gammaGroundMonomialPatch_tensor_congruence X Y T (gammaGroundRVUnitGammaPreimage H) f g hjoint E
  agrees := by
    intro z
    let a : T := ⟨z.val,E.source_subset z.property⟩
    have hs : (E.sourceBox hT).inclusion z = (⟨a.val,hT a.property⟩ : gammaGroundNativeProductDomain X G) :=
      Subtype.ext (Prod.eta z.val)
    have ht : (E.targetBox hjoint).inclusion ((E.bijection hjoint).map z) =
        (⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ : gammaGroundNativeProductDomain Y H) :=
      Subtype.ext ((Prod.eta ((E.bijection hjoint).map z).val).trans (E.bijection_agrees hjoint z))
    rw [hs,ht]
    exact hgraph a

/-- Source and target restrictions of the monomial formula construct all
the cut data for a two-sided local match. -/
def gammaGroundMonomialPatchLocalMatch
    (F : GammaGroundBijection U0 V0)
    (X Y : GammaGroundRESUnitChart hc B r) (G H : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)) (g : GammaGroundMap T Y.native)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (hgraph : ∀ a : T, t ⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ =
      F.map (s ⟨a.val,hT a.property⟩))
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g) :
    GammaGroundTensorLocalMatch F X G s Y H t where
  source := E.sourceBox hT
  target := E.targetBox hjoint
  data := gammaGroundMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E
  sourceCuts := by
    intro L hA hG hneA hneG
    let E' := E.restrict L.residue hA hneA L.gamma hG hneG
    have he : E'.sourceBox hT = L := GammaGroundTensorBox.ext rfl rfl
    have hd := gammaGroundMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E'
    exact ⟨E'.targetBox hjoint,⟨he ▸ hd⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    let E' := E.restrictTarget R.residue hA hneA R.gamma hG hneG
    have he : E'.targetBox hjoint = R := GammaGroundTensorBox.ext
      (E.restrictTarget_residue_image R.residue hA hneA R.gamma hG hneG)
      (E.restrictTarget_gamma_image R.residue hA hneA R.gamma hG hneG)
    have hd := gammaGroundMonomialPatchBoxMatch F X Y G H s t T f g hT hjoint hgraph E'
    exact ⟨E'.sourceBox hT,⟨he ▸ hd⟩⟩
end DiamondIntegral.Section3
