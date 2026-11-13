import «section 3».GammaGroundRVMapCategory
import «section 3».GammaGroundCarrierBijections

/-! A same-ground cut is an actual coproduct decomposition, with both
inverse graphs retained over the original Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundRVMapObject.restrict (U : GammaGroundRVMapObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) : GammaGroundRVMapObject hc ground k := ⟨U.obj.restrict X hX⟩

def gammaGroundRVMapPartitionIso (U : GammaGroundRVMapObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) :
    (U.restrict X hX).coprod (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) ≅ U := by
  let Y := U.obj.domain.sdiff X
  have hY : Y.carrier ⊆ U.obj.domain.carrier := fun _ h => h.1
  let A := U.restrict X hX
  let B := U.restrict Y hY
  let il : A ⟶ U := GammaGroundMap.inclusion hX
  let ir : B ⟶ U := GammaGroundMap.inclusion hY
  let f : A.coprod B ⟶ U := gammaGroundRVMapDesc il ir
  have hd : Disjoint X.carrier Y.carrier := Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have he : U.obj.domain.carrier = (X.union Y).carrier := by
    ext a
    constructor
    · intro ha
      by_cases hx : a ∈ X.carrier
      · exact Or.inl hx
      · exact Or.inr ⟨ha, hx⟩
    · intro ha
      exact ha.elim (fun hx => hX hx) (fun hy => hY hy)
  let g : U ⟶ A.coprod B :=
    ((gammaGroundRVMapInl A B).union (gammaGroundRVMapInr A B)).comp
      (GammaGroundBijection.ofCarrierEq he).map
  have hfl (a : A.obj.domain) : f (gammaGroundRVMapInl A B a) = il a :=
    congrArg (fun h : A ⟶ U => h a) (gammaGroundRVMapInl_desc il ir)
  have hfr (b : B.obj.domain) : f (gammaGroundRVMapInr A B b) = ir b :=
    congrArg (fun h : B ⟶ U => h b) (gammaGroundRVMapInr_desc il ir)
  have hgl (a : A.obj.domain) : g (il a) = gammaGroundRVMapInl A B a := by
    change ((gammaGroundRVMapInl A B).union (gammaGroundRVMapInr A B)) ⟨a.val, Or.inl a.property⟩ = _
    exact GammaGroundMap.union_on_left _ _ a
  have hgr (b : B.obj.domain) : g (ir b) = gammaGroundRVMapInr A B b := by
    change ((gammaGroundRVMapInl A B).union (gammaGroundRVMapInr A B)) ⟨b.val, Or.inr b.property⟩ = _
    exact GammaGroundMap.union_on_right _ _ hd b
  refine ⟨f, g, ?_, ?_⟩
  · apply GammaGroundMap.ext
    intro a
    change g (f a) = a
    rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
    · have ha : gammaGroundRVMapInl A B u = a := Subtype.ext hu
      rw [← ha, hfl, hgl]
    · have ha : gammaGroundRVMapInr A B v = a := Subtype.ext hv
      rw [← ha, hfr, hgr]
  · apply GammaGroundMap.ext
    intro a
    change f (g a) = a
    by_cases hx : a.val ∈ X.carrier
    · let u : A.obj.domain := ⟨a.val, hx⟩
      have ha : il u = a := rfl
      rw [← ha, hgl, hfl]
    · let b : B.obj.domain := ⟨a.val, a.property, hx⟩
      have ha : ir b = a := rfl
      rw [← ha, hgr, hfr]

end DiamondIntegral.Section3
