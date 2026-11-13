import «section 3».RVScissors
import Section4.RVCoproduct
import Section4.PositiveAdditiveRepresentatives

/-! Genuine definable disjoint unions preserve nonzero finite-to-one
targets. Every element of the fixed-degree positive quotient is represented
by an actual object, before completion or cancellation. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVObject.coprod (U V : RVObject (M := M) S k) : RVObject S k where
  arity := 1 + (U.arity + V.arity)
  domain := (rvCoprodObject U.toCompanion.obj V.toCompanion.obj).domain
  volume := (rvCoprodObject U.toCompanion.obj V.toCompanion.obj).volume
  finite := rvCoprod_finite_volume _ _ U.finite V.finite
  nonzero a i hz := by
    rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
    · have he : rvCoprodLeftMap U.toCompanion.obj V.toCompanion.obj u = a := Subtype.ext hu
      have h := congrFun (rvCoprod_value_left U.toCompanion.obj V.toCompanion.obj u) i
      rw [he] at h
      exact U.nonzero u i ((congrArg Subtype.val h).symm.trans hz)
    · have he : rvCoprodRightMap U.toCompanion.obj V.toCompanion.obj v = a := Subtype.ext hv
      have h := congrFun (rvCoprod_value_right U.toCompanion.obj V.toCompanion.obj v) i
      rw [he] at h
      exact V.nonzero v i ((congrArg Subtype.val h).symm.trans hz)

theorem rvClass_coprod (U V : RVObject (M := M) S k) :
    rvClass (U.coprod V) = rvClass U + rvClass V := by
  let W := U.coprod V
  let X := (rvLeftTagMap U.domain V.arity).image
  let Y := (rvRightTagMap V.domain U.arity).image
  have hX : X.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  have hY : Y.carrier ⊆ W.domain.carrier := fun _ h => Or.inr h
  have hdiff : (W.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp (rvTaggedImages_disjoint U.domain V.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX :=
    ⟨(rvLeftTagMap U.domain V.arity).toImage, rvLeftTagMap_toImage_bijective U.domain V.arity⟩
  let G := (rvRightTagMap V.domain U.arity).toImage
  let gmap : Map V.domain (W.difference X) := G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply (rvRightTagMap_toImage_bijective V.domain U.arity).injective
      exact Subtype.ext (congrArg (fun x : W.difference X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.difference X) (fun _ h => h.1) := ⟨gmap, hg⟩
  have hs := rvClass_scissor W X hX
  rw [← rvClass_iso (asIso f), ← rvClass_iso (asIso g)] at hs
  exact hs.symm

theorem rvClass_surjective : Function.Surjective (rvClass (M := M) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (rvPresentation S k) RVObject.coprod rvClass_coprod

end DiamondIntegral.Section3
