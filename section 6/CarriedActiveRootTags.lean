import «section 6».CarriedRootContexts

/-! A prepared lower root locus gives an actual original-base RV
active locus for the pushed roots. The equivalence holds on the whole
current ambient, and every root lies over an active tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CarriedChainLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

theorem active_root_tags_after_preparation (h00 : M ⊨ Axioms.ACVF00)
    (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle) (C : DefSet (rawMixedSpace (M := M) n r) S)
    (hCA : C.carrier ⊆ A.carrier)
    (hSource : ∀ p : X.bundle,
      (Fin.init p.val.1,p.val.2) ∈ R.activeBase.carrier ↔ (X.oldPoint p).val ∈ C.carrier)
    (hPrepared : IsRVPullback (f.restrict hCA).image.carrier)
    (htag : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ U : DefSet (rawRVSpace (M := M) F.target.arity) S,
      ∀ q ∈ F.target.bundle.carrier, q.2 ∈ U.carrier ↔
        ((F.pushCoordinateRoots hinj R).fibre (Fin.init q.1) q.2).Nonempty := by
  let Q := (f.restrict hCA).image
  let U := selectedRVTagSet (locusTags B Q) F.target.labels
  refine ⟨U,fun q hq => ?_⟩
  obtain ⟨p,hp⟩ := (F.special.bijective h00).surjective ⟨q,hq⟩
  have hPoint : (F.map p).val = q := congrArg Subtype.val hp
  have hOldMem : (f (X.oldPoint p)).val ∈ Q.carrier ↔ (X.oldPoint p).val ∈ C.carrier :=
    restricted_image_mem_iff_of_inverse f hinj hCA (X.oldPoint p) (f (X.oldPoint p)).val rfl
  have hTags := locus_iff_tags B Q hPrepared htag (f (X.oldPoint p)).property
  have hOldTags : (f (X.oldPoint p)).val.2 = q.2 ∘ F.target.labels := by
    have h := congrArg Prod.snd (F.commutes p)
    rw [hPoint] at h
    exact h.symm
  have hIndicator := F.root_indicator_transport h00 hinj R p
  rw [hPoint,CoordinateRootFamily.mem_activeBase] at hIndicator
  change q.2 ∘ F.target.labels ∈ (locusTags B Q).carrier ↔ _
  exact (hOldTags ▸ hTags.symm).trans (hOldMem.trans ((hSource p).symm.trans hIndicator.symm))

end DiamondIntegral.Section6.CarriedChainLift
