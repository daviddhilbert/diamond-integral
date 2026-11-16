import «section 6».PairedDiscOffsets
import «section 6».UnaryGraphFibreDiscImages

/-! Paired offsets on an actual mixed graph fibre. The target offset is
the difference of two actual image coordinates, and the paired whole-disc
identity retains both old RV tuples and every center point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_mixed_paired_disc_offsets_at_point
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f) (p : A) (α β : Gamma M) :
    ∃ η : Gamma M,∀ (d : VF M) (hd : d ≠ 0),η.val < vfValue d →
      ∃ q : A,q.val.1 0=p.val.1 0+d ∧ q.val.2=p.val.2 ∧ (f q).val.2=(f p).val.2 ∧
      ∃ he : (f q).val.1 0-(f p).val.1 0 ≠ 0,
        α ≤ finiteValue d hd ∧ β ≤ finiteValue ((f q).val.1 0-(f p).val.1 0) he ∧
        centeredGammaDisc (p.val.1 0) (finiteValue d hd) ⊆ unaryGraphFibreSource f p.val.2 (f p).val.2 ∧
        ∀ z : B,z.val.1 0 ∈ centeredGammaDisc ((f p).val.1 0)
            (finiteValue ((f q).val.1 0-(f p).val.1 0) he) ∧ z.val.2=(f p).val.2 ↔
          ∃ a : A,a.val.1 0 ∈ centeredGammaDisc (p.val.1 0) (finiteValue d hd) ∧
            a.val.2=p.val.2 ∧ f a=z := by
  have hSmallU := small_union_finite hκ S hsmall _ (Set.finite_range (rvValues p.val.2))
  have hSmall := small_union_finite hκ (S ∪ Set.range (rvValues p.val.2)) hSmallU _
    (Set.finite_range (rvValues (f p).val.2))
  obtain ⟨η,hη⟩ := continuous_bijection_paired_disc_offsets hc hκ hs hSmall hv
    (unaryGraphFibreSource f p.val.2 (f p).val.2) (unaryGraphFibreRange f p.val.2 (f p).val.2)
    (unaryGraphFibreSource_open hv f h.covariant p.val.2 (f p).val.2)
    (unaryGraphFibreMap f p.val.2 (f p).val.2)
    (unaryGraphFibreMap_bijOn f h.bijective.injective p.val.2 (f p).val.2)
    (unaryGraphFibreMap_graph_definable f p.val.2 (f p).val.2)
    (unaryGraphFibreMap_continuous f h.continuous p.val.2 (f p).val.2)
    (unaryGraphFibreRange_bounded f h.covariant.imageVFBounded p.val.2 (f p).val.2)
    (p.val.1 0) (unaryGraphFibreSource_at f p) α β
  refine ⟨η,fun d hd hηd => ?_⟩
  obtain ⟨hpA,he,hα,hβ,hSource,hTarget,hImage⟩ := hη d hd hηd
  obtain ⟨q,hq,hfq⟩ := graphFibreMap_graph f p.val.2 (f p).val.2 hpA
  have hqx : q.val.1 0=p.val.1 0+d := congrArg (fun z : Mixed M 1 r => z.1 0) hq
  have hqu : q.val.2=p.val.2 := by
    have hh := congrArg (fun z : Mixed M 1 r => z.2) hq
    exact hh
  have hqv : (f q).val.2=(f p).val.2 := by
    have hh := congrArg (fun z : Mixed M 1 s => z.2) hfq
    exact hh
  have hfy : (f q).val.1 0=unaryGraphFibreMap f p.val.2 (f p).val.2 (p.val.1 0+d) :=
    congrArg (fun z : Mixed M 1 s => z.1 0) hfq
  have hOut : ∃ he : (f q).val.1 0-(f p).val.1 0 ≠ 0,
      β ≤ finiteValue ((f q).val.1 0-(f p).val.1 0) he ∧
      centeredGammaDisc ((f p).val.1 0) (finiteValue ((f q).val.1 0-(f p).val.1 0) he) ⊆
        unaryGraphFibreRange f p.val.2 (f p).val.2 ∧
      unaryGraphFibreMap f p.val.2 (f p).val.2 '' centeredGammaDisc (p.val.1 0) (finiteValue d hd)=
        centeredGammaDisc ((f p).val.1 0) (finiteValue ((f q).val.1 0-(f p).val.1 0) he) := by
    simpa only [unaryGraphFibreMap_at f p,← hfy] using
      (show ∃ he,β ≤ finiteValue _ he ∧ _ ∧ _ from ⟨he,hβ,hTarget,hImage⟩)
  obtain ⟨he,hβ,hTarget,hImage⟩ := hOut
  exact ⟨q,hqx,hqu,hqv,he,hα,hβ,hSource,fun z =>
    unaryGraphFibreDisc_mixed_image_iff f p.val.2 (f p).val.2 _ _ hSource hImage z⟩

end DiamondIntegral.Section6
