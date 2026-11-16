import «section 6».OrdinaryFrameRestrictions

/-! The actual core complement admits the complete ordinary-chain
conversion once its selected centers cover the ordinary zero events.
All avoidance and properness hypotheses of the conversion are discharged
by the constructed core geometry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_covariant_realization_outside_offset_cores
    (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (X : OrdinaryUnaryFocusFrame hc A
      (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT) q)
    (F : UnaryFocusData X.source)
    (dMap : Map (focusActive X.source F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (d : (Fin q → RVInfinity M) → VF M)
    (hdMap : ∀ p : focusActive X.source F.activeTags,(dMap p).val 0=d p.val.2)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hCover : ∀ p : X.source,(X.oldMap p).val ∈ ordinaryChainZeroSources T →
      p.val.2 ∈ F.activeTags.carrier ∧ p.val.1 0=F.focus p.val.2) :
    Nonempty (OrdinaryChainCovariantRealization (G := G)
      (X.outsideOffsetCoreFrame h00 hκ hs hv F dMap d hdMap hd) T hT) := by
  let Y := X.outsideOffsetCoreFrame h00 hκ hs hv F dMap d hdMap hd
  apply exists_covariant_realization_off_ordinary_exceptions h00 linear hκ hs hv V hsmall hΓ hV hVS hSV hnt T hT q Y
  intro p hpZero
  let a : X.source := ⟨p.val,p.property.1⟩
  have haZero : (X.oldMap a).val ∈ ordinaryChainZeroSources T := hpZero
  obtain ⟨hu,hCenter⟩ := hCover a haZero
  exact F.offsetCoreComplement_ne_center dMap d hdMap p.val p.property hu (hd p.val.2 hu) hCenter

end DiamondIntegral.Section6
