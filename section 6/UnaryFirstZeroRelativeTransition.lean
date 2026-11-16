import «section 6».UnaryFirstZeroRelativeInvariants

/-! The complete prescribed-core first-zero state advances through an
actual ordinary centripetal instruction, using the constructed endpoint
and a permitted auxiliary variable primitive plus regularization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ r s : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (tail : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.centripetal D) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.centripetal D) tail) hT)
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ)

theorem firstZero_next_live_agrees (a : A₀)
    (hLive : ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map a)).val.2 ∈
      ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier) :
    (Z.frame.afterRelativeCentripetal D hT.1.2 (Z.firstZeroAperture D tail hT h00) Z.pullback
      rfl (fun _ => rfl) h00 hκ hs hv hsmall).oldMap
      ⟨((Z.firstZeroAperture D tail hT h00).stepMap (Z.map a)).val,
        ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map a)).property,hLive⟩=
      Z.firstZeroNextOrdinaryMap D tail hT a := by
  let E := Z.firstZeroAperture D tail hT h00
  have hOldLive := ((Z.firstZero_next_live_iff D tail hT h00 a).mp hLive).1
  let b : focusActive (regularizeMap E.map.image).image (E.stepLiveTags Z.frame.liveLabels) :=
    ⟨(E.stepMap (Z.map a)).val,(E.stepMap (Z.map a)).property,hLive⟩
  have hInv : E.stepLiveInverse h00 Z.frame.liveLabels b=
      (⟨(Z.map a).val,(Z.map a).property,hOldLive⟩ : Z.frame.liveFrame.source) := by
    apply Subtype.ext
    have h := E.stepLiveInverse_point h00 Z.frame.liveLabels b
    have he : (⟨(E.stepLiveInverse h00 Z.frame.liveLabels b).val,
        (E.stepLiveInverse h00 Z.frame.liveLabels b).property.1⟩ : Z.frame.current)=Z.map a :=
      (E.stepMap_bijective h00).injective (Subtype.ext h)
    have hValue := congrArg (fun z : Z.frame.current => z.val) he
    exact hValue
  apply Subtype.ext
  change D.toFocusGeometry.eta (Z.frame.oldMap (E.stepLiveInverse h00 Z.frame.liveLabels b)).val=
    D.toFocusGeometry.eta (Z.ordinaryMap a).val
  rw [hInv,Z.live_agrees a hOldLive]

def afterCentripetal : UnaryFirstZeroState (G := G) hc K tail hT.2 := by
  let E := Z.firstZeroAperture D tail hT h00
  let X := Z.frame.afterRelativeCentripetal D hT.1.2 E Z.pullback rfl (fun _ => rfl) h00 hκ hs hv hsmall
  refine {
    source_pullback := Z.source_pullback
    arity := 1+(1+Z.arity)
    frame := X
    pullback := E.regularized_image_rvPullback Z.pullback
    map := E.stepMap.comp Z.map
    chain := .comp Z.chain (E.stepChain h00 hc hκ hs hv hsmall)
    ordinaryMap := Z.firstZeroNextOrdinaryMap D tail hT
    live_agrees := Z.firstZero_next_live_agrees D tail hT h00 hκ hs hv hsmall
    zero_cover := fun a => Z.zero_cover a
    core_chart := Z.firstZero_after_core_chart D tail hT h00
    centre_status := Z.firstZero_next_centre_status D tail hT h00
    frozen_value := Z.firstZero_next_frozen_value D tail hT h00
    future_bound := fun p => (le_max_right _ _).trans_lt (Z.future_bound p)
    outside_exact := Z.firstZero_next_outside_exact D tail hT h00 }

theorem afterCentripetal_ordinaryMap (a : A₀) :
    ((Z.afterCentripetal D tail hT h00 hκ hs hv hsmall).ordinaryMap a).val=
      D.toFocusGeometry.eta (Z.ordinaryMap a).val := rfl

end DiamondIntegral.Section6.UnaryFirstZeroState
