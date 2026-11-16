import «section 6».UnaryFirstZeroCoreGeometry
import «section 6».LiveOrdinaryRelativeFrames

/-! Exact first-zero invariants for an actual variable centripetal step:
live ordinary values, frozen endpoint values, and the full complement
of the frozen original cores. -/

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
variable (h00 : M ⊨ Axioms.ACVF00)

def firstZeroNextOrdinaryMap : Map A₀ (originalBaseOrdinarySet hc D.etaImage
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) tail hT.2)) :=
  (originalBaseOrdinaryMap hc hT.1.1
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) tail hT.2)
    (SpecialTransformations.Section5.Primitive.centripetal D).toMap
    (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph
      (SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)) (.centripetal D) hT.1)).comp Z.ordinaryMap

theorem firstZero_frozen_ordinary_zero (p : K.centres)
    (hFrozen : (Z.map (K.centre p)).val.2 ∉ Z.frame.liveLabels.carrier) :
    (Z.ordinaryMap (K.centre p)).val.1 0=(0 : VF M) := by
  by_contra hNZ
  exact hFrozen ((Z.centre_status p).mpr hNZ)

theorem firstZero_captured_ordinary_zero (p : K.centres)
    (hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=true) :
    (Z.firstZeroNextOrdinaryMap D tail hT (K.centre p)).val.1 0=(0 : VF M) := by
  obtain ⟨z,hz,hc⟩ := Z.firstZero_centre_selected D tail hT h00 p hCore
  have he : K.centre p=Z.unrestrictedCentreMap D tail hT h00 z := by
    rw [← hc]
    exact Subtype.ext rfl
  change (D.toFocusGeometry.eta (Z.ordinaryMap (K.centre p)).val).1 0=(0 : VF M)
  rw [he]
  exact Z.unrestrictedCentreMap_ordinary_zero D tail hT h00 z

theorem firstZero_next_live_iff (a : A₀) :
    ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map a)).val.2 ∈
      ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier ↔
    (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier ∧
      (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=false :=
  (Z.firstZeroAperture D tail hT h00).stepLiveTags_at h00 Z.frame.liveLabels (Z.map a).val

theorem firstZero_next_centre_status (p : K.centres) :
    ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map (K.centre p))).val.2 ∈
      ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier ↔
    (Z.firstZeroNextOrdinaryMap D tail hT (K.centre p)).val.1 0≠(0 : VF M) := by
  rw [Z.firstZero_next_live_iff D tail hT h00 (K.centre p)]
  constructor
  · rintro ⟨hLive,hCore⟩
    have hField := Z.firstZero_noncore_live_field D tail hT h00 (K.centre p) hLive hCore
    change (D.toFocusGeometry.eta (Z.ordinaryMap (K.centre p)).val).1 0≠(0 : VF M)
    rw [← hField]
    exact (Z.firstZeroAperture D tail hT h00).point_nonzero _
  · intro hNZ
    refine ⟨?_,?_⟩
    · apply (Z.centre_status p).mpr
      intro hZero
      have h := OriginalBaseOrdinaryFocus.eta_fixes_zero D (Z.ordinaryMap (K.centre p)) hZero
      exact hNZ ((congrArg (fun z : Mixed M 1 r => z.1 0) h).trans hZero)
    · apply Bool.eq_false_iff.mpr
      intro hCore
      exact hNZ (Z.firstZero_captured_ordinary_zero D tail hT h00 p hCore)

theorem firstZero_next_frozen_value (p : K.centres)
    (hFrozen : ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map (K.centre p))).val.2 ∉
      ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier) :
    vfValue (((Z.firstZeroAperture D tail hT h00).stepMap (Z.map (K.centre p))).val.1 0)=
      (K.radius p).val := by
  change vfValue (((Z.firstZeroAperture D tail hT h00).point (Z.map (K.centre p)).val).1 0)=_
  by_cases hLive : (Z.map (K.centre p)).val.2 ∈ Z.frame.liveLabels.carrier
  · have hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=true := by
      cases hb : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val with
      | true => rfl
      | false => exact (hFrozen ((Z.firstZero_next_live_iff D tail hT h00 _).mpr ⟨hLive,hb⟩)).elim
    rw [Z.firstZero_output_captured_centre D tail hT h00 p hCore]
    rfl
  · rw [Z.frame.relative_inactive_on_frozen D hT.1.2 (Z.firstZeroAperture D tail hT h00) rfl hLive]
    exact Z.frozen_value p hLive

theorem firstZero_next_outside_exact (a : A₀) :
    ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map a)).val.2 ∈
      ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier ↔
    ¬ ∃ p : K.centres,
      ((Z.firstZeroAperture D tail hT h00).stepMap (Z.map (K.centre p))).val.2 ∉
        ((Z.firstZeroAperture D tail hT h00).stepLiveTags Z.frame.liveLabels).carrier ∧ a.val ∈ K.disc p := by
  constructor
  · intro hNew
    obtain ⟨hLive,hCore⟩ := (Z.firstZero_next_live_iff D tail hT h00 a).mp hNew
    rintro ⟨p,hFrozen,ha⟩
    have hpLive : (Z.map (K.centre p)).val.2 ∈ Z.frame.liveLabels.carrier := by
      by_contra hn
      exact ((Z.outside_exact a).mp hLive) ⟨p,hn,ha⟩
    have hpCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=false := by
      rw [← Z.firstZero_core_constant D tail hT h00 p a ha]
      exact hCore
    exact hFrozen ((Z.firstZero_next_live_iff D tail hT h00 _).mpr ⟨hpLive,hpCore⟩)
  · intro hNo
    apply (Z.firstZero_next_live_iff D tail hT h00 a).mpr
    refine ⟨?_,?_⟩
    · apply (Z.outside_exact a).mpr
      rintro ⟨p,hFrozen,ha⟩
      apply hNo
      refine ⟨p,?_,ha⟩
      intro hNew
      exact hFrozen ((Z.firstZero_next_live_iff D tail hT h00 _).mp hNew).1
    · apply Bool.eq_false_iff.mpr
      intro hCore
      obtain ⟨p,hLive,ha⟩ := Z.firstZero_core_implies_disc D tail hT h00 a hCore
      apply hNo
      refine ⟨p,?_,ha⟩
      intro hpNew
      have hpFalse := ((Z.firstZero_next_live_iff D tail hT h00 _).mp hpNew).2
      rw [Z.firstZero_core_constant D tail hT h00 p a ha,hpFalse] at hCore
      contradiction

end DiamondIntegral.Section6.UnaryFirstZeroState
