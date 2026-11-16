import «section 6».UnaryFirstZeroRelativeTransition

/-! A canonical instruction preserves the full first-zero state. Its
new leading label is constant on every prescribed core by the checked
centre-value bound. The live ordinary diagram commutes literally. -/

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
variable (A : SpecialTransformations.Section5.DefSet (M := M) R 1 r)
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
variable (tail : SpecialTransformations.Section5.Chain R 1 (SpecialTransformations.Section5.canonicalImage A) B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.canonical A) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.canonical A) tail) hT)
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def canonicalNextOrdinaryMap : Map A₀ (originalBaseOrdinarySet hc (SpecialTransformations.Section5.canonicalImage A)
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) tail hT.2)) :=
  (originalBaseOrdinaryMap hc hT.1
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) tail hT.2)
    (SpecialTransformations.Section5.Primitive.canonical A).toMap
    (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph
      (SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)) (.canonical A) hT.1)).comp Z.ordinaryMap

theorem canonical_next_live_iff (a : A₀) :
    ((regularization Z.frame.current).comp Z.map a).val.2 ∈ Z.frame.canonicalLiveLabels.carrier ↔
      (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier := by
  change (regularize (Z.map a).val).2 ∘ Fin.natAdd 1 ∈ Z.frame.liveLabels.carrier ↔ _
  simp only [regularize,Function.comp_def,Fin.append_right]

theorem canonical_centre_bound (p : K.centres) :
    vfValue ((Z.map (K.centre p)).val.1 0)≤(K.radius p).val := by
  by_cases hLive : (Z.map (K.centre p)).val.2 ∈ Z.frame.liveLabels.carrier
  · have hOld := Z.live_agrees (K.centre p) hLive
    have hFrame := Z.frame.point ⟨(Z.map (K.centre p)).val,(Z.map (K.centre p)).property,hLive⟩
    have hField := congrArg (fun z : Mixed M 1 r => z.1 0)
      ((congrArg (fun a : originalBaseOrdinarySet hc A _ => a.val) hOld).symm.trans hFrame)
    rw [← hField]
    exact (ordinary_chain_value_lt_pointRadius_bound (.cons (.canonical A) tail)
      (Z.ordinaryMap (K.centre p)) (K.radius p) (Z.future_bound p) ((Z.centre_status p).mp hLive)).le
  · exact (Z.frozen_value p hLive).le

theorem canonical_next_live_agrees (a : A₀)
    (hLive : ((regularization Z.frame.current).comp Z.map a).val.2 ∈ Z.frame.canonicalLiveLabels.carrier) :
    (Z.frame.afterCanonical h00 hκ hs hv).oldMap
      ⟨((regularization Z.frame.current).comp Z.map a).val,
        ((regularization Z.frame.current).comp Z.map a).property,hLive⟩=
      Z.canonicalNextOrdinaryMap A tail hT a := by
  have hOldLive := (Z.canonical_next_live_iff A tail hT a).mp hLive
  let b : Z.frame.liveFrame.source := ⟨(Z.map a).val,(Z.map a).property,hOldLive⟩
  let c : Z.frame.canonicalLiveDomain :=
    ⟨((regularization Z.frame.current).comp Z.map a).val,
      ((regularization Z.frame.current).comp Z.map a).property,hLive⟩
  have he : Z.frame.canonicalLiveInclusion c=regularization Z.frame.liveFrame.source b := Subtype.ext rfl
  apply Subtype.ext
  change ((Z.frame.liveFrame.afterCanonical h00 hκ hs hv).oldMap (Z.frame.canonicalLiveInclusion c)).val=
    SpecialTransformations.Section5.canonical (Z.ordinaryMap a).val
  rw [he,Z.frame.liveFrame.afterCanonical_at_step h00 hκ hs hv b]
  change SpecialTransformations.Section5.canonical
    (Z.frame.oldMap ⟨(Z.map a).val,(Z.map a).property,hOldLive⟩).val=_
  rw [Z.live_agrees a hOldLive]

def afterCanonical : UnaryFirstZeroState (G := G) hc K tail hT.2 := by
  refine {
    source_pullback := Z.source_pullback
    arity := 1+Z.arity
    frame := Z.frame.afterCanonical h00 hκ hs hv
    pullback := regularization_rvPullback _ Z.pullback
    map := (regularization Z.frame.current).comp Z.map
    chain := .comp Z.chain (.original (.regularize Z.frame.current Z.frame.proper Z.frame.doublyBounded))
    ordinaryMap := Z.canonicalNextOrdinaryMap A tail hT
    live_agrees := Z.canonical_next_live_agrees A tail hT h00 hκ hs hv
    zero_cover := fun a => Z.zero_cover a
    core_chart := fun p => (Z.core_chart p).afterRegularization (Z.canonical_centre_bound A tail hT p)
    centre_status := fun p => (Z.canonical_next_live_iff A tail hT (K.centre p)).trans (Z.centre_status p)
    frozen_value := ?_
    future_bound := fun p => (le_max_right _ _).trans_lt (Z.future_bound p)
    outside_exact := ?_ }
  · intro p hFrozen
    exact Z.frozen_value p (fun hLive => hFrozen ((Z.canonical_next_live_iff A tail hT _).mpr hLive))
  · intro a
    change ((regularization Z.frame.current).comp Z.map a).val.2 ∈ Z.frame.canonicalLiveLabels.carrier ↔
      ¬ ∃ p : K.centres,
        ((regularization Z.frame.current).comp Z.map (K.centre p)).val.2 ∉
          Z.frame.canonicalLiveLabels.carrier ∧ a.val ∈ K.disc p
    simpa only [Z.canonical_next_live_iff A tail hT] using Z.outside_exact a

theorem afterCanonical_ordinaryMap (a : A₀) :
    ((Z.afterCanonical A tail hT h00 hκ hs hv).ordinaryMap a).val=
      SpecialTransformations.Section5.canonical (Z.ordinaryMap a).val := rfl

end DiamondIntegral.Section6.UnaryFirstZeroState
