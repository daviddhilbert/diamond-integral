import «section 6».UnaryFirstZeroStates

/-! At the end of an actual first-zero state every prescribed original
centre is frozen. Its entire core image is an RV-pullback, distinct core
labels stay distinct, and the live locus is exactly the original core
complement with literal ordinary commutation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ r : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (Z : UnaryFirstZeroState (G := G) hc K (.nil A) hA)

theorem nil_centre_frozen (p : K.centres) : (Z.map (K.centre p)).val.2 ∉ Z.frame.liveLabels.carrier := by
  have hZero : (Z.ordinaryMap (K.centre p)).val.1 0=(0 : VF M) :=
    (Z.zero_cover (K.centre p)).mpr p.property
  intro hLive
  exact ((Z.centre_status p).mp hLive) hZero

theorem nil_core_image_rvPullback (p : K.centres) : IsRVPullback (Z.core_chart p).image :=
  (Z.core_chart p).image_rvPullback Z.source_pullback (K.centre_nonzero p) (K.source_bound p).le
    (Z.frame.doublyBounded.nonzero (Z.map (K.centre p)).property 0)
    (Z.frozen_value p (Z.nil_centre_frozen p))

theorem nil_live_complement (a : A₀) : (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier ↔
    ¬ ∃ p : K.centres,a.val ∈ K.disc p := by
  constructor
  · intro hLive
    rintro ⟨p,hDisc⟩
    exact ((Z.outside_exact a).mp hLive) ⟨p,Z.nil_centre_frozen p,hDisc⟩
  · intro hNo
    apply (Z.outside_exact a).mpr
    rintro ⟨p,hFrozen,hDisc⟩
    exact hNo ⟨p,hDisc⟩

theorem nil_outside_ordinary (a : A₀) (hNo : ¬ ∃ p : K.centres,a.val ∈ K.disc p) :
    Z.frame.oldMap ⟨(Z.map a).val,(Z.map a).property,(Z.nil_live_complement a).mpr hNo⟩=Z.ordinaryMap a :=
  Z.live_agrees a ((Z.nil_live_complement a).mpr hNo)

theorem nil_core_labels_unique (h00 : M ⊨ Axioms.ACVF00) (p q : K.centres)
    (hVF : tupleRV M (Z.map (K.centre p)).val.1=tupleRV M (Z.map (K.centre q)).val.1)
    (hRV : (Z.map (K.centre p)).val.2=(Z.map (K.centre q)).val.2) : p=q := by
  have hp : (Z.map (K.centre p)).val ∈ (Z.core_chart p).image :=
    ⟨K.centre p,K.centre_mem_disc p,rfl⟩
  have hq := rvPullback_mem_of_sameRV (Z.nil_core_image_rvPullback p) hp hVF hRV
  obtain ⟨a,ha,hEq⟩ := hq
  have he : a=K.centre q := (Z.chain.bijective h00).injective (Subtype.ext hEq)
  have hqDisc : q.val ∈ K.disc p := by
    rw [he] at ha
    exact ha
  exact (K.centre_unique_in_disc q p hqDisc).symm

end DiamondIntegral.Section6.UnaryFirstZeroState
