import «section 6».UnaryFirstZeroCompletion

/-! At completion the prepared tag fibre of each frozen centre is
exactly the image of its prescribed original core. On the live locus,
equality of prepared labels is exactly ordinary SameRV. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
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

theorem nil_tags_iff_disc (h00 : M ⊨ Axioms.ACVF00) (p : K.centres) (a : A₀) :
    (Z.map a).val.2=(Z.map (K.centre p)).val.2 ↔ a.val ∈ K.disc p := by
  constructor
  · intro hTags
    have hVF := Z.frame.tagged (Z.map (K.centre p)).val (Z.map (K.centre p)).property
      (Z.map a).val (Z.map a).property hTags.symm
    have hp : (Z.map (K.centre p)).val ∈ (Z.core_chart p).image :=
      ⟨K.centre p,K.centre_mem_disc p,rfl⟩
    have ha := rvPullback_mem_of_sameRV (Z.nil_core_image_rvPullback p) hp hVF hTags.symm
    obtain ⟨b,hb,hba⟩ := ha
    have he : b=a := (Z.chain.bijective h00).injective (Subtype.ext hba)
    rw [he] at hb
    exact hb
  · intro ha
    exact (Z.core_chart p).tags a ha.1 ha.2

theorem nil_live_sameRV_iff_tags (a b : A₀)
    (ha : (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier)
    (hb : (Z.map b).val.2 ∈ Z.frame.liveLabels.carrier) :
    SpecialTransformations.Section5.SameRV (Z.ordinaryMap a).val (Z.ordinaryMap b).val ↔
      (Z.map a).val.2=(Z.map b).val.2 := by
  let x : Z.frame.liveFrame.source := ⟨(Z.map a).val,(Z.map a).property,ha⟩
  let y : Z.frame.liveFrame.source := ⟨(Z.map b).val,(Z.map b).property,hb⟩
  have hx : Z.frame.oldMap x=Z.ordinaryMap a := Z.live_agrees a ha
  have hy : Z.frame.oldMap y=Z.ordinaryMap b := Z.live_agrees b hb
  constructor
  · intro hSame
    exact Z.frame.faithful x y (by rwa [hx,hy])
  · intro hTags
    rw [← hx,← hy,Z.frame.point x,Z.frame.point y]
    apply (ordinary_sameRV_iff _ _).mpr
    exact ⟨Z.frame.tagged (Z.map a).val (Z.map a).property (Z.map b).val (Z.map b).property hTags,
      congrArg (fun u => u ∘ Z.frame.labels) hTags⟩

end DiamondIntegral.Section6.UnaryFirstZeroState
