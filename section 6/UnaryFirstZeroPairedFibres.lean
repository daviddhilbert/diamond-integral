import «section 6».UnaryFirstZeroFibres
import «section 6».RVTagConjugation

/-! Completed prescribed-core preparations on both sides recover the
whole prepared tag matching. The proof uses the actual paired original
discs and ordinary comparison only on their common complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R Q : Set M} {r₀ s₀ r s : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {B₀ : DefSet (rawMixedSpace (M := M) 1 s₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀} {L : UnaryCorePlan B₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) Q 1 s}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable {hB : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier B)}
variable (Z : UnaryFirstZeroState (G := G) hc K (.nil A) hA)
variable (Y : UnaryFirstZeroState (G := G) hc L (.nil B) hB)
variable (f : Map A₀ B₀) (C : K.centres → L.centres) (hC : Function.Surjective C)
variable (hPaired : ∀ (p : K.centres) (a : A₀),a.val ∈ K.disc p ↔ (f a).val ∈ L.disc (C p))

include hC hPaired in
theorem firstZero_paired_live_iff (a : A₀) :
    (Y.map (f a)).val.2 ∈ Y.frame.liveLabels.carrier ↔ (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier := by
  rw [Y.nil_live_complement,Z.nil_live_complement]
  constructor
  · intro hNo
    rintro ⟨p,hp⟩
    exact hNo ⟨C p,(hPaired p a).mp hp⟩
  · intro hNo
    rintro ⟨q,hq⟩
    obtain ⟨p,rfl⟩ := hC q
    exact hNo ⟨p,(hPaired p a).mpr hq⟩

include hC hPaired in
theorem firstZero_paired_tags_iff (h00 : M ⊨ Axioms.ACVF00)
    (hOrdinary : ∀ a b : A₀,
      SpecialTransformations.Section5.SameRV (Z.ordinaryMap a).val (Z.ordinaryMap b).val ↔
        SpecialTransformations.Section5.SameRV (Y.ordinaryMap (f a)).val (Y.ordinaryMap (f b)).val)
    (a b : A₀) :
    (Y.map (f a)).val.2=(Y.map (f b)).val.2 ↔ (Z.map a).val.2=(Z.map b).val.2 := by
  constructor
  · intro hTags
    by_cases ha : (Y.map (f a)).val.2 ∈ Y.frame.liveLabels.carrier
    · have hb : (Y.map (f b)).val.2 ∈ Y.frame.liveLabels.carrier := hTags ▸ ha
      have hOld := (Y.nil_live_sameRV_iff_tags (f a) (f b) ha hb).mpr hTags
      exact (Z.nil_live_sameRV_iff_tags a b
        ((firstZero_paired_live_iff Z Y f C hC hPaired a).mp ha)
        ((firstZero_paired_live_iff Z Y f C hC hPaired b).mp hb)).mp ((hOrdinary a b).mpr hOld)
    · have hSome : ∃ q : L.centres,(f a).val ∈ L.disc q := by
        by_contra hn
        exact ha ((Y.nil_live_complement (f a)).mpr hn)
      obtain ⟨q,hqa⟩ := hSome
      obtain ⟨p,rfl⟩ := hC q
      have hqb : (f b).val ∈ L.disc (C p) :=
        (Y.nil_tags_iff_disc h00 (C p) (f b)).mp
          (hTags.symm.trans ((Y.nil_tags_iff_disc h00 (C p) (f a)).mpr hqa))
      exact ((Z.nil_tags_iff_disc h00 p a).mpr ((hPaired p a).mpr hqa)).trans
        ((Z.nil_tags_iff_disc h00 p b).mpr ((hPaired p b).mpr hqb)).symm
  · intro hTags
    by_cases ha : (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier
    · have hb : (Z.map b).val.2 ∈ Z.frame.liveLabels.carrier := hTags ▸ ha
      have hOld := (Z.nil_live_sameRV_iff_tags a b ha hb).mpr hTags
      exact (Y.nil_live_sameRV_iff_tags (f a) (f b)
        ((firstZero_paired_live_iff Z Y f C hC hPaired a).mpr ha)
        ((firstZero_paired_live_iff Z Y f C hC hPaired b).mpr hb)).mp ((hOrdinary a b).mp hOld)
    · have hSome : ∃ p : K.centres,a.val ∈ K.disc p := by
        by_contra hn
        exact ha ((Z.nil_live_complement a).mpr hn)
      obtain ⟨p,hpa⟩ := hSome
      have hpb : b.val ∈ K.disc p :=
        (Z.nil_tags_iff_disc h00 p b).mp (hTags.symm.trans ((Z.nil_tags_iff_disc h00 p a).mpr hpa))
      exact ((Y.nil_tags_iff_disc h00 (C p) (f a)).mpr ((hPaired p a).mp hpa)).trans
        ((Y.nil_tags_iff_disc h00 (C p) (f b)).mpr ((hPaired p b).mp hpb)).symm

def firstZeroConjugate (h00 : M ⊨ Axioms.ACVF00) : Map Z.frame.current Y.frame.current :=
  Y.map.comp (f.comp (Z.map.inverse (Z.chain.bijective h00)))

theorem firstZeroConjugate_at (h00 : M ⊨ Axioms.ACVF00) (a : A₀) :
    firstZeroConjugate Z Y f h00 (Z.map a)=Y.map (f a) := by
  change Y.map (f (Z.map.inverse _ (Z.map a)))=Y.map (f a)
  rw [Map.inverse_apply]

theorem firstZeroConjugate_bijective (h00 : M ⊨ Axioms.ACVF00) (hf : Function.Bijective f) :
    Function.Bijective (firstZeroConjugate Z Y f h00) := by
  have hInv : Function.Bijective (Z.map.inverse (Z.chain.bijective h00)) := by
    constructor
    · intro a b he
      have h := congrArg Z.map he
      simpa only [Map.apply_inverse] using h
    · intro a
      exact ⟨Z.map a,Map.inverse_apply Z.map (Z.chain.bijective h00) a⟩
  exact (Y.chain.bijective h00).comp (hf.comp hInv)

include hC hPaired in
theorem firstZeroConjugate_whole_fibres (h00 : M ⊨ Axioms.ACVF00) (hf : Function.Bijective f)
    (hOrdinary : ∀ a b : A₀,
      SpecialTransformations.Section5.SameRV (Z.ordinaryMap a).val (Z.ordinaryMap b).val ↔
        SpecialTransformations.Section5.SameRV (Y.ordinaryMap (f a)).val (Y.ordinaryMap (f b)).val) :
    MapsWholeTagFibres (firstZeroConjugate Z Y f h00) := by
  apply mapsWholeTagFibres_of_tag_equivalence _ (firstZeroConjugate_bijective Z Y f h00 hf).surjective
  intro x y
  obtain ⟨a,rfl⟩ := (Z.chain.bijective h00).surjective x
  obtain ⟨b,rfl⟩ := (Z.chain.bijective h00).surjective y
  rw [firstZeroConjugate_at Z Y f h00 a,firstZeroConjugate_at Z Y f h00 b]
  exact firstZero_paired_tags_iff Z Y f C hC hPaired h00 hOrdinary a b

end DiamondIntegral.Section6
