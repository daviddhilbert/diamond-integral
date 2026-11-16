import «section 6».UnaryFirstZeroCompletion
import «section 6».OrdinaryMatchingPairedExceptions

/-! A prescribed plan for the actual exceptional set and actual
finite-word bounds yields a completed original-base preparation. The
ordinary terminal map is the original ordinary special bijection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B}

theorem exists_unary_prescribed_core_realization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (T : OriginalBaseOrdinarySpecial A B f) (K : UnaryCorePlan A)
    (hProper : ProperInvariant S A.carrier) (hDB : VFDoublyBounded A.carrier)
    (hPullback : IsRVPullback A.carrier)
    (hTag : ∀ a ∈ A.carrier,∀ b ∈ A.carrier,a.2=b.2 → tupleRV M a.1=tupleRV M b.1)
    (hCover : ∀ a : A,(f a).val.1 0=(0 : VF M) ↔ a.val ∈ K.centres.carrier)
    (hBound : ∀ p : K.centres,
      ordinaryChainPointRadius T.special.chain
        ⟨p.val,(Set.ext_iff.mp T.source_eq p.val).mpr (K.subset p.property)⟩<K.radius p) :
    ∃ W : UnaryFirstZeroState (G := G) hc K (.nil T.target)
        (SpecialTransformations.Section5.GammaChainDefinable.target (ordinaryNamedGammaBase S) T.special.chain T.graphs),
      ∀ a : A,(W.ordinaryMap a).val=(f a).val := by
  let hSub : A.carrier ⊆ SpecialTransformations.Section5.carrier T.source :=
    fun p hp => (Set.ext_iff.mp T.source_eq p).mpr hp
  have hZero (a : A) :
      (T.special.chain.toMap ⟨a.val,hSub a.property⟩).val.1 0=(0 : VF M) ↔
        a.val ∈ K.centres.carrier := by
    have hAgree := T.agrees a
    change (T.special.chain.toMap ⟨a.val,hSub a.property⟩).val=(f a).val at hAgree
    rw [hAgree]
    exact hCover a
  let Z := UnaryFirstZeroState.initial hc K T.special.chain T.graphs hSub
    hProper hDB hPullback hTag hZero hBound
  obtain ⟨W,hW⟩ := UnaryFirstZeroState.exists_terminal h00 hκ hs hv hsmall T.special.chain T.graphs Z
  refine ⟨W,fun a => (hW a).trans (T.agrees a)⟩

theorem ordinary_sameRV_iff_rvCoordinates {q : ℕ} (p z : Mixed M 1 q) :
    SpecialTransformations.Section5.SameRV p z ↔ rvCoordinates M p=rvCoordinates M z := by
  rw [ordinary_sameRV_iff]
  constructor
  · rintro ⟨hVF,hRV⟩
    exact Prod.ext hVF hRV
  · intro h
    have hVF := congrArg Prod.fst h
    have hRV := congrArg Prod.snd h
    exact ⟨hVF,hRV⟩

theorem OriginalBaseOrdinaryUnaryMatching.sameRV_iff
    (F : OriginalBaseOrdinaryUnaryMatching A B f) (a b : A) :
    SpecialTransformations.Section5.SameRV (F.sourceMap a).val (F.sourceMap b).val ↔
      SpecialTransformations.Section5.SameRV (F.targetMap (f a)).val (F.targetMap (f b)).val := by
  rw [ordinary_sameRV_iff_rvCoordinates,ordinary_sameRV_iff_rvCoordinates]
  constructor
  · intro h
    have h' := F.forward (F.sourceMap a) (F.sourceMap b) h
    rwa [F.commutes a,F.commutes b] at h'
  · intro h
    have h' := F.reverse (F.targetMap (f a)) (F.targetMap (f b)) h
    have ha : F.map.inverse F.bijective (F.targetMap (f a))=F.sourceMap a := by
      rw [← F.commutes a,Map.inverse_apply]
    have hb : F.map.inverse F.bijective (F.targetMap (f b))=F.sourceMap b := by
      rw [← F.commutes b,Map.inverse_apply]
    rwa [ha,hb] at h'

end DiamondIntegral.Section6
