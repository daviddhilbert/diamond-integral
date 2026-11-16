import «section 6».TaggedPreparedFamilies
import «section 6».TaggedPullbackRefinements
import «section 6».RVRefinementSynchronizedChains
import «section 6».UnaryIndexedActiveLoci

/-! After preparing one whole-label branch, its complement is an
actual retained-label refinement of the old complement. This transports
a second prepared branch without adding any new primitive operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def rvTagComplement (U : DefSet (rawRVSpace (M := M) r) S) : DefSet (rawRVSpace (M := M) r) S :=
  ⟨U.carrierᶜ,U.definable.compl _⟩

variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map C B}
variable {hQC : ∀ i,(Q i).carrier ⊆ C.carrier} {X : SynchronizedTagBranchFrame C Q}
namespace SynchronizedTagBranchExtension
variable (F : SynchronizedTagBranchExtension (G := G) X f hQC)

def oldLabels : Fin r → Fin s := rvTailIndex F.chain.toChain.toSpecial.retainsRV.choose

theorem oldLabels_at (p : X.ambient) : (F.map p).val.2 ∘ F.oldLabels=p.val.2 :=
  funext (F.chain.toChain.toSpecial.retainsRV.choose_spec p)

theorem outside_recover (h00 : M ⊨ Axioms.ACVF00) (z : F.output.ambient)
    (hOut : z.val.2 ∉ F.output.tags.carrier) :
    ∃ a : X.ambient,(F.map a).val=z.val ∧
      (z.val.1,z.val.2 ∘ F.oldLabels)=a.val ∧ a.val.2 ∉ X.tags.carrier := by
  obtain ⟨a,ha⟩ := (F.chain.toChain.toSpecial.bijective h00).surjective z
  have he : (F.map a).val=z.val := congrArg Subtype.val ha
  have haOut : a.val.2 ∉ X.tags.carrier := fun h => hOut (he ▸ (F.selected a).mpr h)
  refine ⟨a,he,Prod.ext ?_ ?_,haOut⟩
  · exact (congrArg Prod.fst he).symm.trans (F.outside a haOut)
  · exact (congrArg (fun p : Mixed M n s => p.2 ∘ F.oldLabels) he).symm.trans (F.oldLabels_at a)

def outsideFrame (h00 : M ⊨ Axioms.ACVF00)
    (hA : IsRVPullback X.ambient.carrier)
    (hTag : ∀ p ∈ X.ambient.carrier,∀ z ∈ X.ambient.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) :
    RVRefinementFrame (focusActive X.ambient (rvTagComplement X.tags)) :=
  RVRefinementFrame.of_tagged_pullback _
    (focusActive F.output.ambient (rvTagComplement F.output.tags)) F.oldLabels
    (focusActive_properInvariant _ F.output.proper _) (F.output.doublyBounded.mono (fun _ hp => hp.1))
    (focusActive_rvPullback _ _ (F.chain.toChain.target_rvPullback h00 hA))
    (fun p hp z hz => hTag p hp.1 z hz.1) (by
      intro p hp
      obtain ⟨a,ha,hOld,hOut⟩ := F.outside_recover h00 ⟨p,hp.1⟩ hp.2
      exact hOld.symm ▸ (show a.val ∈ (focusActive X.ambient (rvTagComplement X.tags)).carrier from
        ⟨a.property,hOut⟩))

theorem outsideFrame_piece
    (h00 : M ⊨ Axioms.ACVF00) (hA : IsRVPullback X.ambient.carrier)
    (hTag : ∀ p ∈ X.ambient.carrier,∀ z ∈ X.ambient.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (i : Fin k) :
    (F.outsideFrame h00 hA hTag).selectedPiece (focusActive (X.pieces i) (rvTagComplement X.tags))=
      focusActive (F.output.pieces i) (rvTagComplement F.output.tags) := by
  apply defSet_eq_of_carrier_eq
  ext z
  constructor
  · intro hz
    obtain ⟨hzBase,hOld⟩ := ((F.outsideFrame h00 hA hTag).mem_selectedPiece _ z).mp hz
    obtain ⟨a,ha,hOldEq,hOut⟩ := F.outside_recover h00 ⟨z,hzBase.1⟩ hzBase.2
    have haP : a.val ∈ (X.pieces i).carrier := by
      change (z.1,z.2 ∘ F.oldLabels) ∈ (focusActive (X.pieces i) (rvTagComplement X.tags)).carrier at hOld
      rw [hOldEq] at hOld
      exact hOld.1
    refine ⟨?_,hzBase.2⟩
    rw [F.piece_images i]
    exact ⟨⟨a.val,haP⟩,ha⟩
  · rintro ⟨hzPi,hOut⟩
    have hzA := F.output.pieces_subset i hzPi
    obtain ⟨a,ha,hOldEq,haOut⟩ := F.outside_recover h00 ⟨z,hzA⟩ hOut
    have hzImage := hzPi
    rw [F.piece_images i] at hzImage
    obtain ⟨b,hb⟩ := hzImage
    have hab : a=⟨b.val,X.pieces_subset i b.property⟩ :=
      (F.chain.toChain.toSpecial.bijective h00).injective (Subtype.ext (ha.trans hb.symm))
    have haP : a.val ∈ (X.pieces i).carrier := by rw [hab]; exact b.property
    apply ((F.outsideFrame h00 hA hTag).mem_selectedPiece _ z).mpr
    refine ⟨⟨hzA,hOut⟩,?_⟩
    change (z.1,z.2 ∘ F.oldLabels) ∈ (focusActive (X.pieces i) (rvTagComplement X.tags)).carrier
    rw [hOldEq]
    exact ⟨haP,haOut⟩

end SynchronizedTagBranchExtension
end DiamondIntegral.Section6
