import «section 6».SynchronizedTagBranchAssembly

/-! Every finite synchronized branch chain extends to the entire
ambient set. The full protected images and selected next domain are
retained at each stage; outside the branch all VF coordinates are fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SynchronizedCentripetalChain.tag_branch_extension
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map C B}
    {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) (Fin k) C B f Q) :
    ∀ X : SynchronizedTagBranchFrame C Q,
      Nonempty (SynchronizedTagBranchExtension (G := G) X f (fun i => (h.atPiece i).source_subset)) := by
  induction h with
  | identity C hC Q hQC hQ =>
    intro X
    exact SynchronizedTagBranchExtension.ofMap h00 hc hκ hs hv X (Map.id C) Function.surjective_id
      hQC (Map.id X.ambient) (.identity _ X.proper X.pieces X.pieces_subset X.pieces_proper)
      (fun _ => rfl) (fun _ _ => rfl)
  | regularize C hC hCD Q hQC hQ hQD =>
    intro X
    exact SynchronizedTagBranchExtension.ofMap h00 hc hκ hs hv X (regularization C)
      (regularization_bijective C).surjective hQC (regularization X.ambient)
      (.regularize _ X.proper X.doublyBounded X.pieces X.pieces_subset X.pieces_proper
        (fun i => X.doublyBounded.mono (X.pieces_subset i))) (fun _ => rfl) (fun _ _ => rfl)
  | centripetal C D Q hQC E hData =>
    intro X
    exact X.extends_centripetal h00 hc hκ hs hv D E hData hQC
  | @comp r s t C B Z f g Q hQC hf hg ihf ihg =>
    intro X
    obtain ⟨F⟩ := ihf X
    obtain ⟨H⟩ := ihg F.output
    have hGlobal : SynchronizedCentripetalChain (G := G) (Fin k) X.ambient H.output.ambient
        (H.map.comp F.map) X.pieces :=
      .comp X.pieces X.pieces_subset F.chain (H.chain.changePieces (fun i => F.piece_images i))
    apply SynchronizedTagBranchExtension.ofMap h00 hc hκ hs hv X (g.comp f)
      ((hg.toChain.toSpecial.bijective h00).surjective.comp (hf.toChain.toSpecial.bijective h00).surjective)
      hQC (H.map.comp F.map) hGlobal
    · intro x
      have he : F.map ⟨x.val,X.subset x.property⟩=
          ⟨(f x).val,F.output.subset (f x).property⟩ := Subtype.ext (F.branch x)
      change (H.map (F.map ⟨x.val,X.subset x.property⟩)).val=(g (f x)).val
      rw [he]
      exact H.branch (f x)
    · intro x hx
      exact (H.outside (F.map x) (fun h => hx ((F.selected x).mp h))).trans (F.outside x hx)

end DiamondIntegral.Section6
