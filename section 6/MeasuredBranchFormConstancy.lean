import «section 6».MeasuredRVRefinementPreparation
import «section 6».FormCompatibleTagChainExtensions
import «section 6».ComplementaryBranchPreparation

/-! Exact forms on a measured branch agree on every whole ambient
output-label fibre meeting that branch. These comparisons use the
actual local and ambient maps, including their retained old labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}
variable {η : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (T : MeasuredCoordinatePreparation (G := G) C Q hQC η)
variable {X : SynchronizedTagBranchFrame C Q}
namespace SynchronizedTagBranchExtension

theorem source_form_constant_on_selected
    (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : Map X.ambient (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (p q : X.ambient) (he : (F.map p).val.2=(F.map q).val.2) (hpU : p.val.2 ∈ X.tags.carrier) :
    (ω p).val=(ω q).val := by
  have hRet := F.oldLabels_at
  have hOld : p.val.2=q.val.2 := (hRet p).symm.trans ((congrArg (fun u => u ∘ F.oldLabels) he).trans (hRet q))
  have hpC : p.val ∈ C.carrier := (Set.ext_iff.mp X.source_eq p.val).mpr ⟨p.property,hpU⟩
  have hqC : q.val ∈ C.carrier := (Set.ext_iff.mp X.source_eq q.val).mpr ⟨q.property,hOld ▸ hpU⟩
  let a : C := ⟨p.val,hpC⟩
  let b : C := ⟨q.val,hqC⟩
  have hImages : (T.map a).val.2=(T.map b).val.2 := by
    rw [← congrArg Prod.snd (F.branch a),← congrArg Prod.snd (F.branch b)]
    exact he
  have h := T.constant (T.map a).val (T.map a).property (T.map b).val (T.map b).property hImages
  rw [gammaFormExtension_at _ (T.map a),gammaFormExtension_at _ (T.map b)] at h
  exact (hForm a).symm.trans ((T.transport a).symm.trans (h.trans ((T.transport b).trans (hForm b))))

theorem source_form_constant
    (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : Map X.ambient (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (hOutside : ∀ p q : X.ambient,p.val.2=q.val.2 → p.val.2 ∉ X.tags.carrier → (ω p).val=(ω q).val) :
    ∀ p q : X.ambient,(F.map p).val.2=(F.map q).val.2 → (ω p).val=(ω q).val := by
  intro p q he
  by_cases hpU : p.val.2 ∈ X.tags.carrier
  · exact F.source_form_constant_on_selected T ω hForm p q he hpU
  · apply hOutside p q _ hpU
    exact (F.oldLabels_at p).symm.trans
      ((congrArg (fun u => u ∘ F.oldLabels) he).trans (F.oldLabels_at q))

theorem image_branch_form_constant
    (h00 : M ⊨ Axioms.ACVF00) (F : SynchronizedTagBranchExtension (G := G) X T.map hQC)
    (ω : Map X.ambient (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,X.subset p.property⟩).val)
    (Ω : Map F.output.ambient (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hTransport : ∀ p : X.ambient,(Ω (F.map p)).val=(ω p).val) :
    ∀ p q : F.output.ambient,p.val.2=q.val.2 → p.val.2 ∈ F.output.tags.carrier → (Ω p).val=(Ω q).val := by
  intro p q he hpU
  have hf := F.chain.toChain.toSpecial.bijective h00
  let a := F.map.inverse hf p
  let b := F.map.inverse hf q
  have hOut : (F.map a).val.2=(F.map b).val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact he
  have hIn : a.val.2 ∈ X.tags.carrier := (F.selected a).mp (by
    change (F.map (F.map.inverse hf p)).val.2 ∈ F.output.tags.carrier
    rw [Map.apply_inverse]
    exact hpU)
  have h := F.source_form_constant_on_selected T ω hForm a b hOut hIn
  have ha := hTransport a
  have hb := hTransport b
  rw [Map.apply_inverse] at ha hb
  exact ha.trans (h.trans hb.symm)

end SynchronizedTagBranchExtension
end DiamondIntegral.Section6
