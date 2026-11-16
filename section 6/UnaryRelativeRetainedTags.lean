import «section 6».UnaryRelativeApertureChains
import «section 6».RetainedRVTags

/-! Every auxiliary variable-aperture chain retains all original RV
coordinates. Thus any original form constant on label fibres stays
constant after transport by the actual inverse preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureChain
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B}

theorem retainsRV (H : UnaryRelativeApertureChain (G := G) A B f) :
    ∃ h : r ≤ s, ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i)=p.val.2 i := by
  induction H with
  | original h => exact h.retainsRV
  | relative A D =>
      refine ⟨by omega,?_⟩
      intro p i
      change Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core p.val)) p.val.2 (rvTailIndex _ i)=p.val.2 i
      exact append_rvTailIndex _ _ _ i
  | @comp r s t A B C f g hf hg ihf ihg =>
      obtain ⟨hrs,hfRV⟩ := ihf
      obtain ⟨hst,hgRV⟩ := ihg
      refine ⟨hrs.trans hst,fun p i => ?_⟩
      change (g (f p)).val.2 (rvTailIndex (hrs.trans hst) i)=p.val.2 i
      rw [← rvTailIndex_comp hrs hst i]
      exact (hgRV (f p) (rvTailIndex hrs i)).trans (hfRV p i)

theorem inverse_labels (H : UnaryRelativeApertureChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (p q : B) (hTags : p.val.2=q.val.2) :
    (f.inverse (H.bijective h00) p).val.2=(f.inverse (H.bijective h00) q).val.2 := by
  obtain ⟨h,hh⟩ := H.retainsRV
  funext i
  have hp := hh (f.inverse (H.bijective h00) p) i
  have hq := hh (f.inverse (H.bijective h00) q) i
  rw [Map.apply_inverse] at hp hq
  exact hp.symm.trans ((congrFun hTags (rvTailIndex h i)).trans hq)

end DiamondIntegral.Section6.UnaryRelativeApertureChain
