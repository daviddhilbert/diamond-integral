import «section 6».UnaryRelativePreparedMatching
import «section 6».GammaFormMaps

/-! Actual transported Gamma forms for auxiliary unary matching. Their
graphs remain over the original base and their constancy follows from
the proved retention of every original RV label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativePreparedMatching
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} (H : UnaryRelativePreparedMatching (G := G) A B f)
variable (h00 : M ⊨ Axioms.ACVF00)

def sourceForm (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :=
  ω.comp (H.sourceMap.inverse (H.sourceChain.bijective h00))

def targetForm (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)) :=
  σ.comp (H.targetMap.inverse (H.targetChain.bijective h00))

theorem sourceForm_transport (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : A) :
    H.sourceForm h00 ω (H.sourceMap a)=ω a := by
  change ω (H.sourceMap.inverse _ (H.sourceMap a))=ω a
  rw [Map.inverse_apply]

theorem targetForm_transport (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)) (b : B) :
    H.targetForm h00 σ (H.targetMap b)=σ b := by
  change σ (H.targetMap.inverse _ (H.targetMap b))=σ b
  rw [Map.inverse_apply]

theorem sourceForm_constant (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ a b : A,a.val.2=b.val.2 → ω a=ω b)
    (p q : H.source) (hTags : p.val.2=q.val.2) : H.sourceForm h00 ω p=H.sourceForm h00 ω q :=
  hω _ _ (H.sourceChain.inverse_labels h00 p q hTags)

theorem targetForm_constant (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hσ : ∀ a b : B,a.val.2=b.val.2 → σ a=σ b)
    (p q : H.target) (hTags : p.val.2=q.val.2) : H.targetForm h00 σ p=H.targetForm h00 σ q :=
  hσ _ _ (H.targetChain.inverse_labels h00 p q hTags)

theorem map_eq_conjugate : H.map=H.targetMap.comp (f.comp (H.sourceMap.inverse (H.sourceChain.bijective h00))) := by
  apply Map.ext
  intro p
  obtain ⟨a,rfl⟩ := (H.sourceChain.bijective h00).surjective p
  change H.map (H.sourceMap a)=H.targetMap (f (H.sourceMap.inverse _ (H.sourceMap a)))
  rw [Map.inverse_apply,H.commutes a]

end DiamondIntegral.Section6.UnaryRelativePreparedMatching
