import «section 3».GammaMeasuredGeometricSchemata

/-! The native exact-row operations also commute with essential Gamma
density restriction. Bounds change metadata only. These identities allow
finite geometric proofs to reuse the native parameter-recoding machinery. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem gammaMeasured_rowAgreement_withBound
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B q a (k+1) sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F.toRVTemplate z G.toRVTemplate t)
    (N L : ℕ) : GammaVolumeRowAgreement (F.withBound N).toRVTemplate z (G.withBound L).toRVTemplate t := h

theorem gammaMeasured_rowAgreement_essential
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B q a (k+1) sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F.toRVTemplate z G.toRVTemplate t) :
    GammaVolumeRowAgreement F.essential.toRVTemplate z G.essential.toRVTemplate t := by
  have hObj := essentialFiniteVolumeSchema_rowAgreement h.1
  refine ⟨hObj,hObj.1,?_⟩
  intro x y
  change (_ ∈ F.density ∧ _ ∘ Fin.castAdd 1 ∈ _) ↔ (_ ∈ G.density ∧ _ ∘ Fin.castAdd 1 ∈ _)
  have hL : Fin.append (Fin.append z x) y ∘ Fin.castAdd 1 = Fin.append z x := funext (Fin.append_left _ _)
  have hR : Fin.append (Fin.append t x) y ∘ Fin.castAdd 1 = Fin.append t x := funext (Fin.append_left _ _)
  rw [hL,hR]
  exact and_congr (h.2.2 x y) (hObj.1 x)

theorem gammaMeasured_sameRow_of_agreements
    {E : GammaMeasuredRVSchema hc B p a (k+1) sp}
    {F G : GammaMeasuredRVSchema hc B q a (k+1) sq}
    {z : Fin p → M} {t : Fin q → M}
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement E.toRVTemplate z F.toRVTemplate t)
    (hG : GammaVolumeRowAgreement E.toRVTemplate z G.toRVTemplate t) :
    F.toRVTemplate.sameRow G.toRVTemplate t :=
  gammaVolumeSameRow_of_agreement ht hF hG (E.toRVTemplate.sameRow_refl z hz)

end DiamondIntegral.Section3
