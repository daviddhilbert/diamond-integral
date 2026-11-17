import «section 3».GammaMeasuredLabelSchemata
import IntegrationSection6.GammaSortedSchemaRows
import IntegrationSection6.GammaSchemaFiniteRowPresentations
import IntegrationSection6.GammaWitnessUniformity

/-! Finite-volume rows carrying a fixed actual Gamma form have one
uniform structural bound over the original base. Completeness of the
Gamma code relation is retained when the bound is increased. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem gammaMeasuredLabelSchema_exists_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hfin : F.finiteRow z) (hA : F.rowDomain z ⊆ A.carrier) :
    ∃ N : ℕ, (gammaMeasuredLabelSchema (F.withBound N) ω).valid z := by
  obtain ⟨P⟩ := F.realize_finiteRow z hz hfin
  obtain ⟨N,hN⟩ := F.exists_valid_bound hκ hs hr hg z hz hfin.2.1 P
  exact ⟨N,gammaMeasuredLabelSchema_valid (F.withBound N) ω z hN hA⟩

theorem gammaMeasuredLabelSchema_bound_mono
    (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A)
    {N L : ℕ} (hNL : N ≤ L) (z : Fin p → M)
    (hF : (gammaMeasuredLabelSchema (F.withBound N) ω).valid z) :
    (gammaMeasuredLabelSchema (F.withBound L) ω).valid z := by
  refine ⟨⟨hF.1.1,hF.1.2.1,hF.1.2.2.1,?_⟩,hF.2⟩
  intro y hy
  exact ⟨(hF.1.2.2.2 y hy).1,(hF.1.2.2.2 y hy).2.trans hNL⟩

theorem gammaMeasuredLabelSchema_uniform_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A)
    (hfin : ∀ z, (∀ j, sortEval (sp j) (z j)) → F.finiteRow z)
    (hA : ∀ z, (∀ j, sortEval (sp j) (z j)) → F.rowDomain z ⊆ A.carrier) :
    ∃ N : ℕ, ∀ z, (∀ j, sortEval (sp j) (z j)) → (gammaMeasuredLabelSchema (F.withBound N) ω).valid z := by
  have hAll : DefinableOverBase B sp (sortedUniverse sp) :=
    real_definableOverBase B sp _ (sortedUniverse_definable B.real sp)
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hr hg sp (sortedUniverse sp) hAll
    (fun N : ℕ => {z | (gammaMeasuredLabelSchema (F.withBound N) ω).valid z})
    (fun N => (gammaMeasuredLabelSchema (F.withBound N) ω).valid_definable) (by
      intro z hz
      exact gammaMeasuredLabelSchema_exists_bound hκ hs hr hg F ω z hz (hfin z hz) (hA z hz))
  refine ⟨J.sup id,fun z hz => ?_⟩
  obtain ⟨N,hN,hValid⟩ := hJ z hz
  exact gammaMeasuredLabelSchema_bound_mono F ω (Finset.le_sup (f := id) hN) z hValid

end DiamondIntegral.Section3
