import «section 3».GammaMeasuredSchemaOperationValidity
import IntegrationSection6.GammaWitnessUniformity
import IntegrationSection6.GammaNativeRawObjects
import IntegrationSection6.GammaRawElementarySchemaBridge

/-! Uniform metadata bounds for measured RV families use the existing
finite-cover compactness over the original real/Gamma names. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {sp : Fin p → SortTag}

theorem GammaMeasuredRVSchema.withBound_valid_mono
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (z : Fin p → M)
    {N L : ℕ} (hNL : N ≤ L) (hF : (F.withBound N).valid z) : (F.withBound L).valid z := by
  refine ⟨⟨hF.1.1,hF.1.2.1,hF.1.2.2.1,?_⟩,hF.2⟩
  intro y hy
  exact ⟨(hF.1.2.2.2 y hy).1,(hF.1.2.2.2 y hy).2.trans hNL⟩

theorem GammaMeasuredRVSchema.exists_uniform_valid_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hExists : ∀ t ∈ T, ∃ N : ℕ, (F.withBound N).valid (rvValues t)) :
    ∃ N : ℕ, ∀ t ∈ T, (F.withBound N).valid (rvValues t) := by
  let A := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hr hg (fun _ => .rv) A
    (gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject)
    (fun N : ℕ => {z | (F.withBound N).valid z}) (fun N => (F.withBound N).valid_definable) (by
      rintro z ⟨u,rfl⟩
      exact hExists u.val (BP.domain_eq.le u.property))
  refine ⟨J.sup id,fun t ht => ?_⟩
  obtain ⟨N,hN,hValid⟩ := hJ (rvValues t) ⟨⟨t,BP.domain_eq.ge ht⟩,rfl⟩
  exact F.withBound_valid_mono _ (Finset.le_sup (f := id) hN) hValid

theorem GammaMeasuredRVSchema.exists_uniform_elementary_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A : ℕ)
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hAd : ∀ t ∈ T, (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid (rvValues t)) :
    ∃ N : ℕ, ∀ t ∈ T, (F.elementaryFormula.withBound N).valid (rvValues t) := by
  apply F.elementaryFormula.exists_uniform_valid_bound hκ hs hr hg BP
  intro t ht
  obtain ⟨P⟩ := F.object.realize (rvValues t) (hF t ht).1
  let Ad : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,A⟩
  obtain ⟨N,hN⟩ := F.object.exists_valid_elementary_bound hκ hs h00 hr hg (rvValues t)
    (hF t ht).1.1 P (Fin.last k) (Ad.admissible _ (hAd t ht) P)
  exact ⟨N,F.elementary_valid_of_bound _ (hF t ht) N hN⟩

end DiamondIntegral.Section3
