import «section 3».GammaGroundNameReduction
import «section 5».EmptyGammaSortedDefinability

/-! Gamma names already definable over the real base introduce no new
sets in any actual imaginary presentation. Their full code preimages are
eliminated, without choosing a definable representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local reducible] DiamondIntegral.Section3.volumeGammaSpace
  DiamondIntegral.Section3.rebaseSpace SpecialTransformations.Section4.gammaSpace
  SpecialTransformations.DefinableGeometry.Space.power
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaRealName_singleton {S : Set M} (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base S) γ) :
    (volumeGammaSpace hc).Definable S {γ} := by
  have h := ((Section5.emptyGamma_sorted_definable_iff hc S (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Values.gammaPullback {γ}}).mp hγ).1
  change S.Definable LRV ((volumeGammaSpace hc).preimage {γ})
  have he : (volumeGammaSpace hc).preimage {γ} = {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}} := by
    ext z
    change (∃ hz : iRV (z 0) ∧ z 0 ≠ iRVZero, Values.gammaOf ⟨z 0,hz.1⟩ hz.2 ∈ ({γ} : Set _)) ↔ _
    exact ⟨fun ⟨hz,hv⟩ => ⟨hz.1,hz.2,hv⟩,fun ⟨hr,h0,hv⟩ => ⟨⟨hr,h0⟩,hv⟩⟩
  rw [he]
  exact h

theorem gammaRealNames_tuple_singleton {S : Set M} {k : ℕ} (γ : Fin k → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base S) (γ i)) :
    ((volumeGammaSpace hc).power (Fin k)).Definable S {γ} := by
  have hi (i : Fin k) := (gammaRealName_singleton (hc := hc) (γ i) (hγ i)).preimage_comp
    (fun j : Fin 1 => (i,j))
  have h := Set.definable_iInter_of_finite hi
  change S.Definable LRV (((volumeGammaSpace hc).power (Fin k)).preimage {γ})
  have he : ((volumeGammaSpace hc).power (Fin k)).preimage {γ} =
      ⋂ i : Fin k, (fun z : Fin k × Fin 1 → M => z ∘ fun j => (i,j)) ⁻¹'
        (volumeGammaSpace hc).preimage {γ i} := by
    ext z
    simp only [Set.mem_iInter,Set.mem_preimage]
    change (∃ hz : ∀ i, (fun j : Fin 1 => z (i,j)) ∈ (volumeGammaSpace hc).domain,
      (fun i => (volumeGammaSpace hc).decode ⟨fun j => z (i,j),hz i⟩) ∈ ({γ} : Set _)) ↔
        ∀ i, ∃ hz : (fun j : Fin 1 => z (i,j)) ∈ (volumeGammaSpace hc).domain,
          (volumeGammaSpace hc).decode ⟨fun j => z (i,j),hz⟩ ∈ ({γ i} : Set _)
    constructor
    · rintro ⟨hz,he⟩ i
      exact ⟨hz i,congrFun he i⟩
    · intro he
      choose hz hv using he
      exact ⟨hz,funext hv⟩
  rw [he]
  exact h

theorem GammaGroundDefinable.toRealNames
    (hNames : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base B.real) γ)
    {P : Space LRV M} {A : Set P.Carrier} (hA : GammaGroundDefinable hc B P A) : P.Definable B.real A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  have hTuple := gammaRealNames_tuple_singleton (hc := hc) γ (fun i => hNames (γ i) (hγ i))
  have hDown : GammaGroundDefinable hc (Section5.EmptyGammaGround.base B.real) P A :=
    GammaGroundDefinable.eliminateName hA (GammaGroundDefinable.of_real hTuple)
  exact (Section5.EmptyGammaGround.definable_iff hc B.real P A).mp hDown

def GammaGroundDefSet.toRealNames
    (hNames : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base B.real) γ)
    {P : Space LRV M} (A : GammaGroundDefSet hc B P) : DefSet P B.real :=
  ⟨A.carrier,A.definable.toRealNames hNames⟩

def GammaGroundMap.toRealNames
    (hNames : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base B.real) γ)
    {P Q : Space LRV M} {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q}
    (f : GammaGroundMap A D) : Map (A.toRealNames hNames) (D.toRealNames hNames) :=
  ⟨f.toFun,(relationDefinable_iff_product _).mpr (f.graph_definable.toRealNames hNames)⟩

end DiamondIntegral.Section3
