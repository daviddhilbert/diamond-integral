import «section 5».OriginalGammaFamilyRealizations
import «section 5».OriginalRVRowObjects

/-! Literal total RV families over an original raw RV parameter domain.
The base coordinates are retained, including all zero entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

theorem rvValues_mem_rawDomain_iff (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (x : Fin p → CanonicalRV.RVSort M) : rvValues x ∈ rawDomain X ↔ x ∈ X.carrier := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact rvValues_injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem originalRVTotalFamily_raw_definable
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) :
    DefinableOverBase B (fun _ : Fin (p+a) => .rv)
      {w | w ∈ D.val ∧ w ∘ Fin.castAdd a ∈ rawDomain X} := by
  have hD := allRVGammaDomain_definable D
  have hX := (rawDomain_definable X).preimage_real (fun _ : Fin (p+a) => .rv) (Fin.castAdd a)
  have h := hD.inter hX
  convert h using 1
  ext w
  change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact ⟨fun h => ⟨h.1,h.2,hD.proper w h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩

def originalRVTotalFamily
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) (p+a)) :=
  ofRaw {w | w ∈ D.val ∧ w ∘ Fin.castAdd a ∈ rawDomain X} (originalRVTotalFamily_raw_definable X D)

theorem originalRVTotalFamily_mem
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (u : Fin (p+a) → CanonicalRV.RVSort M) :
    u ∈ (originalRVTotalFamily X D).carrier ↔
      u ∘ Fin.castAdd a ∈ X.carrier ∧ rvValues u ∈ D.val := by
  change (_ ∧ _) ↔ _
  have he : rvValues u ∘ Fin.castAdd a = rvValues (u ∘ Fin.castAdd a) := rfl
  rw [he,rvValues_mem_rawDomain_iff]
  exact and_comm

end DiamondIntegral.Section5
