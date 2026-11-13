import «section 3».GammaGroundRawDescent
import Section3.GammaBaseTools
import Section3.GammaRVSeparation
import Section4.FiniteCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {Q : Space LRV M}

/-- The common real names are used only to apply saturation. The
resulting definitions and finite subcovers retain their original mixed base. -/
theorem GammaGroundDefinable.common_names {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) : Q.Definable (commonRealNames B) A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  let c : ((volumeGammaSpace hc).power (Fin k)).domain :=
    ⟨fun ij => raw (representative (γ ij.1)),fun i => rawTuple_proper (representatives γ) i⟩
  have hcγ : ((volumeGammaSpace hc).power (Fin k)).decode c = γ := by
    funext i
    change value (representative (γ i)) = γ i
    exact representative_value _
  apply (hA.over_real_code c hcγ).mono
  rintro x (hx | ⟨i,rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨γ i.1,hγ i.1,rfl⟩

/-- Genuine saturation gives a finite subcover for arbitrary interpreted
finite-tuple presentations over the original small real/Gamma base. -/
theorem gammaGround_definable_finite_subcover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A : GammaGroundDefSet hc B Q) (C : Set (Set Q.Carrier))
    (hC : ∀ U ∈ C, GammaGroundDefinable hc B Q U)
    (hcover : ∀ a ∈ A.carrier, ∃ U ∈ C, a ∈ U) :
    ∃ D : Set (Set Q.Carrier), D.Finite ∧ D ⊆ C ∧
      ∀ a ∈ A.carrier, ∃ U ∈ D, a ∈ U := by
  let S := commonRealNames B
  have hA : S.Definable LRV (Q.preimage A.carrier) := A.definable.common_names
  have hCs : ∀ U ∈ Q.preimage '' C, S.Definable LRV U := by
    rintro U ⟨V,hV,rfl⟩
    exact (hC V hV).common_names
  have hcov : ∀ z ∈ Q.preimage A.carrier, ∃ U ∈ Q.preimage '' C, z ∈ U := by
    rintro z ⟨hz,ha⟩
    obtain ⟨U,hU,haU⟩ := hcover (Q.decode ⟨z,hz⟩) ha
    exact ⟨Q.preimage U,⟨U,hU,rfl⟩,hz,haU⟩
  obtain ⟨E,hE,hEC,hcovE⟩ := definable_finite_subcover_index hs S
    (commonRealNames_small hκ B hsmall hγsmall) (Q.preimage A.carrier) hA
    (Q.preimage '' C) hCs hcov
  let D : Set (Set Q.Carrier) := {U | U ∈ C ∧ Q.preimage U ∈ E}
  refine ⟨D,(hE.preimage Q.preimage_injective.injOn).subset (fun _ h => h.2),
    fun _ h => h.1,?_⟩
  intro a ha
  obtain ⟨z,hz⟩ := Q.onto a
  have hzA : z.val ∈ Q.preimage A.carrier := (Q.preimage_decode A.carrier z).mpr (hz.symm ▸ ha)
  obtain ⟨V,hV,hzV⟩ := hcovE z.val hzA
  obtain ⟨U,hU,he⟩ := hEC hV
  refine ⟨U,⟨hU,he.symm ▸ hV⟩,?_⟩
  have hu : z.val ∈ Q.preimage U := he.symm ▸ hzV
  exact hz ▸ (Q.preimage_decode U z).mp hu
end DiamondIntegral.Section3
