import IntegrationSection5.GammaPreparation
import Section5.GammaLift

/-! Actual special pullback preparation with any requested internal real
parameters retained in its presentation. Only the original base is small. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

theorem gamma_pullback_preparation_over {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (F : VFFieldBase G.real) (K : Set M) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) :
    ∃ l, ∃ B : Set (Point (M := M) n l), ∃ T : GammaSpecialBijection G A B,
      K ⊆ T.codes ∧ IsRVPullback B := by
  obtain ⟨d,t,ht,D,hD⟩ := gammaPresentationInput G A hA
  let R := (G.real ∪ Set.range (GammaParameters.rawTuple t)) ∪ K
  have hDR : G.real ∪ Set.range (GammaParameters.rawTuple t) ⊆ R := Set.subset_union_left
  have hGR : G.real ⊆ R := fun _ hx => Or.inl (Or.inl hx)
  let AR := extendBase D hDR
  have hAR : GammaSetDefinable G (carrier AR) := by
    change GammaSetDefinable G (carrier D)
    rw [hD]
    exact hA
  obtain ⟨r,s,A',B',TA,TB,hTA,hTB,hAP,_,_,_⟩ :=
    lemma_5_1_gamma_presented hs h00 hsmall F hGR hAR hAR (Map.id AR) (gamma_identity_graph AR hAR)
  let T : GammaSpecialBijection G A (carrier A') := ⟨R,hGR,AR,A',hD,rfl,TA,hTA⟩
  exact ⟨r,carrier A',T,Set.subset_union_right,hAP⟩

end IntegrationInACVF.Section5
