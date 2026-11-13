import «section 3».RVGeometricAngularQuotient
import «section 3».MixedGammaTupleLogic
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def rvUnitMixedRelation {hc : CanonicalStructure.IsCanonical (M := M)}
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S)
    (a : Fin n → M) (γ : Fin m → Values.Gamma (M := M)) : Prop :=
  ∃ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x = a ∧ (x,γ) ∈ T.carrier

theorem rvUnitMixedRelation_unit {hc : CanonicalStructure.IsCanonical (M := M)}
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (γ : Fin m → Values.Gamma (M := M)) :
    rvUnitMixedRelation T (rvUnitValues x) γ ↔ (x,γ) ∈ T.carrier :=
  ⟨fun ⟨y,he,hy⟩ => rvUnitValues_injective he ▸ hy,fun hx => ⟨x,rfl,hx⟩⟩

theorem rvUnitMixedRelation_proper {hc : CanonicalStructure.IsCanonical (M := M)}
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S)
    (a : Fin n → M) (γ : Fin m → Values.Gamma (M := M)) (ha : rvUnitMixedRelation T a γ) :
    ∀ i, iRV (a i) := by
  obtain ⟨x,rfl,hx⟩ := ha
  exact fun i => (x i).val.property

theorem rvUnitMixedRelation_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S) :
    mixedGammaTupleDefinable ⟨S,∅⟩ (rvUnitMixedRelation T) := by
  let R := rvUnitMixedRelation T
  let F (z : Fin n ⊕ Fin m → M) : Fin n ⊕ (Fin m × Fin 1) → M :=
    Sum.elim (fun i => z (.inl i)) (fun ij => z (.inr ij.1))
  have hh := T.definable.preimage_comp
    (Sum.elim (Sum.inl : Fin n → Fin n ⊕ Fin m) (fun ij : Fin m × Fin 1 => Sum.inr ij.1))
  have he : ((rawRVUnitSpace n).prod ((volumeGammaSpace hc).power (Fin m))).preimage T.carrier |> fun U =>
      F ⁻¹' U = {z | GammaSyntax.Proper (z ∘ Sum.inr) ∧ R (z ∘ Sum.inl) (GammaSyntax.decode (z ∘ Sum.inr))} := by
    ext z
    change (∃ hz : F z ∈ ((rawRVUnitSpace n).prod ((volumeGammaSpace hc).power (Fin m))).domain,
      ((rawRVUnitSpace n).decode ⟨z ∘ Sum.inl,hz.1⟩,
        ((volumeGammaSpace hc).power (Fin m)).decode ⟨fun ij => z (.inr ij.1),hz.2⟩) ∈ T.carrier) ↔ _
    have hd (hγ : GammaSyntax.Proper (z ∘ Sum.inr)) :
        ((volumeGammaSpace hc).power (Fin m)).decode ⟨fun ij => z (.inr ij.1),fun i => hγ i⟩ =
          GammaSyntax.decode (z ∘ Sum.inr) := by
      funext i
      exact (codeValue_raw ⟨⟨z (.inr i),(hγ i).1⟩,(hγ i).2⟩).symm
    constructor
    · rintro ⟨⟨hx,hγ⟩,hT⟩
      refine ⟨hγ,(rawRVUnitSpace n).decode ⟨z ∘ Sum.inl,hx⟩,rvUnitValues_decode _,?_⟩
      rw [← hd hγ]
      exact hT
    · rintro ⟨hγ,x,hx,hT⟩
      have hdom : z ∘ Sum.inl ∈ (rawRVUnitSpace (M := M) n).domain := ⟨x,hx⟩
      refine ⟨⟨hdom,fun i => hγ i⟩,?_⟩
      have hx' : (rawRVUnitSpace n).decode ⟨z ∘ Sum.inl,hdom⟩ = x :=
        rvUnitValues_injective ((rvUnitValues_decode _).trans hx.symm)
      rw [hx',hd hγ]
      exact hT
  have hraw : S.Definable LRV {z | GammaSyntax.Proper (z ∘ Sum.inr) ∧ R (z ∘ Sum.inl) (GammaSyntax.decode (z ∘ Sum.inr))} := by
    rw [← he]
    exact hh
  apply FullBaseAtomicity.OverBase.of_real
  rw [canonical_normalize_eq hc]
  exact hraw
end DiamondIntegral.Section3
