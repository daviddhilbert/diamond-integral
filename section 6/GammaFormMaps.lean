import «section 6».MixedGammaCodeGraphs

/-! Actual maps to Gamma from full mixed Gamma graphs, and conversion
back from any actual definable Gamma map. The constructions agree on
their domains and retain all original-base real-code representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem sumMixedGammaGraph_eq_relation (A : DefSet (rawMixedSpace (M := M) n r) S)
    (f : A → DefSet.univ (rawGammaPresentation (M := M)) S) (ω : Mixed M n r → Gamma M)
    (hf : ∀ p : A, (f p).val = ω p.val) :
    (rawMixedSpace (M := M) n r).relation rawGammaPresentation
      (fun x γ => ∃ p : A, p.val = x ∧ (f p).val = γ) = sumMixedGammaGraph A.carrier ω := by
  ext z
  constructor
  · rintro ⟨hx,hγ,p,hpx,hpγ⟩
    refine ⟨hγ,p.val,p.property,?_,?_⟩
    · rw [hpx]
      exact mixedValues_decode _
    · exact hpγ.symm.trans (hf p)
  · rintro ⟨hγ,p,hp,hpc,hpγ⟩
    have hx : z ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain := hpc ▸ mixedValues_mem_domain p
    have hdecode : (rawMixedSpace n r).decode ⟨z ∘ Sum.inl,hx⟩ = p :=
      mixedValues_injective ((mixedValues_decode _).trans hpc.symm)
    refine ⟨hx,hγ,⟨p,hp⟩,hdecode.symm,?_⟩
    exact (hf ⟨p,hp⟩).trans hpγ.symm

def gammaFormMap (A : DefSet (rawMixedSpace (M := M) n r) S) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) := by
  let F (p : A) : DefSet.univ (rawGammaPresentation (M := M)) S := ⟨ω p.val,Set.mem_univ _⟩
  refine ⟨F,?_⟩
  change S.Definable LRV ((rawMixedSpace (M := M) n r).relation rawGammaPresentation
    (fun x γ => ∃ p : A, p.val = x ∧ (F p).val = γ))
  rw [sumMixedGammaGraph_eq_relation A F ω (fun _ => rfl)]
  exact sumMixedGammaGraph_definable A.carrier ω hω

theorem gammaFormMap_at (A : DefSet (rawMixedSpace (M := M) n r) S) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A.carrier ω)) (p : A) :
    (gammaFormMap A ω hω p).val = ω p.val := rfl

def gammaFormExtension {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : Mixed M n r) : Gamma M :=
  if hp : p ∈ A.carrier then (f ⟨p,hp⟩).val else 1

theorem gammaFormExtension_at {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    gammaFormExtension f p.val = (f p).val := by
  simp only [gammaFormExtension,dite_eq_left p.property]

theorem gammaFormExtension_graph_definable {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    S.Definable LRV (mixedGammaGraph A.carrier (gammaFormExtension f)) := by
  apply mixedGammaGraph_definable_of_sum
  have h : S.Definable LRV ((rawMixedSpace (M := M) n r).relation rawGammaPresentation
    (fun x γ => ∃ p : A, p.val = x ∧ (f p).val = γ)) := f.graph_definable
  rw [sumMixedGammaGraph_eq_relation A f (gammaFormExtension f)
    (fun p => (gammaFormExtension_at f p).symm)] at h
  exact h

theorem gammaFormExtension_comp_at {m s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (g : Map B A) (p : B) :
    gammaFormExtension (f.comp g) p.val = gammaFormExtension f (g p).val := by
  rw [gammaFormExtension_at,gammaFormExtension_at]
  rfl

theorem gammaFormExtension_inverse_transport {m s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    gammaFormExtension (ω.comp (f.inverse hf)) (f p).val = (ω p).val := by
  rw [gammaFormExtension_at]
  change (ω (f.inverse hf (f p))).val = (ω p).val
  rw [Map.inverse_apply]

end DiamondIntegral.Section6
