import «section 6».NamedGammaFibreValues

/-! A Gamma-valued map constant on old-label fibres descends without
choosing or naming an RV representative. Empty fibres receive value one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def gammaFibreValue (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (u : Fin r → RVInfinity M) : Gamma M :=
  if h : ∃ p : A,p.val.2=u then (f h.choose).val else 1

theorem gammaFibreValue_at (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : A,p.val.2=q.val.2 → (f p).val=(f q).val) (p : A) :
    gammaFibreValue f p.val.2=(f p).val := by
  have h : ∃ q : A,q.val.2=p.val.2 := ⟨p,rfl⟩
  rw [gammaFibreValue,dite_eq_left h]
  exact hConst h.choose p h.choose_spec

theorem gammaFibreValue_named
    (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : A,p.val.2=q.val.2 → (f p).val=(f q).val) (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {gammaFibreValue f u}} := by
  by_cases h : ∃ p : A,p.val.2=u
  · apply gamma_value_named_on_rv_fibre A.carrier (gammaFormExtension f)
      (gammaFormExtension_graph_definable f) u (gammaFibreValue f u)
      ⟨h.choose.val,h.choose.property,h.choose_spec⟩
    intro p hp hpu
    rw [gammaFormExtension_at f ⟨p,hp⟩,← gammaFibreValue_at f hConst ⟨p,hp⟩,hpu]
  · rw [gammaFibreValue,dite_eq_right h]
    exact gamma_one_named hc

end DiamondIntegral.Section6
