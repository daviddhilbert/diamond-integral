import «section 2».UniformPartialChoice
import «section 2».TypeFibres

/-! Uniform VF choice when each fibre has a point definable over its
actual real input parameters. Promotion of a singleton, compactness, and
finite priority prove the choice; there is no Skolem-function premise. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

private theorem raw_scalar_relation_to_sum (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : S.Definable LRV {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ R}) :
    S.Definable LRV {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ R} := by
  let idx : Fin (n+1) → Fin n ⊕ Fin 1 := Fin.lastCases (.inr 0) Sum.inl
  convert hR.preimage_comp idx using 1
  ext z
  have hi : Fin.init (z ∘ idx) = z ∘ Sum.inl := by
    funext i
    change z (idx i.castSucc) = z (.inl i)
    simp only [idx,Fin.lastCases_castSucc]
  change (z ∘ Sum.inl,z (.inr 0)) ∈ R ↔ (Fin.init (z ∘ idx),(z ∘ idx) (Fin.last n)) ∈ R
  rw [hi]
  simp only [idx,Function.comp_apply,Fin.lastCases_last]

theorem uniform_vf_choice_of_pointwise_definable
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (sn : Fin n → SortTag) (J : Set (Fin n → M)) (hJ : DefinableOver S sn J)
    (T : Set ((Fin n → M) × M))
    (hT : DefinableOver S (Fin.lastCases .vf sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ T})
    (hpoint : ∀ p ∈ J, ∃ x : M, (p,x) ∈ T ∧
      GammaParameters.DefinableClosureAtBase (tupleBase (⟨S,∅⟩ : ParameterBase M) p) .vf x) :
    ∃ f : (Fin n → M) → M,
      S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z ∘ Sum.inl ∈ J ∧ f (z ∘ Sum.inl) = z (.inr 0)} ∧
      ∀ p ∈ J, (p,f p) ∈ T := by
  let B : ParameterBase M := ⟨S,∅⟩
  have hsort : J ⊆ GammaParameters.sortedUniverse sn := by
    obtain ⟨p,φ,hφ,rfl⟩ := hJ
    exact fun _ hp => hp.1
  have hTr := raw_scalar_relation_to_sum S T hT.raw_definable
  apply uniform_partial_unique_choice hs S hsmall J hJ.raw_definable (fun p => {x | (p,x) ∈ T})
  intro p hp
  obtain ⟨x,hxT,hx⟩ := hpoint p hp
  obtain ⟨P,hP,hrow⟩ := GammaParameters.promote_scalar_definable_base B sn p (hsort hp) .vf {x} hx
  have hPdef : DefinableOver S (Fin.lastCases .vf sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ P} := (GammaParameters.base_empty_iff S _ _).mp hP
  have hPr := raw_scalar_relation_to_sum S P hPdef.raw_definable
  let R (q : Fin n → M) : Set M := {y | (q,y) ∈ P ∧ (q,y) ∈ T}
  have hR : S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)} := by
    convert hPr.inter hTr using 1
    ext z
    rfl
  refine ⟨R,hR,fun _ _ _ h => h.2,?_⟩
  change ∃! y, (p,y) ∈ P ∧ (p,y) ∈ T
  refine ⟨x,⟨(Set.ext_iff.mp hrow x).mpr (Set.mem_singleton x),hxT⟩,?_⟩
  rintro y ⟨hy,_⟩
  exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hrow y).mp hy)

end DiamondIntegral.Section2
