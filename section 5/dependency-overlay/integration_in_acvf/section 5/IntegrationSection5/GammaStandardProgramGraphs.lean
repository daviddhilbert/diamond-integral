import IntegrationSection5.StandardProgramComparison
import IntegrationSection5.GammaSurjectiveRVComparison

/-! Full original-Gamma graphs for standard programs and their actual raw
RV contractions; internal real source casts do not add named parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}

theorem standardProgram_program_gamma (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) (hT : GammaProgramDefinable G T) :
    GammaProgramDefinable G (standardContractionOfProgram A B σ hB T).program := by
  cases hB
  exact hT

theorem standardProgram_gamma_graph (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) (hA : GammaSetDefinable G (carrier A))
    (hT : GammaProgramDefinable G T) :
    GammaGraphDefinable G (pointMapGraph (standardContractionOfProgram A B σ hB T).toMap) := by
  cases hB
  exact gamma_composition_graph (vfPermutationBijection A σ) T.toMap
    (gamma_vfPermutation_graph A hA σ) (gamma_program_contraction_graph T hT)

theorem StandardContraction.gamma_raw_output {A : DefSet (M := M) S n m}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ)
    (hC : GammaGraphDefinable G (pointMapGraph C.toMap)) :
    GammaGraphDefinable G (rvOutputGraph C.rawContractionMap) := by
  apply GammaGraphDefinable.congr hC
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    exact ⟨a,ha,congrArg Prod.snd hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨a,ha,Prod.ext (funext fun i => i.elim0) hq⟩

theorem StandardContraction.gamma_rv_domain {A : DefSet (M := M) S n m}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ)
    (hU : GammaSetDefinable G (carrier C.target)) :
    GammaSetDefinable G {p : Point (M := M) 0 C.arity |
      p.2 ∈ carrier (rvObjectDomain C.contractionObject)} := by
  have he : {p : Point (M := M) 0 C.arity | p.2 ∈ carrier (rvObjectDomain C.contractionObject)} =
      carrier C.target := by
    ext p
    constructor
    · rintro ⟨u,hu⟩
      have hp : u.val = p := Prod.ext (funext fun i => i.elim0) hu
      exact hp ▸ u.property
    · intro hp
      exact ⟨⟨p,hp⟩,rfl⟩
  exact he.symm ▸ hU

end IntegrationInACVF.Section5
