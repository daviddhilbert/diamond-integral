import «section 7».SpecialChainSplit

/-! Lemma 7.11 (`special:to:blowup:coa`): a general relative step on a chain set.

The image of relative aperture data `R` on a chain set `X` is the union of the
image of its active part (`RelativeRestrict.restrictActive`) and of the
inactive part with the tag `rv(1)` added. Both pieces are chain sets; the
first is a blowup of length one of the active part of `X`
(`SpecialChainStep.step_rel_active`), and the second has the class of the
inactive part. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.SpecialChainSplit DiamondIntegral.Section7.SpecialChainStep
open DiamondIntegral.Section7.RelativeRestrict DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r : ℕ}

/-! ### Labels with a given tail -/

section Tail
variable {S : Set M} (J : DefSet (rawRVSpace (M := M) r) S)

theorem decode_tail {z : Fin (1 + r) → M} (hz : z ∈ (rawRVSpace (M := M) (1 + r)).domain)
    (hz' : (fun i => z (Fin.natAdd 1 i)) ∈ (rawRVSpace (M := M) r).domain) :
    (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) =
      (rawRVSpace (M := M) r).decode ⟨_, hz'⟩ := by
  apply rvValues_injective
  have h1 := decode_rv ⟨z, hz⟩
  have h2 := decode_rv ⟨_, hz'⟩
  funext i
  have h3 := congrFun h1 (Fin.natAdd 1 i)
  have h4 := congrFun h2 i
  exact h3.trans h4.symm

theorem tailDef_definable : (rawRVSpace (M := M) (1 + r)).Definable S
    {L : Fin (1 + r) → RVInfinity M | (fun i => L (Fin.natAdd 1 i)) ∈ J.carrier} := by
  have h1 : S.Definable LRV ((rawRVSpace (M := M) r).preimage J.carrier) := J.definable
  have h2 := h1.preimage_comp (Fin.natAdd 1 : Fin r → Fin (1 + r))
  have h3 := ((rawRVSpace (M := M) (1 + r)).domain_definable).mono (Set.empty_subset S)
  change S.Definable LRV ((rawRVSpace (M := M) (1 + r)).preimage _)
  convert h3.inter h2 using 1
  ext z
  constructor
  · rintro ⟨hz, hJ⟩
    refine ⟨hz, ?_⟩
    have hz' : (fun i => z (Fin.natAdd 1 i)) ∈ (rawRVSpace (M := M) r).domain := by
      obtain ⟨t, ht⟩ := hz
      exact ⟨fun i => t (Fin.natAdd 1 i), funext (fun i => congrFun ht (Fin.natAdd 1 i))⟩
    refine ⟨hz', ?_⟩
    have hJ1 : (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) ∈ J.carrier := hJ
    rw [decode_tail hz hz'] at hJ1
    exact hJ1
  · rintro ⟨hz, hz', hJ⟩
    refine ⟨hz, ?_⟩
    change (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) ∈ J.carrier
    have hJ' : (rawRVSpace (M := M) r).decode ⟨fun i => z (Fin.natAdd 1 i), hz'⟩ ∈ J.carrier := hJ
    rw [decode_tail hz hz']
    exact hJ'

/-- The labels whose tail lies in `J`. -/
def tailDef : DefSet (rawRVSpace (M := M) (1 + r)) S := ⟨_, tailDef_definable J⟩

theorem mem_tailDef (L : Fin (1 + r) → RVInfinity M) :
    L ∈ (tailDef J).carrier ↔ (fun i => L (Fin.natAdd 1 i)) ∈ J.carrier := Iff.rfl

end Tail

end DiamondIntegral.Section7.SpecialChainRel
