import «section 7».SpecialChainStep

/-! Lemma 7.11 (`special:to:blowup:coa`): splitting a chain set along labels.

For a set `X` of a chain and a definable set `J` of labels, the pieces of `X`
with labels in and outside `J` are again chain sets, and the class of `X` is
the sum of their classes (`clsG_split`). The contraction of the regularization
of a piece is the corresponding restriction of the contraction of the
regularization of `X` (`resIso`, `cresIso`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainSplit
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r : ℕ}

section Split
variable {T : LRV.Substructure M} {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X)
variable (J : DefSet (rawRVSpace (M := M) r) (T : Set M))

/-- The piece of a chain set with labels in `J`. -/
def goodRes : Good T (focusActive X J) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      exact ⟨rvPullback_mem_of_sameRV g.pullback hp.1 h1 h2, h2 ▸ hp.2⟩
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := fun a => (g.finite a).subset (fun _ h => h.1)
  vfBounded := by
    obtain ⟨γ, hγ⟩ := g.vfBounded
    exact ⟨γ, fun p hp => hγ p hp.1⟩
  rvBounded := g.rvBounded.mono (fun _ h => h.1)
  form := g.form.comp (Map.inclusion (fun _ h => h.1))
  form_labels := fun p q he => g.form_labels ⟨p.val, p.property.1⟩ ⟨q.val, q.property.1⟩ he

theorem mem_reg_res {q : Mixed M n (n + r)} :
    q ∈ (regularizeMap (focusActive X J)).image.carrier ↔
      q ∈ (regularizeMap X).image.carrier ∧ (fun i => q.2 (Fin.natAdd n i)) ∈ J.carrier := by
  rw [mem_regularize, mem_regularize]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    have he : (fun i => (regularize p).2 (Fin.natAdd n i)) = p.2 := funext (fun i => regularize_snd_right p i)
    rw [he]
    exact hp.2
  · rintro ⟨⟨p, hp, rfl⟩, hJ⟩
    have he : (fun i => (regularize p).2 (Fin.natAdd n i)) = p.2 := funext (fun i => regularize_snd_right p i)
    rw [he] at hJ
    exact ⟨p, ⟨hp, hJ⟩, rfl⟩

end Split

end DiamondIntegral.Section7.SpecialChainSplit
