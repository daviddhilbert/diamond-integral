import «section 6».DiamondGroupoid
import «section 6».ClopenCriterion

/-! (Moved from `section 7/IntermediateFormsProofLocal.lean`, branch `claude/intermediate-forms-proof`, commit 7b2b7ed2, for the repaired Definition 6.34: intermediate objects of a factorization carry transported forms.)

Local constancy through the inverse of a proper covariant homeomorphism.

If a Γ-valued map `h` on `A` is locally constant on each label fibre of `A`, then
`h ∘ f⁻¹` is locally constant on each label fibre of `B`: near a point `b` of `B_t`
with `f⁻¹ b = (a, u)`, the points of `B_t` lie in the same graph fibre `(t, u)` of
`f⁻¹` (graph fibres are invariant under a radius), and `f⁻¹` is continuous on it,
so their preimages are close to `a` and carry the label `u`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6.TransportedForms
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Local constancy of a Γ-valued map on the label fibres of a mixed set. -/
def LocallyConstantOnFibres {A : DefSet (rawMixedSpace (M := M) n r) S}
    (h : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : Prop :=
  ∀ p : A, ∃ ρ : Gamma M, ∀ q : A, q.val.2 = p.val.2 → Congruent (fun _ => ρ) p.val.1 q.val.1 →
    gammaMapValue h q = gammaMapValue h p

theorem congruent_of_mem_vfBall {a x : Fin n → VF M} {ε : Gamma M} (hx : x ∈ vfBall a ε) :
    Congruent (fun _ => ε) a x := (show Congruent (fun _ => ε) x a from hx).symm

theorem mem_vfBall_of_congruent {a x : Fin n → VF M} {ε : Gamma M} (hx : Congruent (fun _ => ε) a x) :
    x ∈ vfBall a ε := (show Congruent (fun _ => ε) x a from hx.symm)

/-- The componentwise maximum of a finite family of radii with a scalar. -/
theorem exists_scalar_above (α : Fin n → Gamma M) (δ : Gamma M) :
    ∃ ρ : Gamma M, δ ≤ ρ ∧ ∀ i, α i ≤ ρ := by
  obtain ⟨c, hc⟩ := (Set.finite_range α).bddAbove
  exact ⟨max c δ, le_max_right _ _, fun i => (hc (Set.mem_range_self i)).trans (le_max_left _ _)⟩

/-- **Local constancy through `f⁻¹`.** -/
theorem locallyConstant_comp_inverse
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (homeo : ProperCovariantHomeomorphism (G := G) f)
    (h : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hloc : LocallyConstantOnFibres h) :
    LocallyConstantOnFibres (h.comp (f.inverse homeo.bijective)) := by
  intro b
  let g := f.inverse homeo.bijective
  let a := g b
  let t := b.val.2
  let u := a.val.2
  obtain ⟨ρ₀, hρ₀⟩ := hloc a
  -- the graph fibre of `g` through `b`
  have hbsrc : b.val.1 ∈ graphFibreSource g t u := ⟨a.val.1, b, rfl, rfl⟩
  obtain ⟨α, -, -, -, hαinv, -, -⟩ := homeo.inverseCovariant.radii t u
  have hcont := homeo.inverseContinuous t u
  have hopen : IsOpen (graphFibreSource g t u) := hαinv.isOpen hv
  have hF : graphFibreMap g t u b.val.1 = a.val.1 :=
    graphFibre_functional g t u (graphFibreMap_graph g t u hbsrc)
      (⟨b, rfl, rfl⟩ : graphFibre g t u b.val.1 a.val.1)
  -- continuity at `b`
  let F : (Fin n → VF M) → Fin n → VF M := graphFibreMap g t u
  let D : Set (Fin n → VF M) := graphFibreSource g t u
  let x₀ : Fin n → VF M := b.val.1
  let a₀ : Fin n → VF M := a.val.1
  have hcontD : ContinuousOn F D := hcont
  have hx₀ : x₀ ∈ D := hbsrc
  have hFx₀ : F x₀ = a₀ := hF
  have hnhds : F ⁻¹' vfBall a₀ ρ₀ ∩ D ∈ 𝓝 x₀ := by
    have h1 : F ⁻¹' vfBall a₀ ρ₀ ∈ 𝓝[D] x₀ := by
      apply hcontD x₀ hx₀
      rw [hFx₀]
      exact vfBall_mem_nhds hv a₀ ρ₀
    obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h1
    exact Filter.mem_of_superset (Filter.inter_mem hU (hopen.mem_nhds hx₀))
      (fun y hy => ⟨hUsub ⟨hy.1, hy.2⟩, hy.2⟩)
  obtain ⟨δ, hδ⟩ := exists_vfBall_subset_nhds hv x₀ hnhds
  obtain ⟨ρ, hδρ, hαρ⟩ := exists_scalar_above α δ
  refine ⟨ρ, fun c hct hc => ?_⟩
  -- `c` lies in the same graph fibre of `g`
  have hcδ : (c.val.1 : Fin n → VF M) ∈ vfBall x₀ δ :=
    vfBall_anti hδρ (mem_vfBall_of_congruent hc)
  obtain ⟨hcpre, hcsrc⟩ := hδ hcδ
  have hgc : g.graph c.val (graphFibreMap g t u c.val.1, u) := by
    have := graphFibreMap_graph g t u hcsrc
    obtain ⟨c', hc', hgc'⟩ := this
    refine ⟨c', ?_, hgc'⟩
    rw [hc']
    exact Prod.ext rfl hct.symm
  have hgcv : (g c).val = (graphFibreMap g t u c.val.1, u) := (Map.graph_apply g c _).mp hgc
  change gammaMapValue h (g c) = gammaMapValue h (g b)
  apply hρ₀ (g c)
  · have h2 : (g c).val.2 = u := by rw [hgcv]
    exact h2
  · rw [congrArg Prod.fst hgcv]
    exact congruent_of_mem_vfBall hcpre

end DiamondIntegral.Section6.TransportedForms
