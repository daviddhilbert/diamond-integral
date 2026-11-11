import «section 2».PrefixedPolydiscAtomicity
import «section 2».PolydiscNormalForm

/-! Singleton closed coordinates in 2.25 with the pre-existing ground DC
prefix retained. The uniquely decoded singleton points are the only new
real names. The remaining finite disc centres stay inside invariant relations. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem prefix_reconstruct {p n : ℕ} (points : Fin p → VF M) (z : Fin (p+n) → M)
    (he : z ∘ Fin.castAdd n = SpecialTransformations.Section4.vfValues points) :
    Fin.append (SpecialTransformations.Section4.vfValues points) (z ∘ Fin.natAdd p) = z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Fin.append_left, Function.comp_apply] using (congrFun he i).symm
  · simp only [Fin.append_right, Function.comp_apply]

private theorem prefixedNamedPolydisc_proper {p n : ℕ} (points : Fin p → VF M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    prefixedNamedPolydisc points closed a δ ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
  intro z hz j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have he := congrFun hz.1 i
    change z (Fin.castAdd n i) = SpecialTransformations.Section4.vfValues points i at he
    change iVF (z (Fin.castAdd n i))
    rw [he]
    exact (points i).property
  · exact namedPolydisc_proper closed a δ hz.2 i

private theorem append_vf_context (p n : ℕ) :
    Fin.append (fun _ : Fin p => SortTag.vf) (fun _ : Fin n => .vf) =
      (fun _ : Fin (p+n) => .vf) := by
  funext j
  exact Fin.addCases (fun i => by simp only [Fin.append_left])
    (fun i => by simp only [Fin.append_right]) j

theorem lemma_2_25_singleton_with_disc_ground (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k p n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (points : Fin p → VF M) (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (A : Set (Fin (p+n) → M))
    (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : prefixedNamedPolydisc points closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames (tupleBase B (SpecialTransformations.Section4.vfValues points))
      (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) (fun _ => .vf)
      (prefixedNamedPolydisc points closed a δ) := by
  let E := tupleBase B (SpecialTransformations.Section4.vfValues points)
  let D := namedPolydisc closed a δ
  let T : Set (Fin n → M) := {x | Fin.append (SpecialTransformations.Section4.vfValues points) x ∈ A}
  have hprefix (x : Fin n → M) (hx : x ∈ D) :
      Fin.append (SpecialTransformations.Section4.vfValues points) x ∈
        prefixedNamedPolydisc points closed a δ := by
    refine ⟨?_, ?_⟩
    · funext i
      simp only [Function.comp_apply, Fin.append_left]
    · have he : Fin.append (SpecialTransformations.Section4.vfValues points) x ∘ Fin.natAdd p = x := by
        funext i
        simp only [Function.comp_apply, Fin.append_right]
      exact he.symm ▸ hx
  have hneT : T.Nonempty := by
    obtain ⟨x, hx⟩ := namedPolydisc_nonempty closed a δ
    exact ⟨x, hsub (hprefix x hx)⟩
  have hA' : GeneratesTypeOverFiniteDiscNames B ground d τ
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin n => .vf)) A := by
    simpa only [append_vf_context] using hA
  have hT : GeneratesTypeOverFiniteDiscNames E ground d τ (fun _ => .vf) T :=
    hA'.block_fibre hc (SpecialTransformations.Section4.vfValues points) hneT
  have hΓE : NontrivialDefinableGamma E := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  have hD := lemma_2_25_with_disc_ground hc h00 E hΓE unary gamma ground d τ closed a δ T hT
    (fun x hx => hsub (hprefix x hx))
  have hname (i : Fin p) : GammaParameters.DefinableClosureAtBase E .vf (points i).val :=
    GammaParameters.real_definableAtBase E .vf {(points i).val}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self i)) (points i).property)
  have hpoints := GammaParameters.tuple_singleton_definable_base E (fun _ : Fin p => .vf)
    (SpecialTransformations.Section4.vfValues points) hname
  have hP := hpoints.preimage_real (fun _ : Fin (p+n) => .vf) (Fin.castAdd n)
  have hP' := definableOverFiniteDiscNames_of_ground E (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) _ _ hP
  have hQ := hD.1.preimage_real (fun _ : Fin (p+n) => .vf) (Fin.natAdd p)
  have hdef : DefinableOverFiniteDiscNames E (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) (fun _ => .vf)
      (prefixedNamedPolydisc points closed a δ) := by
    convert hP'.inter hQ using 1
    ext z
    constructor
    · intro hz
      have hs := prefixedNamedPolydisc_proper points closed a δ hz
      exact ⟨⟨Set.mem_singleton_iff.mpr hz.1, hs⟩, hz.2, hs⟩
    · rintro ⟨⟨hp, _⟩, hq, _⟩
      exact ⟨Set.mem_singleton_iff.mp hp, hq⟩
  change IsAtomicOverFiniteDiscNames E (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) _ _
  refine ⟨hdef, ?_, prefixedNamedPolydisc_proper points closed a δ, ?_⟩
  · obtain ⟨x, hx⟩ := namedPolydisc_nonempty closed a δ
    exact ⟨_, hprefix x hx⟩
  · intro C hC
    have hC' : DefinableOverFiniteDiscNames E (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ)
        (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin n => .vf)) C := by
      simpa only [append_vf_context] using hC
    let L : Set (Fin n → M) := {x | Fin.append (SpecialTransformations.Section4.vfValues points) x ∈ C}
    have hL : DefinableOverFiniteDiscNames E (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) (fun _ : Fin n => .vf) L :=
      hC'.fix_prefix (SpecialTransformations.Section4.vfValues points) (fun i => Or.inr (Set.mem_range_self i))
    rcases hD.2.2.2 L hL with hDL | hdis
    · left
      intro z hz
      have h := hDL hz.2
      change Fin.append (SpecialTransformations.Section4.vfValues points) (z ∘ Fin.natAdd p) ∈ C at h
      rwa [prefix_reconstruct points z hz.1] at h
    · right
      apply Set.disjoint_left.mpr
      intro z hz hzC
      have hzL : z ∘ Fin.natAdd p ∈ L := by
        change Fin.append (SpecialTransformations.Section4.vfValues points) (z ∘ Fin.natAdd p) ∈ C
        rwa [prefix_reconstruct points z hz.1]
      exact Set.disjoint_left.mp hdis hz.2 hzL

end DiamondIntegral.Section2
