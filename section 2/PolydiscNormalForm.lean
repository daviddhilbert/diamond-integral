import «section 2».SingletonDiscNames
import «section 2».DiscTupleSubstitution
import «section 2».NamedPolydiscAtomicity

/-!
# Lemma 2.25 with singleton closed coordinates in normal form

Singleton coordinates are placed first and decoded to their unique VF
points; the singleton-name equivalence is proved in SingletonDiscNames.
Finite-radius coordinates retain their actual quotient disc names.
The interface is invariant under equality of the entire DC-name tuple.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def normalFormDiscNames {p n : ℕ} (points : Fin p → VF M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) : Fin (p+n) → DC (M := M) :=
  Fin.append (singletonDiscTupleNames points) (finitePolydiscNames closed a δ)

def prefixedNamedPolydisc {p n : ℕ} (points : Fin p → VF M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) : Set (Fin (p+n) → M) :=
  {z | z ∘ Fin.castAdd n = SpecialTransformations.Section4.vfValues points ∧
    z ∘ Fin.natAdd p ∈ namedPolydisc closed a δ}

def IsAtomicOverDiscNamesNormalForm (B : ParameterBase M) {p n m : ℕ}
    (points : Fin p → VF M) (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  IsAtomicOverFiniteDiscNames (tupleBase B (SpecialTransformations.Section4.vfValues points))
    closed a δ sn A

theorem atomicNormalForm_iff_of_names (B : ParameterBase M) {p n m : ℕ}
    (points points' : Fin p → VF M) (closed : Fin n → Bool) (a a' : Fin n → VF M)
    (δ δ' : Fin n → Gamma M)
    (he : normalFormDiscNames points closed a δ = normalFormDiscNames points' closed a' δ')
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    IsAtomicOverDiscNamesNormalForm B points closed a δ sn A ↔
      IsAtomicOverDiscNamesNormalForm B points' closed a' δ' sn A := by
  have hp : singletonDiscTupleNames points = singletonDiscTupleNames points' := by
    funext i
    simpa only [normalFormDiscNames, Fin.append_left] using congrFun he (Fin.castAdd n i)
  have hpoints := singletonDiscTupleNames_injective hp
  subst points'
  have hf : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ' := by
    funext i
    simpa only [normalFormDiscNames, Fin.append_right] using congrFun he (Fin.natAdd p i)
  exact isAtomicOverFiniteDiscNames_iff_of_names _ closed a a' δ δ' hf sn A

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

/-- Lemma 2.25 in the canonical chart with singleton closed coordinates
first, followed by arbitrary finite open/closed coordinates. Points are
decoded from their singleton DC names, not freely added parameters. -/
theorem lemma_2_25_singleton_normal_form (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {p n : ℕ} (points : Fin p → VF M) (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (A : Set (Fin (p+n) → M))
    (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : prefixedNamedPolydisc points closed a δ ⊆ A) :
    IsAtomicOverDiscNamesNormalForm B points closed a δ (fun _ => .vf)
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
  have hA' : GeneratesCompleteType B
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin n => .vf)) A := by
    simpa only [append_vf_context] using hA
  have hT : GeneratesCompleteType E (fun _ => .vf) T :=
    hA'.block_fibre (SpecialTransformations.Section4.vfValues points) hneT
  have hΓE : NontrivialDefinableGamma E := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  have hD := lemma_2_25_finite_names h00 E hΓE unary gamma closed a δ T hT
    (fun x hx => hsub (hprefix x hx))
  have hname (i : Fin p) : GammaParameters.DefinableClosureAtBase E .vf (points i).val :=
    GammaParameters.real_definableAtBase E .vf {(points i).val}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self i)) (points i).property)
  have hpoints := GammaParameters.tuple_singleton_definable_base E (fun _ : Fin p => .vf)
    (SpecialTransformations.Section4.vfValues points) hname
  have hP := hpoints.preimage_real (fun _ : Fin (p+n) => .vf) (Fin.castAdd n)
  have hP' := definableOverFiniteDiscNames_of_ground E closed a δ _ _ hP
  have hQ := hD.1.preimage_real (fun _ : Fin (p+n) => .vf) (Fin.natAdd p)
  have hdef : DefinableOverFiniteDiscNames E closed a δ (fun _ => .vf)
      (prefixedNamedPolydisc points closed a δ) := by
    convert hP'.inter hQ using 1
    ext z
    constructor
    · intro hz
      have hs := prefixedNamedPolydisc_proper points closed a δ hz
      exact ⟨⟨Set.mem_singleton_iff.mpr hz.1, hs⟩, hz.2, hs⟩
    · rintro ⟨⟨hp, _⟩, hq, _⟩
      exact ⟨Set.mem_singleton_iff.mp hp, hq⟩
  change IsAtomicOverFiniteDiscNames E closed a δ _ _
  refine ⟨hdef, ?_, prefixedNamedPolydisc_proper points closed a δ, ?_⟩
  · obtain ⟨x, hx⟩ := namedPolydisc_nonempty closed a δ
    exact ⟨_, hprefix x hx⟩
  · intro C hC
    have hC' : DefinableOverFiniteDiscNames E closed a δ
        (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin n => .vf)) C := by
      simpa only [append_vf_context] using hC
    let L : Set (Fin n → M) := {x | Fin.append (SpecialTransformations.Section4.vfValues points) x ∈ C}
    have hL : DefinableOverFiniteDiscNames E closed a δ (fun _ : Fin n => .vf) L :=
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
