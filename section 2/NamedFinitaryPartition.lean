import «section 2».NamedTaggedPartition
import «section 2».NamedGoodBranches

/-! Corollary 2.30 over the original small real ground base together
with any fixed finite tuple of DC ground names. Every partition member,
branch domain and full branch graph retains those names. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def TaggedPolydiscBranchDecompositionOverDiscNames (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (b : Fin k → VF M) (τ : Fin k → Gamma M)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (F : Set ((Fin n → M) × M)) : Prop :=
  let P := namedPolydisc (fun _ => false) a δ
  ∃ T : Set (RVInfinity M), T.Finite ∧ ∃ g : RVInfinity M → (Fin n → M) → M,
    (∀ t ∈ T,
      DefinableOverFiniteDiscNames (adjoinRV B t) (Fin.append ground (fun _ => false)) (Fin.append b a) (Fin.append τ δ)
        (fun _ : Fin (n+1) => .vf) (vfFunctionGraph P (g t)) ∧
      ((∃ c : VF M, ∀ x ∈ P, g t x = c.val) ∨ IsOpenDisc (g t '' P)) ∧
      ∀ x ∈ P, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g t x = y) ∧
    ∀ x ∈ P, ∀ y, (x,y) ∈ F ↔ ∃ t ∈ T, g t x = y

/-- The complete DC-ground extension of Corollary 2.30. The finite
partition is proved over exactly the original ground names. The four
replaceable cited inputs are unary results of [18, Section 3]. -/
theorem corollary_2_30_disc_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hκ : Cardinal.aleph0 ≤ κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (b : Fin k → VF M) (τ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hfinite : ∀ x ∈ A, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ A, Set.InjOn iRv {y | (x,y) ∈ F}) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) V ∧
        ∀ (a : Fin n → VF M) (δ : Fin n → Gamma M),
          namedPolydisc (fun _ => false) a δ ⊆ V →
          TaggedPolydiscBranchDecompositionOverDiscNames (⟨S,∅⟩ : ParameterBase M) ground b τ a δ F) ∧
      ∀ x ∈ A, ∃ V ∈ Q, x ∈ V := by
  obtain ⟨Q,hQf,hQdis,hQ,hcov⟩ := good_tagged_polydisc_partition_disc_names hc h00 hs hκ S hsmall hΓ
    unary gamma rvbase image ground b τ A hA F hF hfinite hrv
  refine ⟨Q,hQf,hQdis,?_,hcov⟩
  intro V hV
  obtain ⟨hne,hVA,hVdef,hgood⟩ := hQ V hV
  refine ⟨hne,hVA,hVdef,?_⟩
  intro a δ hsub
  let r : Fin n → VF M := fun i => radiusRepresentative (δ i).val
  have hr (i : Fin n) : r i ≠ 0 := fun h => (δ i).property ((radiusRepresentative_zero_iff _).mp h)
  let d := Fin.append (vfValues a) (vfValues r)
  have hd : rawOpenPolydiscProper d := by
    intro i
    have hp : OpenBallCodes.Proper (![(a i).val,(r i).val]) :=
      ⟨by intro j; fin_cases j; exact (a i).property; exact (r i).property,
        fun h => hr i (Subtype.ext h)⟩
    simpa only [d,Fin.append_left,Fin.append_right,vfValues] using hp
  have hδ : (fun i => finiteValue (r i) (hr i)) = δ := by
    funext i
    exact Subtype.ext (radiusRepresentative_value _)
  have he : rawOpenPolydisc d = namedPolydisc (fun _ => false) a δ := by
    have h := rawOpenPolydisc_named a r hr
    rwa [hδ] at h
  have hcode := hgood d hd (he.symm ▸ hsub)
  exact good_named_polydisc_branches_disc_names hc ⟨S,∅⟩ ground b τ a δ d he F hF hcode
    (fun x hx => hfinite x (hVA (hsub hx))) (fun x hx => hrv x (hVA (hsub hx)))

end DiamondIntegral.Section2
