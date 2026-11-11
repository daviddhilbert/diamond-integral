import «section 2».OpenPolydiscNames
import «section 2».RawTaggedPolydiscs
import «section 2».NamedTupleTagBranches

/-! Extracting the finite family in Corollary 2.30 from the uniform good
code. Each full branch graph uses only the original base, the actual disc
tuple, and its RV tag. Finiteness comes from one finite row. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem good_named_polydisc_branches (hc : CanonicalStructure.IsCanonical (M := M))
    (B : ParameterBase M) {n : ℕ} (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (d : Fin (n+n) → M)
    (he : rawOpenPolydisc d = namedPolydisc (fun _ => false) a δ)
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) (hgood : d ∈ rawGoodTaggedPolydiscCodes F)
    (hfinite : ∀ x ∈ namedPolydisc (fun _ => false) a δ, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ namedPolydisc (fun _ => false) a δ, Set.InjOn iRv {y | (x,y) ∈ F}) :
    let P := namedPolydisc (fun _ => false) a δ
    ∃ T : Set (RVInfinity M), T.Finite ∧ ∃ g : RVInfinity M → (Fin n → M) → M,
      (∀ t ∈ T,
        DefinableOverFiniteDiscNames (adjoinRV B t) (fun _ => false) a δ
          (fun _ : Fin (n+1) => .vf) (vfFunctionGraph P (g t)) ∧
        ((∃ c : VF M, ∀ x ∈ P, g t x = c.val) ∨ IsOpenDisc (g t '' P)) ∧
        ∀ x ∈ P, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g t x = y) ∧
      ∀ x ∈ P, ∀ y, (x,y) ∈ F ↔ ∃ t ∈ T, g t x = y := by
  classical
  let P := namedPolydisc (fun _ => false) a δ
  change rawOpenPolydisc d = P at he
  have hcommon : ∀ x ∈ P, ∀ z ∈ P,
      iRv '' {y | (x,y) ∈ F} = iRv '' {y | (z,y) ∈ F} := by
    rw [← he]
    exact rawGoodTaggedPolydiscCodes_rows F d hgood
  have hP := named_open_polydisc_definable hc B a δ
  have hne : P.Nonempty := namedPolydisc_nonempty (fun _ => false) a δ
  have htags := vfRelationTags_finite P F hne hcommon hfinite
  let T : Set (RVInfinity M) := {t | t.val ∈ vfRelationTags P F}
  have hT : T.Finite := htags.preimage Subtype.val_injective.injOn
  have hchoose (t : RVInfinity M) : ∃ g : (Fin n → M) → M, t ∈ T →
      DefinableOverFiniteDiscNames (adjoinRV B t) (fun _ => false) a δ
        (fun _ : Fin (n+1) => .vf) (vfFunctionGraph P g) ∧
      ((∃ c : VF M, ∀ x ∈ P, g x = c.val) ∨ IsOpenDisc (g '' P)) ∧
      ∀ x ∈ P, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g x = y := by
    by_cases ht : t ∈ T
    · obtain ⟨g,hg⟩ := vfTagBranch_function P F hcommon hrv t ht
      have hbranch : ∀ x ∈ P, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g x = y := by
        intro x hx y
        exact ⟨fun hy => (hg x hx y).mp ⟨hx,hy⟩,fun hy => ((hg x hx y).mpr hy).2⟩
      have hG := named_tuple_tag_branch_graph_definable B (fun _ => false) a δ P hP F hF t g hbranch
      have hI : rawTaggedPolydiscImage F (Sum.elim d (fun _ : Fin 1 => t.val)) = g '' P := by
        ext y
        constructor
        · rintro ⟨x,hx,hxy,hyt⟩
          exact ⟨x,he ▸ hx,(hbranch x (he ▸ hx) y).mp ⟨hxy,hyt⟩⟩
        · rintro ⟨x,hx,rfl⟩
          have hf := (hbranch x hx (g x)).mpr rfl
          exact ⟨x,he.symm ▸ hx,hf⟩
      have hshape : (∃ c : M, g '' P = {c}) ∨ IsOpenDisc (g '' P) := by
        have h := rawDiscShapeCodes_nonempty (rawTaggedPolydiscImage F)
          (Sum.elim d (fun _ : Fin 1 => t.val)) (hgood.2 (fun _ => t.val))
        rw [hI] at h
        exact h (hne.image g)
      refine ⟨g,fun _ => ⟨hG,?_,hbranch⟩⟩
      rcases hshape with ⟨c,hc⟩ | hopen
      · left
        obtain ⟨x,hx⟩ := hne
        have hrow : (Fin.snoc x (g x) : Fin (n+1) → M) ∈ vfFunctionGraph P g := by
          simpa only [vfFunctionGraph,Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last,and_true] using hx
        have hvf : iVF (g x) := by
          simpa only [Fin.snoc_last,sortEval,iVF] using hG.proper hrow (Fin.last n)
        refine ⟨⟨g x,hvf⟩,?_⟩
        intro z hz
        have hsmall : (g '' P).Subsingleton := by rw [hc]; exact Set.subsingleton_singleton
        exact hsmall ⟨z,hz,rfl⟩ ⟨x,hx,rfl⟩
      · exact Or.inr hopen
    · exact ⟨fun _ => (0 : VF M).val,fun h => (ht h).elim⟩
  choose g hg using hchoose
  refine ⟨T,hT,g,hg,?_⟩
  intro x hx y
  constructor
  · intro hxy
    obtain ⟨t,ht,_,hxy,hyt⟩ := (vfTagBranch_cover B P F hF x hx y).mp hxy
    exact ⟨t,ht,((hg t ht).2.2 x hx y).mp ⟨hxy,hyt⟩⟩
  · rintro ⟨t,ht,hgy⟩
    exact (((hg t ht).2.2 x hx y).mpr hgy).1

end DiamondIntegral.Section2
