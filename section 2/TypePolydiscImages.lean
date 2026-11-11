import «section 2».TypePolydiscTags
import «section 2».NamedTupleTagBranches
import «section 2».PolydiscImages

/-! Tagged branch images for a polydisc inside a complete type locus.
Atomicity is used only on unary coordinate lines, with the varying disc
kept imaginary. Centres are used later only to present the already-defined
whole image for the independently proved coordinate-chain geometry. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem type_polydisc_tagged_branch_image (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {n : ℕ} (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc (fun _ => false) a δ ⊆ A)
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (t : RVInfinity M) (g : (Fin n → M) → M)
    (hg : ∀ x ∈ namedPolydisc (fun _ => false) a δ, ∀ y,
      ((x,y) ∈ F ∧ iRv y = t.val) ↔ g x = y) :
    (g '' namedPolydisc (fun _ => false) a δ).Subsingleton ∨
      IsOpenDisc (g '' namedPolydisc (fun _ => false) a δ) := by
  let D (i : Fin n) := BallImaginaries.underlying (openDiscCode (a i) (δ i))
  let P := namedPolydisc (fun _ => false) a δ
  have hP : DefinableOverFiniteDiscNames B (fun _ => false) a δ (fun _ => .vf) P :=
    namedPolydisc_definable_of_type h00 B (unary B) hΓ (fun _ => false) a δ A hA hsub
  have hGD := named_tuple_tag_branch_graph_definable B (fun _ => false) a δ P hP F hF t g hg
  obtain ⟨R,hR⟩ := hGD
  let E : ParameterBase M :=
    ⟨(adjoinRV B t).real ∪ Set.range (vfValues a),(adjoinRV B t).gamma ∪ Set.range δ⟩
  have hG : GammaParameters.DefinableOverBase E (fun _ : Fin (n+1) => .vf)
      (vfFunctionGraph P g) := by
    have h := R.definable_fibre a δ
    rwa [hR] at h
  have hne : P.Nonempty := namedPolydisc_nonempty (fun _ => false) a δ
  by_cases hc : ∃ c : M, ∀ x ∈ P, g x = c
  · obtain ⟨c,hc⟩ := hc
    left
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hc x hx).trans (hc y hy).symm
  · right
    have htag (y : M) (hy : y ∈ g '' P) : iRv y = t.val := by
      obtain ⟨x,hx,rfl⟩ := hy
      exact ((hg x hx (g x)).mpr rfl).2
    have hproper : {x : VF M | x.val ∈ g '' P} ≠ Set.univ := by
      intro he
      have hz : (0 : VF M).val ∈ g '' P := (Set.ext_iff.mp he 0).mpr (Set.mem_univ _)
      have ho : (1 : VF M).val ∈ g '' P := (Set.ext_iff.mp he 1).mpr (Set.mem_univ _)
      have heRv : rv M (1 : VF M) = rv M (0 : VF M) :=
        Subtype.ext ((htag _ ho).trans (htag _ hz).symm)
      exact one_ne_zero ((rv_eq_zero_iff (1 : VF M)).mp (heRv.trans rv_zero))
    apply rectangle_image_isOpenDisc h00 E D g hne hG hproper hc
    intro b hb
    cases n with
    | zero => intro i; exact i.elim0
    | succ k =>
      intro i
      let E₀ := tupleBase B (Fin.removeNth i b)
      have hΓ₀ : NontrivialDefinableGamma E₀ :=
        hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have hline := type_polydisc_line_atomic h00 B hΓ unary a δ A hA hsub b hb i
      have hAt := rvbase E₀ h00 hΓ₀ 1 (![false]) (![a i]) (![δ i]) (D i)
        hline ⟨a i,δ i,rfl⟩ t
      let L : Set ((Fin 1 → M) × M) := {z | (Function.update b i (z.1 0),z.2) ∈ F}
      have hL : GammaParameters.DefinableOverBase E₀ (fun _ : Fin 2 => .vf)
          {z | (Fin.init z,z (Fin.last 1)) ∈ L} := by
        convert coordinate_relation_definable B F hF b i using 1
        ext z
        rfl
      have hbranch : ∀ x ∈ D i, ∀ y,
          (((fun _ : Fin 1 => x),y) ∈ L ∧ iRv y = t.val) ↔
            g (Function.update b i x) = y := by
        intro x hx y
        apply hg
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [D,finitePolydiscNames,Bool.false_eq_true,ite_false,Function.update_self] using hx
        · simpa only [D,finitePolydiscNames,Bool.false_eq_true,ite_false,Function.update_of_ne hji] using hb j
      have hgraph := named_tag_branch_graph_definable E₀ (![false]) (![a i]) (![δ i])
        (D i) hline.1 L hL t (fun x => g (Function.update b i x)) hbranch
      have hΓt : NontrivialDefinableGamma (adjoinRV E₀ t) :=
        hΓ₀.mono (Set.subset_insert _ _) (Set.Subset.refl _)
      exact named_open_disc_image h00 (adjoinRV E₀ t) hΓt (image (adjoinRV E₀ t))
        (![false]) (![a i]) (![δ i]) (D i) (fun x => g (Function.update b i x))
        hAt ⟨a i,δ i,rfl⟩ hgraph

end DiamondIntegral.Section2
