import «section 2».RectangleImages
import «section 2».BallConnectedSets
import «section 2».CoordinateGraphs
import «section 2».CitedUnaryImages

/-! The general ACVF image lemma underlying 2.29. The coordinate-chain
and unary-set geometry are proved here. For an atomic open polydisc, only
the cited unary open-image result is supplied, at each extended real/Gamma
base with its standing nontriviality hypothesis retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A nonconstant definable scalar image of a finite rectangle is an open
disc if its image is proper and every coordinate-line image is a point or
an open disc. Atomicity is not required for this general lemma. -/
theorem rectangle_image_isOpenDisc (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) {n : ℕ} (D : Fin n → Set M) (f : (Fin n → M) → M)
    (hne : ({a | ∀ j, a j ∈ D j} : Set (Fin n → M)).Nonempty)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      (vfFunctionGraph {a | ∀ j, a j ∈ D j} f))
    (hproper : {x : VF M | x.val ∈ f '' {a | ∀ j, a j ∈ D j}} ≠ Set.univ)
    (hnc : ¬ ∃ c : M, ∀ a ∈ {a | ∀ j, a j ∈ D j}, f a = c)
    (hlines : ∀ a, (∀ j, a j ∈ D j) → ∀ i,
      (coordinateLineImage D f a i).Subsingleton ∨ IsOpenDisc (coordinateLineImage D f a i)) :
    IsOpenDisc (f '' {a | ∀ j, a j ∈ D j}) := by
  let A : Set (Fin n → M) := {a | ∀ j, a j ∈ D j}
  let C := f '' A
  have hC := vf_function_image_definable B A f hG
  have hpair (p q : M) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
      ∃ U, IsOpenDisc U ∧ U ⊆ C ∧ p ∈ U ∧ q ∈ U :=
    rectangle_image_pair D f {U | IsOpenDisc U}
      (fun U hU V hV hUV => openDiscs_nested U V hU hV hUV) hlines p q hp hq hpq
  apply isOpenDisc_of_pairs_enclosed h00 B C hC (hne.image f) hproper
  intro p hp q hq
  by_cases hpq : p.val = q.val
  · have hnot : ¬ ∀ a ∈ A, f a = p.val := fun h => hnc ⟨p.val, h⟩
    push Not at hnot
    obtain ⟨a, ha, hfa⟩ := hnot
    obtain ⟨U, hU, hUC, hpU, _⟩ := hpair p.val (f a) hp ⟨a, ha, rfl⟩ (Ne.symm hfa)
    exact ⟨U, hU, hUC, hpU, hpq ▸ hpU⟩
  · exact hpair p.val q.val hp hq hpq

/-- The atomic open-polydisc specialization of the general image lemma.
The only geometric cited input is the unary [18, Lemma 3.13], used over
explicit bases naming the other VF coordinates. -/
theorem atomic_open_polydisc_image (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, OpenDiscImageInput E)
    {n : ℕ} (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (f : (Fin n → M) → M)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      (vfFunctionGraph {a | ∀ j, a j ∈ D j} f))
    (hproper : {x : VF M | x.val ∈ f '' {a | ∀ j, a j ∈ D j}} ≠ Set.univ) :
    (∃ c : VF M, ∀ a ∈ {a | ∀ j, a j ∈ D j}, f a = c.val) ∨
      (IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' {a | ∀ j, a j ∈ D j}} ∧
        IsOpenDisc (f '' {a | ∀ j, a j ∈ D j})) := by
  have hI := vf_function_image_atomic B {a | ∀ j, a j ∈ D j} f hA hG
  classical
  by_cases hc : ∃ c : M, ∀ a ∈ {a | ∀ j, a j ∈ D j}, f a = c
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨a, ha⟩ := hA.2.1
    have hcVF := GammaParameters.DefinableAtBase.proper hI.1 c ⟨a, ha, hc a ha⟩
    exact Or.inl ⟨⟨c, hcVF⟩, hc⟩
  · refine Or.inr ⟨hI, rectangle_image_isOpenDisc h00 B D f hA.2.1 hG hproper hc ?_⟩
    intro a ha
    cases n with
    | zero => intro i; exact i.elim0
    | succ k =>
      intro i
      let E := tupleBase B (Fin.removeNth i a)
      have hΓE : NontrivialDefinableGamma E :=
        hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have hline := coordinate_line_atomic D hA a ha i
      have hgraph := coordinate_line_graph_definable B D f hA hG a ha i
      rcases lemma_2_28 h00 E (cited E) hΓE (D i)
          (fun x => f (Function.update a i x)) hline (hopen i) hgraph with
        ⟨c, hc⟩ | ⟨_, ho⟩
      · left
        rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩
        exact (hc x hx).trans (hc w hw).symm
      · exact Or.inr ho

end DiamondIntegral.Section2
