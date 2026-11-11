import «section 2».CitedDiscAtomicity
import «section 2».DiscTupleNames
import «section 2».TypeFibres
import «section 2».DiscGeometry

/-!
# Defining the polydisc over its own names

The unary atomicity result is an accepted input from [18, Section 3].
Coordinate projections of a complete type supply its unary hypotheses.
The conjunction of the resulting actual disc-name formulas defines the
whole product, without choosing any centre as a new ground parameter.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def namedPolydisc {n : ℕ} (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    Set (Fin n → M) :=
  {x | ∀ i, x i ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)}

theorem finitePolydiscNames_center_mem {n : ℕ} (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (i : Fin n) :
    (a i).val ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i) := by
  obtain ⟨G, hG, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  let r := radiusRepresentative (δ i).val
  have hr : r ≠ 0 := fun h => (δ i).property ((radiusRepresentative_zero_iff _).mp h)
  have hval : vfValue r = (δ i).val := radiusRepresentative_value _
  have hf : finiteValue r hr = δ i := Subtype.ext hval
  change a i ∈ discPoints (finitePolydiscNames closed a δ i)
  cases hc : closed i with
  | false =>
    simp only [finitePolydiscNames, hc, Bool.false_eq_true, ite_false]
    rw [← hf, openDiscCode_points v hv _ r hr]
    change v (a i - a i) < v r
    simpa only [sub_self, map_zero] using (pos_iff_ne_zero.mpr ((map_ne_zero v).mpr hr))
  | true =>
    simp only [finitePolydiscNames, hc, ite_true]
    rw [← hval, closedDiscCode_points v hv _ r]
    change v (a i - a i) ≤ v r
    simp

theorem namedPolydisc_nonempty {n : ℕ} (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) : (namedPolydisc closed a δ).Nonempty :=
  ⟨SpecialTransformations.Section4.vfValues a, finitePolydiscNames_center_mem closed a δ⟩

theorem namedPolydisc_proper {n : ℕ} (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    namedPolydisc closed a δ ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
  intro x hx i
  exact disc_underlying_subset_vf _ (hx i)

theorem DefinableOverFiniteDiscNames.sorted_iInter {B : ParameterBase M} {n m l : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} (F : Fin l → Set (Fin m → M))
    (hF : ∀ i, DefinableOverFiniteDiscNames B closed a δ sn (F i)) :
    DefinableOverFiniteDiscNames B closed a δ sn
      {x | x ∈ GammaParameters.sortedUniverse sn ∧ ∀ i, x ∈ F i} := by
  induction l with
  | zero =>
    have h := definableOverFiniteDiscNames_of_ground B closed a δ sn
      (GammaParameters.sortedUniverse sn)
      (GammaParameters.real_definableOverBase B sn _ (GammaParameters.sortedUniverse_definable B.real sn))
    convert h using 1
    ext x
    simp
  | succ l ih =>
    have hprefix := ih (fun i => F i.castSucc) (fun i => hF i.castSucc)
    have h := hprefix.inter (hF (Fin.last l))
    convert h using 1
    ext x
    constructor
    · rintro ⟨hs, hall⟩
      exact ⟨⟨hs, fun i => hall i.castSucc⟩, hall (Fin.last l)⟩
    · rintro ⟨⟨hs, hall⟩, hlast⟩
      exact ⟨hs, Fin.lastCases hlast hall⟩

/-- The definability part of finite-radius Lemma 2.25. Its unary cited
input is kept explicit; the multivariable type-generation part is separate. -/
theorem namedPolydisc_definable_of_type (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (cited : UnaryDiscAtomicityInput B) (hΓ : NontrivialDefinableGamma B)
    {n : ℕ} (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (namedPolydisc closed a δ) := by
  classical
  let D := namedPolydisc closed a δ
  let F (i : Fin n) : Set (Fin n → M) :=
    {x | x i ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i) ∧
      x ∈ GammaParameters.sortedUniverse (fun _ => .vf)}
  have hF (i : Fin n) : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (F i) := by
    let U : Set (Fin 1 → M) :=
      {z | z 0 ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)}
    have hU : GeneratesCompleteType B (fun _ : Fin 1 => .vf) U := by
      apply (hA.image_real (fun _ : Fin 1 => i)).subset_nonempty
      · intro z hz
        change z 0 ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i) at hz
        let x := Function.update (SpecialTransformations.Section4.vfValues a) i (z 0)
        have hx : x ∈ D := by
          intro j
          by_cases hj : j = i
          · subst j
            simpa only [x, Function.update_self] using hz
          · simpa only [x, Function.update_of_ne hj, SpecialTransformations.Section4.vfValues]
              using finitePolydiscNames_center_mem closed a δ j
        refine ⟨x, hsub hx, ?_⟩
        funext j
        fin_cases j
        simp only [Function.comp_apply, x, Function.update_self]
        rfl
      · exact ⟨fun _ => (a i).val, finitePolydiscNames_center_mem closed a δ i⟩
    have hUnary := lemma_2_25_unary h00 B cited hΓ U hU (closed i) (a i) (δ i) (Set.Subset.refl _)
    let π : Fin 1 → Fin n := fun _ => i
    have hclosed : closed ∘ π = ![closed i] := by funext j; fin_cases j; rfl
    have ha : a ∘ π = ![a i] := by funext j; fin_cases j; rfl
    have hδ : δ ∘ π = ![δ i] := by funext j; fin_cases j; rfl
    have hSmall : DefinableOverFiniteDiscNames B (closed ∘ π) (a ∘ π) (δ ∘ π)
        (fun _ : Fin 1 => .vf) U := by
      simpa only [hclosed, ha, hδ, U, finitePolydiscNames] using hUnary.1
    have hAll := DefinableOverFiniteDiscNames.pullback_names closed π a δ hSmall
    have hp := hAll.preimage_real (fun _ : Fin n => .vf) π
    convert hp using 1
    ext x
    rfl
  have h := DefinableOverFiniteDiscNames.sorted_iInter F hF
  convert h using 1
  ext x
  constructor
  · intro hx
    have hs := namedPolydisc_proper closed a δ hx
    exact ⟨hs, fun i => ⟨hx i, hs⟩⟩
  · rintro ⟨_, hall⟩ i
    exact (hall i).1

end DiamondIntegral.Section2
