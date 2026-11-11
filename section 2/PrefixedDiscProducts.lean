import «section 2».NamedCoordinateTypes
import «section 2».PrefixedDiscCoordinates
import «section 2».DiscNameProducts

/-! Definability of a new polydisc over its own names together with every
previous ground disc name. Only the accepted unary result from [18] is used. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem namedPolydisc_definable_with_disc_ground (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (cited : UnaryDiscAtomicityInput B) (hΓ : NontrivialDefinableGamma B)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    DefinableOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ)
      (fun _ => .vf) (namedPolydisc closed a δ) := by
  classical
  let D := namedPolydisc closed a δ
  let F (i : Fin n) : Set (Fin n → M) :=
    {x | x i ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i) ∧
      x ∈ GammaParameters.sortedUniverse (fun _ => .vf)}
  have hF (i : Fin n) : DefinableOverFiniteDiscNames B (Fin.append ground closed)
      (Fin.append d a) (Fin.append τ δ) (fun _ => .vf) (F i) := by
    let U : Set (Fin 1 → M) := {z | z 0 ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)}
    have hU : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .vf) U := by
      apply (hA.image_real (fun _ : Fin 1 => i)).subset_nonempty
      · intro z hz
        change z 0 ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i) at hz
        let x := Function.update (vfValues a) i (z 0)
        have hx : x ∈ D := by
          intro j
          by_cases hj : j = i
          · subst j
            simpa only [x,Function.update_self] using hz
          · simpa only [x,Function.update_of_ne hj,vfValues] using finitePolydiscNames_center_mem closed a δ j
        refine ⟨x,hsub hx,?_⟩
        funext j
        fin_cases j
        simp only [Function.comp_apply,x,Function.update_self]
        rfl
      · exact ⟨fun _ => (a i).val,finitePolydiscNames_center_mem closed a δ i⟩
    have hUnary := cited h00 hΓ k ground d τ U hU (closed i) (a i) (δ i) (Set.Subset.refl _)
    let π : Fin (k+1) → Fin (k+n) := Fin.lastCases (Fin.natAdd k i) (Fin.castAdd n)
    have hc : (Fin.append ground closed) ∘ π = Fin.snoc ground (closed i) := by
      funext j
      refine Fin.lastCases ?_ (fun q => ?_) j <;>
        simp only [Function.comp_apply,π,Fin.lastCases_last,Fin.lastCases_castSucc,
          Fin.append_left,Fin.append_right,Fin.snoc_last,Fin.snoc_castSucc]
    have ha : (Fin.append d a) ∘ π = Fin.snoc d (a i) := by
      funext j
      refine Fin.lastCases ?_ (fun q => ?_) j <;>
        simp only [Function.comp_apply,π,Fin.lastCases_last,Fin.lastCases_castSucc,
          Fin.append_left,Fin.append_right,Fin.snoc_last,Fin.snoc_castSucc]
    have hδ : (Fin.append τ δ) ∘ π = Fin.snoc τ (δ i) := by
      funext j
      refine Fin.lastCases ?_ (fun q => ?_) j <;>
        simp only [Function.comp_apply,π,Fin.lastCases_last,Fin.lastCases_castSucc,
          Fin.append_left,Fin.append_right,Fin.snoc_last,Fin.snoc_castSucc]
    have hSmall : DefinableOverFiniteDiscNames B ((Fin.append ground closed) ∘ π)
        ((Fin.append d a) ∘ π) ((Fin.append τ δ) ∘ π) (fun _ : Fin 1 => .vf) U := by
      rw [hc,ha,hδ]
      exact hUnary.1
    have hAll := DefinableOverFiniteDiscNames.pullback_names (Fin.append ground closed) π
      (Fin.append d a) (Fin.append τ δ) hSmall
    exact hAll.preimage_real (fun _ : Fin n => .vf) (fun _ : Fin 1 => i)
  have h := DefinableOverFiniteDiscNames.sorted_iInter F hF
  convert h using 1
  ext x
  constructor
  · intro hx
    have hs := namedPolydisc_proper closed a δ hx
    exact ⟨hs,fun i => ⟨hx i,hs⟩⟩
  · rintro ⟨_,hall⟩ i
    exact (hall i).1

end DiamondIntegral.Section2
