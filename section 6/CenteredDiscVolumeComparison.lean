import «section 6».CenteredPolydiscDescent

/-! The centered-disc volume calculation with a definable VF-small
exception over the original base. The chart coefficients are adjoined
only in a finite auxiliary real extension, whose smallness is proved.
No chart, generic derivative or Gauss graph is an extra input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n r s : ℕ} {S : Set M}

theorem centered_polydisc_volume_comparison [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b d e : Fin n → VF M) (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0)
    (hA : ∀ x : Fin n → VF M, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i-a i) < v (d i))
    (hB : ∀ x : Fin n → VF M, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i-b i) < v (e i))
    (c : VF M) (hc0 : c ≠ 0) (Z : DefSet (rawMixedSpace (M := M) n r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < n)
    (hconst : ∀ p : A, p.val ∉ Z.carrier → ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c) :
    v c = (∏ i, v (e i)) / ∏ i, v (d i) := by
  let names : Fin 4 → Fin n → VF M :=
    ![fun i => (d i)⁻¹,fun i => (e i)⁻¹,fun i => -(d i)⁻¹*a i,fun i => -(e i)⁻¹*b i]
  let N : Set M := ⋃ j : Fin 4, Set.range (fun i : Fin n => (names j i).val)
  let T := S ∪ N
  have hST : S ⊆ T := Set.subset_union_left
  have hN : N.Finite := Set.finite_iUnion (fun _ => Set.finite_range _)
  have hT : Cardinal.mk T < κ := small_union_finite hκ.le S hsmall N hN
  have hNames (j : Fin 4) (i : Fin n) : (names j i).val ∈ T := by
    apply Or.inr
    simp only [N,Set.mem_iUnion,Set.mem_range]
    exact ⟨j,i,rfl⟩
  have hField : vfParameterField S ≤ vfParameterField T := Subfield.closure_mono (fun _ h => hST h)
  have hconst' (p : A.extend hST) (hp : AlgebraicIndependent (vfParameterField T) p.val.1) :
      ∃ J, HasMixedVFJacobianAt (f.extend hST) p J ∧ v J = v c := by
    apply hconst p
    intro hz
    let q : Z := ⟨p.val,hz⟩
    have hq : AlgebraicIndependent (vfParameterField S) q.val.1 :=
      algebraicIndependent_of_subfield_le hField q.val.1 hp
    have hDim := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Z q
    have hTrdeg : vfTupleTrdeg S q.val.1 = (n : Cardinal) :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) q.val.1).mpr hq
    rw [hTrdeg] at hDim
    exact (not_le_of_gt hZ) (by exact_mod_cast hDim)
  exact centered_polydisc_descent_named_charts hc hκ hs h00 hT v hv (f.extend hST) hf
    a b d e hd he hA hB (hNames 0) (hNames 1) (hNames 2) (hNames 3) c hc0 hconst'

theorem centered_unary_disc_volume_comparison [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b d e : VF M) (hd : d ≠ 0) (he : e ≠ 0)
    (hA : ∀ x : Fin 1 → VF M, (∃ p : A, p.val.1 = x) ↔ v (x 0-a) < v d)
    (hB : ∀ x : Fin 1 → VF M, (∃ p : B, p.val.1 = x) ↔ v (x 0-b) < v e)
    (c : VF M) (hc0 : c ≠ 0) (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier → ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c) :
    v c = v e / v d := by
  have hA' (x : Fin 1 → VF M) : (∃ p : A, p.val.1 = x) ↔ ∀ i : Fin 1, v (x i-a) < v d := by
    rw [hA]
    simp only [Fin.forall_fin_one]
  have hB' (x : Fin 1 → VF M) : (∃ p : B, p.val.1 = x) ↔ ∀ i : Fin 1, v (x i-b) < v e := by
    rw [hB]
    simp only [Fin.forall_fin_one]
  simpa only [Fin.prod_univ_one] using centered_polydisc_volume_comparison hc hκ hs h00 hsmall v hv f hf
    (fun _ => a) (fun _ => b) (fun _ => d) (fun _ => e) (fun _ => hd) (fun _ => he) hA' hB' c hc0 Z hZ hconst

end DiamondIntegral.Section6
