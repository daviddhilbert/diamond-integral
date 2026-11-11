import «section 2».Conventions
import Section4.GenericPoints
import Section4.VFTranscendence
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! Algebraicity descent for Lemma 2.18. The generic tuple is chosen inside
an actual definable region containing the box, not merely in the ambient
VF universe. The original ground parameters remain explicit. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2

/-- Field-theoretic exchange for a whole independent finite tuple. -/
theorem algebraic_of_independent_over_element {K : Type} [Field K] (E : Subfield K) (b : K) {n : ℕ} (a : Fin n → K)
    (ha : AlgebraicIndependent ↥(E ⊔ Subfield.closure {b}) a)
    (hb : IsAlgebraic (tupleField E a) b) : IsAlgebraic E b := by
  classical
  by_contra hn
  let F : Subfield K := E ⊔ Subfield.closure {b}
  letI := (Subfield.inclusion (show E ≤ F from le_sup_left)).toAlgebra
  letI : IsScalarTower E F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hx : AlgebraicIndependent E (fun _ : Fin 1 => b) :=
    algebraicIndependent_unique_type_iff.mpr hn
  have hbF : b ∈ F := (show Subfield.closure {b} ≤ F from le_sup_right) (Subfield.subset_closure (Set.mem_singleton b))
  have hnames : Set.range (fun _ : Fin 1 => b) ⊆ Set.range (algebraMap F K) := by
    rintro _ ⟨_, rfl⟩
    exact ⟨⟨b, hbF⟩, rfl⟩
  have hsum := hx.sumElim_of_tower (S := F) hnames ha
  have hswap : AlgebraicIndependent E (Sum.elim (fun _ : Fin 1 => b) a) := by
    convert hsum.comp Sum.swap (Equiv.sumComm _ _).injective using 1
    funext i
    cases i <;> rfl
  have htrans := algebraicIndependent_unique_type_iff.mp
    (AlgebraicIndependent.sumElim_iff.mp hswap).2
  have heq : (IntermediateField.adjoin E (Set.range a)).toSubfield = tupleField E a := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.algebraMap_ofSubfield,
      Subfield.closure_union]
    have hr : Set.range E.subtype = (E : Set K) := by
      ext x
      exact ⟨fun h => h.choose_spec ▸ h.choose.property, fun h => ⟨⟨x,h⟩, rfl⟩⟩
    rw [hr, E.closure_eq]
    rfl
  have hb' : IsAlgebraic (IntermediateField.adjoin E (Set.range a)) b := by
    change IsAlgebraic (IntermediateField.adjoin E (Set.range a)).toSubfield b
    rwa [heq]
  exact htrans (IntermediateField.isAlgebraic_adjoin_iff.mp hb')

private theorem independent_mono_subfield {K : Type} [Field K]
    (F H : Subfield K) (hFH : F ≤ H) {n : ℕ} {a : Fin n → K}
    (ha : AlgebraicIndependent H a) : AlgebraicIndependent F a := by
  letI := (Subfield.inclusion hFH).toAlgebra
  letI : IsScalarTower F H K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ha.restrictScalars (Subfield.inclusion hFH).injective

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The descent step of 2.18. The source region may need temporary real
parameters T to be defined. A generic point is produced in that region;
the conclusion eliminates T and returns to the original parameter set S.
The passage from algebraicity over a disc code to the pointwise hypothesis
is a separate interface, not assumed to have been formalized here. -/
theorem vf_algebraic_of_uniform_on_box {κ : Cardinal} (hs : Saturated M κ)
    (S T : Set M) (hST : S ⊆ T) (hsmall : Cardinal.mk T < κ)
    (b : VF M) (hbT : b.val ∈ T) {n : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n 0) T)
    (D : Fin n → Set (VF M)) (hinf : ∀ i, (D i).Infinite)
    (hbox : ∀ x ∈ Set.pi Set.univ D, (x, Fin.elim0) ∈ A.carrier)
    (hb : ∀ a : A, AlgebraicAt (S ∪ Set.range (SpecialTransformations.Section4.vfValues a.val.1)) .vf b.val) :
    AlgebraicAt S .vf b.val := by
  obtain ⟨a, ha⟩ := exists_independent_of_contains_box hs hsmall A D hinf Fin.elim0 hbox
  let E := vfParameterField (M := M) S
  let F : Subfield (VF M) := E ⊔ Subfield.closure {b}
  let H := vfParameterField (M := M) T
  have hFT : F ≤ H := by
    apply sup_le
    · exact Subfield.closure_mono (fun x hx => hST hx)
    · apply Subfield.closure_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Subfield.subset_closure hbT
  have haF : AlgebraicIndependent F a.val.1 := independent_mono_subfield F H hFT ha
  have hba : IsAlgebraic (tupleField E a.val.1) b := by
    apply algebraicAt_vf_isAlgebraic (S ∪ Set.range (SpecialTransformations.Section4.vfValues a.val.1))
      (tupleField E a.val.1) ?_ b (hb a)
    intro x hx
    rcases hx with hx | ⟨j, hj⟩
    · exact le_tupleField E a.val.1 (Subfield.subset_closure hx)
    · have he : a.val.1 j = x := Subtype.ext hj
      rw [← he]
      exact tuple_mem_tupleField E a.val.1 j
  exact (algebraicAt_vf_iff_parameterField S b).mpr
    (algebraic_of_independent_over_element E b a.val.1 haF hba)

end DiamondIntegral.Section2
