import «section 5».NativeRVSetArithmetic
import «section 5».OriginalSortedPredicates

/-! Fixed zero-coordinate strata form a finite disjoint partition of an
actual original-ground RV base. The full old parameter tuple is retained;
only the nonzero selected labels enter the later VF lift degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p d : ℕ}

def nativeRVZeroPattern (j : Fin d → Fin p) (I : Finset (Fin d)) (z : Fin p → M) : Prop :=
  ∀ i : Fin d,i ∈ I ↔ z (j i) ≠ iRVZero

theorem nativeRVZeroPattern_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (j : Fin d → Fin p) (I : Finset (Fin d)) :
    OriginalSortedPredicate B (fun _ : Fin p => .rv) (nativeRVZeroPattern j I) := by
  have hz (i : Fin d) : OriginalSortedPredicate B (fun _ : Fin p => .rv)
      (fun z => z (j i) = iRVZero) := by
    have h := parameter_free_formula_original_definable hc B (fun _ : Fin p => .rv)
      ((Term.var (j i)).equal (Term.func Fn.rvZero Fin.elim0))
    apply OriginalSortedPredicate.congr h
    intro z hp
    have he : (Term.func Fn.rvZero (Fin.elim0 : Fin 0 → LRV.Term (Fin p))).realize z = iRVZero := by
      simp only [Term.realize_func,iRVZero]
      congr 1
      exact Subsingleton.elim _ _
    simp only [Formula.realize_equal,Term.realize_var,he]
  have hi (i : Fin d) : OriginalSortedPredicate B (fun _ : Fin p => .rv)
      (fun z => i ∈ I ↔ z (j i) ≠ iRVZero) := by
    by_cases hi : i ∈ I
    · simpa only [hi,true_iff] using (hz i).neg
    · simpa only [hi,false_iff,not_not] using hz i
  exact OriginalSortedPredicate.finite_all hi

def nativeRVZeroPatternBase (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (j : Fin d → Fin p) (I : Finset (Fin d)) : GammaGroundDefSet hc B (rawRVSpace (M := M) p) :=
  X.inter (ofRaw {z | z ∈ sortedUniverse (fun _ : Fin p => .rv) ∧ nativeRVZeroPattern j I z}
    (nativeRVZeroPattern_definable hc j I))

theorem nativeRVZeroPatternBase_mem (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (j : Fin d → Fin p) (I : Finset (Fin d)) (x : Fin p → CanonicalRV.RVSort M) :
    x ∈ (nativeRVZeroPatternBase X j I).carrier ↔ x ∈ X.carrier ∧ nativeRVZeroPattern j I (rvValues x) := by
  change (_ ∧ (_ ∧ _)) ↔ _
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(fun i => (x i).property),h.2⟩⟩

theorem nativeRVZeroPatternBase_disjoint (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (j : Fin d → Fin p) (I J : Finset (Fin d)) (hne : I ≠ J) :
    Disjoint (nativeRVZeroPatternBase X j I).carrier (nativeRVZeroPatternBase X j J).carrier := by
  apply Set.disjoint_left.mpr
  intro x hI hJ
  have hi := (nativeRVZeroPatternBase_mem X j I x).mp hI
  have hj := (nativeRVZeroPatternBase_mem X j J x).mp hJ
  exact hne (Finset.ext (fun i => (hi.2 i).trans (hj.2 i).symm))

theorem nativeRVZeroPatternBase_cover (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (j : Fin d → Fin p) (x : Fin p → CanonicalRV.RVSort M) :
    x ∈ X.carrier ↔ ∃ I : Finset (Fin d),x ∈ (nativeRVZeroPatternBase X j I).carrier := by
  constructor
  · intro hx
    let I := Finset.univ.filter (fun i : Fin d => rvValues x (j i) ≠ iRVZero)
    refine ⟨I,(nativeRVZeroPatternBase_mem X j I x).mpr ⟨hx,?_⟩⟩
    intro i
    simp only [I,Finset.mem_filter,Finset.mem_univ,true_and]
  · rintro ⟨I,hI⟩
    exact ((nativeRVZeroPatternBase_mem X j I x).mp hI).1

theorem nativeRVZeroPatternBase_nonzero
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (j : Fin d → Fin p) (I : Finset (Fin d))
    (x : nativeRVZeroPatternBase X j I) (i : I) : rvValues x.val (j i.val) ≠ iRVZero :=
  (((nativeRVZeroPatternBase_mem X j I x.val).mp x.property).2 i.val).mp i.property

theorem nativeRVZeroPatternBase_zero
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (j : Fin d → Fin p) (I : Finset (Fin d))
    (x : nativeRVZeroPatternBase X j I) (i : Fin d) (hi : i ∉ I) : rvValues x.val (j i) = iRVZero := by
  by_contra h
  exact hi ((((nativeRVZeroPatternBase_mem X j I x.val).mp x.property).2 i).mpr h)

end DiamondIntegral.Section5
