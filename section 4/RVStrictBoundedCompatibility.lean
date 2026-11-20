import «section 4».RVStrictBoundedComparison
import «section 4».RelativeAnnularScalar
import «section 4».ObjectClassAdditiveGeneration

/-! Definition 4.9: compatibility of the identification
`RVStrictBoundedComparison.equivalence : StrictRing B ≃+* RVBoundedRing.Ring B`
(the paper's literal doubly bounded ring, no `∞` coordinates, versus the
Lean bounded ring) with the structure used afterwards.

* Grading: the strict degree-`n` piece (spanned by classes of strict charts
  of degree `n`) maps exactly onto `RVBoundedGrading.gradedPiece B n`
  (`map_strictPiece`, `comap_gradedPiece`).
* `P_γ`: the annulus and point charts defining `P_γ` have no `∞`
  coordinate, and the strict `P_γ` built from them maps to
  `RVRadiusIdeal.pGamma` (`equivalence_strictPGamma`).
* `J_var`: the transported ideal `strictManuscriptIdeal` maps onto
  `manuscriptIdeal B` (`map_strictManuscriptIdeal`), contains the strict
  radius ideal `(P_Γ)` (`strictRadiusIdeal_le`), and the quotients by them
  are isomorphic, compatibly with the classes (`quotientEquiv`). The
  generator-level statement, with Notation 4.17's generators written on
  `∞`-free representatives, is `RVStrictAnnularGenerators.map_strictAnnularIdeal`
  and `RVStrictAnnularGenerators.strictAnnularIdeal_eq`. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVStrictBoundedCompatibility
open RVMeasuredCharts RVStrictBoundedComparison RVRadiusGenerators GammaRVLifts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Additive generation of the strict ring -/

def presentation (B : Base (M := M)) :
    ObjectClassAdditiveGeneration.Presentation (Generator B) (StrictRing B) where
  objectClass a := objectClass a.2
  unit := ⟨0, RVStrictBoundedComparison.unit B⟩
  class_unit := objectClass_unit B
  product a b := ⟨_, RVStrictBoundedComparison.product a.2 b.2⟩
  class_product a b := objectClass_product a.2 b.2
  free := Ideal.Quotient.mk (relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

/-! ### Grading -/

/-- The strict degree-`n` piece: spanned by classes of strict degree-`n` charts. -/
def strictPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (StrictRing B) :=
  AddSubgroup.closure {x | ∃ a : StrictChart B n, x = objectClass a}

theorem objectClass_mem_strictPiece {B : Base (M := M)} {n : ℕ} (a : StrictChart B n) :
    objectClass a ∈ strictPiece B n := AddSubgroup.subset_closure ⟨a, rfl⟩

/-- The degree-`n` projection, computed through the bounded coaction. -/
def projection (B : Base (M := M)) (n : ℕ) : StrictRing B →+ StrictRing B :=
  AddMonoidHom.mk' (fun x => (equivalence B).symm ((RVBoundedGrading.coaction B (equivalence B x)).coeff n))
    (by intro x y; simp only [map_add, Polynomial.coeff_add])

theorem projection_objectClass {B : Base (M := M)} (n : ℕ) {k : ℕ} (a : StrictChart B k) :
    projection B n (objectClass a) = if k = n then objectClass a else 0 := by
  change (equivalence B).symm ((RVBoundedGrading.coaction B (equivalence B (objectClass a))).coeff n) = _
  rw [equivalence_objectClass, RVBoundedGrading.coaction_class, Polynomial.coeff_monomial]
  split_ifs
  · exact equivalence_symm_objectClass B a
  · exact map_zero _

theorem projection_mem (B : Base (M := M)) (n : ℕ) (x : StrictRing B) :
    projection B n x ∈ strictPiece B n := by
  have hx := ObjectClassAdditiveGeneration.mem_span (presentation B) x
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, a⟩, rfl⟩ := hy
    change projection B n (objectClass a) ∈ _
    rw [projection_objectClass]
    split_ifs with h
    · subst h
      exact objectClass_mem_strictPiece a
    · exact (strictPiece B n).zero_mem
  | zero => rw [map_zero]; exact (strictPiece B n).zero_mem
  | add y z _ _ hy hz => rw [map_add]; exact (strictPiece B n).add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact (strictPiece B n).neg_mem hy

/-- The identification carries the strict grading exactly onto the bounded grading. -/
theorem map_strictPiece (B : Base (M := M)) (n : ℕ) :
    (strictPiece B n).map (equivalence B).toAddEquiv.toAddMonoidHom = RVBoundedGrading.gradedPiece B n := by
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap]
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    change equivalence B (objectClass a) ∈ RVBoundedGrading.gradedPiece B n
    rw [equivalence_objectClass]
    exact RVBoundedGrading.class_mem B a.toBoundedChart
  · intro y hy
    refine ⟨(equivalence B).symm y, ?_, (equivalence B).apply_symm_apply y⟩
    have hp : projection B n ((equivalence B).symm y) = (equivalence B).symm y := by
      change (equivalence B).symm ((RVBoundedGrading.coaction B (equivalence B ((equivalence B).symm y))).coeff n) = _
      have hc := (RVBoundedGrading.gradingCoaction B).coefficient_of_mem hy n
      rw [ite_eq_left rfl] at hc
      rw [RingEquiv.apply_symm_apply]
      exact congrArg (equivalence B).symm hc
    rw [← hp]
    exact projection_mem B n _

theorem comap_gradedPiece (B : Base (M := M)) (n : ℕ) :
    (RVBoundedGrading.gradedPiece B n).comap (equivalence B).toAddEquiv.toAddMonoidHom = strictPiece B n := by
  rw [← map_strictPiece]
  exact AddSubgroup.comap_map_eq_self_of_injective (equivalence B).injective _

/-! ### `P_γ` -/

theorem annulus_infinityFree (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : InfinityFree (RVRadiusIdeal.boundedAnnulus B γ hγ).toChart :=
  fun _ hu i => (hu.1 i).2

theorem point_infinityFree (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) : InfinityFree (RVRadiusIdeal.boundedPoint B t ht).toChart := by
  rintro u (rfl : u = ![raw t]) i
  fin_cases i
  exact raw_ne_zero t

def strictAnnulus (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    StrictChart B 1 := ⟨RVRadiusIdeal.boundedAnnulus B γ hγ, annulus_infinityFree B γ hγ⟩

def strictPoint (B : Base (M := M)) (t : Code (M := M)) (ht : DefinableClosureAtBase B .rv (raw t)) :
    StrictChart B 1 := ⟨RVRadiusIdeal.boundedPoint B t ht, point_infinityFree B t ht⟩

/-- `P_γ` in the strict ring, from objects without `∞` coordinates. -/
def strictPGamma (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RVRadiusGenerators.RadiusLift B γ) : StrictRing B :=
  objectClass (strictAnnulus B γ hγ) + objectClass (strictPoint B t.point t.definable) -
    objectClass (strictPoint B oneCode (oneCode_definable B))

theorem equivalence_strictPGamma (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RVRadiusGenerators.RadiusLift B γ) :
    equivalence B (strictPGamma B γ hγ t) = RVRadiusIdeal.pGamma B γ hγ := by
  rw [RVRadiusIdeal.pGamma_eq B γ hγ t, strictPGamma, map_sub, map_add, equivalence_objectClass,
    equivalence_objectClass, equivalence_objectClass]
  rfl

theorem strictPGamma_mem_strictPiece (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RVRadiusGenerators.RadiusLift B γ) :
    strictPGamma B γ hγ t ∈ strictPiece B 1 :=
  (strictPiece B 1).sub_mem ((strictPiece B 1).add_mem (objectClass_mem_strictPiece _)
    (objectClass_mem_strictPiece _)) (objectClass_mem_strictPiece _)

/-- The strict radius ideal `(P_Γ)`. -/
def strictRadiusIdeal (B : Base (M := M)) : Ideal (StrictRing B) :=
  Ideal.span {x | ∃ γ : Values.Gamma (M := M), ∃ hγ : γ ∈ admissibleRadii B,
    ∃ t : RVRadiusGenerators.RadiusLift B γ, x = strictPGamma B γ hγ t}

theorem map_strictRadiusIdeal (B : Base (M := M)) :
    Ideal.map (equivalence B) (strictRadiusIdeal B) = RVRadiusIdeal.radiusIdeal B := by
  rw [strictRadiusIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨γ, hγ, t, rfl⟩, rfl⟩
    exact ⟨γ, hγ, equivalence_strictPGamma B γ hγ t⟩
  · rintro ⟨γ, hγ, rfl⟩
    let t := Classical.choice (RVRadiusGenerators.radiusLift_exists B γ hγ)
    exact ⟨strictPGamma B γ hγ t, ⟨γ, hγ, t, rfl⟩, equivalence_strictPGamma B γ hγ t⟩

/-! ### `J_var` -/

/-- Notation 4.17's `J_var`, transported to the strict ring. -/
def strictManuscriptIdeal (B : Base (M := M)) : Ideal (StrictRing B) :=
  Ideal.comap (equivalence B) (RelativeAnnularGenerators.manuscriptIdeal B)

theorem map_strictManuscriptIdeal (B : Base (M := M)) :
    Ideal.map (equivalence B) (strictManuscriptIdeal B) = RelativeAnnularGenerators.manuscriptIdeal B :=
  Ideal.map_comap_of_surjective _ (equivalence B).surjective _

theorem strictManuscriptIdeal_eq_map_symm (B : Base (M := M)) :
    strictManuscriptIdeal B = Ideal.map (equivalence B).symm (RelativeAnnularGenerators.manuscriptIdeal B) :=
  (Ideal.map_symm (equivalence B)).symm

/-- `I = (P_Γ) ⊆ J_var` in the strict ring. -/
theorem strictRadiusIdeal_le (B : Base (M := M)) : strictRadiusIdeal B ≤ strictManuscriptIdeal B := by
  rw [strictManuscriptIdeal, ← Ideal.map_le_iff_le_comap, map_strictRadiusIdeal]
  exact RelativeAnnularScalar.radiusIdeal_le_manuscriptIdeal

/-- The identification descends to the quotients by `J_var`. -/
def quotientEquiv (B : Base (M := M)) :
    StrictRing B ⧸ strictManuscriptIdeal B ≃+* RVBoundedRing.Ring B ⧸ RelativeAnnularGenerators.manuscriptIdeal B :=
  Ideal.quotientEquiv _ _ (equivalence B) (map_strictManuscriptIdeal B).symm

theorem quotientEquiv_mk (B : Base (M := M)) (x : StrictRing B) :
    quotientEquiv B (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (RelativeAnnularGenerators.manuscriptIdeal B) (equivalence B x) := rfl

theorem quotientEquiv_objectClass (B : Base (M := M)) {k : ℕ} (a : StrictChart B k) :
    quotientEquiv B (Ideal.Quotient.mk _ (objectClass a)) =
      Ideal.Quotient.mk (RelativeAnnularGenerators.manuscriptIdeal B) (RVBoundedRing.objectClass a.toBoundedChart) := by
  rw [quotientEquiv_mk, equivalence_objectClass]

end DiamondIntegral.Section4.RVStrictBoundedCompatibility
