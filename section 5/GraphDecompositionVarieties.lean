import «section 5».EquivariantGraphDecomposition
import «section 5».ImmersedVarietyObjects
import «section 5».AffineBranchBaseCompatibility

/-! The strata and common pieces of the equivariant graph decomposition
are actual objects and equivariant morphisms in the geometric variety
presentation. Their structural maps to the complex base are checked. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety
attribute [local instance] reducedPullback_isReduced
variable {n m : ℕ} {N : ℕ+} {w : Fin n → ℤ} {v : Fin m → ℤ}
variable {G : Set (Fin n ⊕ Fin m → ℂ)}
variable (d : EquivariantGraphDecomposition N w v G)

def EquivariantGraphDecomposition.sourceVariety (i : d.source.index) : EquivariantVariety.Object := by
  letI := d.source.reduced i
  letI := d.source.immersion i
  exact immersedAffineObject (d.source.base i) N (d.source_action i)
    (finiteDiagonalAlgebraAction N w) (d.source_input_equivariant i)

def EquivariantGraphDecomposition.targetVariety (j : d.target.index) : EquivariantVariety.Object := by
  letI := d.target.reduced j
  letI := d.target.immersion j
  exact immersedAffineObject (d.target.base j) N (d.target_action j)
    (finiteDiagonalAlgebraAction N v) (d.target_input_equivariant j)

def EquivariantGraphDecomposition.commonAction (i : d.source.index) (j : d.target.index) :
    rootsOfUnity (N : ℕ) ℂ →* Aut (certifiedCommonPiece d.source d.target i j) :=
  reducedPullbackSchemeAction (d.source.output i) (d.target.base j)
    (d.source_action i) (d.target_action j) (algebraSpecAction (finiteDiagonalAlgebraAction N v))
      (d.source_output_equivariant i) (d.target_input_equivariant j)

@[reassoc]
theorem EquivariantGraphDecomposition.commonAction_left (i : d.source.index) (j : d.target.index)
    (h : rootsOfUnity (N : ℕ) ℂ) :
    (d.commonAction i j h).asIso.hom ≫ certifiedCommonLeft d.source d.target i j =
      certifiedCommonLeft d.source d.target i j ≫ (d.source_action i h).asIso.hom :=
  reducedPullbackSchemeAction_fst _ _ _ _ _ _ _ h

@[reassoc]
theorem EquivariantGraphDecomposition.commonAction_right (i : d.source.index) (j : d.target.index)
    (h : rootsOfUnity (N : ℕ) ℂ) :
    (d.commonAction i j h).asIso.hom ≫ certifiedCommonRight d.source d.target i j =
      certifiedCommonRight d.source d.target i j ≫ (d.target_action j h).asIso.hom :=
  reducedPullbackSchemeAction_snd _ _ _ _ _ _ _ h

theorem EquivariantGraphDecomposition.common_immersions (i : d.source.index) (j : d.target.index) :
    IsImmersion (certifiedCommonLeft d.source d.target i j) ∧
      IsImmersion (certifiedCommonRight d.source d.target i j) := by
  have hv := graph_branches_inverse_complex_compatible d.data G d.graph_contained d.inverse_unique
  have hi := certifiedCommon_immersions hv d.source d.target i j
  exact ⟨hi.1, hi.2.1⟩

def EquivariantGraphDecomposition.commonVariety (i : d.source.index) (j : d.target.index) :
    EquivariantVariety.Object := by
  letI : AlgebraicGeometry.IsReduced (certifiedCommonPiece d.source d.target i j) :=
    reducedPullback_isReduced (d.source.output i) (d.target.base j)
  letI := (d.common_immersions i j).1
  letI := d.source.immersion i
  exact immersedAffineObject (certifiedCommonLeft d.source d.target i j ≫ d.source.base i)
    N (d.commonAction i j) (finiteDiagonalAlgebraAction N w) (by
      intro h
      rw [← Category.assoc, d.commonAction_left, Category.assoc,
        d.source_input_equivariant, ← Category.assoc])

def EquivariantGraphDecomposition.commonToSource (i : d.source.index) (j : d.target.index) :
    EquivariantVariety.Morphism (d.commonVariety i j) (d.sourceVariety i) where
  hom := certifiedCommonLeft d.source d.target i j
  overC := (Category.assoc _ _ _).symm
  equivariant h := d.commonAction_left i j (finiteRootProjection N h)

def EquivariantGraphDecomposition.commonToTarget (i : d.source.index) (j : d.target.index) :
    EquivariantVariety.Morphism (d.commonVariety i j) (d.targetVariety j) where
  hom := certifiedCommonRight d.source d.target i j
  overC := by
    change certifiedCommonRight d.source d.target i j ≫
      (d.target.base j ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))) =
      (certifiedCommonLeft d.source d.target i j ≫ d.source.base i) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ)))
    dsimp only [certifiedCommonRight, certifiedCommonLeft]
    rw [← Category.assoc, ← reducedPullback_condition, Category.assoc,
      (d.source.certificate i).overC, ← Category.assoc]
  equivariant h := d.commonAction_right i j (finiteRootProjection N h)

end DiamondIntegral.Section5
