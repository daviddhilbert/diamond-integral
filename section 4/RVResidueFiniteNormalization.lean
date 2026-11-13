import «section 4».RVResidueFullFibres

/-! An actual finite-value-pattern RV set is a finite disjoint union
of pure-field normalizations. Representatives are chosen only for this
geometric comparison; original-base definability is not asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueFiniteNormalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def pattern {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) : Fin n → Values.GammaTop (M := M) :=
  fun i => Values.vrv (t i)

def Patterns {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :=
  Set.range (fun t : A => pattern t.val)

def representative {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (i : Patterns A) : A := Classical.choose i.property

theorem representative_pattern {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (i : Patterns A) :
    pattern (representative A i).val = i.val := Classical.choose_spec i.property

def forgetFibre (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S)
    (z : Σ i : Patterns A, RVResidueFullFibres.fibre hc A (representative A i).val) : A :=
  ⟨z.2.val, z.2.property.1⟩

theorem forgetFibre_injective (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    Function.Injective (forgetFibre hc A) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ he
  have hv : x.val = y.val := congrArg Subtype.val he
  have hx : pattern x.val = i.val :=
    (funext x.property.2).trans (representative_pattern A i)
  have hy : pattern y.val = j.val :=
    (funext y.property.2).trans (representative_pattern A j)
  have hij : i = j := Subtype.ext (hx.symm.trans ((congrArg pattern hv).trans hy))
  subst j
  have hxy : x = y := Subtype.ext hv
  subst y
  rfl

theorem forgetFibre_surjective (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    Function.Surjective (forgetFibre hc A) := by
  intro t
  let i : Patterns A := ⟨pattern t.val, ⟨t, rfl⟩⟩
  have hv : ∀ j, Values.vrv (t.val j) = Values.vrv ((representative A i).val j) := by
    intro j
    exact (congrFun (representative_pattern A i) j).symm
  exact ⟨⟨i, ⟨t.val, t.property, hv⟩⟩, rfl⟩

def fibreSumEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    (Σ i : Patterns A, RVResidueFullFibres.fibre hc A (representative A i).val) ≃ A :=
  Equiv.ofBijective (forgetFibre hc A)
    ⟨forgetFibre_injective hc A, forgetFibre_surjective hc A⟩

def normalized (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (i : Patterns A) : Set (Fin n → ModelResidue M) :=
  RVResidueFullFibres.normalized hc A (representative A i).val

theorem normalized_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (i : Patterns A) : PureDef (normalized hc A i) :=
  RVResidueFullFibres.normalized_definable hc A (representative A i).val

def sumEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    (Σ i : Patterns A, normalized hc A i) ≃ A :=
  (Equiv.sigmaCongrRight (fun i =>
    (RVResidueFullFibres.normalizationEquiv hc A (representative A i).val).symm)).trans
      (fibreSumEquiv hc A)

theorem sumEquiv_value (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (z : Σ i : Patterns A, normalized hc A i) :
    (sumEquiv hc A z).val = residueScale (representative A z.1).val z.2.val := rfl

end DiamondIntegral.Section4.RVResidueFiniteNormalization
