import «section 3».RVCategories

/-! Definition 3.12 and Notation 3.17. Volume forms are actual Gamma-valued
functions with full original-base invariant graphs. The manuscript's
pointwise Jacobian equation is equivalent to preservation of the combined
weight. This gives composition and inversion at every point, not merely
away from an exceptional locus. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVObject.target (U : RVObject (M := M) S k) (u : U.domain) : Fin k → Section2.RV M :=
  fun i => ⟨(U.volume u).val i, fun he => U.nonzero u i (congrArg Subtype.val he)⟩

structure RVVolumeForm (U : RVObject (M := M) S k) where
  toFun : U.domain → Section2.Gamma M
  graph : GammaParameters.Relation S 1 U.arity (fun _ => .rv)
  graph_spec : ∀ γ t, t ∈ graph.fibre ![γ] ↔
    ∃ u : U.domain, rvValues u.val = t ∧ toFun u = γ

structure MeasuredRVObject (S : Set M) (k : ℕ) where
  underlying : RVObject (M := M) S k
  form : RVVolumeForm underlying

def MeasuredRVObject.combinedWeight (U : MeasuredRVObject (M := M) S k)
    (u : U.underlying.domain) : Section2.Gamma M :=
  U.form.toFun u * ∏ i, Section2.rvFiniteValue (U.underlying.target u i)

theorem measuredRV_equation_iff (U V : MeasuredRVObject (M := M) S k)
    (F : DefinableBijection U.underlying.domain V.underlying.domain)
    (u : U.underlying.domain) :
    U.form.toFun u = V.form.toFun (F.map u) *
      Section2.gammaJacobian (U.underlying.target u, Fin.elim0)
        (V.underlying.target (F.map u), Fin.elim0) ↔
    U.combinedWeight u = V.combinedWeight (F.map u) := by
  simp only [Section2.gammaJacobian, Section2.gammaLabelWeight,
    Fin.prod_univ_zero, mul_one, MeasuredRVObject.combinedWeight]
  rw [← mul_div_assoc, eq_div_iff_mul_eq']

structure MeasuredRVHom (U V : MeasuredRVObject (M := M) S k) where
  bijection : DefinableBijection U.underlying.domain V.underlying.domain
  preserves : ∀ u, U.combinedWeight u = V.combinedWeight (bijection.map u)

namespace MeasuredRVHom

variable {U V W : MeasuredRVObject (M := M) S k}

@[ext] theorem ext {f g : MeasuredRVHom U V} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (U : MeasuredRVObject (M := M) S k) : MeasuredRVHom U U :=
  ⟨DefinableBijection.id U.underlying.domain, fun _ => rfl⟩

def comp (g : MeasuredRVHom V W) (f : MeasuredRVHom U V) : MeasuredRVHom U W :=
  ⟨g.bijection.comp f.bijection, fun u => (f.preserves u).trans (g.preserves (f.bijection.map u))⟩

def symm (f : MeasuredRVHom U V) : MeasuredRVHom V U where
  bijection := f.bijection.symm
  preserves v := by
    have h := f.preserves (f.bijection.symm.map v)
    rw [f.bijection.apply_symm_apply] at h
    exact h.symm

end MeasuredRVHom

instance : Groupoid (MeasuredRVObject (M := M) S k) where
  Hom := MeasuredRVHom
  id := MeasuredRVHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  inv_comp f := by
    apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a
    exact f.bijection.apply_symm_apply a
  comp_inv f := by
    apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a
    exact f.bijection.symm_apply_apply a

def measuredResProperty (S : Set M) (k : ℕ) :
    ObjectProperty (MeasuredRVObject (M := M) S k) := fun U => resProperty S k U.underlying

abbrev MeasuredRESObject (S : Set M) (k : ℕ) :=
  (measuredResProperty (M := M) S k).FullSubcategory

end DiamondIntegral.Section3
