import «section 3».EssentialVFMeasure
import «section 3».GammaVolumeForms
import «section 3».VFDimensionBridge
import Mathlib.CategoryTheory.Groupoid

/-! Definition 3.5 and Remark 3.7 in positive degree. Morphisms are exactly
the quotient of actual essential measure-preserving representatives. The
agreement theorem uses the manuscript's section 2 dimension. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)

/-- The positive-degree finite-volume VF objects of Definition 3.5. -/
structure PositiveMeasuredVF (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawMixedSpace (M := M) (k + 1) arity) (C.base : Set M)
  finite : ∀ a, {t | (a, t) ∈ domain.carrier}.Finite
  form : GammaVolumeForm hc domain

namespace PositiveMeasuredVF

variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {k : ℕ}

def weight (A : PositiveMeasuredVF C hc k) (a : A.domain) : Values.GammaTop (M := M) := (gammaFormValue A.form a).val

def Representative (A B : PositiveMeasuredVF C hc k) :=
  {f : EssentialVFMap A.domain B.domain // f.Preserves Values.vfValueHom A.weight B.weight}

/-- Using a subtype of the independent-point bijections makes agreement
of morphisms ordinary equality. `quotientEquiv` verifies the quotient. -/
def Germ (A B : PositiveMeasuredVF C hc k) :=
  {e : EssentialVFMap.Generic A.domain ≃ EssentialVFMap.Generic B.domain //
    ∃ f : Representative A B, f.val.genericEquiv hc = e}

def ofRepresentative {A B : PositiveMeasuredVF C hc k} (f : Representative A B) : Germ A B :=
  ⟨f.val.genericEquiv hc, f, rfl⟩

def aeSetoid (A B : PositiveMeasuredVF C hc k) : Setoid (Representative A B) where
  r f g := f.val.genericEquiv hc = g.val.genericEquiv hc
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h j => h.trans j⟩

theorem ae_iff_agreement {A B : PositiveMeasuredVF C hc k} (f g : Representative A B) :
    (aeSetoid A B).r f g ↔
    ∃ E : DefSet (rawMixedSpace (M := M) (k + 1) A.arity) (C.base : Set M),
      vfDim (rawRVSpace 1) (A.domain.sdiff E) < k + 1 ∧
      ∀ x ∈ E.carrier, ∃ (p : f.val.source) (q : g.val.source),
        p.val = x ∧ q.val = x ∧ (f.val.map p).val = (g.val.map q).val :=
  EssentialVFMap.genericEquiv_eq_iff hc C.saturated C.small (Nat.zero_lt_succ k) f.val g.val

/-- Remark 3.7's equivalence classes are exactly the implemented germs. -/
def quotientEquiv (A B : PositiveMeasuredVF C hc k) : Quotient (aeSetoid A B) ≃ Germ A B := by
  let F : Quotient (aeSetoid A B) → Germ A B :=
    Quotient.lift ofRepresentative (fun _ _ h => Subtype.ext h)
  apply Equiv.ofBijective F
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g he
    exact Quotient.sound (congrArg Subtype.val he)
  · rintro ⟨e, f, rfl⟩
    exact ⟨Quotient.mk _ f, rfl⟩

instance positiveMeasuredVFGroupoid [CharZero VF] : Groupoid (PositiveMeasuredVF C hc k) where
  Hom := Germ
  id A := ⟨Equiv.refl _, by
    obtain ⟨f, hf, he⟩ := EssentialVFMap.exists_preserving_id hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) Values.vfValueHom A.weight
    exact ⟨⟨f, hf⟩, he⟩⟩
  comp {A B D} f g := ⟨f.val.trans g.val, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨q, hq⟩ := g.property
    obtain ⟨e, he, h⟩ := EssentialVFMap.exists_preserving_comp hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) Values.vfValueHom A.weight B.weight D.weight
      p.val q.val p.property q.property
    exact ⟨⟨e, he⟩, h.trans (congrArg₂ Equiv.trans hp hq)⟩⟩
  id_comp f := by apply Subtype.ext; exact Equiv.refl_trans f.val
  comp_id f := by apply Subtype.ext; exact Equiv.trans_refl f.val
  assoc f g h := by apply Subtype.ext; exact Equiv.trans_assoc f.val g.val h.val
  inv {A B} f := ⟨f.val.symm, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨e, he, h⟩ := EssentialVFMap.exists_preserving_symm hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) Values.vfValueHom A.weight B.weight p.val p.property
    exact ⟨⟨e, he⟩, h.trans (congrArg Equiv.symm hp)⟩⟩
  inv_comp f := by apply Subtype.ext; exact Equiv.symm_trans_self f.val
  comp_inv f := by apply Subtype.ext; exact Equiv.self_trans_symm f.val


/-- Equality of morphisms is precisely agreement outside a set small in
this manuscript's dimension, not just in the reused finite-map dimension. -/
theorem ae_iff_paper_agreement
    {V : Type} [LinearOrderedCommGroupWithZero V] [Valued VF V]
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A B : PositiveMeasuredVF C hc k} (f g : Representative A B) :
    (aeSetoid A B).r f g ↔
    ∃ E : DefSet (rawMixedSpace (M := M) (k + 1) A.arity) (C.base : Set M),
      Section2.vfDimension (A.domain.sdiff E).carrier < ((k + 1 : ℕ) : WithBot ℕ) ∧
      ∀ x ∈ E.carrier, ∃ (p : f.val.source) (q : g.val.source),
        p.val = x ∧ q.val = x ∧ (f.val.map p).val = (g.val.map q).val := by
  rw [ae_iff_agreement]
  apply exists_congr
  intro E
  rw [vf_small_iff_companion hc C.saturated C.small hv (Nat.zero_lt_succ k)]

end PositiveMeasuredVF
end DiamondIntegral.Section3
