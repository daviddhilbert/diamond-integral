import «section 3».MeasuredRVScissors
import «section 3».RVProducts

/-! The RES subcategories use the finite value support of the whole
domain. This condition survives restrictions and actual cartesian products;
their scissors and the forgetful additive maps use those same objects. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

theorem resProperty_restrict (U : RVObject (M := M) S k) (hU : resProperty S k U)
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier) :
    resProperty S k (U.restrict X hX) := by
  apply hU.subset
  rintro γ ⟨t, ht, rfl⟩
  exact ⟨t, hX ht, rfl⟩

def RESObject.empty (S : Set M) (k : ℕ) : RESObject (M := M) S k :=
  ⟨RVObject.empty S k, Set.finite_empty.image _⟩

def RESObject.restrict (U : RESObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.obj.arity) S) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    RESObject S k := ⟨U.obj.restrict X hX, resProperty_restrict U.obj U.property X hX⟩

def RESObject.product (U : RESObject (M := M) S k) (V : RESObject (M := M) S l) :
    RESObject S (k + l) := ⟨U.obj.product V.obj, RVObject.product_res U.property V.property⟩

def resPresentation (S : Set M) (k : ℕ) : ScissorPresentation (RESObject (M := M) S k) where
  iso A B := Nonempty (A ≅ B)
  empty := RESObject.empty S k
  scissor A B D E := RVScissor A.obj B.obj D.obj E.obj

abbrev RESKPlus (S : Set M) (k : ℕ) := KPlus (resPresentation (M := M) S k)
abbrev RESKGroup (S : Set M) (k : ℕ) := KGroup (resPresentation (M := M) S k)

def resClass (U : RESObject (M := M) S k) : RESKPlus S k := positiveClass (resPresentation S k) U

def resToRVKPlus : RESKPlus (M := M) S k →+ RVKPlus S k :=
  PositiveAdditiveGrothendieck.lift (resPresentation S k) {
    toFun U := rvClass U.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact rvClass_iso ((resProperty S k).ι.mapIso e)
    empty := rvClass_empty
    scissor := fun h => positiveClass_scissor (rvPresentation S k) h }

@[simp] theorem resToRVKPlus_class (U : RESObject (M := M) S k) :
    resToRVKPlus (resClass U) = rvClass U.obj := PositiveAdditiveGrothendieck.lift_of _ _ U

def MeasuredRESObject.empty (S : Set M) (k : ℕ) : MeasuredRESObject (M := M) S k :=
  ⟨MeasuredRVObject.empty S k, (RESObject.empty S k).property⟩

def MeasuredRESObject.restrict (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) : MeasuredRESObject S k :=
  ⟨U.obj.restrict hc X hX, resProperty_restrict U.obj.underlying U.property X hX⟩

def measuredRESPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (MeasuredRESObject (M := M) S k) where
  iso A B := Nonempty (A ≅ B)
  empty := MeasuredRESObject.empty S k
  scissor A B D E := MeasuredRVScissor hc A.obj B.obj D.obj E.obj

abbrev MeasuredRESKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (measuredRESPresentation hc S k)
abbrev MeasuredRESKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KGroup (measuredRESPresentation hc S k)

def measuredResClass (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) : MeasuredRESKPlus hc S k :=
  positiveClass (measuredRESPresentation hc S k) U

def measuredResToRVKPlus (hc : CanonicalStructure.IsCanonical (M := M)) :
    MeasuredRESKPlus hc S k →+ MeasuredRVKPlus hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredRESPresentation hc S k) {
    toFun U := measuredRVClass hc U.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact measuredRVClass_iso hc ((measuredResProperty S k).ι.mapIso e)
    empty := measuredRVClass_empty hc
    scissor := fun h => positiveClass_scissor (measuredRVPresentation hc S k) h }

@[simp] theorem measuredResToRVKPlus_class (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) :
    measuredResToRVKPlus hc (measuredResClass hc U) = measuredRVClass hc U.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

end DiamondIntegral.Section3
