import «section 3».GammaGroundRVCoproductMaps
import «section 3».GammaGroundRVEmptyClasses
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundRVCoprodLeft_injective (U V : GammaGroundRVObject hc B k) :
    Function.Injective (gammaGroundRVCoprodLeft U V) := by
  intro a b h
  apply gammaGroundRVLeftTag_injective U.domain V.arity
  have hv := congrArg (fun z : (U.coprod V).domain => z.val) h
  exact Subtype.ext hv

theorem gammaGroundRVCoprodRight_injective (U V : GammaGroundRVObject hc B k) :
    Function.Injective (gammaGroundRVCoprodRight U V) := by
  intro a b h
  apply gammaGroundRVRightTag_injective V.domain U.arity
  have hv := congrArg (fun z : (U.coprod V).domain => z.val) h
  exact Subtype.ext hv

/-- The actual finite RV coproduct in a single label degree. -/
def gammaGroundRVListSum (l : List (GammaGroundRVObject hc B k)) : GammaGroundRVObject hc B k :=
  l.foldr GammaGroundRVObject.coprod (GammaGroundRVObject.empty hc B k)

def gammaGroundRVListInjection (l : List (GammaGroundRVObject hc B k)) :
    ∀ i : Fin l.length, GammaGroundMap (l.get i).domain (gammaGroundRVListSum l).domain := by
  induction l with
  | nil => intro i; exact i.elim0
  | cons U l ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact gammaGroundRVCoprodLeft U (gammaGroundRVListSum l)
    · exact (gammaGroundRVCoprodRight U (gammaGroundRVListSum l)).comp (ih j)

@[simp] theorem gammaGroundRVListInjection_zero (U : GammaGroundRVObject hc B k)
    (l : List (GammaGroundRVObject hc B k)) :
    gammaGroundRVListInjection (U::l) 0 = gammaGroundRVCoprodLeft U (gammaGroundRVListSum l) := rfl

@[simp] theorem gammaGroundRVListInjection_succ (U : GammaGroundRVObject hc B k)
    (l : List (GammaGroundRVObject hc B k)) (i : Fin l.length) :
    gammaGroundRVListInjection (U::l) i.succ =
      (gammaGroundRVCoprodRight U (gammaGroundRVListSum l)).comp (gammaGroundRVListInjection l i) := rfl

theorem gammaGroundRVListInjection_injective (l : List (GammaGroundRVObject hc B k))
    (i : Fin l.length) : Function.Injective (gammaGroundRVListInjection l i) := by
  induction l with
  | nil => exact i.elim0
  | cons U l ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact gammaGroundRVCoprodLeft_injective U (gammaGroundRVListSum l)
    · exact (gammaGroundRVCoprodRight_injective U (gammaGroundRVListSum l)).comp (ih j)

/-- Every point belongs to a genuine component; no class cancellation
or stabilization is needed to recover the component map. -/
theorem gammaGroundRVListInjection_cover (l : List (GammaGroundRVObject hc B k))
    (t : (gammaGroundRVListSum l).domain) :
    ∃ i : Fin l.length, ∃ a : (l.get i).domain, gammaGroundRVListInjection l i a = t := by
  induction l with
  | nil => exact False.elim t.property
  | cons U l ih =>
    rcases t.property with ⟨a,ha⟩ | ⟨b,hb⟩
    · exact ⟨0,a,Subtype.ext ha⟩
    · obtain ⟨i,a,ha⟩ := ih b
      refine ⟨i.succ,a,?_⟩
      change gammaGroundRVCoprodRight U (gammaGroundRVListSum l) (gammaGroundRVListInjection l i a) = t
      rw [ha]
      exact Subtype.ext hb

theorem gammaGroundRVListInjection_disjoint (l : List (GammaGroundRVObject hc B k))
    (i j : Fin l.length) (hij : i ≠ j) :
    Disjoint (gammaGroundRVListInjection l i).image.carrier (gammaGroundRVListInjection l j).image.carrier := by
  induction l with
  | nil => exact i.elim0
  | cons U l ih =>
    revert hij
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact False.elim (hij rfl)
      · intro hij
        apply Set.disjoint_left.mpr
        rintro z ⟨a,ha⟩ ⟨c,hc⟩
        exact Set.disjoint_left.mp (gammaGroundRVTaggedImages_disjoint U.domain (gammaGroundRVListSum l).domain)
          ⟨a,ha⟩ ⟨gammaGroundRVListInjection l b c,hc⟩
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        apply Set.disjoint_left.mpr
        rintro z ⟨c,hc⟩ ⟨b,hb⟩
        exact Set.disjoint_left.mp (gammaGroundRVTaggedImages_disjoint U.domain (gammaGroundRVListSum l).domain)
          ⟨b,hb⟩ ⟨gammaGroundRVListInjection l a c,hc⟩
      · intro hij
        apply Set.disjoint_left.mpr
        rintro z ⟨c,hc⟩ ⟨d,hd⟩
        have he : gammaGroundRVCoprodRight U (gammaGroundRVListSum l) (gammaGroundRVListInjection l a c) =
            gammaGroundRVCoprodRight U (gammaGroundRVListSum l) (gammaGroundRVListInjection l b d) :=
          Subtype.ext (hc.trans hd.symm)
        have he' := gammaGroundRVCoprodRight_injective U (gammaGroundRVListSum l) he
        exact Set.disjoint_left.mp (ih a b (fun h => hij (congrArg Fin.succ h)))
          (Set.mem_range_self c) ⟨d,(congrArg Subtype.val he').symm⟩

theorem gammaGroundRVListSum_class (l : List (GammaGroundRVObject hc B k)) :
    gammaGroundRVClass (gammaGroundRVListSum l) = (l.map gammaGroundRVClass).sum := by
  induction l with
  | nil => exact gammaGroundRVClass_empty
  | cons U l ih =>
    change gammaGroundRVClass (U.coprod (gammaGroundRVListSum l)) = _
    rw [gammaGroundRVClass_coprod,ih]
    rfl
end DiamondIntegral.Section3
