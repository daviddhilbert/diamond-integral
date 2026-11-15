import IntegrationSection5.VerticalMeanTrace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
namespace FibreFocusData
variable {i : Fin n} {k : Fin m}

def extendBase (D : FibreFocusData A i k) (hSR : S ⊆ R) : FibreFocusData (SpecialTransformations.Section5.extendBase A hSR) i k where
  tagged := D.tagged
  locus := D.locus
  locus_definable := by
    let L : DefSet (M := M) S n m := PresentedSet.mk D.locus D.locus_definable
    exact setDefinable (SpecialTransformations.Section5.extendBase L hSR)
  center := D.center
  center_graph := by
    let f := @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
      (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S R D.active
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) D.centerMap hSR
    have h := Map.graph_definable f
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext j
      fin_cases j
      exact hz.symm
  independent := D.independent
  center_sameRV := D.center_sameRV
  locus_saturated := D.locus_saturated

end FibreFocusData
namespace UniformRelativeTrace

def castSource {a b : ℕ} {X Y : DefSet (M := M) S n a} {Z : DefSet (M := M) S n b}
    (T : UniformRelativeTrace S n X Z) (h : X = Y) : UniformRelativeTrace S n Y Z := h ▸ T

theorem castSource_val {a b : ℕ} {X Y : DefSet (M := M) S n a} {Z : DefSet (M := M) S n b}
    (T : UniformRelativeTrace S n X Z) (h : X = Y) (y : Y) :
    ((T.castSource h).toMap y).val = (T.toMap ⟨y.val,h.symm ▸ y.property⟩).val := by
  subst Y
  rfl

def extendBase (T : UniformRelativeTrace S n A B) (hSR : S ⊆ R) :
    UniformRelativeTrace R n (SpecialTransformations.Section5.extendBase A hSR)
      (SpecialTransformations.Section5.extendBase B hSR) := by
  induction T with
  | nil A => exact .nil _
  | @canonical m l A B i tail ih =>
    have he : SpecialTransformations.Section5.extendBase (coordinateCanonicalImage A i) hSR =
        coordinateCanonicalImage (SpecialTransformations.Section5.extendBase A hSR) i := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    exact .canonical i (ih.castSource he)
  | @focus m l A B i k D tail ih =>
    have he : SpecialTransformations.Section5.extendBase D.image hSR = (D.extendBase hSR).image := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    exact .focus (D.extendBase hSR) (ih.castSource he)

theorem extendBase_val (T : UniformRelativeTrace S n A B) (hSR : S ⊆ R)
    (a : SpecialTransformations.Section5.extendBase A hSR) :
    ((T.extendBase hSR).toMap a).val = (T.toMap ⟨a.val,a.property⟩).val := by
  induction T with
  | nil A => rfl
  | @canonical m l A B i tail ih =>
    have he : SpecialTransformations.Section5.extendBase (coordinateCanonicalImage A i) hSR =
        coordinateCanonicalImage (SpecialTransformations.Section5.extendBase A hSR) i := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    change (((tail.extendBase hSR).castSource he).toMap
      (coordinateCanonicalBijection (SpecialTransformations.Section5.extendBase A hSR) i a)).val =
        (tail.toMap (coordinateCanonicalBijection A i ⟨a.val,a.property⟩)).val
    rw [castSource_val]
    exact ih _
  | @focus m l A B i k D tail ih =>
    have he : SpecialTransformations.Section5.extendBase D.image hSR = (D.extendBase hSR).image := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    change (((tail.extendBase hSR).castSource he).toMap ((D.extendBase hSR).toImage a)).val =
      (tail.toMap (D.toImage ⟨a.val,a.property⟩)).val
    rw [castSource_val]
    exact ih _

end UniformRelativeTrace
end IntegrationInACVF.Section5
