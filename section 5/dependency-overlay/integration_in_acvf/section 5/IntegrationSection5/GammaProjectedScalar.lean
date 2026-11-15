import IntegrationSection5.GammaIsoCoordinates
import IntegrationSection5.ActiveUnaryProjection

/-! Project an actual original-Gamma unary isomorphism to a scalar centre, with its full graph, zero extension and complementary-coordinate independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
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
variable {G : GammaParameters.Base (M := M)} {n m l : ℕ}
variable {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) 1 m)} {E : Set (Point (M := M) 1 l)}

def scalarZeroExtension (A : Set (Point (M := M) n m)) (g : A → VF (M := M))
    (p : Point (M := M) n m) : VF (M := M) := if hp : p ∈ A then g ⟨p,hp⟩ else 0

theorem scalarZeroExtension_on (g : A → VF (M := M)) (a : A) : scalarZeroExtension A g a.val = g a := by
  rw [scalarZeroExtension,dif_pos a.property]

theorem gamma_scalarZeroExtension (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y)) :
    GammaScalarGraphDefinable G (fun p y => p ∈ A ∧ y = scalarZeroExtension A g p) := by
  apply GammaScalarGraphDefinable.congr hg
  intro p y
  constructor
  · rintro ⟨a,rfl,he⟩
    exact ⟨a.property,he.symm.trans (scalarZeroExtension_on g a).symm⟩
  · rintro ⟨hp,he⟩
    exact ⟨⟨p,hp⟩,rfl,(scalarZeroExtension_on g ⟨p,hp⟩).symm.trans he.symm⟩

def projectedIsoScalar (e : GammaIso G D E) (i : Fin n)
    (hD : ∀ p ∈ A, activeUnaryProjection i id p ∈ D) (a : A) : VF (M := M) :=
  vfAt (e.equiv ⟨activeUnaryProjection i id a.val,hD a.val a.property⟩).val 0

theorem gamma_projectedIsoScalar (hA : GammaSetDefinable G A) (e : GammaIso G D E) (i : Fin n)
    (hD : ∀ p ∈ A, activeUnaryProjection i id p ∈ D) :
    GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ projectedIsoScalar e i hD a = y) := by
  let X := PresentedSet.univ (pointSpace (M := M) n m) G.real
  let F := activeUnaryProjectionMap i id X
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) G.real)
  have h := (gammaLogicInput G).restrict_graph hA ((gamma_iso_coordinate_scalar_graph e 0).preimage_maps F I)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,u,hu,he⟩
    let a : A := ⟨p,hp⟩
    have hu' : (⟨activeUnaryProjection i id a.val,hD a.val a.property⟩ : D) = u := Subtype.ext hu.symm
    refine ⟨a,rfl,?_⟩
    change vfAt (e.equiv ⟨activeUnaryProjection i id a.val,hD a.val a.property⟩).val 0 = vfAt q 0
    rw [hu']
    exact he
  · rintro ⟨a,rfl,he⟩
    exact ⟨a.property,⟨activeUnaryProjection i id a.val,hD a.val a.property⟩,rfl,he⟩

theorem projectedIsoScalar_independent {A : Set (Point (M := M) 2 m)}
    (e : GammaIso G D E) (hD : ∀ p ∈ A, activeUnaryProjection 1 id p ∈ D)
    (p q : A) (he : erase 0 p.val = erase 0 q.val) :
    projectedIsoScalar e 1 hD p = projectedIsoScalar e 1 hD q := by
  have hpq : activeUnaryProjection 1 id p.val = activeUnaryProjection 1 id q.val := by
    apply Prod.ext
    · funext j
      fin_cases j
      change vfAt p.val 1 = vfAt q.val 1
      have hh := congrArg (fun p : Point (M := M) 2 m => vfAt p 1) he
      simpa only [erase,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using hh
    · have hh := congrArg (fun p : Point (M := M) 2 m => p.2) he
      exact hh
  apply congrArg (fun a : D => vfAt (e.equiv a).val 0)
  exact Subtype.ext hpq

end IntegrationInACVF.Section5
