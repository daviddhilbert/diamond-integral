import IntegrationSection5.MixedVolumeImages
import IntegrationSection5.GammaIsoCoordinates

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
variable {G : GammaParameters.Base (M := M)} {n m u l : ℕ}

/-- The mixed-set condition defining the finite RV-fibre VF category. -/
def FiniteMixedRVFibres (A : Set (Point (M := M) n m)) : Prop :=
  ∀ x : Fin n → VF (M := M), {t : Fin m → RV (M := M) | (x,t) ∈ A}.Finite

theorem finite_mixed_points_over_finite_vf {A : Set (Point (M := M) n m)}
    (hA : FiniteMixedRVFibres A) (F : Set (Fin n → VF (M := M))) (hF : F.Finite) :
    {p : Point (M := M) n m | p ∈ A ∧ p.1 ∈ F}.Finite := by
  have h := hF.biUnion (fun x _ => (hA x).image (fun t => (x,t)))
  apply h.subset
  rintro ⟨x,t⟩ ⟨ha,hx⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,⟨t,ha,rfl⟩⟩⟩

theorem gamma_iso_fixed_vf_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u l)}
    (e : GammaIso G A B) (x : Fin n → VF (M := M)) :
    {y : Fin u → VF (M := M) | ∃ a : A, a.val.1 = x ∧ (e.equiv a).val.1 = y}.Finite := by
  let D (i : Fin u) := {y : VF (M := M) | ∃ a : A, a.val.1 = x ∧ vfAt (e.equiv a).val i = y}
  have hD (i : Fin u) : (D i).Finite :=
    fixed_vf_scalar_image_finite hκ hs G hsmall A (fun a => vfAt (e.equiv a).val i)
      (gamma_iso_coordinate_scalar_graph e i) x
  apply (Set.Finite.pi hD).subset
  rintro y ⟨a,ha,rfl⟩ i _
  exact ⟨a,ha,rfl⟩

/-- Definable bijections preserve finite auxiliary RV fibres over the original Gamma base. -/
theorem GammaIso.finite_mixed_rv_fibres {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u l)}
    (e : GammaIso G A B) (hA : FiniteMixedRVFibres A) : FiniteMixedRVFibres B := by
  intro y
  let inv := e.symm (gammaLogicInput G)
  let F := {x : Fin n → VF (M := M) | ∃ b : B, b.val.1 = y ∧ (inv.equiv b).val.1 = x}
  have hF : F.Finite := gamma_iso_fixed_vf_image_finite hκ hs hsmall inv y
  have hP := finite_mixed_points_over_finite_vf hA F hF
  have hSub := hP.preimage (f := fun a : A => a.val) Subtype.val_injective.injOn
  have hImg := hSub.image (fun a : A => (e.equiv a).val.2)
  apply hImg.subset
  intro t ht
  let b : B := ⟨(y,t),ht⟩
  let a := inv.equiv b
  refine ⟨a,⟨a.property,b,rfl,rfl⟩,?_⟩
  exact congrArg (fun z : B => z.val.2) (e.equiv.apply_symm_apply b)

end IntegrationInACVF.Section5
