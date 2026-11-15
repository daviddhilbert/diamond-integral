import IntegrationSection5.CanonicalHeadGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}

theorem coordinateCanonical_oldRV (i : Fin n) (p : Point (M := M) n m) :
    (coordinateCanonical i p).2 ∘ Fin.natAdd 1 = p.2 := by
  funext j
  simp only [coordinateCanonical,Function.comp_apply,Fin.append_right]

theorem activeUnaryProjection_dropCanonical (i j : Fin n) (p : Point (M := M) n m) :
    activeUnaryProjection i (Fin.natAdd 1) (coordinateCanonical j p) = activeUnaryProjection i id p := by
  refine Prod.ext rfl ?_
  exact coordinateCanonical_oldRV j p

theorem coordinateCanonical_slice_image (i : Fin n) (D : Set (Point (M := M) n m))
    (E : Set (Fin m → RV (M := M))) :
    coordinateCanonical i '' {p | p ∈ D ∧ p.2 ∈ E} =
      {q | q ∈ coordinateCanonical i '' D ∧ q.2 ∘ Fin.natAdd 1 ∈ E} := by
  ext q
  constructor
  · rintro ⟨p,⟨hp,hE⟩,rfl⟩
    exact ⟨⟨p,hp,rfl⟩,by rw [coordinateCanonical_oldRV]; exact hE⟩
  · rintro ⟨⟨p,hp,rfl⟩,hE⟩
    rw [coordinateCanonical_oldRV] at hE
    exact ⟨p,⟨hp,hE⟩,rfl⟩

theorem headSaturated_coordinateCanonical_slice {n : ℕ}
    (D : Set (Point (M := M) (n+1) m)) (E : Set (Fin m → RV (M := M)))
    (hD : HeadSaturated {p | p ∈ D ∧ p.2 ∈ E}) :
    HeadSaturated {q | q ∈ coordinateCanonical 0 '' D ∧ q.2 ∘ Fin.natAdd 1 ∈ E} := by
  rw [← coordinateCanonical_slice_image]
  exact headSaturated_coordinateCanonical_image _ hD

theorem coordinateCanonical_image_tagged (i : Fin n) (D : Set (Point (M := M) n m)) :
    Tagged (coordinateCanonical i '' D) i (0 : Fin (1+m)) := by
  rintro q ⟨p,hp,rfl⟩
  change Fin.append (fun _ : Fin 1 => rv (vfAt p i)) p.2 (0 : Fin (1+m)) = rv (vfAt p i)
  exact Fin.append_left _ _ (0 : Fin 1)

theorem mixed_first_projection_tagged (D : Set (Point (M := M) 2 m)) (k : Fin m)
    (hD : Tagged D 0 k) : Tagged (mixedUnaryProjectionSet D 0) 0 k := by
  rintro q ⟨p,hp,hpq⟩
  rw [← hpq]
  exact hD p hp

end IntegrationInACVF.Section5
