import IntegrationSection5.CellGammaBridge
import IntegrationSection5.GammaActiveUnaryFocus

/-! The actual unary presentations of both native VF cell projections
remain definable over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

def vfUnarySet (D : Set (VF (M := M))) : Set (Point (M := M) 1 0) :=
  {p | vfAt p 0 ∈ D}

theorem gamma_activeUnaryProjection_image (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (i : Fin n) :
    GammaSetDefinable G (activeUnaryProjection i Fin.elim0 '' A) := by
  let X := PresentedSet.univ (pointSpace (M := M) n m) G.real
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph hA
    ((gammaLogicInput G).real_map_graph (activeUnaryProjectionMap i Fin.elim0 X)))
  convert h using 1
  ext q
  constructor
  · rintro ⟨p,hp,hq⟩
    exact ⟨p,hp,⟨p,Set.mem_univ _⟩,rfl,hq⟩
  · rintro ⟨p,hp,a,ha,hq⟩
    exact ⟨p,hp,(congrArg (activeUnaryProjection i Fin.elim0) ha).symm.trans hq⟩

theorem cell_first_unary_gamma (R : Set (VF (M := M) × VF (M := M)))
    (hR : GammaSetDefinable G (cellPointSet R)) : GammaSetDefinable G (vfUnarySet (first R)) := by
  have h := gamma_activeUnaryProjection_image (cellPointSet R) hR (0 : Fin 2)
  have he : activeUnaryProjection (0 : Fin 2) Fin.elim0 '' cellPointSet R = vfUnarySet (first R) := by
    ext q
    constructor
    · rintro ⟨p,hp,hq⟩
      exact ⟨pointCell p,hp,congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) hq⟩
    · rintro ⟨p,hp,hq⟩
      refine ⟨cellPoint p,hp,Prod.ext ?_ (Subsingleton.elim _ _)⟩
      funext j
      fin_cases j
      exact hq
  exact he ▸ h

theorem cell_second_unary_gamma (R : Set (VF (M := M) × VF (M := M)))
    (hR : GammaSetDefinable G (cellPointSet R)) : GammaSetDefinable G (vfUnarySet (second R)) := by
  have h := gamma_activeUnaryProjection_image (cellPointSet R) hR (1 : Fin 2)
  have he : activeUnaryProjection (1 : Fin 2) Fin.elim0 '' cellPointSet R = vfUnarySet (second R) := by
    ext q
    constructor
    · rintro ⟨p,hp,hq⟩
      exact ⟨pointCell p,hp,congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) hq⟩
    · rintro ⟨p,hp,hq⟩
      refine ⟨cellPoint p,hp,Prod.ext ?_ (Subsingleton.elim _ _)⟩
      funext j
      fin_cases j
      exact hq
  exact he ▸ h

end IntegrationInACVF.Section5
