import IntegrationSection5.GlobalNonrectangleHeads
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}

theorem coordinateCanonical_replace_sameRV (i : Fin n) (p : Point (M := M) n m)
    (x : VF (M := M)) (hx : rv x = rv (vfAt p i)) :
    coordinateCanonical i (replace i p x) = replace i (coordinateCanonical i p) x := by
  apply Prod.ext
  · rfl
  · funext j
    cases j using Fin.addCases with
    | left j =>
      fin_cases j
      simp only [coordinateCanonical,replace,vfAt,Function.update_self]
      exact congrArg (fun r => Fin.append (fun _ : Fin 1 => r) p.2 (0 : Fin (1+m))) hx
    | right j => simp only [coordinateCanonical,replace,Fin.append_right]

theorem headSaturated_coordinateCanonical_image (D : Set (Point (M := M) (n+1) m))
    (hD : HeadSaturated D) : HeadSaturated (coordinateCanonical 0 '' D) := by
  rintro p ⟨a,ha,rfl⟩ x hx
  have hx' : rv x = rv (vfAt a 0) := hx
  exact ⟨replace 0 a x,hD a ha x hx',coordinateCanonical_replace_sameRV 0 a x hx'⟩

theorem rvFibreRectangles_coordinateCanonical (A : Set (Point (M := M) 2 m))
    (hA : RVFibreRectangles A) : RVFibreRectangles (coordinateCanonical 0 '' A) := by
  rintro p ⟨a,ha,rfl⟩ q ⟨b,hb,rfl⟩ hLabels
  have hOld : a.2 = b.2 := by
    funext j
    have h := congrFun hLabels (Fin.natAdd 1 j)
    simpa only [coordinateCanonical,Fin.append_right] using h
  have hCross := hA a ha b hb hOld
  refine ⟨(![vfAt a 0,vfAt b 1],a.2),hCross,?_⟩
  apply Prod.ext
  · funext j; fin_cases j <;> rfl
  · funext j
    cases j using Fin.addCases with
    | left j => fin_cases j; rfl
    | right j => rfl

end IntegrationInACVF.Section5
