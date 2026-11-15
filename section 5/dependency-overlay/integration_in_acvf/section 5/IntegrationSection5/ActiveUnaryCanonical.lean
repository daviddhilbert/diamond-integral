import IntegrationSection5.ActiveUnaryProjection

/-! The selected-coordinate canonical map commutes exactly with unary
projection, with every new and old RV label in its specified position. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m l : ℕ}

def activeCanonicalProjection (ρ : Fin m → Fin l) : Fin (1+m) → Fin (1+l) :=
  Fin.addCases (Fin.castAdd l) (fun j => Fin.natAdd 1 (ρ j))

theorem activeCanonicalProjection_bijective (ρ : Fin m → Fin l) (hρ : Function.Bijective ρ) :
    Function.Bijective (activeCanonicalProjection ρ) := by
  let e : Fin (1+m) ≃ Fin (1+l) := finSumFinEquiv.symm.trans
    (((Equiv.refl (Fin 1)).sumCongr (Equiv.ofBijective ρ hρ)).trans finSumFinEquiv)
  have he : e.toFun = activeCanonicalProjection ρ := by
    funext j
    cases j using Fin.addCases with
    | left j => simp [e,activeCanonicalProjection]
    | right j => simp [e,activeCanonicalProjection]
  rw [← he]
  exact e.bijective

theorem activeUnaryProjection_canonical (i : Fin n) (ρ : Fin m → Fin l)
    (p : Point (M := M) n l) :
    activeUnaryProjection i (activeCanonicalProjection ρ) (coordinateCanonical i p) =
      canonical (activeUnaryProjection i ρ p) := by
  refine Prod.ext rfl ?_
  funext j
  cases j using Fin.addCases with
  | left j =>
    fin_cases j
    rfl
  | right j =>
    simp only [activeUnaryProjection,activeCanonicalProjection,coordinateCanonical,canonical,
      Function.comp_apply,Fin.addCases_right,Fin.append_right]

end IntegrationInACVF.Section5
