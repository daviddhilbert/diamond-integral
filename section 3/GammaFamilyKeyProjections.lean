import «section 3».GammaRVProjectionChain

/-! The family comparison uses existing full keys. The index key and
unchanged old labels cover them, so their coordinate projection loses no
data and preserves the complete VF-volume prefix. -/
set_option autoImplicit false
noncomputable section
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace DiamondIntegral.Section3
variable {Y : Type} {p l a r : ℕ}

def gammaFamilyKeyIndices (σ : Fin l → Fin r) (ι : Fin a → Fin r) :
    Fin ((p+l)+a) → Fin (p+r) :=
  Fin.addCases (Fin.addCases (Fin.castAdd r) (fun j => Fin.natAdd p (σ j))) (fun j => Fin.natAdd p (ι j))

def gammaFamilyKeyCode (σ : Fin l → Fin r) (ι : Fin a → Fin r) (u : Fin (p+r) → Y) :=
  u ∘ gammaFamilyKeyIndices (p := p) σ ι

theorem gammaFamilyKeyCode_append (σ : Fin l → Fin r) (ι : Fin a → Fin r)
    (x : Fin p → Y) (t : Fin r → Y) :
    gammaFamilyKeyCode σ ι (Fin.append x t) = Fin.append (Fin.append x (t ∘ σ)) (t ∘ ι) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
      simp only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  · simp only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_right,Fin.append_right]

theorem gammaFamilyKeyCode_injective (σ : Fin l → Fin r) (ι : Fin a → Fin r)
    (hcover : ∀ j, (∃ k, σ k = j) ∨ ∃ k, ι k = j) :
    Function.Injective (gammaFamilyKeyCode (Y := Y) (p := p) σ ι) := by
  intro u v h
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_left] using
      congrFun h (Fin.castAdd a (Fin.castAdd l k))
  · rcases hcover k with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · simpa only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right] using
        congrFun h (Fin.castAdd a (Fin.natAdd p i))
    · simpa only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_right] using
        congrFun h (Fin.natAdd (p+l) i)

theorem gammaFamilyKeyCode_prefix (σ : Fin l → Fin r) (ι : Fin a → Fin r)
    (u : Fin (p+r) → Y) :
    gammaFamilyKeyCode σ ι u ∘ Fin.castAdd a ∘ Fin.castAdd l = u ∘ Fin.castAdd r := by
  funext j
  simp only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right]

theorem gammaFamilyKeyCode_old (σ : Fin l → Fin r) (ι : Fin a → Fin r)
    (u : Fin (p+r) → Y) :
    gammaFamilyKeyCode σ ι u ∘ Fin.natAdd (p+l) = u ∘ Fin.natAdd p ∘ ι := by
  funext j
  simp only [gammaFamilyKeyCode,gammaFamilyKeyIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right]

end DiamondIntegral.Section3
