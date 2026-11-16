import «section 6».FiniteFocusImages

/-! A scalar function supplied by a complete original-base map that is
constant on existing RV-label fibres has a canonical label presentation.
The choice is eliminated from its pointwise factor identity; no section
of the global RV map is postulated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawVFSpace (M := M) 1) S}

def scalarRVValue (f : Map A B) (u : Fin r → RVInfinity M) : VF M :=
  if h : ∃ p : A,p.val.2=u then (f h.choose).val 0 else 0

theorem scalarRVValue_at (f : Map A B)
    (hConst : ∀ p q : A,p.val.2=q.val.2 → (f p).val 0=(f q).val 0) (p : A) :
    scalarRVValue f p.val.2=(f p).val 0 := by
  have h : ∃ q : A,q.val.2=p.val.2 := ⟨p,rfl⟩
  rw [scalarRVValue,dif_pos h]
  exact hConst h.choose p h.choose_spec

end DiamondIntegral.Section6
