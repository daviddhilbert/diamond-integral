import IntegrationSection5.RVProjectionPadding
import IntegrationSection5.GammaGraphOperations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m l : ℕ} {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def fixedVFProjectionPadding (f : Map A B) (hf : Function.Bijective f)
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val) :
    RVProjectionPadding (G := G) B A ρ := by
  let e : GammaIso G (carrier A) (carrier B) := ⟨Equiv.ofBijective f hf,hfG⟩
  refine ⟨e.symm (gammaLogicInput G),?_,?_⟩
  · intro p
    obtain ⟨a,rfl⟩ := e.equiv.surjective p
    change (e.equiv.symm (e.equiv a)).val = _
    rw [e.equiv.symm_apply_apply]
    apply Prod.ext
    · funext i
      fin_cases i
      exact (hVF a 0).symm
    · exact (hLabels a).symm
  · intro p q
    obtain ⟨a,rfl⟩ := e.equiv.surjective p
    obtain ⟨b,rfl⟩ := e.equiv.surjective q
    change SameRV (e.equiv.symm (e.equiv a)).val (e.equiv.symm (e.equiv b)).val ↔ _
    rw [e.equiv.symm_apply_apply,e.equiv.symm_apply_apply]
    exact (fixedVF_sameRV_kernel f hVF ρ hLabels hRV a b).symm

end IntegrationInACVF.Section5
