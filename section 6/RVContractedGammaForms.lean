import «section 6».UnaryTagDiscFibres

/-! Actual original-base descent of a Gamma form constant on old-tag
fibers. The full raw Gamma graph is the checked mixed-family image;
every proper representative is retained and no RV section is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def rvContractedGamma (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (t : Fin r → M) : Gamma M :=
  if ht : ∃ p ∈ A, rvInputValues p.2 = t then ω ht.choose else 1

theorem rvContractedGamma_at (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → ω p = ω q) (p : Mixed M n r) (hp : p ∈ A) :
    rvContractedGamma A ω (rvInputValues p.2) = ω p := by
  have ht : ∃ q ∈ A, rvInputValues q.2 = rvInputValues p.2 := ⟨p,hp,rfl⟩
  rw [rvContractedGamma,dite_eq_left ht]
  exact hω ht.choose ht.choose_spec.1 p hp (rvInputValues_injective ht.choose_spec.2)

theorem mixedGammaFamily_eq_contracted_singleton
    (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → ω p = ω q)
    (t : Fin r → M) (ht : t ∈ rvInputValues '' (Prod.snd '' A)) :
    mixedGammaFamily A ω t = {rvContractedGamma A ω t} := by
  ext γ
  constructor
  · rintro ⟨p,hp,hpt,rfl⟩
    change ω p = rvContractedGamma A ω t
    rw [← hpt,rvContractedGamma_at A ω hω p hp]
  · intro hγ
    obtain ⟨u,⟨p,hp,rfl⟩,hut⟩ := ht
    refine ⟨p,hp,hut,?_⟩
    have h := rvContractedGamma_at A ω hω p hp
    rw [hut] at h
    exact (Set.mem_singleton_iff.mp hγ).trans h

theorem rvContractedGamma_graph_definable
    (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A ω))
    (hω : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → ω p = ω q) :
    S.Definable LRV (rawGammaFamilyGraph (rvInputValues '' (Prod.snd '' A))
      (fun t => {rvContractedGamma A ω t})) := by
  convert mixedGammaFamily_graph_definable S A ω hGraph using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
  apply and_congr_right
  intro hz
  rw [mixedGammaFamily_eq_contracted_singleton A ω hω _ hz]

theorem rvContractedGamma_image (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → ω p = ω q) :
    rvContractedGamma A ω '' (rvInputValues '' (Prod.snd '' A)) = ω '' A := by
  ext γ
  constructor
  · rintro ⟨t,⟨u,⟨p,hp,rfl⟩,rfl⟩,rfl⟩
    exact ⟨p,hp,(rvContractedGamma_at A ω hω p hp).symm⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨rvInputValues p.2,⟨p.2,⟨p,hp,rfl⟩,rfl⟩,rvContractedGamma_at A ω hω p hp⟩

end DiamondIntegral.Section6
