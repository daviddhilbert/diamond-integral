import «section 6».ConstrainedContinuousVFTemplates

/-! One first-order admissibility condition for a whole RV-indexed
family of continuous total VF graphs. The family is tested with all
existing RV labels quantified, before compactness is applied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}
variable {ι : Type} [Finite ι]

def rvFamilyJointGraph (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) :
    Set ((ι ⊕ Fin r) ⊕ (Fin n ⊕ Fin m) → M) :=
  {z | Sum.elim (fun i => z (.inl (.inl i)))
    (Sum.elim (fun j => z (.inl (.inr j))) (z ∘ Sum.inr)) ∈ R}

theorem rvFamilyJointGraph_definable
    (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvFamilyJointGraph R) := by
  let e : ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → (ι ⊕ Fin r) ⊕ (Fin n ⊕ Fin m) :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  convert hR.preimage_comp e using 1
  ext z
  have he : z ∘ e=Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (fun j => z (.inl (.inr j))) (z ∘ Sum.inr)) := by
    funext i; rcases i with i | (i | i) <;> rfl
  change _ ∈ R ↔ z ∘ e ∈ R
  rw [he]

def rvFamilyGoodRows (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) : Set (ι ⊕ Fin r → M) :=
  (totalVFGraphParameterLocus (rvFamilyJointGraph R) ∩ singleVFGraphParameterLocus (rvFamilyJointGraph R)) ∩
    continuousParameterLocus (rvFamilyJointGraph R)

theorem rvFamilyGoodRows_definable
    (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvFamilyGoodRows R) :=
  ((totalVFGraphParameterLocus_definable _ (rvFamilyJointGraph_definable R hR)).inter
    (singleVFGraphParameterLocus_definable _ (rvFamilyJointGraph_definable R hR))).inter
      (continuousParameterLocus_definable _ (rvFamilyJointGraph_definable R hR))

def rvFamilyGoodParameterLocus (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) : Set (ι → M) :=
  {a | ∀ u : Fin r → M,u ∈ Set.range (rvValues (M := M)) → Sum.elim a u ∈ rvFamilyGoodRows R}

theorem rvFamilyGoodParameterLocus_definable
    (R : Set (ι ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvFamilyGoodParameterLocus R) := by
  have hRV : S.Definable LRV (Set.range (rvValues (M := M) (n := r))) :=
    (rawRVSpace (M := M) r).definable_domain S
  have hBad := (hRV.preimage_comp (Sum.inr : Fin r → ι ⊕ Fin r)).inter (rvFamilyGoodRows_definable R hR).compl
  convert hBad.exists_of_finite.compl using 1
  ext a
  change (∀ u : Fin r → M,u ∈ Set.range rvValues → Sum.elim a u ∈ rvFamilyGoodRows R) ↔
    ¬ ∃ u : Fin r → M,u ∈ Set.range rvValues ∧ Sum.elim a u ∉ rvFamilyGoodRows R
  simp only [not_exists,not_and,not_not]

end DiamondIntegral.Section6
