import «section 3».GammaGroundRVFormProductCharts
import Mathlib.Data.Fintype.Sigma
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {Q : Space LRV M}
variable {w v : Q.Carrier → Values.Gamma (M := M)}

def GammaGroundRVFormProductChart.changeWeight
    (C : GammaGroundRVFormProductChart hc B Q w)
    (v : Q.Carrier → Values.Gamma (M := M)) (hv : ∀ x ∈ C.source.carrier, v x = w x) :
    GammaGroundRVFormProductChart hc B Q v where
  source := C.source
  residueArity := C.residueArity
  gammaArity := C.gammaArity
  residue := C.residue
  gamma := C.gamma
  residue_finite := C.residue_finite
  bijection := C.bijection
  weight := C.weight
  weight_definable := C.weight_definable
  preserves a := (hv a.val a.property).trans (C.preserves a)

/-- Finite disjoint chart decompositions assemble without cancelling
any positive scissors classes. -/
theorem gammaGroundRVFormProductCharts_assemble
    (A : GammaGroundDefSet hc B Q) {N : ℕ}
    (X : Fin N → GammaGroundDefSet hc B Q)
    (hXd : ∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier)
    (hXc : ∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (X i).carrier)
    (hlocal : ∀ i, ∃ L : ℕ, ∃ C : Fin L → GammaGroundRVFormProductChart hc B Q w,
      (∀ j k, j ≠ k → Disjoint (C j).source.carrier (C k).source.carrier) ∧
      (∀ x, x ∈ (X i).carrier ↔ ∃ j, x ∈ (C j).source.carrier)) :
    ∃ L : ℕ, ∃ C : Fin L → GammaGroundRVFormProductChart hc B Q w,
      (∀ j k, j ≠ k → Disjoint (C j).source.carrier (C k).source.carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ j, x ∈ (C j).source.carrier) := by
  choose L C hCd hCc using hlocal
  let J := (i : Fin N) × Fin (L i)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let D : J → GammaGroundRVFormProductChart hc B Q w := fun j => C j.1 j.2
  have hsub : ∀ i j, (C i j).source.carrier ⊆ (X i).carrier :=
    fun i j x hx => (hCc i x).mpr ⟨j,hx⟩
  have hDd : ∀ i j : J, i ≠ j → Disjoint (D i).source.carrier (D j).source.carrier := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hne
    by_cases hij : i = j
    · subst j
      exact hCd i a b (fun he => hne (by cases he; rfl))
    · exact (hXd i j hij).mono (hsub i a) (hsub j b)
  refine ⟨Fintype.card J,fun i => D (e i),fun i j hij => hDd (e i) (e j) (fun he => hij (e.injective he)),?_⟩
  intro x
  rw [hXc x]
  constructor
  · rintro ⟨i,hx⟩
    obtain ⟨j,hj⟩ := (hCc i x).mp hx
    obtain ⟨k,hk⟩ := e.surjective ⟨i,j⟩
    exact ⟨k,by simpa only [hk,D] using hj⟩
  · rintro ⟨k,hk⟩
    exact ⟨(e k).1,hsub (e k).1 (e k).2 hk⟩
end DiamondIntegral.Section3
