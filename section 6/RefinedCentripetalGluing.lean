import «section 6».CentripetalCoreMembership

/-! Finite components can be put at one named aperture coefficient
before gluing. The old noncore maps are retained exactly. Released old
cores still require the lower-dimensional preparation induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {I : Type} [Finite I] {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem exists_refined_finite_centripetal_gluing
    (D : I → CentripetalData (G := G) A)
    (hsep : ∀ i k u, u ∈ (D i).activeTags.carrier → u ∈ (D k).activeTags.carrier → i = k)
    (j : Fin n) (hj : ∀ i, (D i).coordinate = j)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ E : CentripetalData (G := G) A,
      E.coordinate = j ∧ (∀ i, vfValue (D i).coefficient ≤ vfValue E.coefficient) ∧
      E.activeTags.carrier = ⋃ i, (D i).activeTags.carrier ∧
      (∀ i p, p ∈ A.carrier → p.2 ∈ (D i).activeTags.carrier → (D i).core p = false → E.point p = (D i).point p) ∧
      (∀ p ∈ A.carrier, (∀ i, p.2 ∉ (D i).activeTags.carrier) → (E.point p).1 = p.1) := by
  obtain ⟨c,hc0,hcdef,hcpos,hcdom⟩ := exists_common_named_coefficient (fun i => (D i).coefficient)
    (fun i => (D i).coefficient_nonzero) (fun i => (D i).coefficient_nonnegative)
    (fun i => (D i).coefficient_definable)
  let F (i : I) := (D i).refineCoefficient c hc0 hcdef (hcdom i)
  have hFsep : ∀ i k u, u ∈ (F i).activeTags.carrier → u ∈ (F k).activeTags.carrier → i = k := hsep
  have hFj (i) : (F i).coordinate = j := hj i
  have hFc (i) : (F i).coefficient = c := rfl
  obtain ⟨E,hEj,hEc,hEU,hEpoint,hEout⟩ := exists_finite_centripetal_gluing F hFsep j hFj c hFc
    hc0 hcpos hcdef hA hAD htag
  refine ⟨E,hEj,fun i => ?_,hEU,?_,hEout⟩
  · rw [hEc]
    exact hcdom i
  · intro i p hp hu hcore
    exact (hEpoint i p hp hu).trans ((D i).refineCoefficient_noncore_agrees c hc0 hcdef (hcdom i) p hcore)

end DiamondIntegral.Section6
