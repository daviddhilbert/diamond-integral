import «section 3».GammaGroundFiniteCoverPartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {Q : Space LRV M}

/-- A finite ordered cover has a disjoint refinement indexed by the
same formulas. Empty pieces cause no choice of a fallback formula. -/
theorem gammaGround_ordered_cover_partition {N : ℕ}
    (A : GammaGroundDefSet hc B Q) (E : Fin N → GammaGroundDefSet hc B Q)
    (hcover : ∀ a : A, ∃ i, a.val ∈ (E i).carrier) :
    ∃ P : Fin N → GammaGroundDefSet hc B Q,
      (∀ i, (P i).carrier ⊆ A.carrier ∧ (P i).carrier ⊆ (E i).carrier) ∧
      ∀ a : A, ∃! i, a.val ∈ (P i).carrier := by
  let V (i j : Fin N) : GammaGroundDefSet hc B Q :=
    if j < i then (E j).compl else GammaGroundDefSet.univ hc B Q
  let P : Fin N → GammaGroundDefSet hc B Q := fun i =>
    (A.inter (E i)).inter ⟨⋂ j, (V i j).carrier,GammaGroundDefinable.iInter (fun j => (V i j).definable)⟩
  have hmem (i : Fin N) (x : Q.Carrier) : x ∈ (P i).carrier ↔
      x ∈ A.carrier ∧ x ∈ (E i).carrier ∧ ∀ j, j < i → x ∉ (E j).carrier := by
    change ((x ∈ A.carrier ∧ x ∈ (E i).carrier) ∧ x ∈ ⋂ j, (V i j).carrier) ↔ _
    simp only [Set.mem_iInter,V]
    constructor
    · rintro ⟨⟨ha,he⟩,h⟩
      refine ⟨ha,he,fun j hj => ?_⟩
      simpa only [if_pos hj,GammaGroundDefSet.compl,Set.mem_compl_iff] using h j
    · rintro ⟨ha,he,h⟩
      refine ⟨⟨ha,he⟩,fun j => ?_⟩
      by_cases hj : j < i
      · exact (if_pos hj) ▸ h j hj
      · simp only [if_neg hj,GammaGroundDefSet.univ,GammaGroundDefSet.ofReal,DefSet.univ,Set.mem_univ]
  refine ⟨P,fun i => ⟨fun _ hx => ((hmem i _).mp hx).1,fun _ hx => ((hmem i _).mp hx).2.1⟩,?_⟩
  intro a
  obtain ⟨i,hi,hmin⟩ := Set.exists_min_image {i | a.val ∈ (E i).carrier} (fun i => i)
    (Set.toFinite _) (hcover a)
  have hp : a.val ∈ (P i).carrier := (hmem i a.val).mpr
    ⟨a.property,hi,fun j hj hje => (not_le_of_gt hj) (hmin j hje)⟩
  refine ⟨i,hp,?_⟩
  intro j hj
  have h := (hmem j a.val).mp hj
  exact le_antisymm (le_of_not_gt (fun hji => h.2.2 i hji hi)) (hmin j h.2.1)

end DiamondIntegral.Section3
