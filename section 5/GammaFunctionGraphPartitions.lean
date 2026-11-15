import «section 5».ScalarGammaParameterControl

/-! Restricting a Gamma function partitions its full value-torsor graph
by the original RV input pieces; every output representative is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

theorem groundGammaFunctionGraphLift_restrict_mem
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (hA : A.carrier ⊆ X.carrier)
    (u : Fin (n+1) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (groundGammaFunctionGraphLift (f.restrict hA)).carrier ↔
      Fin.init u ∈ A.carrier ∧ u ∈ (groundGammaFunctionGraphLift f).carrier := by
  constructor
  · rintro ⟨a, ha, hf⟩
    exact ⟨ha ▸ a.property, ⟨⟨a.val, hA a.property⟩, ha, hf⟩⟩
  · rintro ⟨hAinit, x, hx, hf⟩
    let a : A := ⟨Fin.init u, hAinit⟩
    have hxa : x = (⟨a.val, hA a.property⟩ : X) := Subtype.ext hx
    rw [hxa] at hf
    exact ⟨a, rfl, hf⟩

theorem groundGammaFunctionGraphLift_finite_partition {ι : Type} [Fintype ι]
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint
      (groundGammaFunctionGraphLift (f.restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩))).carrier
      (groundGammaFunctionGraphLift (f.restrict (fun x hx => (hcov x).mpr ⟨j,hx⟩))).carrier) ∧
    ∀ u, u ∈ (groundGammaFunctionGraphLift f).carrier ↔
      ∃ i, u ∈ (groundGammaFunctionGraphLift (f.restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩))).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact Set.disjoint_left.mp (hd i j hij)
      ((groundGammaFunctionGraphLift_restrict_mem f (A i) _ u).mp hi).1
      ((groundGammaFunctionGraphLift_restrict_mem f (A j) _ u).mp hj).1
  · intro u
    constructor
    · intro hu
      have hu' := hu
      obtain ⟨x, hx, _⟩ := hu'
      have hX : Fin.init u ∈ X.carrier := hx ▸ x.property
      obtain ⟨i, hi⟩ := (hcov _).mp hX
      exact ⟨i, (groundGammaFunctionGraphLift_restrict_mem f (A i) _ u).mpr ⟨hi, hu⟩⟩
    · rintro ⟨i, hi⟩
      exact ((groundGammaFunctionGraphLift_restrict_mem f (A i) _ u).mp hi).2

end DiamondIntegral.Section5
