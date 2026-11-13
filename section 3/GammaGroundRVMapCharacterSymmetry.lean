import «section 3».GammaGroundRVCharacterSymmetry
import «section 3».GammaGroundRawGraphs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)
variable {n m : ℕ}

/-- Every actual original-ground RV map commutes with the character
symmetries, on its full actual domain. -/
theorem gammaGroundRVMap_character_equivariant
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (f : GammaGroundMap A D) (u : A) :
    ∃ v : A, v.val = (fun i => rvOriginalGroundCharacterTwistZero B χ (u.val i)) ∧
      (f v).val = (fun i => rvOriginalGroundCharacterTwistZero B χ ((f u).val i)) := by
  let Q := rawRVSpace (M := M) n
  let R := rawRVSpace (M := M) m
  let G := Q.relation R f.graph
  have hg : GammaGroundRawDefinable hc B G := f.raw_graph_definable
  have hp : ∀ z ∈ G, ∀ i, iRV (z i) := by
    intro z hz i
    obtain ⟨hx,hy,_⟩ := hz
    cases i with
    | inl i =>
      obtain ⟨a,ha⟩ := hx
      have h := congrFun ha i
      simpa only [rvValues,Function.comp_apply] using Eq.mp (congrArg iRV h) (a i).property
    | inr i =>
      obtain ⟨a,ha⟩ := hy
      have h := congrFun ha i
      simpa only [rvValues,Function.comp_apply] using Eq.mp (congrArg iRV h) (a i).property
  let z : Fin n ⊕ Fin m → CanonicalRV.RVSort M := Sum.elim u.val (f u).val
  have hrow (a : Fin n → CanonicalRV.RVSort M) (b : Fin m → CanonicalRV.RVSort M) :
      (fun i => (Sum.elim a b i).val) ∈ G ↔ f.graph a b := by
    have h := Space.relation_decode Q R f.graph
      ⟨rvValues a,⟨a,rfl⟩⟩ ⟨rvValues b,⟨b,rfl⟩⟩
    rw [decode_rvValues,decode_rvValues] at h
    exact h
  have hz : (fun i => (z i).val) ∈ G := (hrow u.val (f u).val).mpr ⟨u,rfl,rfl⟩
  have htw := (gammaGroundRawRV_character_invariant B χ G hg hp z).mp hz
  have he : (fun i => (rvOriginalGroundCharacterTwistZero B χ (z i)).val) =
      (fun i => (Sum.elim (fun j => rvOriginalGroundCharacterTwistZero B χ (u.val j))
        (fun j => rvOriginalGroundCharacterTwistZero B χ ((f u).val j)) i).val) := by
    funext i
    cases i <;> rfl
  have hh := Eq.mp (congrArg (fun t => t ∈ G) he) htw
  exact (hrow _ _).mp hh

end DiamondIntegral.Section3
