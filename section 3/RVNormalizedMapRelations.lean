import «section 3».RVResidueNormalizedPoints
import «section 3».GammaGroundRVMapCharacterSymmetry
import «section 3».GammaGroundRawResiduePurity
import «section 3».ACFGenericTargetIndependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
variable {D : GammaGroundDefSet hc B (rawRVSpace (M := M) m)}

def rvNormalizedMapRelation (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ) :
    Set (Fin n ⊕ Fin m → ModelResidue M) :=
  {z | f.graph (fun i => rvNormalizedPoint (a i) (z (Sum.inl i)))
    (fun j => rvNormalizedPoint (b j) (z (Sum.inr j)))}

theorem rvNormalizedMapRelation_functional (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (y z : Fin m → ModelResidue M)
    (hy : Sum.elim x y ∈ rvNormalizedMapRelation f a b)
    (hz : Sum.elim x z ∈ rvNormalizedMapRelation f a b) : y = z := by
  obtain ⟨u,hu,hy⟩ := hy
  obtain ⟨v,hv,hz⟩ := hz
  have he : u = v := Subtype.ext (hu.trans hv.symm)
  subst v
  funext j
  apply rvNormalizedPoint_raw_injective (b j)
  exact congrArg (fun t => (t j).val) (hy.symm.trans hz)

theorem rvNormalizedMapRelation_inverse_functional (f : GammaGroundMap A D)
    (hf : Function.Injective f)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ)
    (x z : Fin n → ModelResidue M) (y : Fin m → ModelResidue M)
    (hx : Sum.elim x y ∈ rvNormalizedMapRelation f a b)
    (hz : Sum.elim z y ∈ rvNormalizedMapRelation f a b) : z = x := by
  obtain ⟨u,hu,hy⟩ := hx
  obtain ⟨v,hv,hz⟩ := hz
  have he : u = v := hf (Subtype.ext (hy.trans hz.symm))
  subst v
  funext i
  apply rvNormalizedPoint_raw_injective (a i)
  exact congrArg (fun t => (t i).val) (hv.symm.trans hu)

/-- Normalization of an actual map graph is pure-field definable; this
is an extraction from its original-ground graph, not a new input. -/
theorem rvNormalizedMapRelation_pure {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk B.real < κ)
    (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ) :
    ResiduePurity.PureDef (rvNormalizedMapRelation f a b) := by
  let Q := rawRVSpace (M := M) n
  let R := rawRVSpace (M := M) m
  let G := Q.relation R f.graph
  have hp : ∀ z ∈ G, ∀ i, iRV (z i) := by
    intro z hz i
    obtain ⟨hx,hy,_⟩ := hz
    cases i with
    | inl i =>
      obtain ⟨u,hu⟩ := hx
      simpa only [rvValues,Function.comp_apply] using Eq.mp (congrArg iRV (congrFun hu i)) (u i).property
    | inr i =>
      obtain ⟨u,hu⟩ := hy
      simpa only [rvValues,Function.comp_apply] using Eq.mp (congrArg iRV (congrFun hu i)) (u i).property
  let t : Fin n ⊕ Fin m → CanonicalRV.RVSort M :=
    Sum.elim (fun i => (a i : CanonicalRV.RVSort M)) (fun j => (b j : CanonicalRV.RVSort M))
  let S : Set (Fin n ⊕ Fin m → ModelResidue M) :=
    {z | (fun i => (t i * residueRV (z i)).val) ∈ G}
  have h : ResiduePurity.PureDef S := gammaGroundRaw_residue_pullback_pure hκ hsmall
    G f.raw_graph_definable hp t
  have hRS : rvNormalizedMapRelation f a b = S := by
    ext z
    let u := fun i => rvNormalizedPoint (a i) (z (Sum.inl i))
    let v := fun j => rvNormalizedPoint (b j) (z (Sum.inr j))
    have he : (fun i => (t i * residueRV (z i)).val) =
        Sum.elim (rvValues u) (rvValues v) := by
      funext i
      cases i <;> rfl
    change f.graph u v ↔ (fun i => (t i * residueRV (z i)).val) ∈ G
    rw [he]
    have hr := Space.relation_decode Q R f.graph ⟨rvValues u,⟨u,rfl⟩⟩ ⟨rvValues v,⟨v,rfl⟩⟩
    rw [decode_rvValues,decode_rvValues] at hr
    exact hr.symm
  exact hRS.symm ▸ h

end DiamondIntegral.Section3
