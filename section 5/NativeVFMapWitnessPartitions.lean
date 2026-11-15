import «section 5».NativeVFMapWitnessUniformity
import «section 3».GammaGroundFiniteCoverPartition

/-! A finite native base partition selects one whole actual VF fibre
package on every nonempty piece. The partition and every selected full
graph remain over the original Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s p q : ℕ}

theorem native_vf_map_whole_witness_partition
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    ∃ N : ℕ,∃ P : Fin N → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q),
      (∀ i,(P i).carrier ⊆ C.carrier ∧ ((P i).carrier = ∅ ∨
        ∃ W : NativeVFLiftEqualitySchema (B := B)
          (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc .bounded
            (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val,
          ∀ b : P i,W.Valid hc (nativeMixedCode b.val))) ∧
      (∀ i j,i ≠ j → Disjoint (P i).carrier (P j).carrier) ∧
      ∀ b,b ∈ C.carrier ↔ ∃ i,b ∈ (P i).carrier := by
  obtain ⟨J,hJ⟩ := native_vf_map_finite_whole_witness_catalog h00 linear hκ hs hr hγ hΓ f f' h
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let V : Fin (Fintype.card J) → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q) := fun i =>
    nativeMixedOfRaw {z | (e i).val.Valid hc z}
      ((e i).val.valid_definable hc (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property)
  have hcover : ∀ b ∈ C.carrier,∃ i,b ∈ (V i).carrier := by
    intro b hb
    obtain ⟨W,hW,hw⟩ := hJ (nativeMixedCode b) ⟨b,hb,rfl⟩
    obtain ⟨i,hi⟩ := e.surjective ⟨W,hW⟩
    refine ⟨i,?_⟩
    change (e i).val.Valid hc (nativeMixedCode b)
    rw [hi]
    exact hw
  obtain ⟨N,P,hP,hd,hcov⟩ := gammaGround_finite_cover_partition C V hcover
  refine ⟨N,P,?_,hd,hcov⟩
  intro i
  refine ⟨(hP i).1,?_⟩
  rcases (hP i).2 with hempty | ⟨j,hj⟩
  · exact Or.inl hempty
  · exact Or.inr ⟨(e j).val,fun b => hj b.property⟩

end DiamondIntegral.Section5
