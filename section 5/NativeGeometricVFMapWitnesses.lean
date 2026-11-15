import «section 5».NativeGeometricVFLiftSchemata
import «section 5».NativeMixedMapFibres
import «section 3».GammaGroundFiniteCoverPartition

/-! Pointwise geometric fibre equalities supply a finite original-ground
catalogue, and then a finite disjoint base partition, of complete geometric
witnesses. Common denominator degrees and all RES certificates are chosen
before preparation; no uniform denominator bound is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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

def NativeGeometricVFFibreLiftEquality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) : Prop :=
  ∃ k l : ℕ,
    ∃ U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k,
    ∃ V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l,
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f z) (gammaGroundObjectLift U)) ∧
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f' z) (gammaGroundObjectLift V)) ∧
      nativeGeometricRetraction h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
        (RVOrdinaryPNormalization.quotient _ (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U))) =
      nativeGeometricRetraction h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
        (RVOrdinaryPNormalization.quotient _ (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart V)))

theorem native_geometric_vf_map_finite_whole_witness_catalog
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    ∃ J : Finset (NativeGeometricVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val),
      ∀ z ∈ nativeMixedDomain C,∃ W ∈ J,W.Valid z := by
  apply native_geometric_vf_lift_finite_catalog hκ hs hr hγ (nativeMixedDomain C)
    (nativeMixedDomain_definable C) (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val
    (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property
  intro z hz
  obtain ⟨k,l,U,V,⟨e⟩,⟨e'⟩,he⟩ := h z hz
  exact native_geometric_vf_lift_schema_at_parameter h00 linear hκ hs hr hγ hΓ
    (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val z
    ((nativeMixedDomain_definable C).proper z hz)
    (nativeMixedMapFibreAt f z) (nativeMixedMapFibreAt f' z)
    (nativeMixedMapFibreAt_domain f z).symm (nativeMixedMapFibreAt_domain f' z).symm U V e e' he

theorem native_geometric_vf_map_whole_witness_partition
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    ∃ N : ℕ,∃ P : Fin N → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q),
      (∀ i,(P i).carrier ⊆ C.carrier ∧ ((P i).carrier = ∅ ∨
        ∃ W : NativeGeometricVFLiftEqualitySchema (B := B)
          (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc
            (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val,
          ∀ b : P i,W.Valid (nativeMixedCode b.val))) ∧
      (∀ i j,i ≠ j → Disjoint (P i).carrier (P j).carrier) ∧
      ∀ b,b ∈ C.carrier ↔ ∃ i,b ∈ (P i).carrier := by
  obtain ⟨J,hJ⟩ := native_geometric_vf_map_finite_whole_witness_catalog h00 linear hκ hs hr hγ hΓ f f' h
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let V : Fin (Fintype.card J) → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q) := fun i =>
    nativeMixedOfRaw {z | (e i).val.Valid z}
      ((e i).val.valid_definable (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property)
  have hcover : ∀ b ∈ C.carrier,∃ i,b ∈ (V i).carrier := by
    intro b hb
    obtain ⟨W,hW,hw⟩ := hJ (nativeMixedCode b) ⟨b,hb,rfl⟩
    obtain ⟨i,hi⟩ := e.surjective ⟨W,hW⟩
    refine ⟨i,?_⟩
    change (e i).val.Valid (nativeMixedCode b)
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
