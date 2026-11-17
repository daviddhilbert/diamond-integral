import «section 3».GammaSelectedRetainedData

/-! Generic finite Gamma-measured row proofs propagate through the
specified traced head preparations. This is the selected-family step
used recursively in the RV-density contraction argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n k : ℕ}

theorem GammaSelectedRetainedData.schema_sameRow
    (U : GammaSelectedRetainedData hc B n (k+1)) (N L : ℕ) (x : Fin n → VF (M := M)) :
    (U.schema N).essential.toRVTemplate.sameRow (U.schema L).essential.toRVTemplate (vfValues x) :=
  ⟨⟨fun j => (x j).property,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩,
    ⟨fun j => (x j).property,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩⟩

theorem GammaGenericSelectedRelated.refl {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : GammaSelectedRetainedData hc B n (k+1)) : GammaGenericSelectedRelated U U := by
  obtain ⟨N,hN⟩ := U.uniform_bound hκ hs hr hg
  exact ⟨N,N,hN,hN,fun x _ => ⟨.agreement _ _,(U.schema N).essential_valid _ (hN x),
    (U.schema N).essential_valid _ (hN x),U.schema_sameRow N N x⟩⟩

theorem GammaGenericSelectedRelated.symm
    {U V : GammaSelectedRetainedData hc B n (k+1)} (h : GammaGenericSelectedRelated U V) : GammaGenericSelectedRelated V U := by
  obtain ⟨N,L,hN,hL,hH⟩ := h
  refine ⟨L,N,hL,hN,?_⟩
  intro x hx
  obtain ⟨H,hH⟩ := hH x hx
  exact ⟨.symm H,hH⟩

theorem GammaGenericSelectedRelated.trans
    {U V W : GammaSelectedRetainedData hc B n (k+1)} (h : GammaGenericSelectedRelated U V)
    (g : GammaGenericSelectedRelated V W) : GammaGenericSelectedRelated U W := by
  obtain ⟨N,L,hN,hL,hH⟩ := h
  obtain ⟨P,Q,hP,hQ,hK⟩ := g
  refine ⟨N,Q,hN,hQ,?_⟩
  intro x hx
  obtain ⟨H,hH⟩ := hH x hx
  obtain ⟨K,hK⟩ := hK x hx
  exact ⟨.trans (V.schema L).essential H
    (.trans (V.schema P).essential (.agreement _ _) K),
    hH,⟨⟨(V.schema L).essential_valid _ (hL x),(V.schema P).essential_valid _ (hP x),V.schema_sameRow L P x⟩,hK⟩⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem GammaGenericSelectedRelated.head
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaSelectedRetainedData hc B (n+1) (k+1)}
    (h : GammaGenericSelectedRelated U V) (T : GammaSelectedTracedHead U) (E : GammaSelectedTracedHead V) :
    GammaGenericSelectedRelated (k := 1+k) (T.next hκ.le hs hr) (E.next hκ.le hs hr) := by
  obtain ⟨N,L,hN,hL,hWitness⟩ := h
  obtain ⟨NT,hNT⟩ := (T.next hκ.le hs hr).uniform_bound hκ.le hs hr hg
  obtain ⟨NE,hNE⟩ := (E.next hκ.le hs hr).uniform_bound hκ.le hs hr hg
  refine ⟨NT,NE,hNT,hNE,?_⟩
  intro x hx
  have hFT := Eq.mp (congrArg (fun F => F.valid (vfValues x)) (T.next_schema hκ.le hs hr NT)) (hNT x)
  have hFE := Eq.mp (congrArg (fun F => F.valid (vfValues x)) (E.next_schema hκ.le hs hr NE)) (hNE x)
  have H := gammaGeneric_selected_head_formula_witness hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    T.head E.head T.trace E.trace T.gamma E.gamma T.agrees E.agrees U.select V.select U.finite V.finite
    U.labels V.labels U.labels_mem V.labels_mem U.form V.form N L hWitness NT NE x hx hFT hFE
  rw [T.next_schema hκ.le hs hr NT,E.next_schema hκ.le hs hr NE]
  exact H

end DiamondIntegral.Section3
