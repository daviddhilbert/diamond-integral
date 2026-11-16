import «section 6».NamedFiniteNeighborhoods

/-! Exact paired cores inside any prescribed original-base definable
neighborhoods of a finite center family. All radius choices and both
core graphs remain over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_paired_cores_in_prescribed_neighborhoods
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A B : Set (VF M)) (hA : IsOpen A) (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) (hCont : ContinuousOn f A)
    (hBound : ∃ η : Gamma M, ∀ y ∈ B, η.val ≤ vfValue y)
    (C : Set (Fin 2 → VF M)) (hC : S.Definable LRV (vfValues '' C)) (hCFin : C.Finite)
    (hCenters : ∀ q ∈ C, q 0 ∈ A ∧ f (q 0) = q 1)
    (R T : Set (Fin 2 ⊕ Fin 1 → M)) (hR : S.Definable LRV R) (hT : S.Definable LRV T)
    (hRNear : ∀ q ∈ C, {x : VF M | Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R} ∈ 𝓝 (q 0))
    (hTNear : ∀ q ∈ C, {y : VF M | Sum.elim (vfValues q) (fun _ : Fin 1 => y.val) ∈ T} ∈ 𝓝 (q 1)) :
    ∃ m : VF M, ∃ D : SeparatedPairedCoreData (S := S) A B f C m,
      S.Definable₁ LRV {m.val} ∧
      (∀ q ∈ C, ∀ x ∈ candidateDiscCore D.radii q 0,
        Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R) ∧
      (∀ q ∈ C, ∀ y ∈ candidateDiscCore D.radii q 1,
        Sum.elim (vfValues q) (fun _ : Fin 1 => y.val) ∈ T) := by
  obtain ⟨c,hc0,hcDef,hcPos,hcFit⟩ := exists_named_radius_for_finite_neighborhoods
    h00 hc hv V hV hVS hSV hnt C hC hCFin R hR 0 hRNear
  obtain ⟨d,hd0,hdDef,hdPos,hdFit⟩ := exists_named_radius_for_finite_neighborhoods
    h00 hc hv V hV hVS hSV hnt C hC hCFin T hT 1 hTNear
  obtain ⟨m,hm0,hmDef,hmPos,hmLarger⟩ := exists_common_named_coefficient (![c,d] : Fin 2 → VF M)
    (by intro i; fin_cases i; exact hc0; exact hd0)
    (by intro i; fin_cases i; exact hcPos.le; exact hdPos.le)
    (by intro i; fin_cases i; exact hcDef; exact hdDef)
  obtain ⟨D⟩ := exists_separated_paired_cores h00 hc hκ hs hv V hsmall hV hVS hSV hnt
    A B hA f hbij hGraph hCont hBound C hC hCFin hCenters m hm0 hmPos hmDef
  refine ⟨m,D,hmDef,?_,?_⟩
  · intro q hq x hx
    obtain ⟨γ,δ,hγ,hδ,hSource,hTarget⟩ := D.centered q hq
    have hγc : finiteValue c hc0 ≤ γ := by
      have hm : vfValue c ≤ vfValue m := by
        simpa only [Matrix.cons_val_zero] using hmLarger 0
      change Values.vfValueHom c ≤ γ.val
      simpa only [valueHom_eq_value] using hm.trans hγ
    exact hcFit q hq x (centeredGammaDisc_anti (q 0) hγc (hSource ▸ hx))
  · intro q hq y hy
    obtain ⟨γ,δ,hγ,hδ,hSource,hTarget⟩ := D.centered q hq
    have hδd : finiteValue d hd0 ≤ δ := by
      have hm : vfValue d ≤ vfValue m := by
        simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using hmLarger 1
      change Values.vfValueHom d ≤ δ.val
      simpa only [valueHom_eq_value] using hm.trans hδ
    exact hdFit q hq y (centeredGammaDisc_anti (q 1) hδd (hTarget ▸ hy))

end DiamondIntegral.Section6
