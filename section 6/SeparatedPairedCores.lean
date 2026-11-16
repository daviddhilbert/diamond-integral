import «section 6».CanonicalDiscCores

/-! Canonical disjoint paired cores beyond a prescribed named threshold.
The complete finite candidate graph is retained over S; intersections
choose one actual open disc per center without naming a candidate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

structure SeparatedPairedCoreData (A B : Set (VF M)) (f : VF M → VF M)
    (C : Set (Fin 2 → VF M)) (m : VF M) where
  radii : (Fin 2 → VF M) → Set (Fin 2 → VF M)
  graph : S.Definable LRV (vfCorrespondenceGraph C radii)
  finite : (⋃ q ∈ C, radii q).Finite
  nonempty : ∀ q ∈ C, (radii q).Nonempty
  centered : ∀ q ∈ C, ∃ γ δ : Gamma M, vfValue m ≤ γ.val ∧ vfValue m ≤ δ.val ∧
    candidateDiscCore radii q 0 = centeredGammaDisc (q 0) γ ∧
    candidateDiscCore radii q 1 = centeredGammaDisc (q 1) δ
  source_subset : ∀ q ∈ C, candidateDiscCore radii q 0 ⊆ A
  target_subset : ∀ q ∈ C, candidateDiscCore radii q 1 ⊆ B
  image : ∀ q ∈ C, f '' candidateDiscCore radii q 0 = candidateDiscCore radii q 1
  separated : ∀ q ∈ C, ∀ p ∈ C, q ≠ p → ∀ i : Fin 2,
    Disjoint (candidateDiscCore radii q i) (candidateDiscCore radii p i)

theorem SeparatedPairedCoreData.core_graph_definable
    {A B : Set (VF M)} {f : VF M → VF M} {C : Set (Fin 2 → VF M)} {m : VF M}
    (D : SeparatedPairedCoreData (S := S) A B f C m)
    (hC : S.Definable LRV (vfValues '' C)) (i : Fin 2) :
    S.Definable LRV (candidateDiscCoreGraph C D.radii i) :=
  candidateDiscCoreGraph_definable C hC D.radii D.graph i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_separated_paired_cores
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
    (m : VF M) (hm0 : m ≠ 0) (hmPos : (1 : GammaInfinity M) ≤ vfValue m)
    (hmDef : S.Definable₁ LRV {m.val}) :
    Nonempty (SeparatedPairedCoreData (S := S) A B f C m) := by
  let E : Set (VF M) := ⋃ q ∈ C, Set.range q
  have hEFin : E.Finite := hCFin.biUnion (fun q _ => Set.finite_range q)
  have hEDef : S.Definable₁ LRV (Subtype.val '' E) := finite_tuple_values_definable C hC
  have hMem (q) (hq : q ∈ C) (i : Fin 2) : q i ∈ E := by
    simp only [E,Set.mem_iUnion]
    exact ⟨q,hq,i,rfl⟩
  obtain ⟨s,hs0,hsDef,hsPos,hSeparate⟩ := exists_named_separating_radius h00 hc hv V hV hVS hSV hnt E hEDef hEFin
  obtain ⟨c,hc0,hcDef,hcPos,hLarger⟩ := exists_common_named_coefficient (![s,m] : Fin 2 → VF M)
    (by intro i; fin_cases i; exact hs0; exact hm0)
    (by intro i; fin_cases i; exact hsPos.le; exact hmPos)
    (by intro i; fin_cases i; exact hsDef; exact hmDef)
  obtain ⟨F,hF,hFin,hNe,hData⟩ := exists_finite_paired_discs_beyond_named_thresholds h00 hc hκ hs hv V hsmall
    hV hVS hSV hnt A B hA f hbij hGraph hCont hBound C hC hCFin hCenters c c hc0 hc0 hcDef hcDef
  have hFq (q) (hq : q ∈ C) : (F q).Finite := hFin.subset (by
    intro r hr
    simp only [Set.mem_iUnion]
    exact ⟨q,hq,hr⟩)
  have hPair (q) (hq : q ∈ C) (r) (hr : r ∈ F q) :
      ∃ hr0 : r 0 ≠ 0, ∃ hr1 : r 1 ≠ 0,
        f '' centeredGammaDisc (q 0) (finiteValue (r 0) hr0) = centeredGammaDisc (q 1) (finiteValue (r 1) hr1) := by
    obtain ⟨hr0,hr1,hL,hR,hSource,hImage⟩ := hData q hq r hr
    exact ⟨hr0,hr1,hImage⟩
  have hCore (q) (hq : q ∈ C) := candidateDiscCores_paired F q (hFq q hq) ((hNe q).mpr hq) f (hPair q hq)
  have hSmall (q) (hq : q ∈ C) (i : Fin 2) :
      candidateDiscCore F q i ⊆ centeredGammaDisc (q i) (finiteValue s hs0) := by
    obtain ⟨r,hr⟩ := (hNe q).mpr hq
    obtain ⟨hr0,hr1,hL,hR,hSource,hImage⟩ := hData q hq r hr
    have hNZ (j : Fin 2) : r j ≠ 0 := by fin_cases j; exact hr0; exact hr1
    have hVal (j : Fin 2) : vfValue c ≤ vfValue (r j) := by fin_cases j; exact hL; exact hR
    have hGamma : finiteValue s hs0 ≤ finiteValue (r i) (hNZ i) := by
      change Values.vfValueHom s ≤ Values.vfValueHom (r i)
      simpa only [Matrix.cons_val_zero,valueHom_eq_value] using (hLarger 0).trans (hVal i)
    intro x hx
    exact centeredGammaDisc_anti (q i) hGamma
      ((rawOpenBall_iff_centeredGammaDisc _ _ _ (hNZ i)).mp (hx r hr))
  have hDistinct (q) (hq : q ∈ C) (p) (hp : p ∈ C) (hne : q ≠ p) (i : Fin 2) : q i ≠ p i := by
    have hFirst : q 0 ≠ p 0 := by
      intro he
      apply hne
      funext j
      fin_cases j
      · exact he
      · exact (hCenters q hq).2.symm.trans ((congrArg f he).trans (hCenters p hp).2)
    fin_cases i
    · exact hFirst
    · intro he
      apply hFirst
      exact hbij.injOn (hCenters q hq).1 (hCenters p hp).1
        ((hCenters q hq).2.trans (he.trans (hCenters p hp).2.symm))
  refine ⟨{
    radii := F
    graph := hF
    finite := hFin
    nonempty := fun q hq => (hNe q).mpr hq
    centered := ?_
    source_subset := ?_
    target_subset := ?_
    image := ?_
    separated := fun q hq p hp hn i =>
      (hSeparate (q i) (hMem q hq i) (p i) (hMem p hp i) (hDistinct q hq p hp hn i)).mono (hSmall q hq i) (hSmall p hp i)
  }⟩
  · intro q hq
    obtain ⟨r,hr,hr0,hr1,hSource,hTarget,hImage⟩ := hCore q hq
    obtain ⟨h0,h1,hL,hR,hA,hI⟩ := hData q hq r hr
    refine ⟨finiteValue (r 0) hr0,finiteValue (r 1) hr1,?_,?_,hSource,hTarget⟩
    · simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,finiteValue,valueHom_eq_value] using (hLarger 1).trans hL
    · simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,finiteValue,valueHom_eq_value] using (hLarger 1).trans hR
  · intro q hq x hx
    obtain ⟨r,hr⟩ := (hNe q).mpr hq
    obtain ⟨hr0,hr1,hL,hR,hSource,hImage⟩ := hData q hq r hr
    exact hSource ((rawOpenBall_iff_centeredGammaDisc _ _ _ hr0).mp (hx r hr))
  · intro q hq y hy
    obtain ⟨r,hr,hr0,hr1,hSource,hTarget,hImage⟩ := hCore q hq
    have hImageCore := hImage
    obtain ⟨x,hx,rfl⟩ := hImageCore.symm ▸ hy
    obtain ⟨t,ht⟩ := (hNe q).mpr hq
    obtain ⟨ht0,ht1,hL,hR,hA,hI⟩ := hData q hq t ht
    exact hbij.mapsTo (hA ((rawOpenBall_iff_centeredGammaDisc _ _ _ ht0).mp (hx t ht)))
  · intro q hq
    obtain ⟨r,hr,hr0,hr1,hSource,hTarget,hImage⟩ := hCore q hq
    exact hImage

end DiamondIntegral.Section6
