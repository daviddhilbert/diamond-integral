import IntegrationSection5.GammaCellComparison
import IntegrationSection5.ProductStandardComparison
import IntegrationSection5.CellUnaryPreparations

/-! Original-Gamma certification of the actual RV[2] product comparison.
The quotient graph is obtained by existential composition of the two
constructed contraction graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b c : ℕ}

theorem gamma_product_program_cell_comparison
    (R : Set (VF (M := M) × VF (M := M)))
    (H : DefSet (M := M) S 2 0) (hRH : carrier H = cellPointSet R)
    (hGS : G.real ⊆ S) (hHG : GammaSetDefinable G (carrier H))
    (AD AE : DefSet (M := M) S 1 0) (BD : DefSet (M := M) S 1 b) (BE : DefSet (M := M) S 1 c)
    (d : Map AD BD) (e : Map AE BE)
    (P : ProductContractionProgram (G := G) H AD AE BD BE d e)
    (Q : ProductContractionProgram (G := G) (vfPermutationImage H (Equiv.swap 0 1)) AE AD BE BD e d) :
    Nonempty (GammaCellStandardComparison G R) := by
  let HS := vfPermutationImage H (Equiv.swap 0 1)
  have hId : H = vfPermutationImage H (Equiv.refl _) := (vfPermutationImage_identity H).symm
  let C12 := standardContractionOfProgram H H (Equiv.refl _) hId P.program
  let C21 := standardContractionOfProgram H HS (Equiv.swap 0 1) rfl Q.program
  let s12 := standardProgramSourceMap H H (Equiv.refl _) hId
  let s21 := standardProgramSourceMap H HS (Equiv.swap 0 1) rfl
  have hD (a : H) : Q.eSource (s21 a) = P.dSource (s12 a) := by
    apply unary_zeroRV_ext
    rw [Q.e_spec,P.d_spec]
    rfl
  have hE (a : H) : Q.dSource (s21 a) = P.eSource (s12 a) := by
    apply unary_zeroRV_ext
    rw [Q.d_spec,P.e_spec]
    rfl
  have hker (a b : H) : C12.rawContractionMap a = C12.rawContractionMap b ↔
      C21.rawContractionMap a = C21.rawContractionMap b := by
    rw [standardProgram_kernel H H (Equiv.refl _) hId P.program,
      standardProgram_kernel H HS (Equiv.swap 0 1) rfl Q.program,
      P.kernel_formula,Q.kernel_formula]
    change (SameRV (d (P.dSource (s12 a))).val (d (P.dSource (s12 b))).val ∧
      SameRV (e (P.eSource (s12 a))).val (e (P.eSource (s12 b))).val) ↔ _
    rw [hE a,hE b,hD a,hD b]
    exact and_comm
  have hvol (a : H) : (rvObjectVolume C21.contractionObject (C21.rawContractionMap a)).val =
      (rvObjectVolume C12.contractionObject (C12.rawContractionMap a)).val := by
    rw [standardProgram_volume H HS (Equiv.swap 0 1) rfl Q.program,
      standardProgram_volume H H (Equiv.refl _) hId P.program,
      Q.volume_formula,P.volume_formula]
    change (![rv (vfAt (e (Q.dSource (s21 a))).val 0),rv (vfAt (d (Q.eSource (s21 a))).val 0)] ∘
      (Equiv.swap (0 : Fin 2) 1).symm) =
        ![rv (vfAt (d (P.dSource (s12 a))).val 0),rv (vfAt (e (P.eSource (s12 a))).val 0)] ∘ (Equiv.refl _).symm
    rw [hE a,hD a]
    funext j
    fin_cases j <;> simp
  have h12 := standardProgram_gamma_graph H H (Equiv.refl _) hId P.program hHG P.gamma_program
  have h21 := standardProgram_gamma_graph H HS (Equiv.swap 0 1) rfl Q.program hHG Q.gamma_program
  exact ⟨{
    codes := S
    real_contains := hGS
    source := H
    source_eq := hRH
    source_gamma := hHG
    contraction12 := C12
    contraction21 := C21
    program12_gamma := standardProgram_program_gamma H H (Equiv.refl _) hId P.program P.gamma_program
    program21_gamma := standardProgram_program_gamma H HS (Equiv.swap 0 1) rfl Q.program Q.gamma_program
    comparison := gammaRVIsoOfSurjectiveKernels C12.contractionObject C21.contractionObject
      C12.rawContractionMap C12.rawContractionMap_surjective C21.rawContractionMap C21.rawContractionMap_surjective
      hker hvol (C12.gamma_raw_output h12) (C21.gamma_raw_output h21) }⟩

theorem gamma_rectangle_cell_comparison {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (R : Set (VF (M := M) × VF (M := M))) (hR : GammaSetDefinable G (cellPointSet R))
    (hRect : R = first R ×ˢ second R) : Nonempty (GammaCellStandardComparison G R) := by
  obtain ⟨P⟩ := cell_unary_preparations hs h00 hsmall F R hR
  have hSource : carrier P.source = cellPointSet (first R ×ˢ second R) :=
    P.source_eq.trans (congrArg cellPointSet hRect)
  have hSG : GammaSetDefinable G (carrier P.source) := P.source_eq.symm ▸ hR
  obtain ⟨U⟩ := product_contraction_program (first R) (second R) P.sourceD_eq P.sourceE_eq
    P.specialD P.specialE P.gammaD P.gammaE P.pullbackD P.pullbackE P.source hSource hSG
  obtain ⟨V⟩ := product_contraction_program (second R) (first R) P.sourceE_eq P.sourceD_eq
    P.specialE P.specialD P.gammaE P.gammaD P.pullbackE P.pullbackD
    (vfPermutationImage P.source (Equiv.swap 0 1)) (product_swapped_source _ _ P.source hSource)
    (gamma_vfPermutationImage P.source hSG (Equiv.swap 0 1))
  exact gamma_product_program_cell_comparison R P.source P.source_eq P.real_contains hSG
    P.sourceD P.sourceE P.targetD P.targetE P.specialD.toMap P.specialE.toMap U V

end IntegrationInACVF.Section5
