import IntegrationSection5.FiniteRVComparison

/-! The completed [18] cell producer retains its existing proof that the new RV labels determine every old RV coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section4
namespace DiamondIntegral.Section5
open IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}

theorem exists_coherent_positioned_cell_label_injection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    ∃ T : PositionedCellLabelInjection G A,
      ∀ a b, (T.iso.equiv a).val.2 = (T.iso.equiv b).val.2 → a.val.2 = b.val.2 := by
  let E := gammaPermutationIso A hA (Equiv.swap 0 1)
  have hB := E.target_definable (gammaLogicInput G)
  obtain ⟨V⟩ := MixedVerticalPresentation.exists_presentation hs h00 G hsmall hGenerated _ hB
  let Af := GammaScalarFamilies.family V.domain
  let f := GammaScalarFamilies.value V.position
  have hf := GammaScalarFamilies.graph_definable G V.domain V.position V.position_graph
  obtain ⟨d,Q,hQ,hRows⟩ := ScalarPositionDecomposition.exists_map hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 Af (GammaScalarFamilies.domain_vf V.domain) f (GammaScalarFamilies.value_vf V.position)
    hf V.paradigm_index
  let P := V.pullback Q
  let QA := P.precomp E.equiv E.graph
  have hQL : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2 :=
    fun a b he => ((sameRV_iff _ _).mp (hQ a b he)).2
  have hP : ∀ a b, P.toFun a = P.toFun b → SameRV a.val b.val :=
    fun a b he => V.inverse_rv a b (hQ _ _ he)
  have hAL : ∀ a b, QA.toFun a = QA.toFun b → a.val.2 = b.val.2 :=
    fun a b he => ((sameRV_iff _ _).mp (hP (E.equiv a) (E.equiv b) he)).2
  let D := rvRecodeTarget Q
  let g : D → VF (M := M) := rvKeyedFunction Q hQL V.scalarPosition
  have hg := rvKeyedFunction_graph Q hQL V.scalarPosition V.scalarPosition_graph
  have hCells (a₀ : A) :
      ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
        Cells.DefinableCellData (RVLabelSlices.labelBase G (QA.toFun a₀))
          (nativeTwoFibre (rvRecodeTarget QA) (QA.toFun a₀)) f t ∧
        ∀ x ∈ Cells.first (nativeTwoFibre (rvRecodeTarget QA) (QA.toFun a₀)), ∃ u : D,
          u.val = (fun _ : Fin 1 => x,QA.toFun a₀) ∧ g u = f x := by
    let b₀ := E.equiv a₀
    let u₀ := V.scalarProjection b₀
    obtain ⟨row⟩ := hRows u₀
    have hNative := recoded_native_fibre hA P a₀
    have hRow := V.pullback_fibre Q b₀ row
    have hPoly := mixedPairFibre_polydisc P hP b₀
    rw [hRow] at hPoly
    have hCell := row.cell hPoly
    rw [← hRow] at hCell
    have hDef := DefinableParadigms.cellData (RVLabelSlices.labelBase G (P.toFun b₀))
      _ row.position _ hCell (mixedPairFibre_nonempty P b₀)
      (MixedFibreDefinability.pairFibre_definable P b₀) (V.position_definable Q b₀ row)
    have hNative' : nativeTwoFibre (rvRecodeTarget QA) (QA.toFun a₀) = mixedPairFibre P b₀ := hNative
    have hDef' : Cells.DefinableCellData (RVLabelSlices.labelBase G (QA.toFun a₀))
        (nativeTwoFibre (rvRecodeTarget QA) (QA.toFun a₀)) row.position (u₀.val.2 V.paradigm_index) := by
      rw [hNative']
      exact hDef
    refine ⟨row.position,u₀.val.2 V.paradigm_index,hDef',?_⟩
    intro x hx
    have hxD : x ∈ row.domain := by
      rw [hNative',hRow,CellsFromFibres.first_eq] at hx
      exact hx
    let z : Point (M := M) 1 V.arity := unaryPoint x u₀.val.2
    obtain ⟨u,hu,hQu⟩ := (Set.ext_iff.mp row.fibre z).mpr ⟨hxD,rfl⟩
    let v := (rvRecodeIso Q hQL).equiv u
    have hVF : vfAt u.val 0 = x := congrArg (fun z : Point (M := M) 1 V.arity => vfAt z 0) hu
    have hLabels : u.val.2 = u₀.val.2 := by
      have hh := congrArg (fun z : Point (M := M) 1 V.arity => z.2) hu
      exact hh
    have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels u₀.val :=
      congrArg (fun v : Fin V.arity → RV (M := M) => fun i => (v i).val) hLabels
    have hPos := V.scalarPosition_value u
    rw [hContext,hVF] at hPos
    have hPos' : V.scalarPosition u = row.position x := Subtype.ext (hPos.trans (row.value x hxD).symm)
    refine ⟨v,Prod.ext ?_ hQu,?_⟩
    · funext j
      fin_cases j
      exact hVF
    · exact (rvKeyedFunction_apply Q hQL V.scalarPosition u).trans hPos'
  refine ⟨⟨d,rvRecodeTarget QA,rvRecodeIso QA hAL,fun _ => rfl,D,g,hg,?_⟩,?_⟩
  · intro s hs
    obtain ⟨p,a,ha⟩ := hs
    have hCode : QA.toFun a = s := congrArg Prod.snd ha
    have h := hCells a
    rwa [hCode] at h
  · intro a b he
    exact hAL a b he

end DiamondIntegral.Section5
