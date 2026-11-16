import «section 6».RVTemplateCodeImages
import «section 6».ComponentMetadataRVTemplates

/-! Finitely many RV-data families of different arities pack into one
original-base relation. Nonzero unit tags and padding preserve bounds;
the complete packed row recovers every constituent row exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p m L l : ℕ}

def rvDataPack (i : Fin l) (u : Fin m → RVInfinity M) : Fin (L+l) → RVInfinity M :=
  Fin.append (fun j : Fin L => if h : j.val < m then u ⟨j.val,h⟩ else branchTag false)
    (fun j : Fin l => branchTag (decide (j=i)))

def rvDataPackCodes (i : Fin l) (z : Fin p ⊕ Fin m → M) : Fin (L+l) → M :=
  Fin.append (fun j : Fin L => if h : j.val < m then z (.inr ⟨j.val,h⟩) else (branchTag (M := M) false).val)
    (fun j : Fin l => (branchTag (M := M) (decide (j=i))).val)

theorem rvDataPackCodes_definable (i : Fin l) :
    S.DefinableMap LRV (rvDataPackCodes (M := M) (p := p) (m := m) (L := L) i) := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · by_cases hk : k.val < m
    · simpa only [rvDataPackCodes,Fin.append_left,dif_pos hk] using
        (show S.DefinableFun LRV (fun z : Fin p ⊕ Fin m → M => z (.inr ⟨k.val,hk⟩)) from
          Set.DefinableFun.proj LRV)
    · simpa only [rvDataPackCodes,Fin.append_left,dif_neg hk] using
        (branchTag_definable (I := Fin p ⊕ Fin m) S false)
  · simpa only [rvDataPackCodes,Fin.append_right] using
      (branchTag_definable (I := Fin p ⊕ Fin m) S (decide (k=i)))

theorem rvDataPackCodes_at (i : Fin l) (a : Fin p → M) (u : Fin m → RVInfinity M) :
    rvDataPackCodes (L := L) i (Sum.elim a (rvValues u))=rvValues (rvDataPack (L := L) i u) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · by_cases hk : k.val < m
    · simp only [rvDataPackCodes,rvDataPack,rvValues,Fin.append_left,dif_pos hk,Sum.elim_inr]
    · simp only [rvDataPackCodes,rvDataPack,rvValues,Fin.append_left,dif_neg hk]
  · simp only [rvDataPackCodes,rvDataPack,rvValues,Fin.append_right]

theorem rvDataPack_label_injective (h00 : M ⊨ Axioms.ACVF00)
    {m₁ m₂ : ℕ} {i j : Fin l} {u : Fin m₁ → RVInfinity M} {v : Fin m₂ → RVInfinity M}
    (he : rvDataPack (L := L) i u=rvDataPack (L := L) j v) : i=j := by
  by_contra hij
  have h := congrArg (fun w : Fin (L+l) → RVInfinity M => w (Fin.natAdd L i)) he
  have hBad : branchTag (M := M) true=branchTag false := by
    simpa only [rvDataPack,Fin.append_right,decide_true,decide_false,hij] using h
  have hBool := branchTag_injective h00 hBad
  cases hBool

theorem rvDataPack_input (hm : m ≤ L) (i : Fin l) (u : Fin m → RVInfinity M) (j : Fin m) :
    rvDataPack (L := L) i u (Fin.castAdd l (Fin.castLE hm j))=u j := by
  simp only [rvDataPack,Fin.append_left,Fin.coe_castLE,dif_pos j.isLt]

theorem rvDataPack_injective (hm : m ≤ L) (i : Fin l) :
    Function.Injective (rvDataPack (M := M) (m := m) (L := L) i) := by
  intro u v he
  funext j
  have h := congrArg (fun w : Fin (L+l) → RVInfinity M => w (Fin.castAdd l (Fin.castLE hm j))) he
  simpa only [rvDataPack_input hm] using h

def packedRVDataTemplate (T : RVSetParameterTemplate (M := M) S p m) (i : Fin l) (L : ℕ) :
    RVSetParameterTemplate (M := M) S p (L+l) :=
  T.codeImage (rvDataPackCodes (L := L) i) (rvDataPackCodes_definable i)

theorem packedRVDataTemplate_fibre (T : RVSetParameterTemplate (M := M) S p m)
    (i : Fin l) (L : ℕ) (a : Fin p → M) :
    ((packedRVDataTemplate T i L).fibre a).carrier=rvDataPack (L := L) i '' (T.fibre a).carrier :=
  T.codeImage_fibre _ (rvDataPackCodes_definable i) (fun _ u => rvDataPack (L := L) i u)
    (rvDataPackCodes_at i) a

def packedRVDataFamily {m : Fin l → ℕ} (T : ∀ i,RVSetParameterTemplate (M := M) S p (m i)) (L : ℕ) :
    RVSetParameterTemplate (M := M) S p (L+l) :=
  RVSetParameterTemplate.finiteUnion (fun i => packedRVDataTemplate (T i) i L)

theorem mem_packedRVDataFamily_iff (h00 : M ⊨ Axioms.ACVF00)
    {m : Fin l → ℕ} (T : ∀ i,RVSetParameterTemplate (M := M) S p (m i)) (hm : ∀ i,m i ≤ L)
    (a : Fin p → M) (i : Fin l) (u : Fin (m i) → RVInfinity M) :
    rvDataPack (L := L) i u ∈ ((packedRVDataFamily T L).fibre a).carrier ↔ u ∈ ((T i).fibre a).carrier := by
  change rvDataPack (L := L) i u ∈ ((RVSetParameterTemplate.finiteUnion
    (fun j => packedRVDataTemplate (T j) j L)).fibre a).carrier ↔ _
  rw [RVSetParameterTemplate.finiteUnion_fibre]
  simp only [Set.mem_iUnion,packedRVDataTemplate_fibre,Set.mem_image]
  constructor
  · rintro ⟨j,v,hv,he⟩
    have hji := rvDataPack_label_injective h00 he
    subst j
    have hvu := rvDataPack_injective (hm i) i he
    simpa only [hvu] using hv
  · intro hu
    exact ⟨i,u,hu,rfl⟩

theorem constituent_rows_eq_of_packed_eq (h00 : M ⊨ Axioms.ACVF00)
    {m : Fin l → ℕ} (T : ∀ i,RVSetParameterTemplate (M := M) S p (m i)) (hm : ∀ i,m i ≤ L)
    (a b : Fin p → M) (he : ((packedRVDataFamily T L).fibre a).carrier=((packedRVDataFamily T L).fibre b).carrier)
    (i : Fin l) : ((T i).fibre a).carrier=((T i).fibre b).carrier := by
  ext u
  rw [← mem_packedRVDataFamily_iff h00 T hm a i u,← mem_packedRVDataFamily_iff h00 T hm b i u,he]

theorem rvDataPack_image_doublyBounded (i : Fin l) (U : Set (Fin m → RVInfinity M))
    (hU : RVValueDoublyBounded U) : RVValueDoublyBounded (rvDataPack (L := L) i '' U) := by
  obtain ⟨γ,hγ⟩ := hU
  let δ := max γ 1
  have hLowγ : (δ⁻¹).val ≤ (γ⁻¹).val := show δ⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hLow1 : (δ⁻¹).val ≤ (1 : GammaInfinity M) := by
    exact show δ⁻¹ ≤ (1 : Gamma M) from by simpa only [inv_one] using inv_le_inv' (le_max_right γ 1)
  refine ⟨δ,?_⟩
  rintro _ ⟨u,hu,rfl⟩ j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · by_cases hk : k.val < m
    · simpa only [rvDataPack,Fin.append_left,dif_pos hk] using
        (show (δ⁻¹).val ≤ Values.vrv (u ⟨k.val,hk⟩) ∧ Values.vrv (u ⟨k.val,hk⟩) ≤ δ.val from
          ⟨hLowγ.trans (hγ u hu _).1,(hγ u hu _).2.trans (le_max_left γ 1)⟩)
    · simpa only [rvDataPack,Fin.append_left,dif_neg hk,branchTag_value] using
        (show (δ⁻¹).val ≤ (1 : GammaInfinity M) ∧ (1 : GammaInfinity M) ≤ δ.val from ⟨hLow1,le_max_right γ 1⟩)
  · simpa only [rvDataPack,Fin.append_right,branchTag_value] using
      (show (δ⁻¹).val ≤ (1 : GammaInfinity M) ∧ (1 : GammaInfinity M) ≤ δ.val from ⟨hLow1,le_max_right γ 1⟩)

theorem rv_value_doublyBounded_finite_union {I : Type} [Finite I]
    {d : ℕ} (U : I → Set (Fin d → RVInfinity M)) (hU : ∀ i,RVValueDoublyBounded (U i)) :
    RVValueDoublyBounded (⋃ i,U i) := by
  choose γ hγ using hU
  obtain ⟨δ,hδ⟩ := (Set.finite_range γ).bddAbove
  refine ⟨δ,?_⟩
  rintro u hu j
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
  have hγδ : γ i ≤ δ := hδ (Set.mem_range_self i)
  exact ⟨(show (δ⁻¹).val ≤ ((γ i)⁻¹).val from inv_le_inv' hγδ).trans (hγ i u hi j).1,
    (hγ i u hi j).2.trans (show (γ i).val ≤ δ.val from hγδ)⟩

theorem packedRVDataFamily_doublyBounded
    {m : Fin l → ℕ} (T : ∀ i,RVSetParameterTemplate (M := M) S p (m i)) (L : ℕ) (a : Fin p → M)
    (hT : ∀ i,RVValueDoublyBounded ((T i).fibre a).carrier) :
    RVValueDoublyBounded ((packedRVDataFamily T L).fibre a).carrier := by
  change RVValueDoublyBounded ((RVSetParameterTemplate.finiteUnion (fun i => packedRVDataTemplate (T i) i L)).fibre a).carrier
  rw [RVSetParameterTemplate.finiteUnion_fibre]
  apply rv_value_doublyBounded_finite_union
  intro i
  rw [packedRVDataTemplate_fibre]
  exact rvDataPack_image_doublyBounded i _ (hT i)

end DiamondIntegral.Section6
