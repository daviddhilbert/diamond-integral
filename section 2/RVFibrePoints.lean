import «section 2».ScalarBoundary
import «section 2».RVImage
import «section 2».OpenDiscGeometry

/-! Definable points in partially met RV fibres, as used by the approved
boundary induction. An arbitrary RV fibre is not given a section. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvRawFibre (t : RVInfinity M) : Set M := {x | iVF x ∧ iRv x = t.val}

theorem rvRawFibre_definable (B : ParameterBase M) (t : RVInfinity M) :
    GammaParameters.DefinableAtBase (adjoinRV B t) .vf (rvRawFibre t) := by
  let sn : Fin 2 → SortTag := Fin.lastCases .rv (fun _ : Fin 1 => .vf)
  let E : Set (Fin 2 → M) :=
    {z | z ∈ GammaParameters.sortedUniverse sn ∧ iRv (z 0) = z (Fin.last 1)}
  have hE : GammaParameters.DefinableOverBase B sn E :=
    rv_eq_definable B sn 0 (Fin.last 1) (by rfl) (by simp only [sn,Fin.lastCases_last])
  let R : Set ((Fin 1 → M) × M) := {q | Fin.snoc q.1 q.2 ∈ E}
  have hR : GammaParameters.DefinableOverBase B sn
      {z | (Fin.init z,z (Fin.last 1)) ∈ R} := by
    convert hE using 1
    ext z
    change Fin.snoc (Fin.init z) (z (Fin.last 1)) ∈ E ↔ z ∈ E
    rw [Fin.snoc_init_self]
  have h := rv_row_definable B R hR t
  change GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ : Fin 1 => .vf)
    {a | a 0 ∈ rvRawFibre t}
  convert h using 1
  ext a
  have hsort : (Fin.snoc a t.val : Fin 2 → M) ∈ GammaParameters.sortedUniverse sn ↔ iVF (a 0) := by
    constructor
    · intro hs
      have hv := hs (0 : Fin 1).castSucc
      simpa only [sn,Fin.lastCases_castSucc,Fin.snoc_castSucc,sortEval,iVF] using hv
    · intro ha i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [sn,Fin.lastCases_last,Fin.snoc_last,sortEval,iRV] using t.property
      · fin_cases j
        change iVF (a 0)
        exact ha
  change (iVF (a 0) ∧ iRv (a 0) = t.val) ↔
    ((Fin.snoc a t.val : Fin 2 → M) ∈ GammaParameters.sortedUniverse sn ∧
      iRv ((Fin.snoc a t.val : Fin 2 → M) 0) = (Fin.snoc a t.val : Fin 2 → M) (Fin.last 1))
  rw [hsort,Fin.snoc_last]
  rfl

theorem rvRawFibre_isOpenDisc (t : RVInfinity M) (ht : t ≠ rvZero M) : IsOpenDisc (rvRawFibre t) := by
  obtain ⟨a,hat⟩ := rv_surjective t
  have ha : a ≠ 0 := fun h => ht (hat.symm.trans (h ▸ rv_zero))
  obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  have hpoints : {x : VF M | x.val ∈ rvRawFibre t} =
      discPoints (openDiscCode a (finiteValue a ha)) := by
    have h := (Balls.rvFibre_eq_openDisc v hv a ha).trans (openDiscCode_points v hv a a ha).symm
    ext x
    have hh := Set.ext_iff.mp h x
    change (iVF x.val ∧ iRv x.val = t.val) ↔ _
    rw [and_iff_right x.property]
    change iRv x.val = (rv M a).val ↔ _ at hh
    rwa [hat] at hh
  refine ⟨a,finiteValue a ha,?_⟩
  ext x
  constructor
  · intro hx
    exact (Set.ext_iff.mp hpoints (⟨x,hx.1⟩ : VF M)).mp hx
  · intro hx
    exact (Set.ext_iff.mp hpoints (⟨x,disc_underlying_subset_vf _ hx⟩ : VF M)).mpr hx

theorem boundary_rv_fibre_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (A : Set M) (hA : GammaParameters.DefinableAtBase B .vf A)
    (t : RVInfinity M) (ht : t ∈ scalarRVBoundary A) :
    ∃ x ∈ rvRawFibre t, GammaParameters.DefinableClosureAtBase (adjoinRV B t) .vf x := by
  have ht0 : t ≠ rvZero M := fun h => rvZero_not_mem_scalarRVBoundary A (h ▸ ht)
  have hopen := rvRawFibre_isOpenDisc t ht0
  obtain ⟨⟨a,ha,hat⟩,b,hb,hbt⟩ := ht
  have haD : a.val ∈ rvRawFibre t := ⟨a.property,congrArg Subtype.val hat⟩
  have hbD : b.val ∈ rvRawFibre t := ⟨b.property,congrArg Subtype.val hbt⟩
  have hne : (A ∩ rvRawFibre t).Nonempty := ⟨a.val,ha,haD⟩
  have hproper : A ∩ rvRawFibre t ⊂ rvRawFibre t := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,?_⟩
    intro he
    have hm : b.val ∈ A ∩ rvRawFibre t := he.symm ▸ hbD
    exact hb hm.1
  exact lemma_2_21 h00 (adjoinRV B t) A (rvRawFibre t)
    (hA.mono (Set.subset_insert _ _) (Set.Subset.refl _)) (rvRawFibre_definable B t)
    hopen.isBall hne hproper

end DiamondIntegral.Section2
