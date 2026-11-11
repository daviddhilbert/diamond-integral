import «section 2».CoordinateBoundaryPoints

/-! The uniform family of unary boundary tags. Every membership condition
uses the original ground base, including all sort and zero-tag guards. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem sorted_init_last_iff {n : ℕ} (sn : Fin n → SortTag) (σ : SortTag) (z : Fin (n+1) → M) :
    z ∈ GammaParameters.sortedUniverse (Fin.lastCases σ sn) ↔
      Fin.init z ∈ GammaParameters.sortedUniverse sn ∧ sortEval σ (z (Fin.last n)) := by
  constructor
  · intro h
    refine ⟨fun j => ?_,?_⟩
    · simpa only [Fin.lastCases_castSucc,Fin.init] using h j.castSucc
    · simpa only [Fin.lastCases_last] using h (Fin.last n)
  · rintro ⟨hi,hl⟩ j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simpa only [Fin.lastCases_last] using hl
    · simpa only [Fin.lastCases_castSucc,Fin.init] using hi q

def boundaryParameterSort (n : ℕ) : Fin (n+1) → SortTag := Fin.lastCases .rv (fun _ : Fin n => .vf)

def boundaryFibreRelation (n : ℕ) : Set ((Fin (n+1) → M) × M) :=
  {q | q.1 ∈ GammaParameters.sortedUniverse (boundaryParameterSort n) ∧
    iVF q.2 ∧ iRv q.2 = q.1 (Fin.last n)}

def coordinateBoundaryPairs {n : ℕ} (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) :
    Set (Fin (n+1) → M) :=
  {p | p ∈ GammaParameters.sortedUniverse (boundaryParameterSort n) ∧
    (∃ x, iVF x ∧ iRv x = p (Fin.last n) ∧ Fin.insertNth i x (Fin.init p) ∈ A) ∧
    ∃ y, iVF y ∧ iRv y = p (Fin.last n) ∧ Fin.insertNth i y (Fin.init p) ∉ A}

theorem boundaryFibreRelation_definable (B : ParameterBase M) (n : ℕ) :
    GammaParameters.DefinableOverBase B (Fin.lastCases .vf (boundaryParameterSort n))
      {z | (Fin.init z,z (Fin.last (n+1))) ∈ boundaryFibreRelation (M := M) n} := by
  let sm : Fin (n+2) → SortTag := Fin.lastCases SortTag.vf (boundaryParameterSort n)
  have h := rv_eq_definable B sm (Fin.last (n+1)) (Fin.last n).castSucc
    (by simp only [sm,Fin.lastCases_last])
    (by simp only [sm,Fin.lastCases_castSucc,boundaryParameterSort,Fin.lastCases_last])
  convert h using 1
  ext z
  change (Fin.init z ∈ GammaParameters.sortedUniverse (boundaryParameterSort n) ∧
    iVF (z (Fin.last (n+1))) ∧ iRv (z (Fin.last (n+1))) = z (Fin.last n).castSucc) ↔
    (z ∈ GammaParameters.sortedUniverse (Fin.lastCases .vf (boundaryParameterSort n)) ∧
      iRv (z (Fin.last (n+1))) = z (Fin.last n).castSucc)
  rw [sorted_init_last_iff]
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

theorem coordinateBoundaryPairs_definable (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin (n+1) → M)) (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (i : Fin (n+1)) :
    GammaParameters.DefinableOverBase B (boundaryParameterSort n) (coordinateBoundaryPairs A i) := by
  let sm : Fin (n+2) → SortTag := Fin.lastCases SortTag.vf (boundaryParameterSort n)
  let idx : Fin (n+1) → Fin (n+2) :=
    Fin.insertNth i (Fin.last (n+1)) (fun j => j.castSucc.castSucc)
  have hmap (w : Fin (n+2) → M) : w ∘ idx =
      Fin.insertNth i (w (Fin.last (n+1))) (Fin.init (Fin.init w)) := by
    funext j
    refine i.succAboveCases ?_ (fun q => ?_) j
    · simp only [Function.comp_apply,idx,Fin.insertNth_apply_same]
    · simp only [Function.comp_apply,idx,Fin.insertNth_apply_succAbove,Fin.init]
  have hpre := hA.preimage_real sm idx
  have hR := boundaryFibreRelation_definable B n
  have hin := (hpre.inter hR).image_real Fin.castSucc
  have hout := (hpre.compl.inter hR).image_real Fin.castSucc
  have hsn : sm ∘ Fin.castSucc = boundaryParameterSort n := by
    funext j
    simp only [sm,Function.comp_apply,Fin.lastCases_castSucc]
  rw [hsn] at hin hout
  convert hin.inter hout using 1
  ext p
  constructor
  · rintro ⟨hp,⟨x,hxVF,hxrv,hxA⟩,y,hyVF,hyrv,hyA⟩
    let wx : Fin (n+2) → M := Fin.snoc p x
    let wy : Fin (n+2) → M := Fin.snoc p y
    have hxsort : wx ∈ GammaParameters.sortedUniverse sm := by
      apply (sorted_init_last_iff _ _ wx).mpr
      simpa only [wx,Fin.init_snoc,Fin.snoc_last,sortEval,iVF] using And.intro hp hxVF
    have hysort : wy ∈ GammaParameters.sortedUniverse sm := by
      apply (sorted_init_last_iff _ _ wy).mpr
      simpa only [wy,Fin.init_snoc,Fin.snoc_last,sortEval,iVF] using And.intro hp hyVF
    have hxP : wx ∘ idx ∈ A := by
      rw [hmap]
      simpa only [wx,Fin.init_snoc,Fin.snoc_last] using hxA
    have hyP : wy ∘ idx ∉ A := by
      rw [hmap]
      simpa only [wy,Fin.init_snoc,Fin.snoc_last] using hyA
    have hxR : (Fin.init wx,wx (Fin.last (n+1))) ∈ boundaryFibreRelation n := by
      simpa only [boundaryFibreRelation,Set.mem_ofPred_eq,wx,Fin.init_snoc,Fin.snoc_last] using And.intro hp (And.intro hxVF hxrv)
    have hyR : (Fin.init wy,wy (Fin.last (n+1))) ∈ boundaryFibreRelation n := by
      simpa only [boundaryFibreRelation,Set.mem_ofPred_eq,wy,Fin.init_snoc,Fin.snoc_last] using And.intro hp (And.intro hyVF hyrv)
    refine ⟨⟨wx,⟨⟨hxP,hxsort⟩,hxR⟩,?_⟩,⟨wy,⟨⟨hysort,fun h => hyP h.1⟩,hyR⟩,?_⟩⟩
    · funext j
      simp only [wx,Function.comp_apply,Fin.snoc_castSucc]
    · funext j
      simp only [wy,Function.comp_apply,Fin.snoc_castSucc]
  · rintro ⟨⟨wx,⟨⟨hxA,hxsort⟩,hxR⟩,hxp⟩,⟨wy,⟨hyN,hyR⟩,hyp⟩⟩
    change Fin.init wx = p at hxp
    change Fin.init wy = p at hyp
    have hpsort : p ∈ GammaParameters.sortedUniverse (boundaryParameterSort n) := hxp ▸ hxR.1
    have hxrv : iRv (wx (Fin.last (n+1))) = p (Fin.last n) := by
      have h := hxR.2.2
      rwa [hxp] at h
    have hyrv : iRv (wy (Fin.last (n+1))) = p (Fin.last n) := by
      have h := hyR.2.2
      rwa [hyp] at h
    have hxA' : Fin.insertNth i (wx (Fin.last (n+1))) (Fin.init p) ∈ A := by
      rw [hmap,hxp] at hxA
      exact hxA
    have hyA' : Fin.insertNth i (wy (Fin.last (n+1))) (Fin.init p) ∉ A := by
      intro h
      apply hyN.2
      refine ⟨?_,hyN.1⟩
      rwa [hmap,hyp]
    exact ⟨hpsort,⟨wx (Fin.last (n+1)),hxR.2.1,hxrv,hxA'⟩,
      wy (Fin.last (n+1)),hyR.2.1,hyrv,hyA'⟩

end DiamondIntegral.Section2
