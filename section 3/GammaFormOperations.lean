import «section 3».GammaVolumeForms
import Section4.CodeMaps
import Section3.RVOperations

/-! Multiplication and the constant unit for genuine Gamma volume forms.
Their entire graphs are definable: code multiplication is the actual RV
multiplication, and no representative is selected as a new parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def gammaMultiplyMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Map (DefSet.univ ((volumeGammaSpace hc).prod (volumeGammaSpace hc)) S)
      (DefSet.univ (volumeGammaSpace hc) S) := by
  let F (z : Fin 1 ⊕ Fin 1 → M) : Fin 1 → M :=
    fun _ => iRVMul (z (.inl 0)) (z (.inr 0))
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
        (show S.DefinableMap LRV (fun z : Fin 1 ⊕ Fin 1 → M => ![z (.inl 0), z (.inr 0)]) from
          fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hdom (c : ((volumeGammaSpace hc).prod (volumeGammaSpace hc)).domain) :
      F c.val ∈ (volumeGammaSpace hc).domain := by
    let x : CanonicalRV.RVSort M := ⟨c.val (.inl (0 : Fin 1)), c.property.1.1⟩
    let y : CanonicalRV.RVSort M := ⟨c.val (.inr (0 : Fin 1)), c.property.2.1⟩
    have hx : x ≠ 0 := fun he => c.property.1.2 ((congrArg Subtype.val he).trans RVOperations.zero_val)
    have hy : y ≠ 0 := fun he => c.property.2.2 ((congrArg Subtype.val he).trans RVOperations.zero_val)
    refine ⟨rv_mul_mem hM x.property y.property, ?_⟩
    intro he
    apply mul_ne_zero hx hy
    apply Subtype.ext
    exact (RVOperations.mul_val x y).trans (he.trans RVOperations.zero_val.symm)
  refine Map.ofCodes _ (fun p : Values.Gamma (M := M) × Values.Gamma (M := M) => p.1 * p.2)
    F hF hdom ?_
  intro c
  apply Subtype.ext
  exact Values.vrv_mul (M := M)
    ⟨c.val (.inl (0 : Fin 1)), c.property.1.1⟩
    ⟨c.val (.inr (0 : Fin 1)), c.property.2.1⟩

def gammaOneForm (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Space LRV M} (A : DefSet P S) : GammaVolumeForm hc A := by
  let F (_ : P.Index → M) : Fin 1 → M := fun _ => iRVOne
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvOne)).comp
        (show S.DefinableMap LRV (fun _ : P.Index → M => Fin.elim0) from fun i => i.elim0)
  have hdom (c : P.domain) : F c.val ∈ (volumeGammaSpace hc).domain := by
    refine ⟨rv_one_mem hM, ?_⟩
    intro he
    have hz : (1 : CanonicalRV.RVSort M) = 0 :=
      Subtype.ext (RVOperations.one_val.trans (he.trans RVOperations.zero_val.symm))
    exact one_ne_zero hz
  refine Map.ofCodes A (fun _ => (1 : Values.Gamma (M := M))) F hF hdom ?_
  intro c
  apply Subtype.ext
  have he : (⟨iRVOne, rv_one_mem hM⟩ : CanonicalRV.RVSort M) = 1 :=
    Subtype.ext RVOperations.one_val.symm
  change Values.vrv ⟨iRVOne, rv_one_mem hM⟩ = (1 : Values.Gamma (M := M)).val
  rw [he, RVOperations.vrv_one, Values.gamma_val_one]

@[simp] theorem gammaOneForm_value (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Space LRV M} (A : DefSet P S) (a : A) : gammaFormValue (gammaOneForm hc A) a = 1 := rfl

def GammaVolumeForm.mul {hc : CanonicalStructure.IsCanonical (M := M)}
    {P : Space LRV M} {A : DefSet P S} (ω σ : GammaVolumeForm hc A) : GammaVolumeForm hc A :=
  (gammaMultiplyMap hc S).comp (ω.pair σ).toUniv

@[simp] theorem GammaVolumeForm.mul_value {hc : CanonicalStructure.IsCanonical (M := M)}
    {P : Space LRV M} {A : DefSet P S} (ω σ : GammaVolumeForm hc A) (a : A) :
    gammaFormValue (ω.mul σ) a = gammaFormValue ω a * gammaFormValue σ a := rfl

end DiamondIntegral.Section3
