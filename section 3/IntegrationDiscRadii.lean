import «section 3».IntegrationDiscBases
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Auxiliary VF radius presentations and their complete Gamma-code rows. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {k n : ℕ}

def integrationDiscRadiiMap (z : (Fin k ⊕ Fin k) ⊕ Fin n → M) : Fin k ⊕ Fin (k+n) → M :=
  Sum.elim (fun i => @iRv M (CanonicalStructure.normalize (M := M)) (z (.inl (.inr i))))
    (Fin.addCases (fun i => z (.inl (.inl i))) (fun i => z (.inr i)))

theorem integrationDiscRadiiMap_definable (S : Set M) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      ((Fin k ⊕ Fin k) ⊕ Fin n) (Fin k ⊕ Fin (k+n)) S
      (integrationDiscRadiiMap (M := M)) := by
  let F := integrationDiscRadiiMap (M := M) (k := k) (n := n)
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  intro j
  cases j with
  | inl i =>
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
      Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (L := LRV) Fn.rvMap)
    exact hf.comp
      (g := fun z : (Fin k ⊕ Fin k) ⊕ Fin n → M => ![z (.inl (.inr i))])
      (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  | inr i =>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [integrationDiscRadiiMap,Sum.elim_inr,Fin.addCases_left]
      exact Set.DefinableFun.proj LRV
    · simp only [integrationDiscRadiiMap,Sum.elim_inr,Fin.addCases_right]
      exact Set.DefinableFun.proj LRV

def integrationDiscPoint (a r : Fin k → Section2.VF M) (b : Fin n → M) :
    (Fin k ⊕ Fin k) ⊕ Fin n → M :=
  Sum.elim (Sum.elim (fun i => (a i).val) (fun i => (r i).val)) b

def integrationRadiiCodes (r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) :
    Fin k → GammaParameters.Code (M := M) :=
  fun i => ⟨Section2.rv M (r i),fun he => hr i ((CanonicalRV.encodedRv_zero_iff (r i)).mp he)⟩

theorem integrationRadiiCodes_values (r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) :
    GammaParameters.values (integrationRadiiCodes r hr) = (fun i => Section2.finiteValue (r i) (hr i)) := by
  funext i
  apply Subtype.ext
  rfl

theorem integrationDiscRadiiMap_row (a r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) (b : Fin n → M) :
    integrationDiscRadiiMap (integrationDiscPoint a r b) =
      Sum.elim (GammaParameters.rawTuple (integrationRadiiCodes r hr))
        (Fin.append (SpecialTransformations.Section4.vfValues a) b) := by
  funext j
  cases j with
  | inl i =>
    change @iRv M (CanonicalStructure.normalize (M := M)) (r i).val = @iRv M sM (r i).val
    exact @CanonicalStructure.normalize_fun M sM 1 Fn.rvMap
      ![(r i).val] (by intro j; fin_cases j; exact (r i).property)
  | inr i =>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [integrationDiscRadiiMap,integrationDiscPoint,Sum.elim_inr,Sum.elim_inl,
        Fin.addCases_left,Fin.append_left,SpecialTransformations.Section4.vfValues]
    · simp only [integrationDiscRadiiMap,integrationDiscPoint,Sum.elim_inr,Sum.elim_inl,
        Fin.addCases_right,Fin.append_right]

theorem integrationDiscTail_row (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) (b : Fin n → M) :
    integrationDiscRadiiMap (integrationDiscPoint a r b) ∈
      integrationGammaTailRelation R.relation (fun i => Sum.inr (R.support i)) ↔
    b ∈ R.fibre a (fun i => Section2.finiteValue (r i) (hr i)) := by
  rw [integrationDiscRadiiMap_row]
  rw [integrationGammaTail_row,integrationRadiiCodes_values]
  rfl
end DiamondIntegral.Section3
