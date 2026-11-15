import «section 5».OriginalRVTotalEquivalences
import «section 5».RawEquivalenceBijections
import «section 5».OriginalSortedPredicates
import «section 5».GammaJoinedRowGraphs

/-! Totalization of an original bijective family preserves original-base
definability of its full graph and produces an actual native RV bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem rawRowTotal_definable
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) :
    DefinableOverBase B (fun _ => .rv) (rawRowTotal (rawDomain X) D.val) := by
  convert originalRVTotalFamily_raw_definable X D using 1
  ext w
  exact and_comm

theorem originalRawTotalEquiv_joined_definable
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ z ∈ rawDomain X, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z) :
    DefinableOverBase B (fun _ : Fin ((p+b)+(p+a)) => .rv)
      {w | ∃ u : rawRowTotal (rawDomain X) D.val,
        w = join (p+b) (p+a) u.val (originalRawTotalEquiv (rawDomain X) D E H hv u).val} := by
  let I := headIndex (p+b) (p+a)
  let J := tailIndex (p+b) (p+a)
  let st := fun _ : Fin ((p+b)+(p+a)) => SortTag.rv
  have hX : OriginalSortedPredicate B st (fun w => (w ∘ I) ∘ Fin.castAdd a ∈ rawDomain X) := by
    exact (OriginalSortedPredicate.of_definable (rawDomain_definable X)).pullback (t := st)
      (I ∘ Fin.castAdd a) (fun _ => rfl)
  have hH : OriginalSortedPredicate B st
      (fun w => Fin.append (w ∘ I) ((w ∘ J) ∘ Fin.natAdd p) ∈ H.val) := by
    have h := (OriginalSortedPredicate.of_definable H.property).pullback (t := st)
      (Fin.append I (J ∘ Fin.natAdd p)) (by
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
            simp only [Fin.append_left,Fin.append_right,st]
        · simp only [Fin.append_right,st])
    convert h using 1
    funext w
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_def,Fin.append_left,Fin.append_right]
  have hEq : OriginalSortedPredicate B st
      (fun w => (w ∘ J) ∘ Fin.castAdd b = (w ∘ I) ∘ Fin.castAdd a) := by
    have hi (j : Fin p) : OriginalSortedPredicate B st
        (fun w => w (J (Fin.castAdd b j)) = w (I (Fin.castAdd a j))) := by
      exact parameter_free_formula_original_definable hc B st
        ((Term.var (J (Fin.castAdd b j))).equal (Term.var (I (Fin.castAdd a j))))
    exact (OriginalSortedPredicate.finite_all hi).congr (fun w _ =>
      ⟨fun h => funext h,fun h j => congrFun h j⟩)
  have h := hX.conj (hEq.conj hH)
  unfold OriginalSortedPredicate at h
  convert h using 1
  ext w
  have hg : (∃ u : rawRowTotal (rawDomain X) D.val,
      w = join (p+b) (p+a) u.val (originalRawTotalEquiv (rawDomain X) D E H hv u).val) ↔
      (w ∘ I) ∘ Fin.castAdd a ∈ rawDomain X ∧
      (w ∘ J) ∘ Fin.castAdd b = (w ∘ I) ∘ Fin.castAdd a ∧
      Fin.append (w ∘ I) ((w ∘ J) ∘ Fin.natAdd p) ∈ H.val := by
    rw [← originalRawTotalEquiv_graph (rawDomain X) D E H hv (w ∘ I) (w ∘ J)]
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨u,(funext (join_head _ _ _ _)).symm,(funext (join_tail _ _ _ _)).symm⟩
    · rintro ⟨u,hu,hv'⟩
      refine ⟨u,?_⟩
      calc
        w = join (p+b) (p+a) (w ∘ I) (w ∘ J) := (join_reconstruct _ _ w).symm
        _ = _ := by rw [← hu,← hv']
  change _ ↔ (w ∈ sortedUniverse st ∧ _)
  constructor
  · intro hw
    refine ⟨?_,hg.mp hw⟩
    obtain ⟨u,rfl⟩ := hw
    change ∀ j, iRV (join (p+b) (p+a) u.val
      (originalRawTotalEquiv (rawDomain X) D E H hv u).val j)
    exact forall_join_property iRV (p+b) (p+a) _ _
      (fun j => (allRVGammaDomain_definable D).proper _ u.property.2 j)
      (fun j => (allRVGammaDomain_definable E).proper _
        (originalRawTotalEquiv (rawDomain X) D E H hv u).property.2 j)
  · exact fun hw => hg.mpr hw.2

def originalRVTotalBijection
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ x : X, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val (rvValues x.val)) :
    GammaGroundBijection (originalRVTotalFamily X D) (originalRVTotalFamily X E) := by
  have hraw : ∀ z ∈ rawDomain X, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z := by
    rintro z ⟨x,hx,rfl⟩
    exact hv ⟨x,hx⟩
  let e := rawEquivalenceBijection (hc := hc) (rawRowTotal (rawDomain X) D.val)
    (rawRowTotal (rawDomain X) E.val) (rawRowTotal_definable X D) (rawRowTotal_definable X E)
    (originalRawTotalEquiv (rawDomain X) D E H hraw)
    (originalRawTotalEquiv_joined_definable X D E H hraw)
  have hA : (originalRVTotalFamily X D).carrier =
      (ofRaw (hc := hc) (rawRowTotal (rawDomain X) D.val) (rawRowTotal_definable X D)).carrier := by
    ext u
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_comm
  have hC : (originalRVTotalFamily X E).carrier =
      (ofRaw (hc := hc) (rawRowTotal (rawDomain X) E.val) (rawRowTotal_definable X E)).carrier := by
    ext u
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_comm
  exact (gammaGroundBijectionOfCarrierEq _ _ hC.symm).comp
    (e.comp (gammaGroundBijectionOfCarrierEq _ _ hA))

end DiamondIntegral.Section5
