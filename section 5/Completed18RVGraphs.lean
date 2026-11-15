import «section 5».Completed18NativeRVObjects
import IntegrationSection6.FiniteRVMorphisms
import IntegrationSection6.GammaRVSetRealization

/-! Full original-Gamma graph conversions for the actual RV domains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
open FiniteTupleBlocks Section3RVCodeBridge
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b k : ℕ}
variable {D : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}
  {E : GammaGroundDefSet hc B (rawRVSpace (M := M) b)}
local notation "N" => (@CanonicalStructure.normalize M sM)

def groundRVMapRawGraph (f : D → E) : Set (Fin (a+b) → M) :=
  {w | ∃ u : D,Fin.append (rvValues u.val) (rvValues (f u).val) = w}

theorem groundRVMapRawGraph_definable (f : GammaGroundMap D E) :
    DefinableOverBase B (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv))
      (groundRVMapRawGraph f) := by
  let π : Fin (b+a) → Fin (a+b) := join b a (Fin.castAdd b) (Fin.natAdd a)
  have hπ (x : Fin a → M) (y : Fin b → M) : Fin.append x y ∘ π = join b a x y := by
    rw [comp_join]
    simp only [Function.comp_def,Fin.append_left,Fin.append_right]
  have h := (joinedGraph_definable f).preimage_real
    (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)) π
  convert h using 1
  ext w
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨⟨u,hπ _ _⟩,?_⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,sortEval,iRV,rvValues] using (u.val i).property
    · simpa only [Fin.append_right,sortEval,iRV,rvValues] using ((f u).val i).property
  · rintro ⟨⟨u,hu⟩,_⟩
    refine ⟨u,?_⟩
    have hx (i : Fin a) : w (Fin.castAdd b i) = rvValues u.val i := by
      have hh := congrFun hu (headIndex b a i)
      simpa only [Function.comp_apply,π,join_head] using hh
    have hy (i : Fin b) : w (Fin.natAdd a i) = rvValues (f u).val i := by
      have hh := congrFun hu (tailIndex b a i)
      simpa only [Function.comp_apply,π,join_tail] using hh
    funext j
    exact Fin.addCases (fun i => (Fin.append_left _ _ i).trans (hx i).symm)
      (fun i => (Fin.append_right _ _ i).trans (hy i).symm) j

theorem groundRV_gamma_map (f : GammaGroundMap D E) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ u : D,u.val=p.2 ∧ (f u).val=q.2) := by
  let st := Fin.append (gammaPointSort 0 a) (gammaPointSort 0 b)
  have hW := (groundRVMapRawGraph_definable f).preimage_real st (groundRVPairIndex a b)
  have h := gamma_graph_of_sorted_formula hW
  apply GammaGraphDefinable.congr h
  intro p q
  have he : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ groundRVPairIndex a b =
      Fin.append (rvValues p.2) (rvValues q.2) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply,groundRVPairIndex,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointCode,rvValues]
  change (_ ∈ groundRVMapRawGraph f ∧ _) ↔ _
  rw [he]
  constructor
  · rintro ⟨⟨u,hu⟩,_⟩
    have hx : rvValues u.val=rvValues p.2 := by
      funext i
      simpa only [Fin.append_left] using congrFun hu (Fin.castAdd b i)
    have hy : rvValues (f u).val=rvValues q.2 := by
      funext i
      simpa only [Fin.append_right] using congrFun hu (Fin.natAdd a i)
    exact ⟨u,rvValues_injective hx,rvValues_injective hy⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨⟨u,congrArg₂ Fin.append (congrArg rvValues hu) (congrArg rvValues hv)⟩,?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [st,Fin.append_left] using groundPointCode_sorted p j
    · simpa only [st,Fin.append_right] using groundPointCode_sorted q j

def groundRVMapOfRawGraph (f : D → E)
    (hG : DefinableOverBase B (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv))
      (groundRVMapRawGraph f)) : GammaGroundMap D E where
  toFun := f
  graph_definable := by
    let π : Fin (a+b) → Fin a ⊕ Fin b := Fin.addCases Sum.inl Sum.inr
    have hraw := ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hG.proper).mpr hG).preimage_comp π
    apply GammaGroundDefinable.of_real_codes
    change GammaGroundRawDefinable hc B (ι := Fin a ⊕ Fin b) _
    apply hraw.congr
    intro z
    have he : z ∘ π = Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Function.comp_apply,π,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
    change (z ∘ π ∈ groundRVMapRawGraph f) ↔ _
    rw [he]
    constructor
    · rintro ⟨u,hu⟩
      have hx : rvValues u.val=z ∘ Sum.inl := by
        funext i
        simpa only [Fin.append_left] using congrFun hu (Fin.castAdd b i)
      have hy : rvValues (f u).val=z ∘ Sum.inr := by
        funext i
        simpa only [Fin.append_right] using congrFun hu (Fin.natAdd a i)
      refine ⟨⟨hx ▸ Set.mem_range_self u.val,hy ▸ Set.mem_range_self (f u).val⟩,u,?_,?_⟩
      · apply rvValues_injective
        rw [rvValues_decode]
        exact hx
      · apply rvValues_injective
        rw [rvValues_decode]
        exact hy
    · rintro ⟨⟨hu,hv⟩,u,hx,hy⟩
      refine ⟨u,?_⟩
      apply congrArg₂ Fin.append
      · rw [hx,rvValues_decode]
      · rw [hy,rvValues_decode]

def fullWeightIsoAtOfEquiv (U V : GammaObjectAt B Set.univ k)
    (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V)
    (e : SpecialTransformations.Section5.rvObjectDomain U.object.obj ≃
      SpecialTransformations.Section5.rvObjectDomain V.object.obj)
    (hG : GammaGraphDefinable B (fun (p : Point (M := M) 0
        (SpecialTransformations.Section5.rvObjectArity U.object.obj))
      (q : Point (M := M) 0 (SpecialTransformations.Section5.rvObjectArity V.object.obj)) =>
        ∃ u : SpecialTransformations.Section5.rvObjectDomain U.object.obj,
          u.val=p.2 ∧ (e u).val=q.2)) : GammaIsoAt U V := by
  let F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ Set.univ
      (SpecialTransformations.Section5.rvObjectDomain U.object.obj)
      (SpecialTransformations.Section5.rvObjectDomain V.object.obj) := by
    refine @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ Set.univ
      (SpecialTransformations.Section5.rvObjectDomain U.object.obj)
      (SpecialTransformations.Section5.rvObjectDomain V.object.obj) e ?_
    obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize hG
    exact @Space.RelationDefinable.mono LRV M N _ _ _ Set.univ _ hr (Set.subset_univ _)
  refine ⟨@isoOfDefinableBijection M N Set.univ k U.object V.object F e.bijective ?_,hG⟩
  intro u
  exact (hU u).trans (hV (e u)).symm

end DiamondIntegral.Section5
