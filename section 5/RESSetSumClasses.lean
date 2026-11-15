import «section 5».RESSetSumSchemata
import «section 5».NativeRESChartClasses
import «section 5».RESSetChartPresentations

/-! Literal tagged schema sums realize addition in the actual native RES
ring. The proof uses original-base cuts and actual coordinate bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Milestone0.Transfer
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem RESSetSchema.sum_native_class (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    nativeRESChartClass ((F.sum G).chart hc z (F.sum_valid hc G z hF hG)) =
      nativeRESChartClass (F.chart hc z hF) + nativeRESChartClass (G.chart hc z hG) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range z, B.gamma⟩
  let S := (F.sum G).chart hc z (F.sum_valid hc G z hF hG)
  let I : Set (Fin (1+(a+b)) → M) := {w | w ∈ S.domain ∧ w (Fin.castAdd (a+b) 0) = iRVZero}
  have hI : DefinableOverBase C (fun _ : Fin (1+(a+b)) => .rv) I := by
    have htag := (RVNamedTuples.zero_definable C).preimage_real
      (fun _ : Fin (1+(a+b)) => .rv) (fun _ : Fin 1 => Fin.castAdd (a+b) 0)
    have hS : DefinableOverBase C (fun _ : Fin (1+(a+b)) => .rv) S.domain := S.domain_definable
    have h := hS.inter htag
    convert h using 1
    ext w
    change (_ ∧ _) ↔ (_ ∧ (_ ∧ _))
    constructor
    · exact fun hw => ⟨hw.1, hw.2, S.domain_definable.proper w hw.1⟩
    · exact fun hw => ⟨hw.1, hw.2.1⟩
  have hsub : I ⊆ S.domain := fun _ h => h.1
  have hsum (w : Fin (1+(a+b)) → M) : w ∈ S.domain ↔
      (∃ x ∈ F.rowDomain z, w = rawRVLeftTag b x) ∨
      (∃ y ∈ G.rowDomain z, w = rawRVRightTag a y) := by
    rw [show S.domain = (F.sum G).rowDomain z from (F.sum G).chart_domain hc z _]
    exact F.sum_row G z w
  have hneq (x : Fin a → M) (y : Fin b → M) : rawRVLeftTag b x ≠ rawRVRightTag a y := by
    intro h
    have ht := congrFun h (Fin.castAdd (a+b) 0)
    exact RVCalc.rv_one_ne_zero hM ht.symm
  have hleft (w : Fin (1+(a+b)) → M) : w ∈ I ↔ ∃ x ∈ F.rowDomain z, w = rawRVLeftTag b x := by
    constructor
    · rintro ⟨hw, ht⟩
      rcases (hsum w).mp hw with h | ⟨y, hy, rfl⟩
      · exact h
      · exact False.elim (RVCalc.rv_one_ne_zero hM ht)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hsum _).mpr (Or.inl ⟨x, hx, rfl⟩), rfl⟩
  have hright (w : Fin (1+(a+b)) → M) : w ∈ S.domain \ I ↔
      ∃ y ∈ G.rowDomain z, w = rawRVRightTag a y := by
    constructor
    · rintro ⟨hw, hn⟩
      rcases (hsum w).mp hw with ⟨x, hx, he⟩ | h
      · exact False.elim (hn ((hleft w).mpr ⟨x, hx, he⟩))
      · exact h
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hsum _).mpr (Or.inr ⟨y, hy, rfl⟩), ?_⟩
      intro hi
      obtain ⟨x, hx, he⟩ := (hleft _).mp hi
      exact hneq x y he.symm
  let L := Section3RESChartCuts.restrict S I hI hsub
  let R := Section3RESChartCuts.outside S I hI
  have hbijL : Set.BijOn (fun w : Fin (1+(a+b)) → M => w ∘ rvTagLeftIndex a b) L.domain (F.chart hc z hF).domain := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := (hleft w).mp hw
      rw [F.chart_domain hc z hF]
      simpa only [Function.comp_def, rawRVLeftTag, rvTagLeftIndex, Fin.append_left, Fin.append_right] using hx
    · intro w hw v hv he
      obtain ⟨x, hx, rfl⟩ := (hleft w).mp hw
      obtain ⟨y, hy, rfl⟩ := (hleft v).mp hv
      have hxy : x = y := by
        simpa only [Function.comp_def, rawRVLeftTag, rvTagLeftIndex, Fin.append_left, Fin.append_right] using he
      rw [hxy]
    · intro x hx
      refine ⟨rawRVLeftTag b x, (hleft _).mpr ⟨x, ?_, rfl⟩, ?_⟩
      · exact (F.chart_domain hc z hF) ▸ hx
      · simp only [Function.comp_def, rawRVLeftTag, rvTagLeftIndex, Fin.append_left, Fin.append_right]
  have hbijR : Set.BijOn (fun w : Fin (1+(a+b)) → M => w ∘ rvTagRightIndex a b) R.domain (G.chart hc z hG).domain := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := (hright w).mp hw
      rw [G.chart_domain hc z hG]
      simpa only [Function.comp_def, rawRVRightTag, rvTagRightIndex, Fin.append_right] using hy
    · intro w hw v hv he
      obtain ⟨x, hx, rfl⟩ := (hright w).mp hw
      obtain ⟨y, hy, rfl⟩ := (hright v).mp hv
      have hxy : x = y := by
        simpa only [Function.comp_def, rawRVRightTag, rvTagRightIndex, Fin.append_right] using he
      rw [hxy]
    · intro y hy
      refine ⟨rawRVRightTag a y, (hright _).mpr ⟨y, ?_, rfl⟩, ?_⟩
      · exact (G.chart_domain hc z hG) ▸ hy
      · simp only [Function.comp_def, rawRVRightTag, rvTagRightIndex, Fin.append_right]
  let isoL := RVUnderlyingIsomorphisms.ofMap L.toChart (F.chart hc z hF).toChart
    (fun w => w ∘ rvTagLeftIndex a b)
    (RVCoordinateMaps.coordinate_graph_definable C L.domain L.domain_definable (rvTagLeftIndex a b)) hbijL
  let isoR := RVUnderlyingIsomorphisms.ofMap R.toChart (G.chart hc z hG).toChart
    (fun w => w ∘ rvTagRightIndex a b)
    (RVCoordinateMaps.coordinate_graph_definable C R.domain R.domain_definable (rvTagRightIndex a b)) hbijR
  exact (nativeRESChartClass_cut S I hI hsub).symm.trans
    (congrArg₂ (fun x y : RESDimensionFreeReduction.Ring C => x+y)
      (nativeRESChartClass_iso L _ isoL) (nativeRESChartClass_iso R _ isoR))

end DiamondIntegral.Section5
