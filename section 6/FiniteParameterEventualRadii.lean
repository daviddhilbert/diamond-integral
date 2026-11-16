import «section 6».FinitePrefixUniformRadii

/-! A finite definable real parameter domain admits one original-base
named eventual radius. No individual parameter or radius is named. The
final VF coefficient also works for every offset beyond its value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem finite_parameter_eventual_gamma_named_threshold
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D) (hFinite : D.Finite)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hEventual : ∀ x ∈ D,∃ δ,∀ γ,δ ≤ γ → γ ∈ P x) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1 ≤ δ ∧ ∀ x ∈ D,∀ γ,δ < γ → γ ∈ P x := by
  let cutoff (x : Fin n → M) : Gamma M := if hx : x ∈ D then (hEventual x hx).choose else 1
  obtain ⟨b,hb⟩ := (hFinite.image cutoff).bddAbove
  let Q (x : Fin n → M) : Set (Gamma M) := {γ | 1 ≤ γ ∧ γ ∉ P x}
  have hBound : ∃ β : Gamma M,∀ x ∈ D,∀ γ ∈ Q x,β⁻¹ ≤ γ ∧ γ ≤ β := by
    refine ⟨max b 1,fun x hx γ hγ => ?_⟩
    have hCut : γ ≤ cutoff x := by
      apply le_of_not_gt
      intro hlt
      have hGood := (hEventual x hx).choose_spec γ (by simpa only [cutoff,dif_pos hx] using hlt.le)
      exact hγ.2 hGood
    exact ⟨(inv_le_one'.mpr (le_max_right b 1)).trans hγ.1,
      hCut.trans ((hb (Set.mem_image_of_mem cutoff hx)).trans (le_max_left b 1))⟩
  obtain ⟨δ,hδ,hUnion⟩ := bounded_gamma_rows_named_bound hc h00 D Q
    (positive_bad_gamma_rows_definable hc D hD P hP) hBound
  refine ⟨max δ 1,gamma_max_named δ 1 hδ (gamma_one_named hc),le_max_right _ _,fun x hx γ hγ => ?_⟩
  by_contra hn
  have hγ1 : 1 ≤ γ := ((le_max_right δ 1).trans_lt hγ).le
  have hγδ := (hUnion x hx γ ⟨hγ1,hn⟩).2
  exact (not_le_of_gt ((le_max_left δ 1).trans_lt hγ)) hγδ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_parameter_eventual_named_vf_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D) (hFinite : D.Finite)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hEventual : ∀ x ∈ D,∃ δ,∀ γ,δ ≤ γ → γ ∈ P x) :
    ∃ c : VF M,c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧ (1 : GammaInfinity M) < vfValue c ∧
      ∀ x ∈ D,∀ (d : VF M) (hd : d ≠ 0),vfValue c ≤ vfValue d → finiteValue d hd ∈ P x := by
  obtain ⟨δ,hδ,hδ1,hGood⟩ := finite_parameter_eventual_gamma_named_threshold hc h00 D hD hFinite P hP hEventual
  obtain ⟨c,hc0,hcDef,hδc⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ1 hδ
  refine ⟨c,hc0,hcDef,(show (1 : GammaInfinity M) ≤ δ.val from hδ1).trans_lt hδc,fun x hx d hd hcd => ?_⟩
  exact hGood x hx (finiteValue d hd) (hδc.trans_le hcd)

end DiamondIntegral.Section6
