import «section 6».FiniteNeighborhoodRadiusGraphs

/-! One original-base named VF radius fits all prescribed neighborhoods
of a finite definable center family. The finite local choices are only
used to prove cofinality; the actual named point is constructed from
the complete first-order radius predicate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

def finiteNeighborhoodRadii (C : Set (Fin n → VF M)) (R : Set (Fin n ⊕ Fin 1 → M))
    (j : Fin n) : Set (VF M) := {c | (fun _ : Fin 1 => c.val) ∈ finiteNeighborhoodRadiusCodes C R j}

theorem finiteNeighborhoodRadii_positive (C : Set (Fin n → VF M))
    (R : Set (Fin n ⊕ Fin 1 → M)) (j : Fin n) (c : VF M) (hc : c ∈ finiteNeighborhoodRadii C R j) :
    c ≠ 0 ∧ (1 : GammaInfinity M) < vfValue c := by
  obtain ⟨a,ha,he⟩ := hc.1
  have hac : a 0 = c := Subtype.ext (congrFun he 0)
  exact ⟨hac ▸ ha.1,hac ▸ ha.2⟩

theorem finiteNeighborhoodRadii_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : Set (Fin n → VF M)) (hC : S.Definable LRV (vfValues '' C))
    (R : Set (Fin n ⊕ Fin 1 → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable₁ LRV (Subtype.val '' finiteNeighborhoodRadii C R j) := by
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' finiteNeighborhoodRadii C R j}
  convert finiteNeighborhoodRadiusCodes_definable hc C hC R hR j using 1
  ext z
  constructor
  · rintro ⟨c,hcP,he⟩
    have hEq : (fun _ : Fin 1 => c.val) = z := by funext i; fin_cases i; exact he
    exact hEq ▸ hcP
  · intro hz
    obtain ⟨a,ha,he⟩ := hz.1
    have hEq : (fun _ : Fin 1 => (a 0).val) = z := by funext i; fin_cases i; exact congrFun he 0
    refine ⟨a 0,?_,congrFun he 0⟩
    change (fun _ : Fin 1 => (a 0).val) ∈ finiteNeighborhoodRadiusCodes C R j
    rw [hEq]
    exact hz

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_named_radius_for_finite_neighborhoods
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (C : Set (Fin n → VF M)) (hC : S.Definable LRV (vfValues '' C)) (hFin : C.Finite)
    (R : Set (Fin n ⊕ Fin 1 → M)) (hR : S.Definable LRV R) (j : Fin n)
    (hNear : ∀ q ∈ C, {x : VF M | Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R} ∈ 𝓝 (q j)) :
    ∃ c : VF M, ∃ hc0 : c ≠ 0, S.Definable₁ LRV {c.val} ∧ (1 : GammaInfinity M) < vfValue c ∧
      ∀ q ∈ C, ∀ x ∈ centeredGammaDisc (q j) (finiteValue c hc0),
        Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R := by
  have hLocal (q) (hq : q ∈ C) : ∃ γ : Gamma M, centeredGammaDisc (q j) γ ⊆
      {x : VF M | Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R} := by
    obtain ⟨γ,hγ⟩ := exists_puncturedGammaDisc_subset_nhds hv (q j) (hNear q hq)
    refine ⟨γ,?_⟩
    rintro x (rfl | hx)
    · exact mem_of_mem_nhds (hNear q hq)
    · exact hγ hx
  let γ (q : Fin n → VF M) : Gamma M := if hq : q ∈ C then (hLocal q hq).choose else 1
  obtain ⟨β,hβ⟩ := (hFin.image γ).bddAbove
  obtain ⟨δ,hδ⟩ := exists_gt (max β (1 : Gamma M))
  obtain ⟨b,hb0,hbVal⟩ := gamma_has_vf_representative δ
  have hbΓ : finiteValue b hb0 = δ := Subtype.ext hbVal
  have hbPos : (1 : GammaInfinity M) < vfValue b := by
    have hbVal' : vfValue b = δ.val := by simpa only [valueHom_eq_value] using hbVal
    rw [hbVal']
    exact (le_max_right β (1 : Gamma M)).trans_lt hδ
  have hNonempty : (finiteNeighborhoodRadii C R j).Nonempty := by
    refine ⟨b,(finiteNeighborhoodRadiusCodes_at C R j b hb0).mpr ⟨hbPos,?_⟩⟩
    intro q hq x hx
    have hqβ : (hLocal q hq).choose ≤ β := by
      simpa only [γ,dif_pos hq] using hβ (Set.mem_image_of_mem γ hq)
    have hqδ := hqβ.trans ((le_max_left β (1 : Gamma M)).trans_lt hδ).le
    exact (hLocal q hq).choose_spec (centeredGammaDisc_anti (q j) hqδ (hbΓ ▸ hx))
  have hUp (a) (ha : a ∈ finiteNeighborhoodRadii C R j) (b : VF M) (hb0 : b ≠ 0)
      (hab : vfValue a ≤ vfValue b) : b ∈ finiteNeighborhoodRadii C R j := by
    have ha0 := (finiteNeighborhoodRadii_positive C R j a ha).1
    obtain ⟨haPos,haFit⟩ := (finiteNeighborhoodRadiusCodes_at C R j a ha0).mp ha
    apply (finiteNeighborhoodRadiusCodes_at C R j b hb0).mpr
    refine ⟨haPos.trans_le hab,fun q hq x hx => ?_⟩
    have hΓ : finiteValue a ha0 ≤ finiteValue b hb0 := by
      change Values.vfValueHom a ≤ Values.vfValueHom b
      simpa only [valueHom_eq_value] using hab
    exact haFit q hq x (centeredGammaDisc_anti (q j) hΓ hx)
  obtain ⟨c,hcP,hcDef⟩ := exists_named_positive_choice Valued.v hv hc h00 V S hV hVS hSV hnt
    (finiteNeighborhoodRadii C R j) (finiteNeighborhoodRadii_definable hc C hC R hR j) hNonempty
    (fun a ha => let h := finiteNeighborhoodRadii_positive C R j a ha; ⟨h.1,h.2.le⟩) hUp
  have hc0 := (finiteNeighborhoodRadii_positive C R j c hcP).1
  obtain ⟨hcPos,hcFit⟩ := (finiteNeighborhoodRadiusCodes_at C R j c hc0).mp hcP
  exact ⟨c,hc0,hcDef,hcPos,hcFit⟩

end DiamondIntegral.Section6
