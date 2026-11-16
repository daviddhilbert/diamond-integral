import «section 6».AttainableRadii

/-! Original-base choice in a definable nonempty set closed upwards in
nonnegative finite valuation. Taking the product of a finite definable
subset removes the individual algebraic choices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G]

theorem exists_named_positive_choice (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (P : Set (VF M)) (hP : S.Definable₁ LRV (Subtype.val '' P)) (hne : P.Nonempty)
    (hpositive : ∀ c ∈ P, c ≠ 0 ∧ (1 : GammaInfinity M) ≤ vfValue c)
    (hup : ∀ a ∈ P, ∀ b : VF M, b ≠ 0 → vfValue a ≤ vfValue b → b ∈ P) :
    ∃ c ∈ P, S.Definable₁ LRV {c.val} := by
  classical
  let D : Set (Fin 1 → VF M) := {a | a 0 ∈ P}
  have hD : S.Definable LRV (vfValues '' D) := by
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' P} at hP
    convert hP using 1
    ext z
    exact ⟨fun ⟨a,ha,he⟩ => ⟨a 0,ha,congrFun he 0⟩,
      fun ⟨a,ha,he⟩ => ⟨fun _ => a,ha,by funext i; fin_cases i; exact he⟩⟩
  have hDne : D.Nonempty := by obtain ⟨a,ha⟩ := hne; exact ⟨fun _ => a,ha⟩
  obtain ⟨C,hCD,hCfin,hCne,hCdef⟩ := exists_nonempty_finite_definable_vf_subset v hv hc h00 V S
    hV hVS hSV hnt D hD hDne
  let E : Set (VF M) := (fun a : Fin 1 → VF M => a 0) '' C
  have hEfin : E.Finite := hCfin.image _
  let F := hEfin.toFinset
  have hF (x : VF M) : x ∈ F ↔ ∃ a ∈ C, a 0 = x := hEfin.mem_toFinset
  have hFP (x : VF M) (hx : x ∈ F) : x ∈ P := by
    obtain ⟨a,ha,rfl⟩ := (hF x).mp hx
    exact hCD ha
  have hFdef : S.Definable₁ LRV (Subtype.val '' (F : Set (VF M))) := by
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (F : Set (VF M))}
    convert hCdef using 1
    ext z
    exact ⟨fun ⟨x,hx,hxz⟩ => by
      obtain ⟨a,ha,rfl⟩ := (hF x).mp hx
      exact ⟨a,ha,by funext i; fin_cases i; exact hxz⟩,
      fun ⟨a,ha,he⟩ => ⟨a 0,(hF _).mpr ⟨a,ha,rfl⟩,congrFun he 0⟩⟩
  let c : VF M := ∏ x ∈ F, x
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun x hx => (hpositive x (hFP x hx)).1)
  obtain ⟨a,ha⟩ := hCne
  have haF : a 0 ∈ F := (hF _).mpr ⟨a,ha,rfl⟩
  have hlarge : vfValue (a 0) ≤ vfValue c := by
    rw [show vfValue c = ∏ x ∈ F, vfValue x from map_prod Values.vfValueHom (fun x => x) F]
    exact Finset.single_le_prod (fun x hx => (hpositive x (hFP x hx)).2) haF
  exact ⟨c,hup (a 0) (hFP _ haF) c hc0 hlarge,finiteProduct_definable S F hFdef⟩

end DiamondIntegral.Section6
