import «section 6».FiniteOpenCenters

/-! The invariant raw center function descends to actual open-ball
imaginaries with a complete graph over the original real parameter base.
All representatives of each ball remain in the graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem open_center_graph_of_code_function
    (A : Set (OpenBallCodes.OpenBall M))
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (g : (Fin 2 → M) → VF M) (hg : S.DefinableFun LRV (fun q => (g q).val))
    (hgmem : ∀ q ∈ OpenBallCodes.pullback A, (g q).val ∈ OpenBallCodes.rawBall q)
    (hginv : ∀ q u, OpenBallCodes.rawBall q = OpenBallCodes.rawBall u → g q = g u) :
    ∃ f : A → VF M, (∀ D, (f D).val ∈ OpenBallCodes.underlying D.val) ∧
      S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (f D).val)) := by
  let rep (D : A) : OpenBallCodes.Code M := (Quotient.exists_rep D.val).choose
  have hrep (D : A) : Quotient.mk _ (rep D) = D.val := (Quotient.exists_rep D.val).choose_spec
  let f (D : A) := g (rep D).val
  have hcode (q : OpenBallCodes.Code M) (D : A) (he : Quotient.mk _ q = D.val) : g q.val = f D := by
    apply hginv
    exact congrArg OpenBallCodes.underlying (he.trans (hrep D).symm)
  have hfmem (D : A) : (f D).val ∈ OpenBallCodes.underlying D.val := by
    have hq : (rep D).val ∈ OpenBallCodes.pullback A := ⟨(rep D).property,(hrep D).symm ▸ D.property⟩
    have hm := hgmem (rep D).val hq
    exact (congrArg OpenBallCodes.underlying (hrep D)) ▸ hm
  have hgraphEq : OpenBallCodes.quotientCenterGraph A (fun D => (f D).val) =
      {z : Fin 3 → M | Fin.init z ∈ OpenBallCodes.pullback A ∧ (g (Fin.init z)).val = z (Fin.last 2)} := by
    ext z
    constructor
    · rintro ⟨q,hq,D,hD,hf⟩
      refine ⟨hq ▸ ⟨q.property,hD.symm ▸ D.property⟩,?_⟩
      rw [← hq,hcode q D hD]
      exact hf
    · rintro ⟨hC,hgval⟩
      let q : OpenBallCodes.Code M := ⟨Fin.init z,hC.1⟩
      let D : A := ⟨Quotient.mk _ q,hC.2⟩
      refine ⟨q,rfl,D,rfl,?_⟩
      change (f D).val = z (Fin.last 2)
      exact (congrArg Subtype.val (hcode q D rfl)).symm.trans hgval
  refine ⟨f,hfmem,?_⟩
  rw [hgraphEq]
  have hfun : S.DefinableFun LRV (fun z : Fin 3 → M => (g (Fin.init z)).val) :=
    hg.comp (show S.DefinableMap LRV (Fin.init : (Fin 3 → M) → Fin 2 → M) from
      fun _ => Set.DefinableFun.proj LRV)
  have heq := hfun.ofPred_eq (Set.DefinableFun.proj (L := LRV) (i := Fin.last 2))
  exact (hAdef.preimage_comp (Fin.castSucc : Fin 2 → Fin 3)).inter heq

theorem exists_original_base_open_center_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A)) :
    ∃ f : A → VF M, (∀ D, (f D).val ∈ OpenBallCodes.underlying D.val) ∧
      S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (f D).val)) := by
  obtain ⟨g,hg,hgmem,hginv⟩ := exists_original_base_open_centers hc h00 hv V S hV hVS hSV hnt A hA hAdef
  exact open_center_graph_of_code_function A hAdef g hg hgmem hginv

end DiamondIntegral.Section6
