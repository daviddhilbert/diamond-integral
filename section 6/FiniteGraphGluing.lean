import «section 6».CentripetalLocusExtension
import Section4.FunctionalRelations

/-! Finite compatible maps glue over their actual definable source
pieces. The whole graph is a finite definable union over the original
base. No enumeration of points or additional names is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {I : Type} [Finite I]

theorem exists_finite_glued_map
    (A : DefSet P S) (B : DefSet Q S) (C : I → DefSet P S) (f : ∀ i, Map (C i) B)
    (hsub : ∀ i, (C i).carrier ⊆ A.carrier)
    (hcover : ∀ p : A, ∃ i, p.val ∈ (C i).carrier)
    (hcompat : ∀ i j (p : C i) (q : C j), p.val = q.val → (f i p).val = (f j q).val) :
    ∃ g : Map A B, ∀ i (p : C i), (g ⟨p.val,hsub i p.property⟩).val = (f i p).val := by
  let R (x : P.Carrier) (y : Q.Carrier) := ∃ i, (f i).graph x y
  have hR : P.RelationDefinable Q S R := by
    change S.Definable L (P.relation Q R)
    have he : P.relation Q R = ⋃ i, P.relation Q (f i).graph := by
      ext z
      simp only [Space.relation,Set.mem_ofPred_eq,Set.mem_iUnion,R]
      aesop
    rw [he]
    exact Set.definable_iUnion_of_finite (fun i => (f i).graph_definable)
  have hdom (x y) (h : R x y) : x ∈ A.carrier ∧ y ∈ B.carrier := by
    obtain ⟨i,p,rfl,rfl⟩ := h
    exact ⟨hsub i p.property,(f i p).property⟩
  have htotal (p : A) : ∃ y, R p.val y := by
    obtain ⟨i,hi⟩ := hcover p
    exact ⟨(f i ⟨p.val,hi⟩).val,i,⟨p.val,hi⟩,rfl,rfl⟩
  have hunique (x y z) (hy : R x y) (hz : R x z) : y = z := by
    obtain ⟨i,p,hp,hfp⟩ := hy
    obtain ⟨j,q,hq,hfq⟩ := hz
    exact hfp.symm.trans ((hcompat i j p q (hp.trans hq.symm)).trans hfq)
  let g : Map A B := Map.ofFunctionalRelation hR hdom htotal hunique
  refine ⟨g,fun i p => ?_⟩
  exact hunique _ _ _
    (Map.ofFunctionalRelation_graph hR hdom htotal hunique ⟨p.val,hsub i p.property⟩)
    ⟨i,p,rfl,rfl⟩

end DiamondIntegral.Section6
