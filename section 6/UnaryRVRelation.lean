import «section 6».UnaryDifferentiabilityException

/-! Full real graph of a finitary unary RV relation pulled back to its
VF input. The parameter base and every output label are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def unaryRVRelationCodes (z : Fin 1 ⊕ Fin 1 → M) : Fin 1 ⊕ Fin 1 → M :=
  Sum.elim (fun _ => iRv (z (.inl 0))) (z ∘ Sum.inr)

theorem unaryRVRelationCodes_definable : S.DefinableMap LRV (unaryRVRelationCodes (M := M)) := by
  rintro (i | i)
  · fin_cases i
    exact (hullRVCode_definable S (.inl (0 : Fin 1)))
  · exact Set.DefinableFun.proj LRV

def unaryRVRelationDomain (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}) :
    DefSet (rawMixedSpace (M := M) 1 1) S := by
  let D : Set (Mixed M 1 1) := {p | R (iRv (p.1 0).val) (p.2 0).val}
  refine ⟨D,(mixed_definable_iff_values_image S D).mpr ?_⟩
  have hU := (mixed_definable_iff_values_image S (Set.univ : Set (Mixed M 1 1))).mp
    (DefSet.univ (rawMixedSpace (M := M) 1 1) S).definable
  have hRel := hR.preimage_map (unaryRVRelationCodes_definable (M := M) (S := S))
  convert hU.inter hRel using 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,Set.mem_univ _,rfl⟩,hp⟩
  · rintro ⟨⟨p,_,he⟩,hRel⟩
    rw [← he] at hRel
    exact ⟨p,hRel,he⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_unary_relation_center_function
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))})
    (hFin : ∀ u, {v | R u v}.Finite) (hRV : ∀ u v, R u v → iRV v) :
    ∃ f : (Fin 2 → M) → VF M, S.DefinableFun LRV (fun z => (f z).val) ∧
      ∀ a : Fin 1 → VF M, ∀ v, R (iRv (a 0).val) v →
        iRv (f (Fin.snoc (vfValues a) v)).val = v := by
  have hA : S.Definable LRV (vfValues '' (Set.univ : Set (Fin 1 → VF M))) := by
    convert vfRawUniverse_definable S 1 using 1
    ext z
    exact ⟨by rintro ⟨a,_,rfl⟩ i; exact (a i).property,
      fun h => ⟨(fun i => ⟨z i,h i⟩),Set.mem_univ _,rfl⟩⟩
  have hC := hR.preimage_map (unaryRVRelationCodes_definable (M := M) (S := S))
  obtain ⟨f,hf,hval⟩ := exists_parametric_rv_centers hc h00 hs hv V S hV hVS hSV hnt hsmall
    Set.univ hA (fun a => {v | R (iRv (a 0)) v}) hC
    (fun a => hFin _) (fun a v h => hRV _ _ h)
  exact ⟨f,hf,fun a v hv => hval a (Set.mem_univ _) v hv⟩

end DiamondIntegral.Section6
