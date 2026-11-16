import «section 6».UnarySmallLiftLabels

/-! Finite original-base RV volume families have actual definable VF
centers indexed by their original labels. The real graph contains the
whole code family; no representative becomes an additional parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rawRVScalarCenterMap (f : (Fin 1 → M) → VF M)
    (hf : S.DefinableFun LRV (fun z => (f z).val)) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := rawRVSpace (M := M) 1
  let Q := rawVFSpace (M := M) 1
  let F (z : Fin 1 → M) : Fin 1 → M := fun _ => (f z).val
  have hdom (c : P.domain) : F c.val ∈ Q.domain := ⟨fun _ => f c.val,rfl⟩
  refine Map.ofCodes (DefSet.univ P S) (fun x => fun _ : Fin 1 => f (rvValues x)) F (fun _ => hf) hdom ?_
  intro c
  funext i
  apply Subtype.ext
  have h := congrFun (vfValues_decode (⟨F c.val,hdom c⟩ : Q.domain)) i
  change ((Q.decode ⟨F c.val,hdom c⟩) i).val = (f c.val).val at h
  change ((Q.decode ⟨F c.val,hdom c⟩) i).val = (f (rvValues (P.decode c))).val
  rw [h,rvValues_decode]

theorem rawRVScalarCenterMap_value (f : (Fin 1 → M) → VF M)
    (hf : S.DefinableFun LRV (fun z => (f z).val))
    (t : DefSet.univ (rawRVSpace (M := M) 1) S) :
    (rawRVScalarCenterMap f hf t).val 0 = f (rvValues t.val) := rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_unary_rv_object_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (U : RVObject (M := M) S 1) (hFin : U.domain.carrier.Finite) :
    ∃ a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∀ u : U.domain, rv M ((a u).val 0) = U.value u 0 := by
  let C := rvCoordinateSet U.volume.image (0 : Fin 1)
  have hC : S.Definable₁ LRV C := rvCoordinateSet_definable _ _
  have hCF : C.Finite := by
    letI : Finite U.domain := hFin.to_subtype
    apply (Set.finite_range (fun u : U.domain => (U.value u 0).val)).subset
    rintro t ⟨a,hat⟩
    obtain ⟨u,hu⟩ := a.property
    exact ⟨u,(congrArg (fun v : Fin 1 → RVInfinity M => (v 0).val) hu).trans hat⟩
  have hCRV (t : M) (ht : t ∈ C) : iRV t := by
    obtain ⟨a,ha⟩ := ht
    exact ha ▸ (a.val 0).property
  obtain ⟨f,hf,hAt⟩ := exists_finite_rv_centers hc h00 hs hv W S hW hWS hSW hnt hsmall C hC hCF hCRV
  let a := (rawRVScalarCenterMap f hf).comp U.volume
  refine ⟨a,fun u => Subtype.ext ?_⟩
  have hCode : rvValues (U.value u) = fun _ : Fin 1 => (U.value u 0).val := by
    funext i
    fin_cases i
    rfl
  change iRv (f (rvValues (U.value u))).val = (U.value u 0).val
  rw [hCode]
  exact hAt _ ⟨⟨U.value u,⟨u,rfl⟩⟩,rfl⟩

end DiamondIntegral.Section6
