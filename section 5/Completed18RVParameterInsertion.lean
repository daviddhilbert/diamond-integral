import IntegrationSection5.FiniteRVComparison

/-! Naming a finite RV tuple gives an actual VF-fixed definable bijection
onto the locus obtained by inserting those constants as old RV labels. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
  CanonicalStructure.normalize
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n m r : ℕ}

def rvParameterInsertMap (S : Set M) (z : Fin r → RV (M := M)) (hz : ∀ i,(z i).val ∈ S) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace n (r+m)) S) :=
  Map.ofCodes _ (fun p => (p.1,Fin.append (fun i => ⟨(z i).val,by exact (z i).property⟩) p.2))
    (fun w => Sum.elim (w ∘ Sum.inl) (Fin.addCases (fun j => (z j).val) (fun j => w (.inr j))))
    (by
      intro j
      cases j with
      | inl j => exact rawProj S (.inl j : Fin n ⊕ Fin m)
      | inr j =>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · letI := @CanonicalStructure.normalize M sM
          simpa only [Sum.elim_inr,Fin.addCases_left] using
            LRV.definableFun_const (Fin n ⊕ Fin m) (hz i)
        · simpa only [Sum.elim_inr,Fin.addCases_right] using
            rawProj S (.inr i : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨c.property.1,?_⟩
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Function.comp_apply,Sum.elim_inr,Fin.addCases_left,sortEval,iRV] using (z i).property
      · simpa only [Function.comp_apply,Sum.elim_inr,Fin.addCases_right] using c.property.2 i)
    (by
      intro c
      refine Prod.ext ?_ ?_
      · funext j; apply Subtype.ext; rfl
      · let x : Fin m → RV (M := M) := fun i => ⟨c.val (.inr i),c.property.2 i⟩
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · apply Subtype.ext
          exact (@Fin.addCases_left r m (fun _ => M) (fun j => (z j).val) (fun j => c.val (.inr j)) i).trans
            (congrArg (fun w : RV (M := M) => w.val) (Fin.append_left z x i)).symm
        · apply Subtype.ext
          exact (@Fin.addCases_right r m (fun _ => M) (fun j => (z j).val) (fun j => c.val (.inr j)) i).trans
            (congrArg (fun w : RV (M := M) => w.val) (Fin.append_right z x i)).symm)

def rvParameterAttachedSet (U : Set (Point (M := M) n m)) (z : Fin r → RV (M := M)) :
    Set (Point (M := M) n (r+m)) := Set.range (fun p : U => (p.val.1,Fin.append z p.val.2))

def rvParameterAttachEquiv (U : Set (Point (M := M) n m)) (z : Fin r → RV (M := M)) :
    U ≃ rvParameterAttachedSet U z :=
  Equiv.ofBijective (fun p => ⟨(p.val.1,Fin.append z p.val.2),⟨p,rfl⟩⟩)
    ⟨by
      intro a b he
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun q : rvParameterAttachedSet U z => q.val.1) he
      · funext i
        simpa only [Fin.append_right] using
          congrArg (fun q : rvParameterAttachedSet U z => q.val.2 (Fin.natAdd r i)) he,
    by rintro ⟨q,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

def rvParameterAttachIso (B : Base (M := M)) (U : Set (Point (M := M) n m))
    (hU : GammaSetDefinable B U) (z : Fin r → RV (M := M)) (hz : ∀ i,(z i).val ∈ B.real) :
    GammaIso B U (rvParameterAttachedSet U z) where
  equiv := rvParameterAttachEquiv U z
  graph := by
    have h := (gammaLogicInput B).restrict_graph hU
      ((gammaLogicInput B).real_map_graph (rvParameterInsertMap B.real z hz (n := n) (m := m)))
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      change (p.1,Fin.append z p.2) = q
      exact (congrArg (fun w : Point (M := M) n m => (w.1,Fin.append z w.2)) ha).symm.trans hq
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

end DiamondIntegral.Section5
