import IntegrationSection5.FiniteRVComparison

/-! Restricting an RV-labelled prepared cell family to a condition on
its old RV labels preserves its entire nonempty cells and positioning. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}
variable {A A' : Set (Point (M := M) 2 m)}

def cellRestrictionTarget (T : PositionedCellLabelInjection G A) (hsub : A' ⊆ A) :
    Set (Point (M := M) 2 T.arity) :=
  Set.range (fun a : A' => (T.iso.equiv ⟨a.val,hsub a.property⟩).val)

def cellRestrictionEquiv (T : PositionedCellLabelInjection G A) (hsub : A' ⊆ A) :
    A' ≃ cellRestrictionTarget T hsub :=
  Equiv.ofBijective (fun a => ⟨(T.iso.equiv ⟨a.val,hsub a.property⟩).val,⟨a,rfl⟩⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      have hv : (T.iso.equiv ⟨a.val,hsub a.property⟩).val =
          (T.iso.equiv ⟨b.val,hsub b.property⟩).val :=
        congrArg (fun q : cellRestrictionTarget T hsub => q.val) h
      have he := T.iso.equiv.injective (Subtype.ext hv)
      exact congrArg (fun w : A => w.val) he,
    by rintro ⟨q,a,ha⟩; exact ⟨a,Subtype.ext ha⟩⟩

theorem cellRestriction_graph (T : PositionedCellLabelInjection G A) (hsub : A' ⊆ A)
    (hA' : GammaSetDefinable G A') :
    GammaGraphDefinable G (fun p q => ∃ a : A',a.val=p ∧ (cellRestrictionEquiv T hsub a).val=q) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA' T.iso.graph)
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    have he : (⟨p,hsub hp⟩ : A) = a := Subtype.ext ha.symm
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    change (T.iso.equiv ⟨p,hsub hp⟩).val = q
    rw [he]
    exact hq
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,hsub a.property⟩,ha,hq⟩

theorem cellRestriction_fibre (T : PositionedCellLabelInjection G A) (hsub : A' ⊆ A)
    (hcoh : ∀ a b,(T.iso.equiv a).val.2 = (T.iso.equiv b).val.2 → a.val.2 = b.val.2)
    (hsat : ∀ a b : A,a.val.2=b.val.2 → a.val∈A' → b.val∈A')
    (s : Fin T.arity → RV (M := M)) (hs : (nativeTwoFibre (cellRestrictionTarget T hsub) s).Nonempty) :
    nativeTwoFibre (cellRestrictionTarget T hsub) s = nativeTwoFibre T.target s := by
  obtain ⟨p₀,a₀,ha₀⟩ := hs
  have hlabel₀ : (T.iso.equiv ⟨a₀.val,hsub a₀.property⟩).val.2 = s := congrArg Prod.snd ha₀
  ext p
  constructor
  · rintro ⟨a,ha⟩
    change (![p.1,p.2],s) ∈ T.target
    rw [← ha]
    exact (T.iso.equiv ⟨a.val,hsub a.property⟩).property
  · intro hp
    let q : T.target := ⟨(![p.1,p.2],s),hp⟩
    let b := T.iso.equiv.symm q
    have hb : (T.iso.equiv b).val = (![p.1,p.2],s) :=
      congrArg Subtype.val (T.iso.equiv.apply_symm_apply q)
    have hlabels : (T.iso.equiv ⟨a₀.val,hsub a₀.property⟩).val.2 = (T.iso.equiv b).val.2 :=
      hlabel₀.trans (congrArg Prod.snd hb).symm
    have hb' : b.val ∈ A' := hsat _ b (hcoh _ b hlabels) a₀.property
    exact ⟨⟨b.val,hb'⟩,hb⟩

def restrictPositionedCells (T : PositionedCellLabelInjection G A) (hsub : A' ⊆ A)
    (hA' : GammaSetDefinable G A')
    (hcoh : ∀ a b,(T.iso.equiv a).val.2 = (T.iso.equiv b).val.2 → a.val.2 = b.val.2)
    (hsat : ∀ a b : A,a.val.2=b.val.2 → a.val∈A' → b.val∈A') :
    PositionedCellLabelInjection G A' where
  arity := T.arity
  target := cellRestrictionTarget T hsub
  iso := ⟨cellRestrictionEquiv T hsub,cellRestriction_graph T hsub hA'⟩
  fixes_vf := fun a => T.fixes_vf ⟨a.val,hsub a.property⟩
  positionDomain := T.positionDomain
  position := T.position
  position_graph := T.position_graph
  cells := by
    intro s hs
    have he := cellRestriction_fibre T hsub hcoh hsat s hs
    rw [he] at hs ⊢
    exact T.cells s hs

end DiamondIntegral.Section5
