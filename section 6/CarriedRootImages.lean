import «section 6».CarriedFibreContexts

/-! Push actual coordinate roots through a carried lower-dimensional
chain. Their full image is definable over S; each output fiber embeds
in one old root fiber, retaining the original uniform cardinal bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

namespace CarriedChainLift

def rootImage (F : CarriedChainLift (G := G) X f) (R : CoordinateRootFamily X.bundle) :=
  (F.map.restrict R.subset).image

theorem rootImage_fibre_subset (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle) (a : X.bundle)
    (b : Fin n → VF M) (u : Fin F.target.arity → RVInfinity M)
    (hVF : Fin.init (F.map a).val.1 = b) (hRV : (F.map a).val.2 = u) :
    {x : VF M | (Fin.snoc b x,u) ∈ (F.rootImage R).carrier} ⊆
      {x | (Fin.snoc (Fin.init a.val.1) x,a.val.2) ∈ R.roots.carrier} := by
  rintro x ⟨p,hp⟩
  let pA : X.bundle := ⟨p.val,R.subset p.property⟩
  have he : (F.map pA).val = (Fin.snoc b x,u) := hp
  have hInit : Fin.init (F.map pA).val.1 = Fin.init (F.map a).val.1 := by
    rw [he,Fin.init_snoc,hVF]
  have hTags : (F.map pA).val.2 = (F.map a).val.2 := (congrArg Prod.snd he).trans hRV.symm
  have hInput := F.input_point_on_fibre hinj pA a hInit hTags
  rw [he] at hInput
  change pA.val = (Fin.snoc (Fin.init a.val.1)
    ((Fin.snoc b x : Fin (n+1) → VF M) (Fin.last n)),a.val.2) at hInput
  rw [Fin.snoc_last] at hInput
  change (Fin.snoc (Fin.init a.val.1) x,a.val.2) ∈ R.roots.carrier
  rw [← hInput]
  exact p.property

def pushCoordinateRoots (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle) : CoordinateRootFamily F.target.bundle where
  roots := F.rootImage R
  subset := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (F.map ⟨p.val,R.subset p.property⟩).property
  finite := by
    intro b u
    by_cases hne : {x : VF M | (Fin.snoc b x,u) ∈ (F.rootImage R).carrier}.Nonempty
    · obtain ⟨x,⟨p,hp⟩⟩ := hne
      let a : X.bundle := ⟨p.val,R.subset p.property⟩
      have he : (F.map a).val = (Fin.snoc b x,u) := hp
      have hVF : Fin.init (F.map a).val.1 = b := by rw [he,Fin.init_snoc]
      have hRV : (F.map a).val.2 = u := congrArg Prod.snd he
      exact (R.finite (Fin.init a.val.1) a.val.2).subset (F.rootImage_fibre_subset hinj R a b u hVF hRV)
    · exact (Set.not_nonempty_iff_eq_empty.mp hne).symm ▸ Set.finite_empty

theorem pushCoordinateRoots_bound (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle) (N : ℕ) (hN : R.Bound N) :
    (F.pushCoordinateRoots hinj R).Bound N := by
  intro b u
  by_cases hne : ((F.pushCoordinateRoots hinj R).fibre b u).Nonempty
  · obtain ⟨x,hx⟩ := hne
    obtain ⟨p,hp⟩ := ((F.pushCoordinateRoots hinj R).mem_fibre b u x).mp hx
    let a : X.bundle := ⟨p.val,R.subset p.property⟩
    have he : (F.map a).val = (Fin.snoc b x,u) := hp
    have hVF : Fin.init (F.map a).val.1 = b := by rw [he,Fin.init_snoc]
    have hRV : (F.map a).val.2 = u := congrArg Prod.snd he
    have hSub : (F.pushCoordinateRoots hinj R).fibre b u ⊆ R.fibre (Fin.init a.val.1) a.val.2 := by
      intro y hy
      exact (R.mem_fibre _ _ _).mpr ((F.rootImage_fibre_subset hinj R a b u hVF hRV)
        (((F.pushCoordinateRoots hinj R).mem_fibre b u y).mp hy))
    exact (Finset.card_le_card hSub).trans (hN _ _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    exact Nat.zero_le _

end CarriedChainLift
end DiamondIntegral.Section6
