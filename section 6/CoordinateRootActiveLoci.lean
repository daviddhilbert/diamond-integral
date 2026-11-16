import «section 6».ScalarIndicatorMaps

/-! The actual projected nonempty-root locus, its full original-base
graph, and exact transport under protected freezing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def activeBase (R : CoordinateRootFamily A) := (vfDropLast R.roots).image

theorem activeBase_subset (R : CoordinateRootFamily A) :
    R.activeBase.carrier ⊆ (vfDropLast A).image.carrier := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,R.subset p.property⟩,hp⟩

theorem mem_activeBase (R : CoordinateRootFamily A) (b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    (b,u) ∈ R.activeBase.carrier ↔ (R.fibre b u).Nonempty := by
  constructor
  · rintro ⟨p,hp⟩
    have hB : Fin.init p.val.1 = b := congrArg Prod.fst hp
    have hU : p.val.2 = u := congrArg Prod.snd hp
    refine ⟨p.val.1 (Fin.last n),(R.mem_fibre b u _).mpr ?_⟩
    rw [← hB,← hU,Fin.snoc_init_self]
    exact p.property
  · rintro ⟨x,hx⟩
    exact ⟨⟨(Fin.snoc b x,u),(R.mem_fibre b u x).mp hx⟩,by
      apply Prod.ext
      · change Fin.init (Fin.snoc b x : Fin (n+1) → VF M) = b
        rw [Fin.init_snoc]
      · rfl⟩

theorem frozen_activeBase (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (p : Mixed M n r) :
    p ∈ (R.frozen balls centers j hsep hballs hcenters hprod).activeBase.carrier ↔
      FMT.mixedFamilyFreeze balls centers j p ∈ R.activeBase.carrier := by
  rw [mem_activeBase,frozen_fibre,mem_activeBase]
  rfl

end DiamondIntegral.Section6.CoordinateRootFamily
