import «section 6».CoordinateRootActiveLoci

/-! Full bundle geometry and bijectivity force forward as well as
inverse context compatibility. Consequently the actual root indicator
is transported exactly by a whole carried lower-dimensional chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CarriedChainLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

theorem output_point_on_fibre (h00 : M ⊨ Axioms.ACVF00)
    (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f) (p a : X.bundle)
    (hVF : Fin.init p.val.1 = Fin.init a.val.1) (hRV : p.val.2 = a.val.2) :
    (F.map p).val = (Fin.snoc (Fin.init (F.map a).val.1) (p.val.1 (Fin.last n)),(F.map a).val.2) := by
  let q : Mixed M (n+1) F.target.arity :=
    (Fin.snoc (Fin.init (F.map a).val.1) (p.val.1 (Fin.last n)),(F.map a).val.2)
  have hQ : q ∈ F.target.bundle.carrier := by
    constructor
    · simpa only [q,Fin.init_snoc] using (F.map a).property.1
    · change rv M (q.1 (Fin.last n)) = q.2 F.target.freeLabel
      change rv M ((Fin.snoc (Fin.init (F.map a).val.1) (p.val.1 (Fin.last n)) : Fin (n+1) → VF M) (Fin.last n)) = _
      rw [Fin.snoc_last]
      calc
        rv M (p.val.1 (Fin.last n)) = p.val.2 X.freeLabel := p.property.2
        _ = a.val.2 X.freeLabel := congrFun hRV X.freeLabel
        _ = rv M (a.val.1 (Fin.last n)) := a.property.2.symm
        _ = rv M ((F.map a).val.1 (Fin.last n)) := congrArg (rv M) (F.carried a).symm
        _ = (F.map a).val.2 F.target.freeLabel := (F.map a).property.2
  obtain ⟨b,hb⟩ := (F.special.bijective h00).surjective ⟨q,hQ⟩
  have hBpoint : (F.map b).val = q := congrArg Subtype.val hb
  have hBinit : Fin.init (F.map b).val.1 = Fin.init (F.map a).val.1 := by
    rw [hBpoint]
    exact Fin.init_snoc _ _
  have hBtags : (F.map b).val.2 = (F.map a).val.2 := by
    rw [hBpoint]
  have hInput := F.input_point_on_fibre hinj b a hBinit hBtags
  rw [hBpoint] at hInput
  change b.val = (Fin.snoc (Fin.init a.val.1)
    ((Fin.snoc (Fin.init (F.map a).val.1) (p.val.1 (Fin.last n)) : Fin (n+1) → VF M) (Fin.last n)),a.val.2) at hInput
  rw [Fin.snoc_last] at hInput
  rw [← hVF,← hRV,Fin.snoc_init_self] at hInput
  have hbp : b = p := Subtype.ext hInput
  exact (congrArg (fun z => (F.map z).val) hbp).symm.trans hBpoint

theorem root_indicator_transport (h00 : M ⊨ Axioms.ACVF00)
    (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle) (a : X.bundle) :
    (Fin.init (F.map a).val.1,(F.map a).val.2) ∈ (F.pushCoordinateRoots hinj R).activeBase.carrier ↔
      (Fin.init a.val.1,a.val.2) ∈ R.activeBase.carrier := by
  rw [CoordinateRootFamily.mem_activeBase,CoordinateRootFamily.mem_activeBase]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,(R.mem_fibre _ _ x).mpr ((F.rootImage_fibre_subset hinj R a _ _ rfl rfl)
      (((F.pushCoordinateRoots hinj R).mem_fibre _ _ x).mp hx))⟩
  · rintro ⟨x,hx⟩
    have hpRoot := (R.mem_fibre _ _ x).mp hx
    let p : X.bundle := ⟨(Fin.snoc (Fin.init a.val.1) x,a.val.2),R.subset hpRoot⟩
    have hpInit : Fin.init p.val.1 = Fin.init a.val.1 := Fin.init_snoc _ _
    have hPoint := F.output_point_on_fibre h00 hinj p a hpInit rfl
    have hpLast : p.val.1 (Fin.last n) = x := by
      change (Fin.snoc (Fin.init a.val.1) x : Fin (n+1) → VF M) (Fin.last n) = x
      rw [Fin.snoc_last]
    rw [hpLast] at hPoint
    exact ⟨x,((F.pushCoordinateRoots hinj R).mem_fibre _ _ x).mpr ⟨⟨p.val,hpRoot⟩,hPoint⟩⟩

end DiamondIntegral.Section6.CarriedChainLift
