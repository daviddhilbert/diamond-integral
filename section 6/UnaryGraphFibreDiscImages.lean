import «section 6».MixedPairedDiscFibres

/-! Scalar paired-disc equality is exactly equality of the full mixed
sets with both old RV tuples fixed. Every source and target point,
including the center, participates in the actual bijection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unaryGraphFibreMap_at_source (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (p : A)
    (hu : p.val.2=u) (hp : p.val.1 0 ∈ unaryGraphFibreSource f u v) :
    (f p).val=(fun _ : Fin 1 => unaryGraphFibreMap f u v (p.val.1 0),v) := by
  obtain ⟨a,ha,hfa⟩ := graphFibreMap_graph f u v hp
  have hap : a=p := Subtype.ext (ha.trans (Prod.ext (scalarGraphFibre_tuple_eta p.val.1) hu.symm))
  subst a
  exact hfa.trans (Prod.ext (scalarGraphFibre_tuple_eta _).symm rfl)

theorem unaryGraphFibreSource_at (f : Map A B) (p : A) :
    p.val.1 0 ∈ unaryGraphFibreSource f p.val.2 (f p).val.2 := by
  refine ⟨(f p).val.1,p,?_,rfl⟩
  exact Prod.ext (scalarGraphFibre_tuple_eta p.val.1).symm rfl

theorem unaryGraphFibreMap_at (f : Map A B) (p : A) :
    unaryGraphFibreMap f p.val.2 (f p).val.2 (p.val.1 0)=(f p).val.1 0 := by
  exact (congrArg (fun q : Mixed M 1 s => q.1 0)
    (unaryGraphFibreMap_at_source f p.val.2 (f p).val.2 p rfl (unaryGraphFibreSource_at f p))).symm

theorem unaryGraphFibreDisc_mixed_image_iff (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (D E : Set (VF M))
    (hD : D ⊆ unaryGraphFibreSource f u v) (hImage : unaryGraphFibreMap f u v '' D=E) (q : B) :
    q.val.1 0 ∈ E ∧ q.val.2=v ↔
      ∃ p : A,p.val.1 0 ∈ D ∧ p.val.2=u ∧ f p=q := by
  constructor
  · rintro ⟨hq,hqv⟩
    obtain ⟨x,hx,hFx⟩ := hImage.symm ▸ hq
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v (hD hx)
    have hpx : p.val.1 0=x := congrArg (fun a : Mixed M 1 r => a.1 0) hp
    have hpu : p.val.2=u := congrArg Prod.snd hp
    refine ⟨p,hpx.symm ▸ hx,hpu,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i
      exact (congrArg (fun a : Mixed M 1 s => a.1 0) hfp).trans hFx
    · exact (congrArg Prod.snd hfp).trans hqv.symm
  · rintro ⟨p,hp,hpu,rfl⟩
    have hfp := unaryGraphFibreMap_at_source f u v p hpu (hD hp)
    refine ⟨?_,congrArg Prod.snd hfp⟩
    rw [hfp]
    exact hImage ▸ Set.mem_image_of_mem (unaryGraphFibreMap f u v) hp

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_mixed_paired_discs_at_point
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f) (p : A) :
    ∃ ρ : Gamma M ≃o Gamma M, ∃ γ₀ : Gamma M,∀ γ : Gamma M,γ₀ ≤ γ →
      centeredGammaDisc (p.val.1 0) γ ⊆ unaryGraphFibreSource f p.val.2 (f p).val.2 ∧
      ∀ q : B, q.val.1 0 ∈ centeredGammaDisc ((f p).val.1 0) (ρ γ) ∧ q.val.2=(f p).val.2 ↔
        ∃ a : A,a.val.1 0 ∈ centeredGammaDisc (p.val.1 0) γ ∧ a.val.2=p.val.2 ∧ f a=q := by
  obtain ⟨ρ,γ₀,hDiscs⟩ := paired_discs_for_unary_graph_fibre hc hκ hs hsmall hv f h
    p.val.2 (f p).val.2 (p.val.1 0) (unaryGraphFibreSource_at f p)
  refine ⟨ρ,γ₀,fun γ hγ => ?_⟩
  obtain ⟨hSource,hTarget,hImage⟩ := hDiscs γ hγ
  rw [unaryGraphFibreMap_at f p] at hImage
  exact ⟨hSource,fun q => unaryGraphFibreDisc_mixed_image_iff f p.val.2 (f p).val.2 _ _ hSource hImage q⟩

end DiamondIntegral.Section6
