import «section 6».AffineTailDifferentiability
import Section9.AffineLiftJacobian

/-! Transfer full head and coefficient derivatives to an actual mixed
affine lift. One fixed-label ball supports all coefficient charts and
the ambient lift chart simultaneously. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

theorem mixedDerivative_affineTail_of_coefficient_derivatives
    (U V : MeasuredRVObject (M := M) S (k+m))
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft k m)).FiniteFibres)
    (F : Map (rvLift (rvFiniteHead ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead ⟨V.object,V.finiteVolume⟩ (productLeft k m) hV).obj))
    (G : Map (rvLift U.object) (rvLift V.object))
    (a b c : Map (rvLift (rvFiniteHead ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (hG : ∀ p : rvLift U.object,
      let x := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU p
      (G p).val = (productTuple (F x).val.1
        (affineTail (a x).val (b x).val (c x).val (p.val.1 ∘ productRight k m)),(F x).val.2))
    (p : rvLift U.object)
    (hF : ∃ L, HasMixedVFDerivativeAt F
      (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU p) L)
    (ha : ∃ L, HasMixedVFTupleDerivativeAt a
      (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU p) L)
    (hb : ∃ L, HasMixedVFTupleDerivativeAt b
      (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU p) L)
    (hc : ∃ L, HasMixedVFTupleDerivativeAt c
      (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU p) L) :
    ∃ L, HasMixedVFDerivativeAt G p L := by
  let H := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft k m) hU
  let l := productLeft k m
  obtain ⟨L,F₀,⟨ρF,hρF⟩,hF₀⟩ := hF
  obtain ⟨La,a₀,⟨ρa,hρa⟩,ha₀⟩ := ha
  obtain ⟨Lb,b₀,⟨ρb,hρb⟩,hb₀⟩ := hb
  obtain ⟨Lc,c₀,⟨ρc,hρc⟩,hc₀⟩ := hc
  obtain ⟨ρ₀,hρ₀⟩ := exists_fixed_label_ball_in_rvLift U p
  let δ := max ρ₀ (max ρF (max ρa (max ρb ρc)))
  have h₀ : ρ₀ ≤ δ := le_max_left _ _
  have hFδ : ρF ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have haδ : ρa ≤ δ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbδ : ρb ≤ δ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hcδ : ρc ≤ δ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨D,hD⟩ := vfdifferentiableAt_liftWithAffineTail F₀ a₀ b₀ c₀ p.val.1
    ⟨L,hF₀⟩ ⟨La,ha₀⟩ ⟨Lb,hb₀⟩ ⟨Lc,hc₀⟩
  refine ⟨D,liftWithAffineTail F₀ a₀ b₀ c₀,⟨δ,fun z hz => ?_⟩,hD⟩
  let q : rvLift U.object := ⟨(z,p.val.2),hρ₀ z (vfBall_anti h₀ hz)⟩
  have hHead : z ∘ l ∈ vfBall (H p).val.1 δ := fun i => hz (l i)
  obtain ⟨hzF,hFval⟩ := hρF (z ∘ l) (vfBall_anti hFδ hHead)
  obtain ⟨hza,haval⟩ := hρa (z ∘ l) (vfBall_anti haδ hHead)
  obtain ⟨hzb,hbval⟩ := hρb (z ∘ l) (vfBall_anti hbδ hHead)
  obtain ⟨hzc,hcval⟩ := hρc (z ∘ l) (vfBall_anti hcδ hHead)
  refine ⟨q.property,?_⟩
  change (G q).val = _
  rw [hG q]
  change (productTuple (F (H q)).val.1
    (affineTail (a (H q)).val (b (H q)).val (c (H q)).val (z ∘ productRight k m)),
      (F (H q)).val.2) = _
  have hFq : (F (H q)).val = (F₀ (z ∘ l),(F (H p)).val.2) := hFval
  have haq : (a (H q)).val = a₀ (z ∘ l) := haval
  have hbq : (b (H q)).val = b₀ (z ∘ l) := hbval
  have hcq : (c (H q)).val = c₀ (z ∘ l) := hcval
  rw [hFq,haq,hbq,hcq]
  exact Prod.ext rfl (congrArg Prod.snd (hG p)).symm

end DiamondIntegral.Section6
