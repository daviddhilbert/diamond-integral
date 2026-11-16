import «section 6».RVTagConjugation
import «section 2».BadFibreChoice

/-! A finite VF exception set cannot change the contraction of a unary
proper covariant map. Its actual fixed-input/output-label graph sources
are open. The comparison function need not be continuous or definable.
This addresses the finite-point allowance in Lemma 6.38 independently
of any proposed preparation invariant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ProperCovariant

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s m : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem tags_eq_of_finite_vf_exceptions
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : ProperCovariant f) (g : A → B)
    (hg : ∀ p q : A, p.val.2 = q.val.2 → (g p).val.2 = (g q).val.2)
    (E : Set (Fin 1 → VF M)) (hE : E.Finite)
    (hAway : ∀ p : A, p.val.1 ∉ E → (f p).val.2 = (g p).val.2) :
    ∀ p : A, (f p).val.2 = (g p).val.2 := by
  intro p
  let U := graphFibreSource f p.val.2 (f p).val.2
  obtain ⟨α,β,hαdef,hβdef,hInv,hRange,hCov⟩ := hf.radii p.val.2 (f p).val.2
  have hOpen : IsOpen U := hInv.isOpen hv
  have hNonempty : U.Nonempty := ⟨p.val.1,(f p).val.1,p,rfl,rfl⟩
  obtain ⟨x,hx,hxE⟩ := ((vf_open_nonempty_infinite hv (by decide : 0 < 1) U
    hOpen hNonempty).sdiff hE).nonempty
  obtain ⟨y,q,hq,hfq⟩ := hx
  have hqVF : q.val.1 = x := congrArg Prod.fst hq
  have hqTags := congrArg Prod.snd hq
  change q.val.2 = p.val.2 at hqTags
  have hqNot : q.val.1 ∉ E := fun he => hxE (hqVF ▸ he)
  have hfqTags := congrArg Prod.snd hfq
  change (f q).val.2 = (f p).val.2 at hfqTags
  exact hfqTags.symm.trans ((hAway q hqNot).trans (hg q p hqTags))

theorem whole_tag_fibres_of_finite_vf_exceptions
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : ProperCovariant f) (hSurj : Function.Surjective f) (g : A → B)
    (hg : ∀ p q : A, (g p).val.2 = (g q).val.2 ↔ p.val.2 = q.val.2)
    (E : Set (Fin 1 → VF M)) (hE : E.Finite)
    (hAway : ∀ p : A, p.val.1 ∉ E → (f p).val.2 = (g p).val.2) :
    MapsWholeTagFibres f := by
  have hTags := tags_eq_of_finite_vf_exceptions hv f hf g (fun p q he => (hg p q).mpr he) E hE hAway
  apply mapsWholeTagFibres_of_tag_equivalence f hSurj
  intro p q
  rw [hTags p,hTags q,hg p q]

end DiamondIntegral.Section6.ProperCovariant
