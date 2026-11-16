import «section 6».BinaryRootTermination

/-! A carried lift has one input complementary tuple and one full
input RV tuple on each output complementary/RV fiber. The old lower
map is injective, every old tag is retained, and the carried coordinate
is fixed. No fiberwise inverse is supplied as an additional input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

theorem CarriedChainLift.same_input_context (F : CarriedChainLift (G := G) X f)
    (hinj : Function.Injective f) (p q : X.bundle)
    (hVF : Fin.init (F.map p).val.1 = Fin.init (F.map q).val.1)
    (hRV : (F.map p).val.2 = (F.map q).val.2) :
    Fin.init p.val.1 = Fin.init q.val.1 ∧ p.val.2 = q.val.2 := by
  have hTarget : F.target.oldPoint (F.map p) = F.target.oldPoint (F.map q) := by
    apply Subtype.ext
    apply Prod.ext
    · exact hVF
    · exact congrArg (fun u => u ∘ F.target.labels) hRV
  have hImage : f (X.oldPoint p) = f (X.oldPoint q) := Subtype.ext
    ((F.commutes p).symm.trans ((congrArg Subtype.val hTarget).trans (F.commutes q)))
  have hInput := hinj hImage
  obtain ⟨hle,hRetains⟩ := F.special.retainsRV
  refine ⟨congrArg (fun z : A => z.val.1) hInput,?_⟩
  funext i
  exact (hRetains p i).symm.trans ((congrFun hRV (rvTailIndex hle i)).trans (hRetains q i))

theorem CarriedChainLift.input_point_on_fibre (F : CarriedChainLift (G := G) X f)
    (hinj : Function.Injective f) (p a : X.bundle)
    (hVF : Fin.init (F.map p).val.1 = Fin.init (F.map a).val.1)
    (hRV : (F.map p).val.2 = (F.map a).val.2) :
    p.val = (Fin.snoc (Fin.init a.val.1) ((F.map p).val.1 (Fin.last n)),a.val.2) := by
  obtain ⟨hInputVF,hInputRV⟩ := F.same_input_context hinj p a hVF hRV
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (F.carried p).symm
    · simpa only [Fin.snoc_castSucc,Fin.init] using congrFun hInputVF j
  · exact hInputRV

theorem restricted_image_mem_iff_of_inverse {m t u : ℕ}
    {C P : DefSet (rawMixedSpace (M := M) m t) S} {D : DefSet (rawMixedSpace (M := M) m u) S}
    (g : Map C D) (hg : Function.Injective g) (hPC : P.carrier ⊆ C.carrier)
    (a : C) (q : Mixed M m u) (he : (g a).val = q) :
    q ∈ (g.restrict hPC).image.carrier ↔ a.val ∈ P.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    have hEq : a = (⟨p.val,hPC p.property⟩ : C) := hg (Subtype.ext (he.trans hp.symm))
    exact (congrArg Subtype.val hEq).symm ▸ p.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,he⟩

end DiamondIntegral.Section6
