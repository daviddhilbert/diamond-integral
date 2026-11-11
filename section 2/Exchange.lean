import «section 2».Bases
import Section3.VFExchange
import Section3.RVExchange

/-! Lemma 2.14: exchange for single elements over the same fixed base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The scalar VF assertion of Lemma 2.14, over the original field base. -/
theorem lemma_2_14_vf (S : Set M) (F : VFFieldBase S) (a b : VF M)
    (hab : AlgebraicAt (insert b.val S) .vf a.val)
    (ha : ¬ AlgebraicAt S .vf a.val) : AlgebraicAt (insert a.val S) .vf b.val :=
  lemma_3_6_vf S F a b hab ha

/-- The scalar RV assertion of Lemma 2.14. Smallness and saturation are the
actual model-theoretic hypotheses; the base is unchanged. The stronger
RV-infinity version includes the single absorbing element. -/
theorem lemma_2_14_rv {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (a b : RVInfinity M)
    (hab : AlgebraicAt (insert b.val S) .rv a.val)
    (ha : ¬ AlgebraicAt S .rv a.val) : AlgebraicAt (insert a.val S) .rv b.val :=
  GammaParameters.lemma_3_6_rv hκ hs h00 S hsmall b a hab ha

end DiamondIntegral.Section2
