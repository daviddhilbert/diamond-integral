import «section 5».RESBijectionPromotion
import «section 5».OriginalSortedPredicates

/-! Products of native RES row schemata retain their literal raw domains
and an explicit product bound on full value supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def productLeftParameterIndex (p a b : ℕ) : Fin (p+a) → Fin (p+(b+a)) :=
  Fin.append (Fin.castAdd (b+a)) (fun i => Fin.natAdd p (headIndex b a i))
def productRightParameterIndex (p a b : ℕ) : Fin (p+b) → Fin (p+(b+a)) :=
  Fin.append (Fin.castAdd (b+a)) (fun i => Fin.natAdd p (tailIndex b a i))

theorem productLeftParameterIndex_row (z : Fin p → M) (w : Fin (b+a) → M) :
    Fin.append z w ∘ productLeftParameterIndex p a b = Fin.append z (w ∘ headIndex b a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply, productLeftParameterIndex, Fin.append_left, Fin.append_right]

theorem productRightParameterIndex_row (z : Fin p → M) (w : Fin (b+a) → M) :
    Fin.append z w ∘ productRightParameterIndex p a b = Fin.append z (w ∘ tailIndex b a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply, productRightParameterIndex, Fin.append_left, Fin.append_right]

def RESSetSchema.product (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) :
    RESSetSchema B p (b+a) sp := by
  let st := Fin.append sp (fun _ : Fin (b+a) => .rv)
  let A := productLeftParameterIndex p a b
  let C := productRightParameterIndex p a b
  have hA : ∀ i, Fin.append sp (fun _ : Fin a => .rv) i = st (A i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st, A, productLeftParameterIndex, Fin.append_left, Fin.append_right]
  have hC : ∀ i, Fin.append sp (fun _ : Fin b => .rv) i = st (C i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st, C, productRightParameterIndex, Fin.append_left, Fin.append_right]
  exact ⟨⟨{w | w ∈ sortedUniverse st ∧ w ∘ A ∈ F.domain.val ∧ w ∘ C ∈ G.domain.val},
    ((OriginalSortedPredicate.of_definable F.domain.property).pullback A hA).conj
      ((OriginalSortedPredicate.of_definable G.domain.property).pullback C hC)⟩,
    F.valueBound * G.valueBound⟩

theorem RESSetSchema.product_row (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (z : Fin p → M) (w : Fin (b+a) → M) :
    w ∈ (F.product G).rowDomain z ↔
      w ∘ headIndex b a ∈ F.rowDomain z ∧ w ∘ tailIndex b a ∈ G.rowDomain z := by
  change (_ ∈ sortedUniverse _ ∧ _ ∧ _) ↔ _
  rw [productLeftParameterIndex_row, productRightParameterIndex_row]
  constructor
  · exact fun h => h.2
  · rintro ⟨hf, hg⟩
    refine ⟨?_, hf, hg⟩
    have hhead (i : Fin a) : iRV (w (headIndex b a i)) := by
      simpa only [Function.comp_apply, Fin.append_right, sortEval, iRV] using
        F.domain.property.proper _ hf (Fin.natAdd p i)
    have htail (i : Fin b) : iRV (w (tailIndex b a i)) := by
      simpa only [Function.comp_apply, Fin.append_right, sortEval, iRV] using
        G.domain.property.proper _ hg (Fin.natAdd p i)
    have hw := forall_join_property iRV b a (w ∘ headIndex b a) (w ∘ tailIndex b a) hhead htail
    rw [join_reconstruct] at hw
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using F.domain.property.proper _ hf (Fin.castAdd a j)
    · simpa only [Fin.append_right, sortEval, iRV] using hw j

theorem rawRVValuePattern_join (x : Fin a → M) (y : Fin b → M) :
    rawRVValuePattern (join b a x y) = join b a (rawRVValuePattern x) (rawRVValuePattern y) := by
  exact comp_join (fun t : M => if h : iRV t then Values.vrv ⟨t, h⟩ else Values.infinity) b a x y

theorem RESSetSchema.product_value_image (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (z : Fin p → M) :
    rawRVValuePattern '' (F.product G).rowDomain z =
      (fun xy => join b a xy.1 xy.2) ''
        ((rawRVValuePattern '' F.rowDomain z) ×ˢ (rawRVValuePattern '' G.rowDomain z)) := by
  ext γ
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hf, hg⟩ := (F.product_row G z w).mp hw
    refine ⟨⟨rawRVValuePattern (w ∘ headIndex b a), rawRVValuePattern (w ∘ tailIndex b a)⟩,
      ⟨⟨_, hf, rfl⟩, ⟨_, hg, rfl⟩⟩, ?_⟩
    change join b a (rawRVValuePattern (w ∘ headIndex b a))
      (rawRVValuePattern (w ∘ tailIndex b a)) = rawRVValuePattern w
    rw [← rawRVValuePattern_join, join_reconstruct]
  · rintro ⟨⟨γ, δ⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    refine ⟨join b a x y, (F.product_row G z _).mpr ?_, rawRVValuePattern_join x y⟩
    exact ⟨by simpa only [Function.comp_def, join_head] using hx,
      by simpa only [Function.comp_def, join_tail] using hy⟩

theorem RESSetSchema.product_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) : (F.product G).Valid hc z := by
  obtain ⟨hz, hf, hn⟩ := (F.valid_iff_finite_values hc z).mp hF
  obtain ⟨_, hg, hm⟩ := (G.valid_iff_finite_values hc z).mp hG
  apply ((F.product G).valid_iff_finite_values hc z).mpr
  rw [F.product_value_image G z]
  refine ⟨hz, (hf.prod hg).image _, ?_⟩
  exact (Set.ncard_image_le (hf.prod hg)).trans (by
    rw [Set.ncard_prod]
    exact Nat.mul_le_mul hn hm)

end DiamondIntegral.Section5
