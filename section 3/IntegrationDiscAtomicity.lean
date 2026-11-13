import «section 3».IntegrationDiscInverse
import «section 3».IntegrationFullFiniteSupport
import IntegrationSection3ACVF.CompleteTypeBallAtomicity
import IntegrationSection3ACVF.BallEnlargementGeometry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Checked [18] 3.3 and 3.4 in the native finite-disc parameter syntax.
Finite real support supplies the ball theorem at every enlarged real base
used in the local polydisc induction. No selected code is named. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationFiniteDiscNames_snoc {k : ℕ} (closed : Fin k → Bool)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (isClosed : Bool) (c : Section2.VF M) (γ : Section2.Gamma M) :
    Section2.finitePolydiscNames (Fin.snoc closed isClosed) (Fin.snoc a c) (Fin.snoc δ γ) =
      Fin.snoc (Section2.finitePolydiscNames closed a δ)
        (if isClosed then Section2.closedDiscCode c γ.val else Section2.openDiscCode c γ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Section2.finitePolydiscNames,Fin.snoc_last]
  · simp only [Section2.finitePolydiscNames,Fin.snoc_castSucc]

theorem integrationDiscBase_snoc (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (isClosed : Bool) (c : Section2.VF M) (γ : Section2.Gamma M) :
    integrationDiscBase B (Fin.snoc closed isClosed) (Fin.snoc a c) (Fin.snoc δ γ) =
      (integrationDiscBase B closed a δ).adjoin
        (Sum.inl (if isClosed then Section2.closedDiscCode c γ.val else Section2.openDiscCode c γ)) := by
  simp only [integrationDiscBase,integrationFiniteDiscNames_snoc,Fin.range_snoc,Set.image_insert_eq,
    Set.union_insert,ImaginaryParameters.Base.adjoin]

theorem integrationDiscSorted (B : GammaParameters.Base (M := M)) {k n : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (sn : Fin n → SortTag) :
    FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) (GammaParameters.sortedUniverse sn) := by
  have hs := GammaParameters.real_definableOverBase B sn _ (GammaParameters.sortedUniverse_definable B.real sn)
  exact FullBaseAtomicity.OverBase.mono (integrationGammaDefinable hs) Set.Subset.rfl
    (integrationDiscBase_mono B closed a δ)

theorem integrationDiscAtomic {B : GammaParameters.Base (M := M)} {k n : ℕ}
    {closed : Fin k → Bool} {a : Fin k → Section2.VF M} {δ : Fin k → Section2.Gamma M}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : Section2.IsAtomicOverFiniteDiscNames B closed a δ sn A) :
    FullGammaAtomicity.AtomicTuple (integrationDiscBase B closed a δ) A := by
  refine ⟨integrationFiniteDiscDefinable_to_full B closed a δ sn A hA.1,?_⟩
  intro T hT
  have hcut := FullBaseAtomicity.OverBase.inter hT (integrationDiscSorted B closed a δ sn)
  have hn := integrationFiniteDiscDefinable_of_full B closed a δ sn
    (T ∩ GammaParameters.sortedUniverse sn) (fun _ h => h.2) hcut
  rcases hA.2.2.2 _ hn with h | h
  · exact Or.inl (fun _ hb => (h hb).1)
  · exact Or.inr (Set.disjoint_left.mpr fun b hb ht =>
      Set.disjoint_left.mp h hb ⟨ht,hA.2.2.1 hb⟩)

theorem integrationDiscAtomic_to_native {B : GammaParameters.Base (M := M)} {k n : ℕ}
    {closed : Fin k → Bool} {a : Fin k → Section2.VF M} {δ : Fin k → Section2.Gamma M}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : FullGammaAtomicity.AtomicTuple (integrationDiscBase B closed a δ) A)
    (hne : A.Nonempty) (hp : A ⊆ GammaParameters.sortedUniverse sn) :
    Section2.IsAtomicOverFiniteDiscNames B closed a δ sn A := by
  refine ⟨integrationFiniteDiscDefinable_of_full B closed a δ sn A (fun _ h => hp h) hA.1,hne,hp,?_⟩
  intro T hT
  exact hA.2 T (integrationFiniteDiscDefinable_to_full B closed a δ sn T hT)

theorem integrationDiscUnaryComplete {B : GammaParameters.Base (M := M)} {k : ℕ}
    {closed : Fin k → Bool} {a : Fin k → Section2.VF M} {δ : Fin k → Section2.Gamma M}
    {A : Set (Fin 1 → M)}
    (hA : Section2.GeneratesTypeOverFiniteDiscNames B closed a δ (fun _ => .vf) A) :
    FullBallCoset.CompleteType (integrationDiscBase B closed a δ) {x | ![x] ∈ A} := by
  intro T hT
  have hc := FullBaseAtomicity.OverBase.inter hT (integrationDiscSorted B closed a δ (fun _ : Fin 1 => .vf))
  have hn := integrationFiniteDiscDefinable_of_full B closed a δ (fun _ : Fin 1 => .vf)
    ({z | z 0 ∈ T} ∩ GammaParameters.sortedUniverse (fun _ => .vf)) (fun _ h => h.2) hc
  rcases hA.2.2 _ hn with hs | hd
  · exact Or.inl (fun _ hx => (hs hx).1)
  · exact Or.inr (Set.disjoint_left.mpr fun x hx ht =>
      Set.disjoint_left.mp hd hx ⟨ht,hA.2.1 hx⟩)

theorem integrationDiscUnaryAtomic_to_native {B : GammaParameters.Base (M := M)} {k : ℕ}
    {closed : Fin k → Bool} {a : Fin k → Section2.VF M} {δ : Fin k → Section2.Gamma M}
    {U : Set M} (hU : AdjoinBall.AtomicOver (integrationDiscBase B closed a δ) U)
    (hne : U.Nonempty) (hp : U ⊆ {x | iVF x}) :
    Section2.IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ U} := by
  have ht : FullGammaAtomicity.AtomicTuple (integrationDiscBase B closed a δ) {z : Fin 1 → M | z 0 ∈ U} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.unary_tuple_atomic_iff.mpr hU
  apply integrationDiscAtomic_to_native ht
  · obtain ⟨x,hx⟩ := hne
    exact ⟨![x],hx⟩
  · intro z hz i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
    simpa only [sortEval,iVF,Set.mem_ofPred_eq] using hp hz

theorem integrationDisc_center_mem (isClosed : Bool) (c : Section2.VF M) (γ : Section2.Gamma M) :
    c.val ∈ BallImaginaries.underlying
      (if isClosed then Section2.closedDiscCode c γ.val else Section2.openDiscCode c γ) := by
  cases isClosed with
  | false =>
    rw [ite_eq_right Bool.false_ne_true,integrationOpenDisc_gammaBall]
    exact BallEnlargementGeometry.gammaBall_centre_mem c γ true
  | true =>
    rw [ite_eq_left rfl,integrationClosedDisc_gammaBall]
    exact BallEnlargementGeometry.gammaBall_centre_mem c γ false

theorem integrationAtomicDiscGammaBaseChangeInput (B : GammaParameters.Base (M := M)) :
    Section2.AtomicDiscGammaBaseChangeInput B := by
  intro h00 hΓ k n closed a δ sn A hA γ
  obtain ⟨ρ,hρ,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let C := integrationDiscBase B closed a δ
  have hd : FullGammaSyntax.Scalar C {ρ} :=
    FullBaseAtomicity.OverBase.mono hρ Set.Subset.rfl (integrationDiscBase_mono B closed a δ)
  have ht := FullGammaAtomicity.lemma_3_3_one h00 C ρ hd hρ1 (integrationDiscAtomic hA) γ
  rw [← integrationDiscBase_adjoinGamma] at ht
  exact (integrationDiscAtomic_to_native ht hA.2.1 hA.2.2.1).2

theorem integrationUnaryDiscAtomicityInput_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ) :
    Section2.UnaryDiscAtomicityInput B := by
  intro h00 hΓ k closed a δ A hA isClosed c γ hsub
  obtain ⟨ρ,_,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let C := integrationDiscBase B closed a δ
  let D := if isClosed then Section2.closedDiscCode c γ.val else Section2.openDiscCode c γ
  have ha : BallImaginaries.underlying D ⊆ {x | ![x] ∈ A} := by
    intro x hx
    exact hsub (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ BallImaginaries.underlying D} from hx)
  have hu := CompleteTypeBallAtomicity.lemma_3_4 hκ hs C hsmall h00 ρ hρ1
    (integrationDiscUnaryComplete hA) D ha
  rw [← integrationDiscBase_snoc] at hu
  exact integrationDiscUnaryAtomic_to_native hu ⟨c.val,integrationDisc_center_mem isClosed c γ⟩
    (BallImaginaries.underlying_subset_vf D)
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationUnaryDiscAtomicityInput {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : GammaParameters.Base (M := M)) :
    Section2.UnaryDiscAtomicityInput B := by
  intro h00 hΓ k closed a δ A hA isClosed c γ hsub
  obtain ⟨ρ,_,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let C := integrationDiscBase B closed a δ
  let D := if isClosed then Section2.closedDiscCode c γ.val else Section2.openDiscCode c γ
  have ha : BallImaginaries.underlying D ⊆ {x | ![x] ∈ A} := by
    intro x hx
    exact hsub (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ BallImaginaries.underlying D} from hx)
  have hu := integrationFullBallAtomicity hκ hs h00 C ρ hρ1 (integrationDiscUnaryComplete hA) D ha
  rw [← integrationDiscBase_snoc] at hu
  exact integrationDiscUnaryAtomic_to_native hu ⟨c.val,integrationDisc_center_mem isClosed c γ⟩
    (BallImaginaries.underlying_subset_vf D)
end DiamondIntegral.Section3
