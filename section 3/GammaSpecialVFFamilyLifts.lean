import «section 3».GammaVFProjectionChains

/-! Preparing a VF prefix of a mixed family is represented by an actual
Gamma special chain on the whole family. All complementary VF values
and all old RV parameters are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p k l a : ℕ}
variable {X : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}

structure GammaSpecialVFFamilyLift (T : SpecialBijection X Z) (H : DefSet (M := M) S (p+k) a)
    (hHX : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier X) where
  arity : ℕ
  target : DefSet (M := M) S (p+k) arity
  special : SpecialBijection H target
  graph : GammaChainDefinable B special.chain
  projection : Fin l → Fin arity
  square : ∀ q : H, vfRVProjection (Fin.castAdd k) projection (special.toMap q).val =
    (T.toMap ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hHX _ q.property⟩).val
  other : ∀ q : H, ∀ j : Fin k, (special.toMap q).val.1 (Fin.natAdd p j) = q.val.1 (Fin.natAdd p j)

theorem gammaSpecialVFFamilyLift_exists (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (H : DefSet (M := M) S (p+k) a) (hH : GammaSetDefinable B (carrier H))
    (hHX : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier X) :
    Nonempty (GammaSpecialVFFamilyLift (B := B) T H hHX) := by
  have hSub : ∀ q ∈ carrier H, vfRVProjection (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin a) q ∈ carrier X := by
    intro q hq
    have he : vfRVProjection (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin a) q =
        (q.1 ∘ Fin.castAdd k,Fin.elim0) := Prod.ext rfl (by funext i; exact Fin.elim0 i)
    exact he.symm ▸ hHX q hq
  obtain ⟨r,K,σ,W,hW,hWG,hSquare,_,hOther⟩ := gammaVFProjection_chain_lift T.chain hT
    (Fin.castAdd k) (by intro i j h; apply Fin.ext; exact congrArg (fun u : Fin (p+k) => u.val) h) H hH Fin.elim0 hSub none T.alternating
  have hSquare' : ∀ q : H, vfRVProjection (Fin.castAdd k) σ (W.toMap q).val =
      (T.toMap ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hHX _ q.property⟩).val := by
    intro q
    have he : (⟨vfRVProjection (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin a) q.val,hSub _ q.property⟩ : X) =
        ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hHX _ q.property⟩ :=
      Subtype.ext (Prod.ext rfl (by funext i; exact Fin.elim0 i))
    exact (hSquare q).trans (congrArg (fun u => (T.toMap u).val) he)
  refine ⟨⟨r,K,⟨W,hW⟩,hWG,σ,hSquare',?_⟩⟩
  intro q j
  apply hOther q (Fin.natAdd p j)
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem GammaSpecialVFFamilyLift.packed_square
    {T : SpecialBijection X Z} {H : DefSet (M := M) S (p+k) a}
    {hHX : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier X}
    (L : GammaSpecialVFFamilyLift (B := B) T H hHX) (q : H) :
    gammaRVProjection (Fin.append L.projection (gammaChainOldLabelIndex L.special.chain)) (L.special.toMap q).val =
      (Fin.append (T.toMap ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hHX _ q.property⟩).val.1 (q.val.1 ∘ Fin.natAdd p),
        Fin.append (T.toMap ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hHX _ q.property⟩).val.2 q.val.2) := by
  refine Prod.ext ?_ ?_
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      change (L.special.toMap q).val.1 (Fin.castAdd k j) = Fin.append _ _ (Fin.castAdd k j)
      rw [Fin.append_left]
      exact congrFun (congrArg Prod.fst (L.square q)) j
    · intro j
      change (L.special.toMap q).val.1 (Fin.natAdd p j) = Fin.append _ _ (Fin.natAdd p j)
      rw [Fin.append_right]
      exact L.other q j
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      change (L.special.toMap q).val.2 (Fin.append L.projection (gammaChainOldLabelIndex L.special.chain) (Fin.castAdd a j)) =
        Fin.append _ _ (Fin.castAdd a j)
      rw [Fin.append_left,Fin.append_left]
      exact congrFun (congrArg Prod.snd (L.square q)) j
    · intro j
      change (L.special.toMap q).val.2 (Fin.append L.projection (gammaChainOldLabelIndex L.special.chain) (Fin.natAdd l j)) =
        Fin.append _ _ (Fin.natAdd l j)
      rw [Fin.append_right,Fin.append_right]
      exact congrFun (gammaChain_old_labels L.special.chain q) j

end DiamondIntegral.Section3
