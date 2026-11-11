import «section 2».DiscNameProducts
import Section3.OpenBallCenters

/-! Uniform real presentations of open polydiscs. Every radius is nonzero;
the presentation is auxiliary and does not enter the ground base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawOpenPolydiscProper {n : ℕ} (d : Fin (n+n) → M) : Prop :=
  ∀ i, OpenBallCodes.Proper (![d (Fin.castAdd n i),d (Fin.natAdd n i)])

def rawOpenPolydisc {n : ℕ} (d : Fin (n+n) → M) : Set (Fin n → M) :=
  {x | ∀ i, x i ∈ OpenBallCodes.rawBall (![d (Fin.castAdd n i),d (Fin.natAdd n i)])}

theorem rawOpenPolydiscProper_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {d : Fin (n+n) → M | rawOpenPolydiscProper d} := by
  have hz : S.DefinableFun LRV (fun _ : Fin (n+n) → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have h (i : Fin n) :=
    (((definableAt_sort S .vf).raw_definable.preimage_comp
      (fun _ : Fin 1 => Fin.castAdd n i)).inter
      ((definableAt_sort S .vf).raw_definable.preimage_comp
        (fun _ : Fin 1 => Fin.natAdd n i))).inter
      (((Set.DefinableFun.proj LRV (i := Fin.natAdd n i)).ofPred_eq hz).compl)
  convert Set.definable_iInter_of_finite h using 1
  ext d
  simp only [rawOpenPolydiscProper,OpenBallCodes.Proper,Set.mem_ofPred_eq,
    Set.mem_iInter,Set.mem_inter_iff,Set.mem_preimage,Set.mem_compl_iff]
  apply forall_congr'
  intro i
  simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  tauto

theorem rawOpenPolydisc_membership_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {z : Fin (n+n) ⊕ Fin n → M |
      z ∘ Sum.inr ∈ rawOpenPolydisc (z ∘ Sum.inl)} := by
  let idx (i : Fin n) : Fin 3 → Fin (n+n) ⊕ Fin n :=
    ![.inl (Fin.castAdd n i),.inl (Fin.natAdd n i),.inr i]
  have h (i : Fin n) := (OpenBallCodes.membership_raw_definable S).preimage_comp (idx i)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq]
  apply forall_congr'
  intro i
  have he : Fin.init (z ∘ idx i) = ![z (.inl (Fin.castAdd n i)),z (.inl (Fin.natAdd n i))] := by
    funext j
    fin_cases j <;> rfl
  change _ ↔ _ ∈ OpenBallCodes.rawBall (Fin.init (z ∘ idx i))
  rw [he]
  rfl

theorem rawOpenPolydisc_proper {n : ℕ} (d : Fin (n+n) → M) :
    rawOpenPolydisc d ⊆ GammaParameters.sortedUniverse (fun _ => .vf) :=
  fun _ hx i => (hx i).2.1

theorem rawOpenPolydisc_named (a r : Fin n → VF M) (hr : ∀ i, r i ≠ 0) :
    rawOpenPolydisc (Fin.append (vfValues a) (vfValues r)) =
      namedPolydisc (fun _ => false) a (fun i => finiteValue (r i) (hr i)) := by
  obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  have hball (i : Fin n) : OpenBallCodes.rawBall (![(a i).val,(r i).val]) =
      BallImaginaries.underlying (openDiscCode (a i) (finiteValue (r i) (hr i))) := by
    ext x
    by_cases hx : iVF x
    · let y : VF M := ⟨x,hx⟩
      have hq : OpenBallCodes.Proper (![(a i).val,(r i).val]) :=
        ⟨by intro j; fin_cases j; exact (a i).property; exact (r i).property,
          fun he => hr i (Subtype.ext he)⟩
      change y ∈ OpenBallCodes.ball (![(a i).val,(r i).val]) ↔
        y ∈ discPoints (openDiscCode (a i) (finiteValue (r i) (hr i)))
      rw [OpenBallCodes.ball_eq_open v hv _ hq,openDiscCode_points v hv _ _ (hr i)]
      rfl
    · exact ⟨fun h => (hx h.2.1).elim,fun h => (hx (disc_underlying_subset_vf _ h)).elim⟩
  ext x
  apply forall_congr'
  intro i
  change x i ∈ OpenBallCodes.rawBall _ ↔ _
  simp only [Fin.append_left,Fin.append_right]
  exact Set.ext_iff.mp (hball i) (x i)

theorem rawOpenPolydisc_presentation {n : ℕ} (d : Fin (n+n) → M)
    (hd : rawOpenPolydiscProper d) :
    ∃ (a : Fin n → VF M) (δ : Fin n → Gamma M),
      rawOpenPolydisc d = namedPolydisc (fun _ => false) a δ := by
  let a : Fin n → VF M := fun i => ⟨d (Fin.castAdd n i),(hd i).1 0⟩
  let r : Fin n → VF M := fun i => ⟨d (Fin.natAdd n i),(hd i).1 1⟩
  have hr (i) : r i ≠ 0 := fun he => (hd i).2 (congrArg Subtype.val he)
  have he : Fin.append (vfValues a) (vfValues r) = d := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left,vfValues,a]
    · simp only [Fin.append_right,vfValues,r]
  exact ⟨a,fun i => finiteValue (r i) (hr i),he ▸ rawOpenPolydisc_named a r hr⟩

end DiamondIntegral.Section2
