import «section 6».FrozenFocusRepair
import «section 2».RawDiscShapes

/-! The actual finite same-radius open-ball family around a finite
original-base exceptional set. All real representatives remain in its
defining pullback; no enumeration of the exceptions is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def pointedOpenBallCode (a r : VF M) (hr : r ≠ 0) : OpenBallCodes.Code M :=
  ⟨![a.val,r.val],⟨by intro i; fin_cases i; exact a.property; exact r.property,
    fun h => hr (Subtype.ext h)⟩⟩

def pointedOpenBall (a r : VF M) (hr : r ≠ 0) : OpenBallCodes.OpenBall M :=
  Quotient.mk _ (pointedOpenBallCode a r hr)

def exceptionalOpenBalls (E : Set (Fin 1 → VF M)) (r : VF M) (hr : r ≠ 0) :
    Set (OpenBallCodes.OpenBall M) := (fun a => pointedOpenBall (a 0) r hr) '' E

theorem exceptionalOpenBalls_finite (E : Set (Fin 1 → VF M)) (hE : E.Finite)
    (r : VF M) (hr : r ≠ 0) : (exceptionalOpenBalls E r hr).Finite :=
  hE.image _

theorem exceptionalOpenBalls_cover (E : Set (Fin 1 → VF M)) (r : VF M) (hr : r ≠ 0)
    (a : Fin 1 → VF M) (ha : a ∈ E) :
    ∃ D : exceptionalOpenBalls E r hr, a 0 ∈ vfOpenBall D.val := by
  refine ⟨⟨pointedOpenBall (a 0) r hr,⟨a,ha,rfl⟩⟩,?_⟩
  exact OpenBallCodes.raw_center_mem _ (pointedOpenBallCode (a 0) r hr).property

theorem rawOpenBallEquality_definable (S : Set M) :
    S.Definable LRV {z : Fin 2 ⊕ Fin 2 → M |
      OpenBallCodes.rawBall (z ∘ Sum.inl) = OpenBallCodes.rawBall (z ∘ Sum.inr)} := by
  let left : Fin 3 → (Fin 2 ⊕ Fin 2) ⊕ Fin 1 :=
    ![.inl (.inl 0),.inl (.inl 1),.inr 0]
  let right : Fin 3 → (Fin 2 ⊕ Fin 2) ⊕ Fin 1 :=
    ![.inl (.inr 0),.inl (.inr 1),.inr 0]
  have h := (raw_iff_definable
    ((OpenBallCodes.membership_raw_definable S).preimage_comp left)
    ((OpenBallCodes.membership_raw_definable S).preimage_comp right)).forall_of_finite
  convert h using 1
  ext z
  have hleft (y : Fin 1 → M) : Fin.init (Sum.elim z y ∘ left) = z ∘ Sum.inl := by
    funext i
    fin_cases i <;> rfl
  have hright (y : Fin 1 → M) : Fin.init (Sum.elim z y ∘ right) = z ∘ Sum.inr := by
    funext i
    fin_cases i <;> rfl
  change _ ↔ ∀ y : Fin 1 → M, _
  simp only [Set.mem_preimage,Set.mem_setOf_eq,hleft,hright]
  constructor
  · intro he y
    exact Set.ext_iff.mp he (y 0)
  · intro he
    exact Set.ext (fun x => he (fun _ => x))

theorem exceptionalOpenBalls_definable
    (E : Set (Fin 1 → VF M)) (hE : S.Definable LRV (vfValues '' E))
    (r : VF M) (hr : r ≠ 0) (hrdef : S.Definable₁ LRV {r.val}) :
    S.Definable LRV (OpenBallCodes.pullback (exceptionalOpenBalls E r hr)) := by
  let args (z : Fin 2 ⊕ Fin 1 → M) : Fin 2 ⊕ Fin 2 → M :=
    Sum.elim (z ∘ Sum.inl) ![z (.inr 0),r.val]
  have hargs : S.DefinableMap LRV args := by
    rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact definable_named_constant r.val hrdef
  have h := ((hE.preimage_comp (Sum.inr : Fin 1 → Fin 2 ⊕ Fin 1)).inter
    ((rawOpenBallEquality_definable S).preimage_map hargs)).exists_of_finite
  convert h using 1
  ext q
  change (∃ hq, Quotient.mk _ (⟨q,hq⟩ : OpenBallCodes.Code M) ∈ exceptionalOpenBalls E r hr) ↔
    ∃ a : Fin 1 → M, a ∈ vfValues '' E ∧
      OpenBallCodes.rawBall q = OpenBallCodes.rawBall ![a 0,r.val]
  constructor
  · rintro ⟨hq,a,ha,he⟩
    refine ⟨vfValues a,⟨a,ha,rfl⟩,?_⟩
    exact congrArg OpenBallCodes.underlying he.symm
  · rintro ⟨a,⟨b,hb,rfl⟩,he⟩
    change OpenBallCodes.rawBall q = OpenBallCodes.rawBall ![(b 0).val,r.val] at he
    have hmem : (b 0).val ∈ OpenBallCodes.rawBall q := by
      rw [he]
      exact OpenBallCodes.raw_center_mem _ (pointedOpenBallCode (b 0) r hr).property
    refine ⟨hmem.1,b,hb,?_⟩
    apply OpenBallCodes.underlying_injective
    exact he.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exceptionalOpenBalls_sameRadius
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (r : VF M) (hr : r ≠ 0) :
    SameOpenRadius (G := G) (exceptionalOpenBalls E r hr) r := by
  rintro D ⟨a,ha,rfl⟩
  refine ⟨a 0,?_⟩
  exact OpenBallCodes.ball_eq_open Valued.v hv _ (pointedOpenBallCode (a 0) r hr).property

end DiamondIntegral.Section6.FMT
