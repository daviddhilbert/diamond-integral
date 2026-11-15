import «section 5».FramedRVConstructibility
import «section 3».RVMonomialSyntax

/-! The auxiliary Kummer root set is original-Laurent-base definable.
Its elements are exactly the actual normalized RV roots used in descent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section3
local instance rootDefinabilityStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

def rvUnitTagHom : RationalRVUnits ℂ →* CanonicalRV.RVSort Carrier where
  toFun u := rvTag (some u)
  map_one' := by
    apply Subtype.ext
    rw [RVOperations.one_val]
    rfl
  map_mul' u v := rvTag_mul (some u) (some v)

theorem rvTag_some_pow (u : RationalRVUnits ℂ) (j : ℕ) :
    rvTag (some u) ^ j = rvTag (some (u ^ j)) :=
  (map_pow rvUnitTagHom u j).symm

def originalKummerRoots (N : ℕ+) : DefSet (rawRVSpace (M := Carrier) 1) {c | baseCarrier c} where
  carrier := {r | r 0 ^ (N : ℕ) = rvUnitTagHom (Multiplicative.ofAdd 1, 1)}
  definable := by
    let term := rvIntegerMonomialTerm (fun _ : Fin 1 => (N : ℤ))
    have ht (r : Fin 1 → CanonicalRV.RVSort Carrier) :
        term.realize (rvValues r) = (r 0 ^ (N : ℕ)).val := by
      simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, zpow_natCast] using
        rvIntegerMonomialTerm_realize (fun _ : Fin 1 => (N : ℤ)) r
    have hbase : baseCarrier (rvUnitTagHom (Multiplicative.ofAdd 1, 1)).val :=
      ⟨1, rfl⟩
    have hfun : {c | baseCarrier c}.DefinableFun LRV
        (fun z : Fin 1 → Carrier => term.realize z) :=
      Set.DefinableFun.of_empty term.definableFun_realize
    have hp := hfun.ofPred_eq_const
      (show (rvUnitTagHom (Multiplicative.ofAdd 1, 1)).val ∈ {c | baseCarrier c} from hbase)
    have hd := ((rawRVSpace (M := Carrier) 1).definable_domain {c | baseCarrier c}).inter hp
    change {c | baseCarrier c}.Definable LRV _
    convert hd using 1
    ext z
    constructor
    · rintro ⟨hz, hr⟩
      refine ⟨hz, ?_⟩
      have he := congrArg Subtype.val hr
      rw [← ht, rvValues_decode] at he
      exact he
    · rintro ⟨hz, hr⟩
      refine ⟨hz, ?_⟩
      apply Subtype.ext
      rw [← ht, rvValues_decode]
      exact hr

def originalKummerRootMap (N : ℕ+) (r : KummerRVRoot N) : originalKummerRoots N :=
  ⟨fun _ => rvTag (some r.val), by
    change rvTag (some r.val) ^ (N : ℕ) = _
    rw [rvTag_some_pow, r.property]
    rfl⟩

theorem originalKummerRootMap_bijective (N : ℕ+) : Function.Bijective (originalKummerRootMap N) := by
  constructor
  · intro r s h
    apply Subtype.ext
    have hh := congrArg (fun t : originalKummerRoots N => taggedRVEquiv (t.val 0)) h
    exact Option.some.inj hh
  · intro r
    have hr := r.property
    change r.val 0 ^ (N : ℕ) = rvUnitTagHom (Multiplicative.ofAdd 1, 1) at hr
    have he := rvSort_tag (r.val 0)
    cases hv : rvPart (r.val 0).val with
    | none =>
      have hz : r.val 0 = 0 := by
        apply Subtype.ext
        rw [← he, hv, RVOperations.zero_val]
        rfl
      rw [hz, zero_pow N.ne_zero] at hr
      rw [← rvTag_zero] at hr
      have hh := congrArg taggedRVEquiv hr
      change (none : RV) = some (Multiplicative.ofAdd 1, 1) at hh
      cases hh
    | some u =>
      have hu : r.val 0 = rvTag (some u) := Subtype.ext (he.symm.trans (congrArg Sum.inr hv))
      rw [hu, rvTag_some_pow] at hr
      let root : KummerRVRoot N := ⟨u, Option.some.inj (congrArg taggedRVEquiv hr)⟩
      refine ⟨root, ?_⟩
      apply Subtype.ext
      funext i
      fin_cases i
      exact hu.symm

def originalKummerRootEquiv (N : ℕ+) : KummerRVRoot N ≃ originalKummerRoots N :=
  _root_.Equiv.ofBijective (originalKummerRootMap N) (originalKummerRootMap_bijective N)

end DiamondIntegral.Section5.PuiseuxOriginal
