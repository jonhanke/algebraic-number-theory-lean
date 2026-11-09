import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3KummerCup

/-!
# Milne, *Class Field Theory*, Chapter III §4: the pairing $(\chi, b)$, Proposition 4.3

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

**The pairing is the Artin symbol** (`charKummerPairing_eq`): for every invariant system and cup-product family,
$(\chi, b) = \chi(\phi_K(b)|_M)/n$, from the bidegree-$(1,1)$ computation `cup_charClass_kummerClass`, the uniqueness
of the invariant maps and Tau Ceti's character formula. **Proposition 4.3** (left kernel zero) follows from the
surjectivity of the local Artin map onto $\operatorname{Gal}(M/K)^{\mathrm{ab}}$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory MonoidalCategory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable (n : ℕ) [NeZero n]

theorem zmodToQZ_injective : Function.Injective (zmodToQZ n) := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  have hk' : zmodToQZ n (k.val : ZMod n) = 0 := by rwa [ZMod.natCast_zmod_val]
  rw [zmodToQZ_natCast] at hk'
  obtain ⟨z, hz⟩ := (qz_eq_zero_iff _).1 hk'
  have hlt := ZMod.val_lt k
  have hn : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have h0 : (0 : ℚ) ≤ z := by rw [hz]; positivity
  have h1 : (z : ℚ) < 1 := by rw [hz, div_lt_one hn]; exact_mod_cast hlt
  have hz0 : z = 0 := by
    have a : (0 : ℤ) ≤ z := by exact_mod_cast h0
    have b : z < 1 := by exact_mod_cast h1
    omega
  rw [hz0, Int.cast_zero, eq_comm, div_eq_zero_iff] at hz
  have : k.val = 0 := by
    rcases hz with h | h
    · exact_mod_cast h
    · exact absurd h hn.ne'
  exact (ZMod.val_eq_zero k).1 this

/-- **The pairing $(\chi, b)$ is the Artin symbol** (Milne, *CFT*, III, §4, Step 3, p. 112, via Proposition 3.6):
$(\chi, b) = \chi(\phi_K(b)|_M)/n$ for any representative $\sigma \in G_K$ of the local Artin symbol of $b$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §4, Step 3, (χ, b) = χ(φ(b)), p. 112"]
theorem charKummerPairing_eq (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) (χ : Additive Gal(M/K) →+ ZMod n) (β : Mˣ) (b : Kˣ)
    (hb : β ^ n = embUnits M b) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    charKummerPairing n s M c χ β (fixed_of_pow_eq n M hb) =
      zmodToQZ n (χ (Additive.ofMul ((embM M).restrictNormalHom
        (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)))) := by
  unfold charKummerPairing
  rw [cup_charClass_kummerClass n M c χ β b hb, s.invK_eq_tcInvK]
  erw [tcInvK_apply, toBr_powHom_carryZ]
  rw [invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ b σ hσ]
  simp [toCircle]

/-- Every element of $\operatorname{Gal}(M/K)$ has the same abelianization class as the restriction of a local Artin
symbol (Tau Ceti `surjective_localArtinMap`, `artinMap_restrict`). -/
theorem exists_artin_restrict (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (g : Gal(M/K)) : ∃ (b : Kˣ) (σ : Field.absoluteGaloisGroup K),
      (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b ∧
      Abelianization.of ((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)) =
        Abelianization.of g := by
  obtain ⟨b, hb⟩ := surjective_localArtinMap K M (embM M) (Additive.ofMul (Abelianization.of g))
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K (Additive.toMul b))
  refine ⟨Additive.toMul b, σ, hσ, ?_⟩
  have := artinMap_restrict K M (embM M) (Additive.toMul b) σ hσ
  rw [ofMul_toMul, hb] at this
  exact (Additive.ofMul.injective this).symm

/-- A character to an abelian group takes equal values on elements with equal abelianization class. -/
theorem char_eq_of_abelianization {G : Type} [Group G] {A : Type} [AddCommGroup A] (χ : Additive G →+ A)
    {g g' : G} (h : Abelianization.of g = Abelianization.of g') :
    χ (Additive.ofMul g) = χ (Additive.ofMul g') := by
  let χm : G →* Multiplicative A :=
    { toFun := fun g => Multiplicative.ofAdd (χ (Additive.ofMul g))
      map_one' := by simp
      map_mul' := fun a b => by simp [ofMul_mul] }
  have := congrArg (Abelianization.lift χm) h
  simp only [Abelianization.lift_apply_of] at this
  exact Multiplicative.ofAdd.injective this

variable (K Ω) in
/-- **Proposition 4.3** (Milne, *CFT*, III, p. 112), proved unconditionally: the left kernel of the pairing
$(\chi, b)$ is zero. Milne's proof: $(\chi, b) = \chi(\phi_K(b))$ (Proposition 3.6) and the Artin symbols exhaust
$\operatorname{Gal}(M/K)^{\mathrm{ab}}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 4.3, p. 112"]
theorem prop4_3 : Prop4_3 K Ω := by
  refine ⟨fun n _ _ s M _ _ c hroots χ hχ => ?_⟩
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨b, σ, hσ, hab⟩ := exists_artin_restrict M (Additive.toMul x)
  obtain ⟨β, hβ⟩ := hroots b
  have h0 := hχ b β hβ
  rw [charKummerPairing_eq n s M c χ β b hβ σ hσ] at h0
  have h1 := (zmodToQZ_injective n) (h0.trans (map_zero _).symm)
  rw [char_eq_of_abelianization χ hab, ofMul_toMul] at h1
  rw [h1, AddMonoidHom.zero_apply]

end NumberFieldKB.MilneCFT.Ch3
