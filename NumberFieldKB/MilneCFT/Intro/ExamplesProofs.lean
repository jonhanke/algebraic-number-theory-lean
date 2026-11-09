import NumberFieldKB.MilneCFT.Intro.Examples
import NumberFieldKB.MilneANT.Ch8Examples

/-!
# Proof of Milne, *CFT*, Introduction, Exercise 0.11

For a squarefree `D ≠ 1` and `L = ℚ[√D]`, an odd prime `p ∤ D` splits in `L` iff `D` is a square mod `p`
(`NumberFieldKB.MilneANT.example_8_19`), iff the Jacobi symbol `J(D | p) = 1`, which by `jacobiSym.mod_right` depends
only on `p mod 4|D|`. The subgroup `H` is the kernel of the character `u ↦ J(D | u.val)` on `(ℤ/4|D|)ˣ`.
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- Helper: the underlying natural number of a unit mod `4|D|` is odd. -/
theorem odd_val_unit (D : ℤ) (hD : D ≠ 0) (u : (ZMod (4 * D.natAbs))ˣ) :
    Odd (u : ZMod (4 * D.natAbs)).val := by
  haveI : NeZero (4 * D.natAbs) := ⟨by simpa using hD⟩
  have hc := ZMod.val_coe_unit_coprime u
  have h2 : 2 ∣ 4 * D.natAbs := ⟨2 * D.natAbs, by ring⟩
  rw [← Nat.not_even_iff_odd]
  intro he
  have h3 := Nat.dvd_gcd (even_iff_two_dvd.1 he) h2
  rw [Nat.Coprime.gcd_eq_one hc] at h3
  omega

/-- Helper: the Jacobi character on `(ℤ/4|D|)ˣ`, as a multiplicative map to `ℤ`. -/
def jacChar (D : ℤ) (hD : D ≠ 0) : (ZMod (4 * D.natAbs))ˣ →* ℤ :=
  haveI : NeZero (4 * D.natAbs) := ⟨by simpa using hD⟩
  { toFun := fun u => jacobiSym D (u : ZMod (4 * D.natAbs)).val
    map_one' := by
      have h4 : 1 < 4 * D.natAbs := by
        have : 0 < D.natAbs := Int.natAbs_pos.2 hD
        omega
      haveI := Fact.mk h4
      simp [ZMod.val_one]
    map_mul' := by
      intro u u'
      have hu := odd_val_unit D hD u
      have hu' := odd_val_unit D hD u'
      have hv : ((u * u' : (ZMod (4 * D.natAbs))ˣ) : ZMod (4 * D.natAbs)).val =
          ((u : ZMod (4 * D.natAbs)).val * (u' : ZMod (4 * D.natAbs)).val) % (4 * D.natAbs) := by
        rw [Units.val_mul, ZMod.val_mul]
      show jacobiSym D _ = jacobiSym D _ * jacobiSym D _
      rw [hv, ← jacobiSym.mod_right D (hu.mul hu')]
      have h1 : (u : ZMod (4 * D.natAbs)).val ≠ 0 := hu.pos.ne'
      have h2 : (u' : ZMod (4 * D.natAbs)).val ≠ 0 := hu'.pos.ne'
      exact jacobiSym.mul_right' D h1 h2 }

/-- Helper: the kernel of the Jacobi character. -/
def jacKer (D : ℤ) (hD : D ≠ 0) : Subgroup (ZMod (4 * D.natAbs))ˣ where
  carrier := {u | jacChar D hD u = 1}
  one_mem' := map_one _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]; rfl
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h := congrArg (jacChar D hD) (inv_mul_cancel a)
    rw [map_mul, ha, map_one] at h
    simpa using h

/-- Helper: a squarefree integer `D ≠ 1` is not the square of a rational number. -/
theorem not_rat_sq_of_squarefree (D : ℤ) (hsq : Squarefree D) (hD1 : D ≠ 1) (q : ℚ) :
    q ^ 2 ≠ (D : ℚ) := by
  intro h
  have h1 : IsSquare (D : ℚ) := ⟨q, by rw [← h]; ring⟩
  obtain ⟨k, hk⟩ := Rat.isSquare_intCast_iff.1 h1
  have hu : IsUnit k := hsq k ⟨1, by rw [hk]; ring⟩
  apply hD1
  rw [hk]
  obtain ⟨w, rfl⟩ := hu
  have := Int.isUnit_iff.1 w.isUnit
  rcases this with h | h <;> simp [h]

/-- Helper: the rational prime of `v` is `p` when `v` is the prime ideal `(p)`. -/
theorem ratPrime_eq_of_asIdeal {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)}) : NumberFieldKB.MilneANT.ratPrime v = p := by
  have hmem : (p : 𝓞 ℚ) ∈ v.asIdeal := by rw [hv]; exact Ideal.mem_span_singleton_self _
  have h1 : NumberFieldKB.MilneANT.ratPrime v ∣ p := by
    rw [NumberFieldKB.MilneANT.ratPrime, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), Ideal.apply_mem_of_equiv_iff]
    exact hmem
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1 h1

/-- **Exercise 0.11** (proved; Milne, *CFT*, Introduction): for `L = ℚ[√D]` with `D` squarefree, `D ≠ 1`, whether an
odd prime `p ∤ D` splits in `L` depends only on `p mod 4|D|`, through the subgroup `H = ker (u ↦ J(D | u))` of
`(ℤ/4|D|)ˣ`. Proof: `L/ℚ` is Galois (degree 2) and `√D ∉ ℚ` (a squarefree `D ≠ 1` is not a rational square);
`NumberFieldKB.MilneANT.example_8_19` gives `p` splits iff `D` is a square mod `p`, iff `legendreSym p D = 1`, iff
`jacobiSym D p = 1`; and `jacobiSym.mod_right` shows that this symbol depends only on `p mod 4|D|`. -/
@[kb "milne2020cft" "Introduction, Exercise 0.11"]
theorem exercise011 : Exercise011 := by
  refine ⟨fun D hsq hD1 L _ _ hL ⟨s, hs⟩ => ?_⟩
  have hD : D ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  haveI : NeZero (4 * D.natAbs) := ⟨by simpa using hD⟩
  refine ⟨jacKer D hD, ?_⟩
  intro p hp hp2 hpD v hv
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := ratPrime_eq_of_asIdeal hp v hv
  subst hq
  haveI : IsGalois ℚ L := NumberFieldKB.MilneANT.isGalois_of_finrank_eq_two ℚ L hL
  have hsQ : s ∉ Set.range (algebraMap ℚ L) := by
    rintro ⟨q, rfl⟩
    apply not_rat_sq_of_squarefree D hsq hD1 q
    apply (algebraMap ℚ L).injective
    rw [map_pow, hs]; simp
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) v.asIdeal ⊥
    (by
      rw [Ideal.under_bot]
      exact bot_le)
  haveI : Q.IsPrime := hQp
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  have h819 := (NumberFieldKB.MilneANT.example_8_19 L hL D s hs hsQ v hp2 hpD ⟨Q, hQp, inferInstance⟩).2.2
  set p := MilneANT.ratPrime v with hpdef
  have hd0 : (D : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hJ : jacobiSym D p = 1 ↔ IsSquare (D : ZMod p) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact _root_.legendreSym.eq_one_iff p hd0
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [h819, ← hJ]
  constructor
  · intro h
    have hcop : Nat.Coprime p (4 * D.natAbs) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · have : Nat.Coprime p (2 ^ 2) :=
          Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
        simpa using this
      · exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpD (Int.natCast_dvd.2 hd))
    refine ⟨ZMod.unitOfCoprime p hcop, ?_, ZMod.coe_unitOfCoprime p hcop⟩
    show jacobiSym D (((ZMod.unitOfCoprime p hcop : (ZMod (4 * D.natAbs))ˣ) :
      ZMod (4 * D.natAbs)).val) = 1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← jacobiSym.mod_right D hodd]
    exact h
  · rintro ⟨u, hu, hup⟩
    have hu' : jacobiSym D (u : ZMod (4 * D.natAbs)).val = 1 := hu
    have hval : (u : ZMod (4 * D.natAbs)).val = p % (4 * D.natAbs) := by
      rw [hup, ZMod.val_natCast]
    rw [hval, ← jacobiSym.mod_right D hodd] at hu'
    exact hu'

end NumberFieldKB.MilneCFT
