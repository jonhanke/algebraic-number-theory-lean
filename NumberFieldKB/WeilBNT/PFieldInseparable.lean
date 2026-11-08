import NumberFieldKB.WeilBNT.PFieldRamified
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Weil, *Basic Number Theory*, I.§4, Cor. 2 of Prop. 4: purely inseparable extensions

$F$ is a commutative $p$-field of characteristic $p$ (`hF : IsPField F p`, `[CharP F p]`) and $\bar F$ an algebraic
closure (`AlgebraicClosure F`).

* **`weil_I_4_cor2_prop4`**: for every $n\ge0$, $\bar F$ contains one and only one purely inseparable extension of $F$
  of degree $p^n$, namely $F^{p^{-n}}=\{x\in\bar F: x^{p^n}\in F\}$.

*Proof* (Weil's). By Cor. 1 of Prop. 4 (`weil_I_4_cor1_prop4`) $[F:F^p]=p$; transporting by $x\mapsto x^{p^i}$ gives
$[F^{p^i}:F^{p^{i+1}}]=p$, so $[F:F^{p^n}]=p^n$, and $x\mapsto x^{p^n}$ maps $F^{p^{-n}}$ isomorphically onto $F$ and
$F$ onto $F^{p^n}$, so $[F^{p^{-n}}:F]=p^n$. A purely inseparable extension of degree $p^n$ has exponent at most $n$,
so it lies in $F^{p^{-n}}$, and equals it by degree.
-/

open Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

/-- The subfield $\{x\in K: x^{p^n}\in F\}$ of $K$, for an extension $K$ of $F$ (as a `Subfield` of $K$). -/
def rootSubfield (p : ℕ) (F K : Type*) [Field F] [Field K] [Algebra F K] [ExpChar K p] (n : ℕ) : Subfield K :=
  (algebraMap F K).fieldRange.comap (iterateFrobenius K p n)

theorem mem_rootSubfield {p : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] [ExpChar K p] {n : ℕ} {x : K} :
    x ∈ rootSubfield p F K n ↔ ∃ y : F, x ^ (p ^ n) = algebraMap F K y := by
  simp [rootSubfield, Subfield.mem_comap, iterateFrobenius_def, RingHom.mem_fieldRange]
  exact exists_congr fun _ => eq_comm

/-- Base case: $[F^{p^{-1}} : F] = [F : F^p]$. -/
theorem relfinrank_rootSubfield_one {p : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fact p.Prime] [ExpChar F p]
    [ExpChar K p] [PerfectRing K p] (hdeg : Module.finrank (frobenius F p).fieldRange F = p) :
    Subfield.relfinrank (algebraMap F K).fieldRange (rootSubfield p F K 1) = p := by
  have hsurj : Function.Surjective (frobenius K p) := surjective_frobenius K p
  have hE : rootSubfield p F K 1 = (algebraMap F K).fieldRange.comap (frobenius K p) := by
    simp [rootSubfield]
  have h1 : (rootSubfield p F K 1).map (frobenius K p) = (algebraMap F K).fieldRange := by
    rw [hE]; exact Subfield.map_comap_eq_self_of_surjective hsurj _
  have h2 : ((algebraMap F K).fieldRange).map (frobenius K p) =
      (frobenius F p).fieldRange.map (algebraMap F K) := by
    ext z
    simp only [Subfield.mem_map, RingHom.mem_fieldRange]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a ^ p, ⟨a, rfl⟩, by simp [frobenius_def]⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨algebraMap F K a, ⟨a, rfl⟩, by simp [frobenius_def]⟩
  have h3 := Subfield.relfinrank_map_map ((algebraMap F K).fieldRange) (rootSubfield p F K 1)
    (frobenius K p)
  rw [h1, h2] at h3
  rw [← h3]
  have h4 := Subfield.relfinrank_map_map (frobenius F p).fieldRange ⊤ (algebraMap F K)
  rw [Subfield.relfinrank_top_right, hdeg, ← RingHom.fieldRange_eq_map] at h4
  exact h4

/-- $[F^{p^{-n}} : F] = p^n$. -/
theorem relfinrank_rootSubfield {p : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fact p.Prime] [ExpChar F p]
    [ExpChar K p] [PerfectRing K p] (hdeg : Module.finrank (frobenius F p).fieldRange F = p) (n : ℕ) :
    Subfield.relfinrank (algebraMap F K).fieldRange (rootSubfield p F K n) = p ^ n := by
  have hsurj : Function.Surjective (frobenius K p) := surjective_frobenius K p
  induction n with
  | zero =>
    have : rootSubfield p F K 0 = (algebraMap F K).fieldRange := by
      ext x; simp [mem_rootSubfield, RingHom.mem_fieldRange, eq_comm]
    rw [this]; simp
  | succ m ih =>
    have hle1 : (algebraMap F K).fieldRange ≤ rootSubfield p F K 1 := by
      rintro _ ⟨a, rfl⟩
      exact mem_rootSubfield.2 ⟨a ^ p, by simp⟩
    have hle2 : rootSubfield p F K 1 ≤ rootSubfield p F K (m + 1) := by
      intro x hx
      obtain ⟨y, hy⟩ := mem_rootSubfield.1 hx
      rw [pow_one] at hy
      refine mem_rootSubfield.2 ⟨y ^ (p ^ m), ?_⟩
      rw [pow_succ', pow_mul, hy, map_pow]
    have hcomp : rootSubfield p F K (m + 1) = (rootSubfield p F K m).comap (frobenius K p) := by
      ext x
      simp only [mem_rootSubfield, Subfield.mem_comap, frobenius_def]
      rw [pow_succ', pow_mul]
    have hcomp1 : rootSubfield p F K 1 = (algebraMap F K).fieldRange.comap (frobenius K p) := by
      simp [rootSubfield]
    have h5 : Subfield.relfinrank (rootSubfield p F K 1) (rootSubfield p F K (m + 1)) = p ^ m := by
      rw [hcomp, hcomp1, Subfield.relfinrank_comap_comap_eq_relfinrank_of_surjective _ _ _ hsurj]
      exact ih
    have := Subfield.relfinrank_mul_relfinrank hle1 hle2
    rw [h5, relfinrank_rootSubfield_one hdeg] at this
    rw [← this, pow_succ']

/-- **Cor. 2 of Prop. 4.** For every $n$, an algebraic closure of $F$ contains exactly one purely inseparable
extension of $F$ of degree $p^n$: the field $F^{p^{-n}}$ of the $x$ with $x^{p^n}\in F$. -/
@[kb "weil1973bnt" "Ch. I, §4, Cor. 2 of Prop. 4"]
theorem weil_I_4_cor2_prop4 {p : ℕ} {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) [CharP F p] (n : ℕ) :
    ∃ E : IntermediateField F (AlgebraicClosure F),
      (∀ x : AlgebraicClosure F, x ∈ E ↔ ∃ y : F, x ^ (p ^ n) = algebraMap F (AlgebraicClosure F) y) ∧
      Module.finrank F E = p ^ n ∧ IsPurelyInseparable F E ∧
      ∀ E' : IntermediateField F (AlgebraicClosure F), IsPurelyInseparable F E' →
        Module.finrank F E' = p ^ n → E' = E := by
  have : Fact p.Prime := ⟨hF.1⟩
  obtain ⟨π, hπ0, hπ, -⟩ := weil_I_4_thm6_prime hF
  have hdeg : Module.finrank (frobenius F p).fieldRange F = p :=
    (weil_I_4_cor1_prop4 hF hπ0 hπ).1
  set K := AlgebraicClosure F with hK
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  have : ExpChar K p := ExpChar.prime hF.1
  have : PerfectRing K p := PerfectField.toPerfectRing p
  have : ExpChar F p := ExpChar.prime hF.1
  have hrank := relfinrank_rootSubfield (K := K) hdeg n
  have hmem : ∀ x : K, x ∈ rootSubfield p F K n ↔ ∃ y : F, x ^ (p ^ n) = algebraMap F K y :=
    fun x => mem_rootSubfield
  let E : IntermediateField F K :=
    (rootSubfield p F K n).toIntermediateField (fun a => mem_rootSubfield.2 ⟨a ^ (p ^ n), by simp⟩)
  have hEmem : ∀ x : K, x ∈ E ↔ ∃ y : F, x ^ (p ^ n) = algebraMap F K y := fun x => hmem x
  have hfin : Module.finrank F E = p ^ n := by
    rw [← hrank, ← IntermediateField.relfinrank_bot_left]
    rfl
  refine ⟨E, hEmem, hfin, ?_, ?_⟩
  · rw [isPurelyInseparable_iff_pow_mem F p]
    intro x
    obtain ⟨y, hy⟩ := (hEmem x).1 x.2
    exact ⟨n, y, Subtype.ext (by simpa using hy.symm)⟩
  · intro E' hE' hdeg'
    have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfin]; exact pow_pos hF.1.pos _)
    have hle : E' ≤ E := by
      intro x hx
      obtain ⟨m, y, hm⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p (⟨x, hx⟩ : E')
      have hd : p ^ m ∣ p ^ n := by
        rw [← hdeg']
        have := minpoly.degree_dvd (K := F) (x := (⟨x, hx⟩ : E')) (Algebra.IsIntegral.isIntegral _)
        rwa [hm, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow] at this
      have hmn : m ≤ n := (Nat.pow_dvd_pow_iff_le_right hF.1.one_lt).1 hd
      have hpow : (⟨x, hx⟩ : E') ^ (p ^ m) = algebraMap F E' y := by
        have := minpoly.aeval F (⟨x, hx⟩ : E')
        rw [hm] at this
        simpa [sub_eq_zero] using this
      have hpow' : x ^ (p ^ m) = algebraMap F K y := by
        have := congrArg (fun z : E' => (z : K)) hpow
        simpa using this
      refine (hEmem x).2 ⟨y ^ (p ^ (n - m)), ?_⟩
      have hsplit : p ^ n = p ^ m * p ^ (n - m) := by rw [← pow_add, Nat.add_sub_of_le hmn]
      rw [hsplit, pow_mul, hpow', map_pow]
    exact IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hdeg', hfin])

end NumberFieldKB.WeilBNT.FieldModule
