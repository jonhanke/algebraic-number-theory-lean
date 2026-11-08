import NumberFieldKB.MilneANT.Ch8Extensions
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Discriminant.RamifiedSupport.Hermite

/-!
# Milne, *Algebraic Number Theory*, Theorem 8.42: finitely many extensions of bounded degree unramified outside $S$

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 8.42, p. 151; bib key `milne2020ant`.

**`theorem8_42`** proves the named statement `Theorem8_42` (Ch8Extensions.lean) unconditionally, from Tau Ceti's
`TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset` (ported under `NumberFieldKB/TauCetiPort`;
Tau Ceti `TauCeti/NumberTheory/NumberField/Discriminant/RamifiedSupport/Hermite.lean`). That theorem is Milne's
argument: the different exponent at a prime with ramification index $e$ is at most $e - 1 + v_P(e)$, which bounds
the discriminant of $L$ in terms of $[L:K]$, $S$ and $d_K$, and Hermite's theorem (Mathlib
`NumberField.finite_of_discr_bdd`) finishes.

The bridge: if every prime $\mathfrak p \notin S$ is unramified in $\mathcal O_L$ (Mathlib `Algebra.IsUnramifiedIn`),
then the ramified support of $L/K$ (the primes dividing the relative discriminant, equivalently those with a prime
above of ramification index $> 1$: `mem_ramifiedSupport_iff_exists`) is contained in $S$.
-/

open NumberField IsDedekindDomain Module

namespace NumberFieldKB.MilneANT

/-- If every prime outside $S$ is unramified in $L$, the ramified support of $L/K$ lies in $S$. -/
theorem ramifiedSupport_subset_of_isUnramifiedIn {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ S → Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal) :
    TauCeti.NumberField.ramifiedSupport K L ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨P, hP⟩ := TauCeti.NumberField.mem_ramifiedSupport_iff_exists.mp hv
  have hPp : (P : Ideal (𝓞 L)).IsPrime := P.2.1
  have hPl : (P : Ideal (𝓞 L)).LiesOver v.asIdeal := P.2.2
  have hu := h v hvS (P : Ideal (𝓞 L)) hPp hPl
  have he := (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 K) (p := (P : Ideal (𝓞 L)))).mp hu
  omega

/-- **Theorem 8.42** (proved, unconditionally, from the Tau Ceti port): for a number field $K$, an integer $N$ and a
finite set $S$ of finite primes of $K$, there are only finitely many extensions of $K$ of degree $N$ unramified
outside $S$, up to $K$-isomorphism (as subfields of an algebraic closure). -/
@[kb "milne2020ant" "v3.08, Thm. 8.42, p. 151"]
theorem theorem8_42 : Theorem8_42 where
  finite K _ _ N S := by
    have hT := TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset (K := K) (AlgebraicClosure K) N S
    refine (hT.image Subtype.val).subset ?_
    rintro L ⟨hfd, hN, hun⟩
    haveI : FiniteDimensional K L := hfd
    haveI : NumberField L := NumberField.of_module_finite K L
    exact ⟨⟨L, hfd⟩, ⟨hN.le, ramifiedSupport_subset_of_isUnramifiedIn S hun⟩, rfl⟩

end NumberFieldKB.MilneANT
