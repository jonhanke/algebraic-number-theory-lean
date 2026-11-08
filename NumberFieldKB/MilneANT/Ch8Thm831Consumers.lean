import NumberFieldKB.MilneANT.Ch8Thm831
import NumberFieldKB.MilneANT.Ch8Unconditional

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: the natural-density consequences, unconditionally

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

The named statement `Theorem8_31` (Chebotarev, natural density) is proved (`theorem8_31`, `Ch8Thm831.lean`) and so is
`DedekindFrobenius` (`dedekindFrobenius`, `Ch8DedekindProof.lean`). The results of `Ch8Chebotarev.lean` and
`Ch8Dedekind.lean` stated with the hypothesis `h : Theorem8_31` (and `hD : DedekindFrobenius`) therefore hold
unconditionally; they are restated here without hypotheses (primed names).
-/

open NumberField IsDedekindDomain Polynomial
open NumberFieldKB.Chebotarev
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

section Galois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Corollary 8.32**, unconditional: the primes of $K$ that split completely in $L$ have natural density
$1/[L:K]$. -/
@[kb "milne2020ant" "v3.08, Cor. 8.32, p. 147"]
theorem cor_8_32' : HasNaturalDensity (splitPrimes K L) (1 / Module.finrank K L) :=
  cor_8_32 K L theorem8_31

/-- Milne p. 147, unconditional: for abelian $G$ and $\sigma \in G$, the primes with $(\mathfrak p, L/K) = \sigma$
have natural density $1/|G|$. -/
@[kb "milne2020ant" "v3.08, Thm. 8.31 (abelian case), p. 147"]
theorem thm_8_31_abelian' (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (σ : Gal(L/K)) :
    HasNaturalDensity (frobSet K L (ConjClasses.mk σ)) (1 / Nat.card Gal(L/K)) :=
  thm_8_31_abelian K L theorem8_31 hab σ

end Galois

/-- **Example 8.34**, unconditional: each arithmetic progression $k, k+n, k+2n,\dots$ with $\gcd(k, n) = 1$ contains
$1/\varphi(n)$ of the primes (natural density). -/
@[kb "milne2020ant" "v3.08, Ex. 8.34, p. 148"]
theorem example_8_34' (n : ℕ) [NeZero n] (k : ℕ) (hk : k.Coprime n) :
    HasNaturalDensity {v : HeightOneSpectrum (𝓞 ℚ) | (ratPrime v : ZMod n) = k} (1 / n.totient) :=
  example_8_34 theorem8_31 n k hk

/-- **Example 8.35**, unconditional: in a quadratic extension half the primes split and half remain prime (natural
density). -/
@[kb "milne2020ant" "v3.08, Ex. 8.35, p. 148"]
theorem example_8_35' (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    HasNaturalDensity (splitPrimes K L) (1 / 2) ∧ HasNaturalDensity (inertPrimes K L) (1 / 2) :=
  example_8_35 K L theorem8_31 h2

/-- **Densities of factorization types** with natural density, unconditional. -/
@[kb "milne2020ant" "v3.08, Ex. 8.36 and 8.37 (general principle), p. 148"]
theorem factorizationType_hasNaturalDensity' {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) :
    HasNaturalDensity (factorizationTypeSet f τ)
      (Nat.card {σ : (f.map (algebraMap (𝓞 K) K)).Gal //
          (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ} /
        Nat.card (f.map (algebraMap (𝓞 K) K)).Gal) :=
  factorizationType_hasNaturalDensity dedekindFrobenius theorem8_31 f hf hs τ

/-- **Example 8.36**, unconditional: the natural densities of the factorization types of a monic separable cubic
$f \in \mathbb Z[X]$ according to its Galois group (see `example_8_36`). -/
@[kb "milne2020ant" "v3.08, Ex. 8.36, p. 148"]
theorem example_8_36' (f : (𝓞 ℚ)[X]) (hf : f.Monic)
    (h3 : f.natDegree = 3) (hs : (f.map (algebraMap (𝓞 ℚ) ℚ)).Separable) :
    let G := (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal
    (Nat.card G = 1 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) 1) ∧
    (Nat.card G = 2 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 2) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1}) (1 / 2)) ∧
    (Nat.card G = 3 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 3) ∧
      HasNaturalDensity (factorizationTypeSet f {3}) (2 / 3)) ∧
    (Nat.card G = 6 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 6) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1}) (1 / 2) ∧
      HasNaturalDensity (factorizationTypeSet f {3}) (1 / 3)) :=
  example_8_36 dedekindFrobenius theorem8_31 f hf h3 hs

/-- **Example 8.37, the $D_8$ case**, unconditional (see `example_8_37_D8`). -/
@[kb "milne2020ant" "v3.08, Ex. 8.37, p. 148"]
theorem example_8_37_D8' (f : (𝓞 ℚ)[X]) (hf : f.Monic)
    (h4 : f.natDegree = 4) (hs : (f.map (algebraMap (𝓞 ℚ) ℚ)).Separable)
    (hG : Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 8) :
    HasNaturalDensity (factorizationTypeSet f {1, 1, 1, 1}) (1 / 8) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1, 1}) (1 / 4) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 2}) (3 / 8) ∧
      HasNaturalDensity (factorizationTypeSet f {4}) (1 / 4) :=
  example_8_37_D8 dedekindFrobenius theorem8_31 f hf h4 hs hG

end

end NumberFieldKB.MilneANT
