import NumberFieldKB.Chebotarev.Statements
import NumberFieldKB.Ideles.RelativeNorm

/-!
# The Chebotarev density theorem, unconditionally

The only named input of the Chebotarev formalization was `IdelicNormInput` (`DirichletHecke.lean`): every number field
`K` has an idelic norm $N_{K/\mathbb Q} : C_K\to C_{\mathbb Q}$ with its local description (`IdelicNorm K`). It is
proved here:

* **`idelicNorm K : IdelicNorm K`**: the relative norm of idele classes `ideleClassRelNorm` for $K/\mathbb Q$
  (`NumberFieldKB/Ideles/RelativeNorm.lean`, built from QuadFormsKB's adelic norm $\det M(y)$), the place
  $p$ = `underPlace` below $\mathfrak p$, $f = f(\mathfrak p\mid p)$ (Mathlib's `Ideal.inertiaDeg`), with
  $N\mathfrak p = p^f$ (`absNorm_eq_pow_inertiaDeg`) and the local description
  (`ideleClassRelNorm_ofAdicCompletion`, `valued_localNorm`);
* **`idelicNormInput : IdelicNormInput`**;
* the headlines without the input: **`chebotarev_unconditional`** (Milne, *ANT* Theorem 8.31, Dirichlet density) and
  **`splitPrimes_hasDirichletDensity_unconditional`** (Milne 8.32). The conditional versions `chebotarev` and
  `splitPrimes_hasDirichletDensity` (`Statements.lean`) are kept unchanged.
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Ideles QuadFormsKB.Tamagawa.Measure.Weil

namespace NumberFieldKB.Chebotarev

noncomputable section

/-- **The idelic norm $N_{K/\mathbb Q}$ of a number field**, with its local description: the relative norm of idele
classes for $K/\mathbb Q$ in the basis `Module.finBasis ℚ K`; at a finite place $\mathfrak p$ the place below is
`underPlace` and $f = f(\mathfrak p\mid p)$. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on I_L and C_L) [unverified locator]"]
def idelicNorm (K : Type) [Field K] [NumberField K] : IdelicNorm K where
  toHom := ideleClassRelNorm (Module.finBasis ℚ K)
  place v := underPlace (k := ℚ) v
  inertiaDeg v := v.asIdeal.inertiaDeg (𝓞 ℚ)
  absNorm_eq v := absNorm_eq_pow_inertiaDeg v
  map_ofAdicCompletion v u :=
    ⟨localNorm (Module.finBasis ℚ K) v u, ideleClassRelNorm_ofAdicCompletion _ v u,
      valued_localNorm _ v u⟩

/-- **The named input `IdelicNormInput` holds**: every number field has an idelic norm with its local description. -/
@[kb "neukirch1999" "Ch. VI, §2 (the norm of ideles, N_{L|K} on I_L and C_L) [unverified locator]"]
theorem idelicNormInput : IdelicNormInput := ⟨fun K _ _ => ⟨idelicNorm K⟩⟩

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Chebotarev density theorem**, unconditional (Milne, *ANT* Theorem 8.31, here with Dirichlet density): for
$L/K$ a finite Galois extension of number fields and $C$ a conjugacy class of $G = \mathrm{Gal}(L/K)$, the primes of
`K` unramified in `L` with Frobenius class $C$ have Dirichlet density $|C|/|G|$. *Proof:* `chebotarev` with the input
`idelicNormInput`. -/
@[kb "neukirch1999" "Ch. VII, §13 (Chebotarev's density theorem, Dirichlet density) [unverified locator]; Milne, ANT, Theorem 8.31 [unverified locator]"]
theorem chebotarev_unconditional (C : ConjClasses Gal(L/K)) :
    (frobSet K L C).HasDirichletDensity (Nat.card C.carrier / Nat.card Gal(L/K)) :=
  chebotarev K L idelicNormInput C

/-- **Milne 8.32**, unconditional: the primes of `K` that split completely in the finite Galois extension `L` have
Dirichlet density $1/[L:K]$. -/
@[kb "neukirch1999" "Ch. VII, §13 (density of the completely split primes) [unverified locator]; Milne, ANT, Corollary 8.32 [unverified locator]"]
theorem splitPrimes_hasDirichletDensity_unconditional :
    (splitPrimes K L).HasDirichletDensity (1 / Module.finrank K L) :=
  splitPrimes_hasDirichletDensity K L idelicNormInput

end

end NumberFieldKB.Chebotarev
