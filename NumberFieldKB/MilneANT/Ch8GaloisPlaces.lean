import NumberFieldKB.MilneANT.Ch7Places

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: the Galois action on primes (places)

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 141; bib key `milne2020ant`.

**Definition in prose** (p. 141). Let $L/K$ be an extension with group $G = \operatorname{Aut}(L/K)$. For
$\sigma \in G$ and a prime (place) $w$ of $L$, $\sigma w$ is the prime with
$\lvert a \rvert_{\sigma w} = \lvert \sigma^{-1} a \rvert_w$. This is an action of $G$ on the primes of $L$
(`MilnePlace.instMulAction`), and it maps the primes over a prime $v$ of $K$ to themselves
(`MilnePlace.liesOver_smul_iff`).

Primes are Milne's: equivalence classes of nontrivial absolute values (`MilnePlace`, `Ch7Places.lean`), so the
action covers finite and infinite primes at once. (Mathlib has the action on infinite places only,
`NumberField.InfinitePlace`, and on prime ideals by pointwise action.)
-/

namespace NumberFieldKB.MilneANT

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- $\lvert a \rvert_{\sigma w} = \lvert \sigma^{-1} a \rvert_w$, on absolute values. -/
def AbsoluteValue.galoisSMul (σ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := (σ.symm : L ≃ₐ[K] L).toRingEquiv.toRingHom) σ.symm.injective

@[simp]
theorem AbsoluteValue.galoisSMul_apply (σ : L ≃ₐ[K] L) (w : AbsoluteValue L ℝ) (a : L) :
    AbsoluteValue.galoisSMul σ w a = w (σ.symm a) := rfl

theorem AbsoluteValue.galoisSMul_isNontrivial (σ : L ≃ₐ[K] L) {w : AbsoluteValue L ℝ}
    (hw : w.IsNontrivial) : (AbsoluteValue.galoisSMul σ w).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := hw
  refine ⟨σ x, by simpa using hx0, ?_⟩
  simpa using hx1

theorem AbsoluteValue.galoisSMul_isEquiv (σ : L ≃ₐ[K] L) {v w : AbsoluteValue L ℝ}
    (h : v.IsEquiv w) : (AbsoluteValue.galoisSMul σ v).IsEquiv (AbsoluteValue.galoisSMul σ w) :=
  fun x y => h (σ.symm x) (σ.symm y)

/-- **Galois action on primes** (prose definition, Milne p. 141): $\sigma w$ is the class of
$a \mapsto \lvert \sigma^{-1} a \rvert_w$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, definition in prose (the action of G on the primes of L), p. 141"]
def MilnePlace.galoisSMul (σ : L ≃ₐ[K] L) : MilnePlace L → MilnePlace L :=
  Quotient.lift (s := absValueSetoid L)
    (fun w => (Quotient.mk (absValueSetoid L)
      ⟨AbsoluteValue.galoisSMul σ w.1, AbsoluteValue.galoisSMul_isNontrivial σ w.2⟩ : MilnePlace L))
    (fun _ _ h => Quotient.sound (AbsoluteValue.galoisSMul_isEquiv σ h))

theorem MilnePlace.galoisSMul_mk (σ : L ≃ₐ[K] L) (w : {v : AbsoluteValue L ℝ // v.IsNontrivial}) :
    MilnePlace.galoisSMul σ (Quotient.mk (absValueSetoid L) w) =
      Quotient.mk (absValueSetoid L)
        ⟨AbsoluteValue.galoisSMul σ w.1, AbsoluteValue.galoisSMul_isNontrivial σ w.2⟩ := rfl

/-- The Galois group acts on the primes of $L$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, definition in prose (the action of G on the primes of L), p. 141"]
instance MilnePlace.instMulAction : MulAction (L ≃ₐ[K] L) (MilnePlace L) where
  smul := MilnePlace.galoisSMul
  one_smul w := by
    induction w using Quotient.inductionOn with
    | h w =>
      show MilnePlace.galoisSMul 1 (Quotient.mk (absValueSetoid L) w) = Quotient.mk (absValueSetoid L) w
      rw [MilnePlace.galoisSMul_mk]
      exact congrArg _ (Subtype.ext (AbsoluteValue.ext fun a => rfl))
  mul_smul σ τ w := by
    induction w using Quotient.inductionOn with
    | h w =>
      show MilnePlace.galoisSMul (σ * τ) (Quotient.mk (absValueSetoid L) w) =
        MilnePlace.galoisSMul σ (MilnePlace.galoisSMul τ (Quotient.mk (absValueSetoid L) w))
      rw [MilnePlace.galoisSMul_mk, MilnePlace.galoisSMul_mk, MilnePlace.galoisSMul_mk]
      exact congrArg _ (Subtype.ext (AbsoluteValue.ext fun a => rfl))

theorem MilnePlace.smul_def (σ : L ≃ₐ[K] L) (w : MilnePlace L) : σ • w = MilnePlace.galoisSMul σ w := rfl

/-- $G$ acts on the primes of $L$ lying over a fixed prime $v$ of $K$: $\sigma w \mid v$ iff $w \mid v$. -/
@[kb "milne2020ant" "v3.08, Ch. 8, p. 141 (G acts on the primes of L over a prime of K)"]
theorem MilnePlace.liesOver_smul_iff (σ : L ≃ₐ[K] L) (w : MilnePlace L) (v : MilnePlace K) :
    (σ • w).LiesOver v ↔ w.LiesOver v := by
  induction w using Quotient.inductionOn with
  | h w =>
    induction v using Quotient.inductionOn with
    | h v =>
      show (AbsoluteValue.restrictMilne (K := K) (L := L) (AbsoluteValue.galoisSMul σ w.1)).IsEquiv v.1 ↔
        (AbsoluteValue.restrictMilne (K := K) (L := L) w.1).IsEquiv v.1
      have : AbsoluteValue.restrictMilne (K := K) (L := L) (AbsoluteValue.galoisSMul σ w.1) =
          AbsoluteValue.restrictMilne (K := K) (L := L) w.1 := by
        ext x
        simp [AbsoluteValue.restrictMilne]
      rw [this]

end NumberFieldKB.MilneANT
